/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.WeakMemory.X86TSOSequentialConsistency

/-!
# Clients of the immediate-flush simulation

Finite proof examples for the mathematical labelled interface: a read controls which store is
issued, and a lock guard distinguishes enqueue from immediate propagation. No hardware tests.
-/

namespace Cslib.Semantics.WeakMemory.X86TSO.SC.Tests

private abbrev E := Option (Label Bool Bool Bool)
private abbrev Mem := Storage Bool Bool Bool
private abbrev tso := abstractMachine Bool Bool Bool
private def initial : Mem := ⟨fun _ => false, none⟩
private def put (s : Mem) (a v : Bool) : Mem := { s with memory := Function.update s.memory a v }

private inductive PC where
  | start | again | load | loaded (reg : Bool) | taken | other | halt (reg : Bool)

private inductive Move : PC → E → PC → Prop where
  | first : Move .start (some (.write false false true)) .again
  | second : Move .again (some (.write true false true)) .load
  | read (v : Bool) : Move .load (some (.read false false v)) (.loaded v)
  | branch (v : Bool) : Move (.loaded v) none (if v then .taken else .other)
  | taken : Move .taken (some (.write true true true)) (.halt true)
  | other : Move .other (some (.mfence false)) (.halt false)

private def client : LTS PC E := ⟨Move⟩
private def raw : List E := [some (.write false false true), some (.write true false true),
  some (.read false false true), none, some (.write true true true)]
private def labels : List (Label Bool Bool Bool) := [.write false false true,
  .write true false true, .read false false true, .write true true true]
private def once := put initial false true
private def twice := put once false true
private def result := put twice true true
private def done : PC → Prop
  | .halt _ => True
  | _ => False

-- The second writer stores the same value already in memory. Even it gets its own flush.
private theorem run : (coupled client storageMachine).MTr (.start, initial) raw
    (.halt true, result) := by
  refine .stepL (s2 := (PC.again, once)) ⟨Move.first, StorageStep.write (.inl rfl)⟩ ?_
  refine .stepL (s2 := (PC.load, twice)) ⟨Move.second, StorageStep.write (.inl rfl)⟩ ?_
  refine .stepL (s2 := (PC.loaded true, twice)) ⟨Move.read true, StorageStep.read (.inl rfl)⟩ ?_
  refine .stepL (s2 := (PC.taken, twice)) ⟨Move.branch true, rfl⟩ ?_
  exact .stepL (s2 := (PC.halt true, result)) ⟨Move.taken, StorageStep.write (.inl rfl)⟩ .refl

example : (coupled client tso).MTr (.start, initial.embed)
    [some (.write false false true), some (.flush false), some (.write true false true),
     some (.flush true), some (.read false false true), none, some (.write true true true),
     some (.flush true)] (.halt true, result.embed) := mTr_immediate client run

example : Outcome client tso done (.start, initial.embed) labels (.halt true, result.embed) :=
  outcome_of_sc client ⟨True.intro, raw, run, rfl⟩

example : result.embed.memory false = true ∧ result.embed.memory true = true ∧
    (∀ p, result.embed.buffers p = []) ∧ result.embed.lockOwner = none := by decide +revert

-- The program would accept a false read, but storage cannot supply it at this point.
example (d : PC × Mem) : ¬ (coupled client storageMachine).Tr (.load, twice)
    (some (.read false false false)) d := by
  intro h
  have hs : StorageStep twice (.read false false false) d.2 := h.2
  cases hs

-- Starting instead at the same load with initially false memory takes the other branch.
example : (coupled client tso).MTr (.load, initial.embed)
    [some (.read false false false), none, some (.mfence false)] (.halt false, initial.embed) := by
  apply mTr_immediate client (es := [some (.read false false false), none, some (.mfence false)])
    (c := (.load, initial)) (d := (.halt false, initial))
  refine .stepL (s2 := (PC.loaded false, initial)) ⟨Move.read false, StorageStep.read (.inl rfl)⟩ ?_
  refine .stepL (s2 := (PC.other, initial)) ⟨Move.branch false, rfl⟩ ?_
  exact .stepL (s2 := (PC.halt false, initial)) ⟨Move.other, StorageStep.mfence ..⟩ .refl

private def held : Mem := { initial with lockOwner := some true }
private def script : LTS (List E) E := ⟨fun before event after => before = event :: after⟩

-- The program consumes each listed instruction exactly once. The foreign fence is legal.
private def guardCode : List E := [some (.acquire true), some (.write true true false),
  some (.mfence false), some (.release true)]

example : (coupled script tso).MTr (guardCode, initial.embed)
    [some (.acquire true), some (.write true true false), some (.flush true), some (.mfence false),
     some (.release true)] ([], (put initial true false).embed) := by
  apply mTr_immediate script (es := guardCode) (c := (guardCode, initial))
    (d := ([], put initial true false))
  refine .stepL (s2 := (_, held)) ⟨rfl, StorageStep.acquire rfl⟩ ?_
  refine .stepL (s2 := (_, put held true false)) ⟨rfl, StorageStep.write (.inr rfl)⟩ ?_
  refine .stepL (s2 := (_, put held true false)) ⟨rfl, StorageStep.mfence ..⟩ ?_
  exact .stepL (s2 := (([] : List E), put initial true false)) ⟨rfl, StorageStep.release rfl⟩ .refl

-- No initial/final free-lock assumption, including the zero-instruction case.
example : Outcome script tso (· = []) ([], held.embed) [] ([], held.embed) :=
  outcome_of_sc script (c := ([], held)) (d := ([], held)) ⟨rfl, [], .refl, rfl⟩

example (t : Mem) : ¬ StorageStep held (.write false true true) t := by
  intro h
  cases h with | write ok => simp [held] at ok

example (t : Mem) : ¬ StorageStep held (.release false) t := by
  intro h
  cases h with | release owns => simp [held] at owns

example (t : Mem) : ¬ StorageStep held (.acquire false) t := by
  intro h
  cases h with | acquire free => simp [held] at free

private def queued : State Bool Bool Bool := { held.embed with
  buffers := Function.update held.embed.buffers false (held.embed.buffers false ++ [(true, true)]) }

example : tso.Tr held.embed (.write false true true) queued := Step.write ..

example (t : State Bool Bool Bool) : ¬ tso.Tr queued (.flush false) t := by
  intro h
  change Step _ _ _ at h
  cases h with | flush ok _ => simp [State.NotBlocked, queued, Storage.embed, held] at ok

end Cslib.Semantics.WeakMemory.X86TSO.SC.Tests
