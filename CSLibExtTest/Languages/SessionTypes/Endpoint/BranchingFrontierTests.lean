/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.GlobalProgress
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant

/-!
# Connected sequential central-node branching frontier

One actor sends first to peer A and then peer B. It is one sequential prefix
body owning both subjects, not an artificial grouping of independent actors.
-/

namespace Cslib.SessionTypes.Endpoint.BranchingFrontierTests

open PiCalculus

def a : Key := ⟨.var 1, .positive⟩
def b : Key := ⟨.var 0, .positive⟩
def ca : Capability := ⟨0, .sendName .done⟩
def cb : Capability := ⟨1, .sendName .done⟩
def centralContext : Context := (Finmap.singleton a ca).insert b cb

def central : Proc := .out a.name (.const 7) (.out b.name (.const 8) .nil)
def peerA : Proc := .inp a.name .nil
def peerB : Proc := .inp b.name .nil
def frontier : Proc := .par central (.par peerA peerB)

theorem central_ranked : RankedType 2 centralContext central := by
  apply RankedType.outName (e := a) (c := ca) (s := .done)
  · intro e c hc ha he
    by_cases heb : e = b
    · subst e
      rw [centralContext, Finmap.lookup_insert] at hc
      cases hc
      exact Nat.zero_lt_one
    · rw [centralContext, Finmap.lookup_insert_of_ne _ heb] at hc
      have hea := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
      exact False.elim (he hea)
  · rw [centralContext, Finmap.lookup_insert_of_ne _ (by decide : a ≠ b)]
    exact Finmap.lookup_singleton_eq
  · rfl
  · change 1 < 2
    decide
  · trivial
  · rw [centralContext, Finmap.insert_insert_of_ne (s := (Finmap.singleton a ca : Context))
      (a := b) (a' := a) (by decide), Finmap.insert_singleton_eq]
    apply RankedType.outName (e := b) (c := cb) (s := .done)
    · intro e c hc ha he
      by_cases heb : e = b
      · exact False.elim (he heb)
      · rw [Finmap.lookup_insert_of_ne _ heb] at hc
        have hea := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
        subst e
        rw [Finmap.lookup_singleton_eq] at hc
        cases hc
        exact False.elim (ha rfl)
    · exact Finmap.lookup_insert _
    · rfl
    · exact Nat.zero_lt_succ 1
    · trivial
    · rw [Finmap.insert_insert]
      apply RankedType.nil_of_hasType
      apply HasType.nil_insert (HasType.nil_singleton (by change 1 < 2; decide)) rfl
      exact Nat.zero_lt_succ 1

private theorem peer_ranked (e : Key) (c : Capability) (hs : c.protocol.unfold = .recvName .done)
    (he : e.name.ClosedAt 2) : RankedType 2 (Finmap.singleton e c) (.inp e.name .nil) := by
  apply RankedType.inpName (e := e) (c := c) (s := .done)
  · exact guardMin_singleton _ _
  · exact Finmap.lookup_singleton_eq
  · exact hs
  · exact he
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact RankedType.nil_of_hasType (HasType.nil_singleton he.lift)

/-- The binder context connects the ONE sequential central owner to two peers. -/
theorem branching_context : Context.bind cb (Context.bind ca ∅) =
    centralContext ∪ (Finmap.singleton a.opposite ca.dual ∪ Finmap.singleton b.opposite cb.dual) := by
  apply Finmap.ext
  change
    ({⟨b.opposite, cb.dual⟩} + {⟨b, cb⟩} + {⟨a.opposite, ca.dual⟩} + {⟨a, ca⟩} :
      Multiset (Sigma (fun _ : Key => Capability))) =
    ({⟨b, cb⟩} + {⟨a, ca⟩} + ({⟨a.opposite, ca.dual⟩} + {⟨b.opposite, cb.dual⟩}))
  ac_rfl

/-- Genuine rank0<1 sequential fan-out, not independent parallel components. -/
theorem branching_ranked : RankedType 2 (Context.bind cb (Context.bind ca ∅)) frontier := by
  rw [branching_context]
  apply RankedType.par
  · simp [Finmap.Disjoint, Finmap.mem_union, Finmap.mem_insert, Finmap.mem_singleton,
      centralContext, a, b, Key.opposite, Role.opposite]
  · exact central_ranked
  · apply RankedType.par
    · simp [Finmap.Disjoint, Finmap.mem_singleton, a, b, Key.opposite, Role.opposite]
    · exact peer_ranked a.opposite ca.dual rfl (by change 1 < 2; decide)
    · exact peer_ranked b.opposite cb.dual rfl (Nat.zero_lt_succ 1)

/-- GENERAL progress is invoked on the whole balanced branching frontier;
no caller complementary-pair or enabled-edge witness is supplied. -/
theorem branching_frontier_progress : Cong frontier .nil ∨ ∃ q, PiCalculus.Step frontier q :=
  (GuardFrontier.par (GuardFrontier.out _ _ _)
    (GuardFrontier.par (GuardFrontier.inp _ _) (GuardFrontier.inp _ _))).progress
    branching_ranked ((balanced_empty.bind ca).bind cb)

/-- The whole connected branching frontier gets an ACTUAL Step from the
GENERAL theorem; exposed peers show it cannot be process-completed. -/
theorem branching_actual_step : ∃ q, PiCalculus.Step frontier q := by
  rcases branching_frontier_progress with hc | hs
  · have hin : HasUnguardedInput frontier := Or.inr (Or.inl trivial)
    exact False.elim ((input_cong hc).mp hin)
  · exact hs

def network : Proc := .nu (.nu frontier)

/-- Actual two bound channels give the sequential central actor/peers an
empty external interface. Neither independent actor regrouping nor a ready
pair is part of the admission judgement. -/
theorem branching_closed_ranked : RankedType 0 ∅ network :=
  RankedType.nu (c := ca) (RankedType.nu (c := cb) branching_ranked)

/-- GENERAL GLOBAL progress on the genuinely connected, ν-closed fan-out. -/
theorem branching_global_progress : Cong network .nil ∨ ∃ q, PiCalculus.Step network q :=
  branching_closed_ranked.progress_empty

/-- The closed fan-out has an actual Step derived from the GENERAL theorem,
not from the manually presented central/peer guard syntax. -/
theorem branching_global_actual_step : ∃ q, PiCalculus.Step network q := by
  rcases branching_global_progress with hc | hs
  · have hin : HasUnguardedInput network := Or.inr (Or.inl trivial)
    exact False.elim ((input_cong hc).mp hin)
  · exact hs

/-- The stronger GENERAL balanced-interface theorem also covers its open body. -/
theorem branching_body_global_progress : Cong frontier .nil ∨ ∃ q, PiCalculus.Step frontier q :=
  branching_ranked.progress_balanced ((balanced_empty.bind ca).bind cb)

end Cslib.SessionTypes.Endpoint.BranchingFrontierTests
