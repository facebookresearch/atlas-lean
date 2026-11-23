/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Languages.Congruences.HopcroftWorkTimeM

/-!
# Consumers of the complete Hopcroft predecessor-work bound

These checks exercise the actual initialized execution, a waiting-block
replacement, predecessor multiplicity, empty preimages, empty alphabets,
one-state DFAs, and the impossibility of a zero-state DFA. All executable
checks use kernel `decide`, not native evaluation as a proof.
-/

namespace DFA.Hopcroft.WorkTests

private def splitDFA : DFA Unit (Fin 3) where
  step q _ := if q = 2 then 2 else 0
  start := 0
  accept := {0}

private instance : DecidablePred (· ∈ splitDFA.accept) :=
  fun q => inferInstanceAs (Decidable (q ∈ ({0} : Set (Fin 3))))

/-- The complete trace includes an empty-preimage pop, which still costs
one unit. The two sources going to `0` both contribute to the first pop. -/
example :
    hopcroftSplitters splitDFA 4 (initP splitDFA) (initW splitDFA) =
      [({0}, ()), ({1}, ())] ∧
    hopcroftCost splitDFA
      (hopcroftSplitters splitDFA 4 (initP splitDFA) (initW splitDFA)) = 4 ∧
    splitDFA.hopcroftLoop 4 (initP splitDFA) (initW splitDFA) =
      ([{0}, {1}, {2}], []) := by
  decide

/-- A client can use the total theorem without supplying a halving chain
or any amortized-cost assumption. -/
example (k : ℕ) :
    hopcroftCost splitDFA
      (hopcroftSplitters splitDFA k (initP splitDFA) (initW splitDFA)) ≤
        2 * 1 * 3 * (Nat.log 2 3 + 1) :=
  hopcroftCost_init_trace_le splitDFA k

private def replacementDFA : DFA (Fin 2) (Fin 4) where
  step q a := if a = 0 then (if q = 0 ∨ q = 2 then 0 else 2) else 0
  start := 0
  accept := {0, 1}

private instance : DecidablePred (· ∈ replacementDFA.accept) :=
  fun q => inferInstanceAs (Decidable (q ∈ ({0, 1} : Set (Fin 4))))

/-- While letter `0` is processed, the pending letter-`1` entry is
replaced by BOTH halves. Nonpending entries add only the smaller half. -/
example :
    initW replacementDFA = [({0, 1}, 0), ({0, 1}, 1)] ∧
    replacementDFA.hopcroftLoop 1 (initP replacementDFA)
      (initW replacementDFA) =
        ([{0}, {1}, {2}, {3}],
          [({0}, 0), ({0}, 1), ({1}, 1), ({2}, 0), ({2}, 1)]) := by
  decide

/-- The entire instrumented run performs sixteen charged events and
returns the same four singleton blocks, with its waiting list exhausted. -/
example :
    (hopcroftLoopWork replacementDFA 10 (initP replacementDFA)
      (initW replacementDFA)).ret = ([{0}, {1}, {2}, {3}], []) ∧
    (hopcroftLoopWork replacementDFA 10 (initP replacementDFA)
      (initW replacementDFA)).time = 16 := by
  decide

/-- The uniform logarithmic bound is available on the executable
instrumentation, not merely on an externally supplied halving chain. -/
example (k : ℕ) :
    (hopcroftLoopWork replacementDFA k (initP replacementDFA)
      (initW replacementDFA)).time ≤ 4 * 2 * 4 * Nat.log 2 4 := by
  rw [hopcroftLoopWork_time]
  exact hopcroftCost_init_trace_le_log replacementDFA k (by decide)

/-- The returned partition has the original minimization semantics. -/
example : ∀ p q : Fin 4,
    Rel (hopcroftLoopWork replacementDFA 10 (initP replacementDFA)
      (initW replacementDFA)).ret.1 p q ↔
        replacementDFA.acceptsFrom p = replacementDFA.acceptsFrom q := by
  have hret := hopcroftLoopWork_complete_ret replacementDFA
  norm_num at hret
  rw [hopcroftLoopWork_ret, hret]
  exact fun _ _ => (inv_hopcroftPartition replacementDFA).rel_iff

private def emptyAlphabetDFA : DFA (Fin 0) (Fin 2) where
  step _ a := Fin.elim0 a
  start := 0
  accept := {0}

private instance : DecidablePred (· ∈ emptyAlphabetDFA.accept) :=
  fun q => inferInstanceAs (Decidable (q ∈ ({0} : Set (Fin 2))))

/-- There are two initial blocks but no letters, hence no work. -/
example (k : ℕ) :
    hopcroftCost emptyAlphabetDFA (hopcroftSplitters emptyAlphabetDFA k
      (initP emptyAlphabetDFA) (initW emptyAlphabetDFA)) = 0 :=
  hopcroftCost_eq_zero_of_alphabet_card_eq_zero emptyAlphabetDFA k rfl

/-- Every one-state DFA, accepting or rejecting, has zero popped work.
The theorem makes no positive `log₂ 1` claim. -/
example {α : Type*} [Fintype α] [FinEnum α] (M : DFA α Unit)
    [DecidablePred (· ∈ M.accept)] (k : ℕ) :
    hopcroftCost M (hopcroftSplitters M k (initP M) (initW M)) = 0 :=
  hopcroftCost_eq_zero_of_card_le_one M k (by decide)

/-- A zero-state DFA cannot exist: the canonical carrier has a start state. -/
example {α : Type*} (M : DFA α (Fin 0)) : False := Fin.elim0 M.start

/-- Multiplicity is not erased from the accounting. Replacing a
multiply queued parent emits one token per state/letter, not one per copy. -/
example :
    let W : List (Finset (Fin 4) × Fin 2) := [({0, 1}, 0), ({0, 1}, 0)]
    splitterCount 0 0 W = 2 ∧
      splitterCount 0 0 (newSplitters W {0} {0, 1}) = 1 := by
  decide

/-- A pending replacement can retain the larger half: its token is
inherited, not falsely charged as a new halving event. -/
example :
    let D : Finset (Fin 5) := Finset.univ
    let W : List (Finset (Fin 5) × Unit) := [(D, ())]
    ({1, 2, 3, 4}, ()) ∈ newSplitters W {0} D ∧
      splitterCount 1 () (newSplitters W {0} D) = 1 ∧
      ¬2 * ({1, 2, 3, 4} : Finset (Fin 5)).card ≤ D.card := by
  decide

/-- Zero fuel charges nothing and leaves the execution state untouched. -/
example :
    (hopcroftLoopWork replacementDFA 0 (initP replacementDFA)
      (initW replacementDFA)).time = 0 ∧
    (hopcroftLoopWork replacementDFA 0 (initP replacementDFA)
      (initW replacementDFA)).ret =
        (initP replacementDFA, initW replacementDFA) := ⟨rfl, rfl⟩

end DFA.Hopcroft.WorkTests
