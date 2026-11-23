/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovEquivalence

/-!
# Tests for Chickering's covered-reversal characterization

* On `Fin 3`, the chains `0 → 1 → 2` and `0 ← 1 ← 2` (same skeleton, no v-structures) are
  connected by covered-edge reversals, obtained from
  `reflTransGen_coveredReversal_of_markovEquivalent`.
* The collider `0 → 1 ← 2` and the chain `0 → 1 → 2` have different v-structures, so the
  v-structure hypothesis is not vacuous.
-/

@[expose] public section

namespace Cslib.MachineLearning.MarkovEquivalenceTests

open Cslib.MachineLearning.GraphicalModels.BayesianDirichlet in
example : Relation.ReflTransGen CoveredReversal
    (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0} : Finset (Fin 3)) else ({1} : Finset (Fin 3)))
    (fun v : Fin 3 => if v = 0 then ({1} : Finset (Fin 3)) else if v = 1 then ({2} : Finset (Fin 3)) else (∅ : Finset (Fin 3))) := by
  apply reflTransGen_coveredReversal_of_markovEquivalent
  · intro v hv
    have hsingle : ∀ a b : Fin 3,
        a ∈ (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0} : Finset (Fin 3)) else ({1} : Finset (Fin 3))) b →
        a.val < b.val := by decide
    have hall : ∀ a b, Relation.TransGen
        (fun u w => u ∈ (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0} : Finset (Fin 3)) else ({1} : Finset (Fin 3))) w) a b →
        a.val < b.val := by
      intro a b hab
      refine Relation.TransGen.rec (motive := fun b _ => a.val < b.val) ?_ ?_ hab
      · intro b' s
        exact hsingle a b' s
      · intro b' c' h1 s ih
        exact Nat.lt_trans ih (hsingle _ _ s)
    exact (Nat.lt_irrefl _ (hall v v hv)).elim
  · intro v hv
    have hsingle : ∀ a b : Fin 3,
        a ∈ (fun v : Fin 3 => if v = 0 then ({1} : Finset (Fin 3)) else if v = 1 then ({2} : Finset (Fin 3)) else (∅ : Finset (Fin 3))) b →
        b.val < a.val := by decide
    have hall : ∀ a b, Relation.TransGen
        (fun u w => u ∈ (fun v : Fin 3 => if v = 0 then ({1} : Finset (Fin 3)) else if v = 1 then ({2} : Finset (Fin 3)) else (∅ : Finset (Fin 3))) w) a b →
        b.val < a.val := by
      intro a b hab
      refine Relation.TransGen.rec (motive := fun b _ => b.val < a.val) ?_ ?_ hab
      · intro b' s
        exact hsingle a b' s
      · intro b' c' h1 s ih
        exact Nat.lt_trans (hsingle _ _ s) ih
    exact (Nat.lt_irrefl _ (hall v v hv)).elim
  · unfold Adjacent
    decide
  · unfold IsVStructure Adjacent
    decide

open Cslib.MachineLearning.GraphicalModels.BayesianDirichlet in
example : ¬ ∀ u w z : Fin 3,
    IsVStructure (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0, 2} : Finset (Fin 3)) else (∅ : Finset (Fin 3))) u w z ↔
    IsVStructure (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0} : Finset (Fin 3)) else ({1} : Finset (Fin 3))) u w z := by
  have p1 : IsVStructure
      (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0, 2} : Finset (Fin 3)) else (∅ : Finset (Fin 3))) 0 1 2 := by
    unfold IsVStructure Adjacent
    decide
  have p2 : ¬IsVStructure
      (fun v : Fin 3 => if v = 0 then (∅ : Finset (Fin 3)) else if v = 1 then ({0} : Finset (Fin 3)) else ({1} : Finset (Fin 3))) 0 1 2 := by
    unfold IsVStructure Adjacent
    decide
  intro hall
  exact p2 ((hall 0 1 2).mp p1)

end Cslib.MachineLearning.MarkovEquivalenceTests
