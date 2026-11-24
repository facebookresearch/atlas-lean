/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovFactorization
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for the equivalence of the ordered Markov property and factorization

* The joint law of the chain `X₀ → X₁ → X₂` has the ordered Markov property; in particular
  `X₂ ⫫ X₀ | X₁`.
* Round trip: the joint of any Bayesian network is again the joint of the network of its
  conditional tables, on the same graph.
* The equivalence for the empty graph on three nodes (mutual independence).
-/

@[expose] public section

namespace Cslib.MachineLearning.MarkovFactorizationTests

open Cslib.MachineLearning GraphicalModels Convexity Finset MetaMathlibExt.FiniteWeight

/-- The fair coin on `Bool`. -/
noncomputable def fair : StdSimplex ℝ Bool :=
  StdSimplex.duple (s := 1 / 2) (t := 1 / 2) true false (by norm_num) (by norm_num) (by norm_num)

/-- The parents of the chain `X₀ → X₁ → X₂`. -/
def chainPa : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {1}
  | ⟨_ + 3, h⟩ => absurd h (by omega)

/-- Every table is the fair coin. -/
noncomputable def chain : BayesNet Bool 3 where
  pa := chainPa
  cpt _ _ := fair

/-- The ordered Markov property of the chain at `X₂`: `X₀` is its only non-parent predecessor. -/
example : CondIndep chain.joint ↑({2} : Finset (Fin 3)) ↑(nonParentPred chainPa 2)
    ↑(parentSet chainPa 2) :=
  orderedMarkov_joint chain 2

example : nonParentPred chainPa 2 = {0} := by decide

/-- Round trip through the ordered Markov property. -/
example {n : ℕ} (b : BayesNet Bool n) : ∃ b' : BayesNet Bool n, b'.pa = b.pa ∧ b'.joint = b.joint :=
  exists_bayesNet_of_orderedMarkov b.joint (fun x => b.toChain.joint_nonneg n x) b.sum_joint b.pa
    (orderedMarkov_joint b)

/-- The empty graph on three nodes. -/
def emptyPa : (k : Fin 3) → Finset (Fin k) := fun _ => ∅

/-- The ordered Markov property and factorization are equivalent for the empty graph too. -/
example (P : (Fin 3 → Bool) → ℝ) (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1) :
    OrderedMarkov P emptyPa ↔ ∃ b : BayesNet Bool 3, b.pa = emptyPa ∧ b.joint = P :=
  orderedMarkov_iff_exists_bayesNet P hP h1 emptyPa

end Cslib.MachineLearning.MarkovFactorizationTests
