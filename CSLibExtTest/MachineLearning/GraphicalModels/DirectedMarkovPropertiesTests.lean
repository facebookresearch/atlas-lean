/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DirectedMarkovProperties
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for the equivalence of the directed Markov properties

On the chain `X₀ → X₁ → X₂`: the parents `{X₁}` d-separate `X₂` from `X₀`; a law with the global
Markov property for the chain factorizes over it; and the joint of the chain has all four
properties.
-/

@[expose] public section

namespace Cslib.MachineLearning.DirectedMarkovPropertiesTests

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

/-- The parents of `X₂` d-separate it from its other non-descendants. -/
example : chain.DSeparated {2} {j | ¬chain.IsDescendant 2 j ∧ ¬chain.Edge j 2}
    {j | chain.Edge j 2} :=
  chain.dSeparated_localMarkov 2

/-- A law with the global Markov property for the chain factorizes over it. -/
example (P : (Fin 3 → Bool) → ℝ) (hP : ∀ x, 0 ≤ P x) (h1 : ∑ x, P x = 1)
    (hG : GlobalMarkovFor P chain) : ∃ b : BayesNet Bool 3, b.pa = chain.pa ∧ b.joint = P :=
  ((directedMarkov_tfae P hP h1 chain).out 2 1).1 hG

/-- The joint of the chain has the local Markov property. -/
example : LocalMarkovFor chain.joint chain :=
  ((directedMarkov_tfae chain.joint (fun x => chain.toChain.joint_nonneg 3 x) chain.sum_joint
    chain).out 1 3).1 (⟨chain, rfl, rfl⟩ : ∃ b' : BayesNet Bool 3, b'.pa = chain.pa ∧
      b'.joint = chain.joint)

end Cslib.MachineLearning.DirectedMarkovPropertiesTests
