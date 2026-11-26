/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The mass-action vector field

General facts about `ReactionNetwork.massActionField` that use neither complex balancing nor
deficiency: the field is analytic on the whole real state space, and its values lie in the
stoichiometric subspace.

`MetaMathlibExt.contDiff_massActionField` in `MathlibExt.Analysis.ODE.InvariantRegions` states
smoothness for the mass-action field written with a stoichiometric matrix.
-/

public section

namespace MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork

/-- **Analyticity of the mass-action field.** The mass-action vector field is `C^ω` on the whole
real state space `S → ℝ` (`ContDiff ℝ ⊤`, where `⊤ = ω`), so in particular smooth: each
coordinate is a polynomial in the state. -/
theorem massActionField_contDiff {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) :
    ContDiff ℝ ⊤ (N.massActionField k) := by
  unfold ReactionNetwork.massActionField
  apply contDiff_pi.mpr
  intro s
  fun_prop

/-- **Values in the stoichiometric subspace.** At every real state `z`, the mass-action vector
field lies in the stoichiometric subspace, the span of the reaction vectors `prod r - src r`. -/
theorem massActionField_mem {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (z : S → ℝ) :
    N.massActionField k z ∈ N.stoichiometricSubspace := by
  classical
  have h := N.stoichiometricSubspace.sum_mem fun r (_ : r ∈ (Finset.univ : Finset ρ)) =>
    N.stoichiometricSubspace.smul_mem
      (k r * ∏ s, z s ^ N.src r s) (Submodule.subset_span ⟨r, rfl⟩)
  convert h using 1
  ext s
  simp [ReactionNetwork.massActionField]

end MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork
