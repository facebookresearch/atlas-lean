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
deficiency: the field is smooth on the whole real state space, and its values lie in the
stoichiometric subspace.

`MetaMathlibExt.contDiff_massActionField` in `MathlibExt.Analysis.ODE.InvariantRegions` states
smoothness for the mass-action field written with a stoichiometric matrix.
-/

public section

namespace MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork

/-- The mass-action vector field is smooth on the full real state space. -/
theorem massActionField_contDiff {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) :
    ContDiff ℝ ⊤ (N.massActionField k) := by
  unfold ReactionNetwork.massActionField
  apply contDiff_pi.mpr
  intro s
  fun_prop

/-- The mass-action vector field takes values in the stoichiometric subspace. -/
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
