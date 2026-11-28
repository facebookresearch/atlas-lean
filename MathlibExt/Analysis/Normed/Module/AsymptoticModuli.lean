/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Unit-direction asymptotic moduli

For a real seminorm `N` on a normed space, these moduli take the infimum over `N`-unit
centers, then the supremum over closed finite-codimensional subspaces, then the infimum
over `N`-unit directions in that subspace. The equivalent-norm case has constants
`0 < α ≤ β` and `α * ‖z‖ ≤ N z ≤ β * ‖z‖` for every `z`. Closedness uses the ambient
topology, which agrees with the topology of an equivalent norm. For the ambient norm
itself, use `normSeminorm ℝ E`.

The definitions use the total real `sInf` and `sSup`. In particular an empty unit sphere
of centers gives zero, and a subspace with no `N`-unit directions contributes zero to
the supremum. In finite-dimensional domains this can happen for the zero subspace.

The formulas follow OpenAI's *ForestSpace/Moduli.lean*:
<https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Moduli.lean>.
-/

@[expose] public section

namespace MetaMathlibExt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Closed real subspaces with finite-dimensional algebraic quotient. -/
abbrev ClosedFiniteCodimensionalSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {F : Submodule ℝ E // IsClosed (F : Set E) ∧ FiniteDimensional ℝ (E ⧸ F)}

/-- The one-sided asymptotic convexity modulus at `t`: take the infimum over `N`-unit centers `x`,
the supremum over closed finite-codimensional `F`, and the infimum of `N (x + t • y) - 1` over
`N`-unit vectors `y` of `F`, in that order. An empty real infimum is zero. -/
noncomputable def asymptoticConvexityModulus (N : Seminorm ℝ E) (t : ℝ) : ℝ :=
  sInf (Set.range fun x : {x : E // N x = 1} ↦
    sSup (Set.range fun F : ClosedFiniteCodimensionalSubmodule E ↦
      sInf (Set.range fun y : {y : E // y ∈ F.val ∧ N y = 1} ↦ N (x.val + t • y.val) - 1)))

/-- The midpoint asymptotic modulus has the same order of extrema as the one-sided modulus,
but uses the average of `N (x + t • y)` and `N (x - t • y)`, minus one. The centers and directions
have `N`-norm exactly one, and an empty real infimum is zero. -/
noncomputable def asymptoticMidpointModulus (N : Seminorm ℝ E) (t : ℝ) : ℝ :=
  sInf (Set.range fun x : {x : E // N x = 1} ↦
    sSup (Set.range fun F : ClosedFiniteCodimensionalSubmodule E ↦
      sInf (Set.range fun y : {y : E // y ∈ F.val ∧ N y = 1} ↦
        (N (x.val + t • y.val) + N (x.val - t • y.val)) / 2 - 1)))

/-- Negating the step in the one-sided modulus is the same as negating the unit direction. -/
@[simp] theorem asymptoticConvexityModulus_neg (N : Seminorm ℝ E) (t : ℝ) :
    asymptoticConvexityModulus N (-t) = asymptoticConvexityModulus N t := by
  unfold asymptoticConvexityModulus
  congr 1
  apply congrArg Set.range
  funext x
  congr 1
  apply congrArg Set.range
  funext F
  congr 1
  ext r
  simp only [Set.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨-y.val, F.val.neg_mem y.property.1, by simpa using y.property.2⟩, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨-y.val, F.val.neg_mem y.property.1, by simpa using y.property.2⟩, by simp⟩

/-- In the midpoint modulus, negating the step interchanges the two terms of the average. -/
@[simp] theorem asymptoticMidpointModulus_neg (N : Seminorm ℝ E) (t : ℝ) :
    asymptoticMidpointModulus N (-t) = asymptoticMidpointModulus N t := by
  unfold asymptoticMidpointModulus
  simp only [neg_smul, ← sub_eq_add_neg, sub_neg_eq_add]
  simp only [add_comm (N (_ - _)) (N (_ + _))]

private theorem sInf_range_zero {ι : Sort*} : sInf (Set.range fun _ : ι ↦ (0 : ℝ)) = 0 :=
  Real.iInf_const_zero

private theorem sSup_range_zero {ι : Sort*} : sSup (Set.range fun _ : ι ↦ (0 : ℝ)) = 0 :=
  Real.iSup_const_zero

private theorem unit_apply (N : Seminorm ℝ E) (x : {x : E // N x = 1}) : N x.val = 1 :=
  x.property

/-- The one-sided modulus at zero vanishes, including when a unit sphere is empty. -/
@[simp] theorem asymptoticConvexityModulus_zero (N : Seminorm ℝ E) :
    asymptoticConvexityModulus N 0 = 0 := by
  simp only [asymptoticConvexityModulus, zero_smul, add_zero, unit_apply, sub_self,
    sInf_range_zero, sSup_range_zero]

/-- The midpoint modulus at zero vanishes, including when a unit sphere is empty. -/
@[simp] theorem asymptoticMidpointModulus_zero (N : Seminorm ℝ E) :
    asymptoticMidpointModulus N 0 = 0 := by
  have h : ((1 : ℝ) + 1) / 2 = 1 := by rw [← two_mul, mul_one, div_self two_ne_zero]
  simp only [asymptoticMidpointModulus, zero_smul, add_zero, sub_zero, unit_apply, h, sub_self,
    sInf_range_zero, sSup_range_zero]

/-- In an infinite-dimensional space, a positive lower comparison with the ambient norm
ensures that each closed finite-codimensional subspace contains an `N`-unit direction.
An upper comparison is not needed for this normalization. -/
theorem ClosedFiniteCodimensionalSubmodule.exists_seminorm_eq_one
    (F : ClosedFiniteCodimensionalSubmodule E) (N : Seminorm ℝ E) {α : ℝ}
    (hE : ¬ FiniteDimensional ℝ E) (hα : 0 < α) (hN : ∀ z : E, α * ‖z‖ ≤ N z) :
    ∃ y ∈ F.val, N y = 1 := by
  have hF : F.val ≠ ⊥ := by
    intro hbot
    have : FiniteDimensional ℝ (E ⧸ F.val) := F.property.2
    apply hE
    exact FiniteDimensional.of_injective F.val.mkQ
      (LinearMap.ker_eq_bot.mp (F.val.ker_mkQ.trans hbot))
  obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
  have hNy : 0 < N y := (mul_pos hα (norm_pos_iff.mpr hy₀)).trans_le (hN y)
  refine ⟨(N y)⁻¹ • y, F.val.smul_mem _ hy, ?_⟩
  rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hNy.le), inv_mul_cancel₀ hNy.ne']

end MetaMathlibExt
