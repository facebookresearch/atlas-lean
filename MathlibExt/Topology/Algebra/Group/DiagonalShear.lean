/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.Complex.Basic

/-!
# The literal difference-coordinate shear

The original product coordinates transform by `(s,t) ↦ (s*t⁻¹,t)`, with
inverse `(r,t) ↦ (r*t,t)`. This is an actual homeomorphism of the original
topological product. Its inverse gives the literal linear pullback on
compact-support vector functions.

This geometric construction asserts no measure preservation or L2 norm
identity. Those are distinct prerequisites for its Hilbert-space unitary.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CompactlySupported

universe uG uH

namespace Homeomorph

/-- The actual difference-coordinate shear on the original product topological group. -/
def diagonalDifferenceShear (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (G × G) ≃ₜ (G × G) where
  toFun z := (z.1 * z.2⁻¹, z.2)
  invFun z := (z.1 * z.2, z.2)
  left_inv z := by
    apply Prod.ext
    · change (z.1 * z.2⁻¹) * z.2 = z.1
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · rfl
  right_inv z := by
    apply Prod.ext
    · change (z.1 * z.2) * z.2⁻¹ = z.1
      rw [mul_assoc, mul_inv_cancel, mul_one]
    · rfl
  continuous_toFun := (continuous_fst.mul continuous_snd.inv).prodMk continuous_snd
  continuous_invFun := (continuous_fst.mul continuous_snd).prodMk continuous_snd

/-- The forward shear has its literal original difference-coordinate values. -/
@[simp]
theorem diagonalDifferenceShear_apply (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (z : G × G) :
    diagonalDifferenceShear G z = (z.1 * z.2⁻¹, z.2) :=
  rfl

/-- The inverse shear has its literal original multiplication-coordinate values. -/
@[simp]
theorem diagonalDifferenceShear_symm_apply (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (z : G × G) :
    (diagonalDifferenceShear G).symm z = (z.1 * z.2, z.2) :=
  rfl

end Homeomorph

namespace CompactlySupportedContinuousMap

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The actual inverse-shear pullback on the original compact-support vector functions. -/
def diagonalShearPullback : C_c(G × G, H) →ₗ[ℂ] C_c(G × G, H) where
  toFun f :=
    ⟨⟨fun z => f ((Homeomorph.diagonalDifferenceShear G).symm z),
      f.continuous.comp (Homeomorph.diagonalDifferenceShear G).symm.continuous⟩,
      f.hasCompactSupport.comp_homeomorph (Homeomorph.diagonalDifferenceShear G).symm⟩
  map_add' f g := by
    apply CompactlySupportedContinuousMap.ext
    intro z
    rfl
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro z
    rfl

/-- The compact-support pullback retains the exact original inverse-shear vector coordinates. -/
@[simp]
theorem diagonalShearPullback_apply (f : C_c(G × G, H)) (z : G × G) :
    diagonalShearPullback f z = f (z.1 * z.2, z.2) :=
  rfl

end CompactlySupportedContinuousMap
