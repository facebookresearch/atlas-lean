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
# Difference-coordinate shear of a topological group product

For any topological group `G`, the map `(s,t) ↦ (st⁻¹,t)` is a homeomorphism of `G×G`, with
inverse `(r,t) ↦ (rt,t)`. Commutativity is not required.

Pullback along this inverse gives the linear map `f(s,t) ↦ f(st,t)` on compact-support functions
with values in a complex normed space. No measure preservation or L² norm statement is included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CompactlySupported

universe uG uH

namespace Homeomorph

/-- **Difference-coordinate homeomorphism of a group square.** For a topological group `G`,
`diagonalDifferenceShear G : G×G ≃ₜ G×G` has forward map `(s,t) ↦ (st⁻¹,t)` and inverse
`(r,t) ↦ (rt,t)`. The group may be nonabelian. -/
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

/-- **Forward value of the difference-coordinate shear.** For a topological group `G` and
`(s,t)∈G×G`, `diagonalDifferenceShear G (s,t)=(st⁻¹,t)`. -/
@[simp]
theorem diagonalDifferenceShear_apply (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (z : G × G) :
    diagonalDifferenceShear G z = (z.1 * z.2⁻¹, z.2) :=
  rfl

/-- **Inverse value of the difference-coordinate shear.** For a topological group `G` and
`(r,t)∈G×G`, `(diagonalDifferenceShear G).symm (r,t)=(rt,t)`. -/
@[simp]
theorem diagonalDifferenceShear_symm_apply (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (z : G × G) :
    (diagonalDifferenceShear G).symm z = (z.1 * z.2, z.2) :=
  rfl

end Homeomorph

namespace CompactlySupportedContinuousMap

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **Inverse-shear pullback of compact-support vector functions.** Let `G` be a topological
group and `H` a complex normed space, possibly incomplete. `diagonalShearPullback :
C_c(G×G,H) →ₗ[ℂ] C_c(G×G,H)` sends `f` to `(s,t) ↦ f(st,t)`. -/
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

/-- **Pointwise value of inverse-shear pullback.** Let `G` be a topological group, `H` a
complex normed space and `f∈C_c(G×G,H)`. Then `diagonalShearPullback f (s,t)=f(st,t)`. -/
@[simp]
theorem diagonalShearPullback_apply (f : C_c(G × G, H)) (z : G × G) :
    diagonalShearPullback f z = f (z.1 * z.2, z.2) :=
  rfl

end CompactlySupportedContinuousMap
