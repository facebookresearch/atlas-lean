/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMatrixRecognition

/-! Actual orthogonal preservation of the genuine two-root plane. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem projection_fixes_range (x : Fin 24 → ℝ)
    (hx : x ∈ LinearMap.range (Matrix.toLin' generatedSixthPlaneProjection)) :
    generatedSixthPlaneProjection *ᵥ x = x := by
  obtain ⟨v, rfl⟩ := hx
  change generatedSixthPlaneProjection *ᵥ (generatedSixthPlaneProjection *ᵥ v) = _
  rw [Matrix.mulVec_mulVec, generatedSixth_plane_projection_square]
  rfl

private theorem projected_image (g : leechIsomSubgroup)
    (hg : ∀ x, x ∈ generatedSixthRootedPlane → g.val x ∈ generatedSixthRootedPlane) :
    generatedSixthPlaneProjection * leechIsomMatrix g * generatedSixthPlaneProjection =
      leechIsomMatrix g * generatedSixthPlaneProjection := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply]
  apply projection_fixes_range
  rw [generatedSixth_plane_projection_range]
  rw [leechIsomMatrix_mulVec]
  apply hg
  rw [← generatedSixth_plane_projection_range]
  exact ⟨x, rfl⟩

/-- Setwise preservation of the genuine two-root plane forces fixation of its projection. -/
theorem generatedSixth_plane_preservation_projection (g : leechIsomSubgroup)
    (hg : ∀ x, x ∈ generatedSixthRootedPlane ↔ g.val x ∈ generatedSixthRootedPlane) :
    conwayMatrixAction g generatedSixthPlaneProjection = generatedSixthPlaneProjection := by
  have hleft := projected_image g (fun x hx => (hg x).mp hx)
  have hinv : ∀ x, x ∈ generatedSixthRootedPlane → g.val.symm x ∈ generatedSixthRootedPlane := by
    intro x hx
    apply (hg (g.val.symm x)).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hx
  have hright := congrArg Matrix.transpose (projected_image g⁻¹ hinv)
  have hm : leechIsomMatrix g⁻¹ = (leechIsomMatrix g).transpose := by
    ext i j
    exact leechIsom_inverse_coordinate g j i
  simp only [Matrix.transpose_mul, hm, Matrix.transpose_transpose,
    generatedSixth_plane_projection_symm] at hright
  have hc : leechIsomMatrix g * generatedSixthPlaneProjection =
      generatedSixthPlaneProjection * leechIsomMatrix g := by
    exact hleft.symm.trans (by simpa only [Matrix.mul_assoc] using hright)
  rw [conwayMatrixAction_eq_conjugate, hc, Matrix.mul_assoc,
    mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul g), Matrix.mul_one]

private theorem projection_fixed_maps (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g generatedSixthPlaneProjection = generatedSixthPlaneProjection)
    (x : Fin 24 → ℝ) (hx : x ∈ generatedSixthRootedPlane) :
    g.val x ∈ generatedSixthRootedPlane := by
  have h := congrArg (fun A => A * leechIsomMatrix g) hg
  rw [conwayMatrixAction_eq_conjugate] at h
  have hc : leechIsomMatrix g * generatedSixthPlaneProjection =
      generatedSixthPlaneProjection * leechIsomMatrix g := by
    simpa only [Matrix.mul_assoc, leechIsomMatrix_transpose_mul, Matrix.mul_one] using h
  rw [← generatedSixth_plane_projection_range] at hx ⊢
  obtain ⟨v, hv⟩ := hx
  change generatedSixthPlaneProjection *ᵥ v = x at hv
  refine ⟨g.val v, ?_⟩
  change generatedSixthPlaneProjection *ᵥ g.val v = g.val x
  rw [← leechIsomMatrix_mulVec g v, Matrix.mulVec_mulVec, ← hc,
    ← Matrix.mulVec_mulVec, hv, leechIsomMatrix_mulVec]

/-- Fixing the actual projection is equivalent to preserving the actual two-root plane. -/
theorem generatedSixth_plane_projection_fixed_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g generatedSixthPlaneProjection = generatedSixthPlaneProjection ↔
      ∀ x, x ∈ generatedSixthRootedPlane ↔ g.val x ∈ generatedSixthRootedPlane := by
  constructor
  · intro hg
    have hi : conwayMatrixAction g⁻¹ generatedSixthPlaneProjection =
        generatedSixthPlaneProjection := by
      rw [map_inv]
      change (conwayMatrixAction g).symm _ = _
      calc
        (conwayMatrixAction g).symm generatedSixthPlaneProjection =
            (conwayMatrixAction g).symm
              (conwayMatrixAction g generatedSixthPlaneProjection) := by rw [hg]
        _ = generatedSixthPlaneProjection := LinearEquiv.symm_apply_apply _ _
    intro x
    constructor
    · exact projection_fixed_maps g hg x
    · intro hx
      have h := projection_fixed_maps g⁻¹ hi (g.val x) hx
      change g.val.symm (g.val x) ∈ generatedSixthRootedPlane at h
      simpa only [LinearEquiv.symm_apply_apply] using h
  · exact generatedSixth_plane_preservation_projection g

/-- The original matrix recognizes precisely the genuine rooted-A2 plane and root line. -/
theorem generatedSixth_axis_matrix_plane_fixed_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedSixthAxis).1 =
        (griessConwayEncode generatedSixthAxis).1 ↔
      (∀ x, x ∈ generatedSixthRootedPlane ↔ g.val x ∈ generatedSixthRootedPlane) ∧
        griessShortPermutation g generatedSixthPlaneShort = generatedSixthPlaneShort := by
  rw [generatedSixth_axis_matrix_fixed_iff, generatedSixth_plane_projection_fixed_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
