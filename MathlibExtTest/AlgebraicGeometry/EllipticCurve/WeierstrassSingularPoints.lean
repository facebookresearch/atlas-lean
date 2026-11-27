/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.WeierstrassSingularPoints
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.WeierstrassSingularPoints

open WeierstrassCurve
open scoped WeierstrassCurve.Projective

/-- The nodal cubic `y² = x³ + x²` over `ℚ`. -/
private def nodal : WeierstrassCurve ℚ :=
  ⟨0, 1, 0, 0, 0⟩

/-- The cuspidal cubic `y² = x³` over `ℚ`. -/
private def cuspidal : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, 0, 0⟩

/-- The curve `y² = x³ - x` over `ℚ`. -/
private def smooth : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -1, 0⟩

private lemma nodal_Δ : nodal.Δ = 0 := by
  norm_num [nodal, Δ, b₂, b₄, b₆, b₈]

private lemma nodal_c₄ : nodal.c₄ = 16 := by
  norm_num [nodal, c₄, b₂, b₄]

private lemma cuspidal_Δ : cuspidal.Δ = 0 := by
  simp [cuspidal, Δ, b₂, b₄, b₆, b₈]

private lemma cuspidal_c₄ : cuspidal.c₄ = 0 := by
  simp [cuspidal, c₄, b₂, b₄]

private lemma smooth_Δ : smooth.Δ = 64 := by
  norm_num [smooth, Δ, b₂, b₄, b₆, b₈]

local notation "Qbar" => AlgebraicClosure ℚ

/-- Over `ℚ̄`, every point of `y² = x³ - x` is nonsingular. -/
example (P : Fin 3 → Qbar) (hP : P ≠ 0)
    (he : (smooth.map (algebraMap ℚ Qbar)).toProjective.Equation P) :
    (smooth.map (algebraMap ℚ Qbar)).toProjective.Nonsingular P :=
  (map_nonsingular_iff_Δ_ne_zero smooth).2 (by rw [smooth_Δ]; norm_num) P hP he

/-- `(0 : 0 : 1)` is a singular point of `y² = x³ + x²` over `ℚ̄`. -/
private lemma nodal_isSingularPoint :
    (nodal.map (algebraMap ℚ Qbar)).IsSingularPoint ![0, 0, 1] := by
  rw [isSingularPoint_some, Affine.nonsingular_iff, Affine.equation_iff]
  simp [nodal]

/-- `(0 : 0 : 1)` is a node of `y² = x³ + x²` over `ℚ̄`. -/
example : (nodal.map (algebraMap ℚ Qbar)).IsProjectiveNode ![0, 0, 1] :=
  (isProjectiveNode_and_isProjectiveCusp _ nodal_isSingularPoint).1
    (by rw [map_c₄, nodal_c₄]; norm_num)

/-- Every singular point of `y² = x³ + x²` over `ℚ̄` is `(0 : 0 : 1)` up to scaling. -/
example (P : Fin 3 → Qbar) (hP : (nodal.map (algebraMap ℚ Qbar)).IsSingularPoint P) :
    P ≈ ![0, 0, 1] := by
  obtain ⟨S, hS, huniq, -, -, -⟩ := existsUnique_isSingularPoint_map (K := Qbar) nodal nodal_Δ
  exact Setoid.trans (huniq P hP) (Setoid.symm (huniq _ nodal_isSingularPoint))

/-- The singular point of `y² = x³` over `ℚ̄` is a cusp, and it is not `(0 : 1 : 0)`. -/
example : ∃ S : Fin 3 → Qbar, (cuspidal.map (algebraMap ℚ Qbar)).IsSingularPoint S ∧
    (cuspidal.map (algebraMap ℚ Qbar)).IsProjectiveCusp S ∧ ¬ S ≈ ![0, 1, 0] := by
  obtain ⟨S, hS, -, hinf, -, hcusp⟩ :=
    existsUnique_isSingularPoint_map (K := Qbar) cuspidal cuspidal_Δ
  exact ⟨S, hS, hcusp cuspidal_c₄, hinf⟩

/-- The affine origin of `y² = x³` is a cusp; its singular points are its double points. -/
example : (cuspidal.map (algebraMap ℚ Qbar)).IsCusp 0 0 ∧
    (cuspidal.map (algebraMap ℚ Qbar)).IsDoublePoint 0 0 := by
  have he : (cuspidal.map (algebraMap ℚ Qbar)).toAffine.Equation 0 0 := by
    rw [Affine.equation_iff]; simp [cuspidal]
  have hns : ¬ (cuspidal.map (algebraMap ℚ Qbar)).toAffine.Nonsingular 0 0 := by
    rw [Affine.nonsingular_iff]; simp [cuspidal]
  exact ⟨isCusp_of_singular _ he hns (by rw [map_c₄, cuspidal_c₄, map_zero]),
    (isDoublePoint_iff _ 0 0).2 ⟨he, hns⟩⟩

/-- Both parts of the theorem for `y² = x³ + x²` over `ℚ̄`. -/
example : ¬ (∀ P : Fin 3 → Qbar, P ≠ 0 → (nodal.map (algebraMap ℚ Qbar)).toProjective.Equation P →
      (nodal.map (algebraMap ℚ Qbar)).toProjective.Nonsingular P) :=
  fun h ↦ ((singular_points_of_weierstrass_cubic (K := Qbar) nodal).1.1 h) nodal_Δ

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.WeierstrassSingularPoints
