/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.WeierstrassSingularPoints
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Field.ZMod
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

/-- The curve `y² = x³ - x²` over `ℚ`, whose origin is a node with tangent lines `y = ± i x`
defined only over `ℚ(i)`. -/
private def nodalIrrational : WeierstrassCurve ℚ :=
  ⟨0, -1, 0, 0, 0⟩

/-- No line with rational coefficients is tangent to `y² = x³ - x²` at the origin. -/
example : ¬ ∃ c d : ℚ, nodalIrrational.IsTangentLine 0 0 c d := by
  rintro ⟨c, d, -, hcd, g, hg⟩
  rw [homogeneousComponent_two_polynomialAt] at hg
  have h := congrArg (MvPolynomial.eval ![d, -c]) hg
  simp only [quadraticPart, nodalIrrational, map_add, map_sub, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have h2 : c ^ 2 + d ^ 2 = 0 := by linear_combination h
  rcases hcd with hc | hd
  · exact hc (by nlinarith [sq_nonneg c, sq_nonneg d])
  · exact hd (by nlinarith [sq_nonneg c, sq_nonneg d])

/-- Over `ℚ̄`, the origin of `y² = x³ - x²` is a node. -/
example : (nodalIrrational.map (algebraMap ℚ Qbar)).IsNode 0 0 := by
  have he : (nodalIrrational.map (algebraMap ℚ Qbar)).toAffine.Equation 0 0 := by
    rw [Affine.equation_iff]; simp [nodalIrrational]
  have hns : ¬ (nodalIrrational.map (algebraMap ℚ Qbar)).toAffine.Nonsingular 0 0 := by
    rw [Affine.nonsingular_iff]; simp [nodalIrrational]
  refine isNode_of_singular _ he hns ?_
  rw [map_c₄]
  have : nodalIrrational.c₄ = 16 := by norm_num [nodalIrrational, c₄, b₂, b₄]
  rw [this]
  norm_num

/-- The origin of `y² = x³ - x` is a nonsingular point, so no line is tangent there at a double
point: in particular `Y = 0`, although `Y` divides the degree-two part `Y²`, is not a tangent
line. -/
example : ¬ smooth.IsTangentLine 0 0 0 1 := by
  rintro ⟨hdp, -⟩
  have hns := ((isDoublePoint_iff _ 0 0).1 hdp).2
  apply hns
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  simp [smooth]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "F₂t" => RatFunc (ZMod 2)

/-- The curve `y² = x³ + t x²` over `𝔽₂(t)`. -/
private noncomputable def cuspidalCharTwo : WeierstrassCurve F₂t :=
  ⟨0, RatFunc.X, 0, 0, 0⟩

/-- Over an algebraic closure of `𝔽₂(t)`, the origin of `y² = x³ + t x²` is a cusp, with the
double tangent line `Y + √t X = 0`. -/
example : (cuspidalCharTwo.map (algebraMap F₂t (AlgebraicClosure F₂t))).IsCusp 0 0 := by
  have he : (cuspidalCharTwo.map (algebraMap F₂t (AlgebraicClosure F₂t))).toAffine.Equation
      0 0 := by
    rw [Affine.equation_iff]; simp [cuspidalCharTwo]
  have hns : ¬ (cuspidalCharTwo.map
      (algebraMap F₂t (AlgebraicClosure F₂t))).toAffine.Nonsingular 0 0 := by
    rw [Affine.nonsingular_iff]; simp [cuspidalCharTwo]
  refine isCusp_of_singular _ he hns ?_
  rw [map_c₄]
  have h16 : (16 : F₂t) = 0 := by
    have : algebraMap (ZMod 2) F₂t 16 = 0 := by
      rw [show (16 : ZMod 2) = 0 by decide, map_zero]
    simpa only [map_ofNat] using this
  have : cuspidalCharTwo.c₄ = 0 := by
    simp only [cuspidalCharTwo, c₄, b₂, b₄]
    linear_combination RatFunc.X ^ 2 * h16
  rw [this, map_zero]

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.WeierstrassSingularPoints
