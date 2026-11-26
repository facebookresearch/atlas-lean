/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageAdjacentCokernel

/-!
# Adjacent-column connecting maps and the horizontal boundary

Let `K` be a first-quadrant bicomplex in a preadditive category with finite coproducts.
Include bidegree `(p+1,q)` into the total, take its boundary, and project to `(p,q)`. Only the
horizontal differential survives, with first-coordinate total sign `ε₁`; for the standard
totalization this sign is one.

In an abelian category, the adjacent-column short exact sequence gives a connecting map from
direct-column cohomology in degree `-(p+1)-q` to degree `-p-q`. Its vertical-homology
coordinates and the homology map of `K.d(p+1,p)` are defined separately.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

omit [HasZeroObject C] in
/-- The horizontal component of a total boundary.

The total inclusion from `(p+1,q)` followed by the total differential and projection to
`(p,q)` is `ε₁(p+1,q)` times the horizontal bicomplex map. -/
theorem ιTotal_d_horizontalTotalTopProjection_succ (p q : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + 1 + q)
        (by simp) ≫
      (K.total (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) ≫
      horizontalTotalTopProjection K p q =
    ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p + 1, q) •
      (K.d (p + 1) p).f q := by
  change K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + 1 + q)
      (by simp) ≫
      (K.D₁ (ComplexShape.down ℕ) (p + 1 + q) (p + q) +
        K.D₂ (ComplexShape.down ℕ) (p + 1 + q) (p + q)) ≫
      horizontalTotalTopProjection K p q = _
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    K.ι_D₁_assoc, K.ι_D₂_assoc]
  rw [K.d₁_eq (ComplexShape.down ℕ)
    (ComplexShape.down_mk (p + 1) p rfl) q (p + q) (by simp)]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTotal_horizontalTotalTopProjection, dite_eq_left rfl]
  simp only [ComplexShape.ε₁_def, eqToHom_refl, Category.comp_id,
    one_smul, add_eq_left]
  have h₂ : K.d₂ (ComplexShape.down ℕ) (p + 1) q (p + q) ≫
      horizontalTotalTopProjection K p q = 0 := by
    cases q with
    | zero =>
        rw [K.d₂_eq_zero (ComplexShape.down ℕ) (p + 1) 0 (p + 0) (by simp),
          zero_comp]
    | succ q =>
        rw [K.d₂_eq (ComplexShape.down ℕ) (p + 1)
          (ComplexShape.down_mk (q + 1) q rfl) (p + (q + 1)) (by simp; omega)]
        simp only [Linear.units_smul_comp, Category.assoc]
        rw [ιTotal_horizontalTotalTopProjection, dite_eq_right (by omega),
          comp_zero, smul_zero]
  rw [h₂]

/-- The projection to a preceding column in a finite filtration stage.

Project total degree `p+q` of stage `p+1` onto its column-`p`, vertical-degree-`q` summand. -/
noncomputable def horizontalFilteredPreviousColumnProjection (p q : ℕ) :
    horizontalFilteredTotalObj K (p + 1) (p + q) ⟶ (K.X p).X q :=
  horizontalFilteredTotalToTotal K (p + 1) (p + q) ≫
    horizontalTotalTopProjection K p q

omit [HasZeroObject C] in
/-- The signed previous-column component of a filtered top boundary.

The top section of column `p+1`, followed by the filtered total differential and preceding-
column projection, is the horizontal map multiplied by the first-coordinate total sign. -/
theorem horizontalFilteredTopSection_d_previousColumnProjection (p q : ℕ) :
    horizontalFilteredTopSection K p q ≫
        horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) ≫
        horizontalFilteredPreviousColumnProjection K p q =
      ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p + 1, q) •
        (K.d (p + 1) p).f q := by
  unfold horizontalFilteredPreviousColumnProjection
  have hι := horizontalFilteredTotalι_toTotal K (p + 1) (p + 1 + q)
    (horizontalFilteredTopIndex (p + 1) q)
  change horizontalFilteredTopSection K p q ≫
      horizontalFilteredTotalToTotal K (p + 1) (p + 1 + q) =
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + 1 + q) (by simp) at hι
  have hD :
      horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) ≫
          horizontalFilteredTotalToTotal K (p + 1) (p + q) =
        horizontalFilteredTotalToTotal K (p + 1) (p + 1 + q) ≫
          (K.total (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) := by
    rw [show p + 1 + q = p + q + 1 by omega]
    exact horizontalFilteredTotalD_toTotal K (p + 1) (p + q)
  calc
    _ = horizontalFilteredTopSection K p q ≫
        (horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) ≫
          horizontalFilteredTotalToTotal K (p + 1) (p + q)) ≫
        horizontalTotalTopProjection K p q := by
      simp only [Category.assoc]
    _ = horizontalFilteredTopSection K p q ≫
        (horizontalFilteredTotalToTotal K (p + 1) (p + 1 + q) ≫
          (K.total (ComplexShape.down ℕ)).d (p + 1 + q) (p + q)) ≫
        horizontalTotalTopProjection K p q := by
      rw [hD]
    _ = (horizontalFilteredTopSection K p q ≫
          horizontalFilteredTotalToTotal K (p + 1) (p + 1 + q)) ≫
        (K.total (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) ≫
        horizontalTotalTopProjection K p q := by
      simp only [Category.assoc]
    _ = K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + 1 + q)
          (by simp) ≫
        (K.total (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) ≫
        horizontalTotalTopProjection K p q := by rw [hι]
    _ = _ := ιTotal_d_horizontalTotalTopProjection_succ K p q

omit [HasZeroObject C] in
/-- The standard horizontal component of a filtered top boundary.

For the standard first-quadrant total signs, the preceding-column boundary component is
exactly `(K.d(p+1,p)).f q`. -/
theorem horizontalFilteredTopSection_d_previousColumnProjection_eq
    (p q : ℕ) :
    horizontalFilteredTopSection K p q ≫
        horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) ≫
        horizontalFilteredPreviousColumnProjection K p q =
      (K.d (p + 1) p).f q := by
  simpa using horizontalFilteredTopSection_d_previousColumnProjection K p q

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The connecting map of adjacent direct columns.

The adjacent-column short exact sequence gives a map from column `p+1` homology at degree
`-(p+1)-q` to column `p` homology at degree `-p-q`. -/
noncomputable def horizontalFirstPageAdjacentConnectingMap (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).homology
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) :=
  (horizontalFirstPageAdjacentDirectShortExact K p).δ
    (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
    (by simp only [ComplexShape.up_Rel]; push_cast; omega)

/-- The adjacent connecting map in vertical-homology coordinates.

Transport the direct-column connecting morphism to a map `H_q(K_(p+1)) → H_q(K_p)` through the
direct-column homology isomorphisms. -/
noncomputable def horizontalFirstPageAdjacentVerticalConnectingMap (p q : ℕ) :
    (K.X (p + 1)).homology q ⟶ (K.X p).homology q :=
  (horizontalDirectColumnHomologyIso K (p + 1) q).inv ≫
    horizontalFirstPageAdjacentConnectingMap K p q ≫
    (horizontalDirectColumnHomologyIso K p q).hom

/-- The vertical-homology map of a horizontal bicomplex differential.

Take `H_q` of the chain map `K.d(p+1,p)` between the two vertical columns. -/
noncomputable def horizontalFirstPageHorizontalHomologyMap (p q : ℕ) :
    (K.X (p + 1)).homology q ⟶ (K.X p).homology q :=
  HomologicalComplex.homologyMap (K.d (p + 1) p) q

end HomologicalComplex₂

end
