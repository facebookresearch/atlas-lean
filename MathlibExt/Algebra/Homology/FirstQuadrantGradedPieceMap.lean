/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPiece

/-!
# The projection onto a horizontal graded piece

This file assembles the degreewise top-column projections into a cochain map.
For a transparent differential calculation, the target is presented directly
as the extension along `q ↦ -p-q`, with differential multiplied by the same
`(-1)^p` sign supplied by the standard cochain shift.  A later comparison
identifies this direct presentation with `horizontalColumnCochain`.
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

@[simp]
theorem horizontalColumnDegree_eq (p q : ℕ) :
    horizontalColumnDegree p (-(p : ℤ) - q) = q := by
  unfold horizontalColumnDegree
  omega

/-- Direct presentation of the shifted `p`th vertical column. -/
noncomputable def horizontalDirectColumnCochain (p : ℕ) :
    CochainComplex C ℤ where
  X := ((K.X p).extend (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).X
  d i j := (p : ℤ).negOnePow •
    ((K.X p).extend (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).d i j
  shape i j h := by
    rw [((K.X p).extend (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).shape i j h,
      smul_zero]
  d_comp_d' i j k hij hjk := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
    rw [HomologicalComplex.d_comp_d, smul_zero]

/-- Canonical degree identification for the direct column presentation. -/
noncomputable def horizontalDirectColumnCochainXIso (p q : ℕ) :
    (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) ≅
      (K.X p).X q :=
  (K.X p).extendXIso (ComplexShape.embeddingUpIntLE (-(p : ℤ))) (by
    simp only [ComplexShape.embeddingUpIntLE_f])

omit [HasFiniteCoproducts C] in
theorem horizontalDirectColumnCochain_isZero_X_of_lt
    (p : ℕ) (i : ℤ) (hi : -(p : ℤ) < i) :
    IsZero ((horizontalDirectColumnCochain K p).X i) :=
  (K.X p).isZero_extend_X (ComplexShape.embeddingUpIntLE (-(p : ℤ))) i
    (by simpa only [ComplexShape.notMem_range_embeddingUpIntLE_iff] using hi)

omit [HasFiniteCoproducts C] in
@[reassoc]
theorem horizontalDirectColumnCochainXIso_inv_d_hom (p q : ℕ) :
    (horizontalDirectColumnCochainXIso K p (q + 1)).inv ≫
        (horizontalDirectColumnCochain K p).d (-(p : ℤ) - (q + 1))
          (-(p : ℤ) - q) ≫
        (horizontalDirectColumnCochainXIso K p q).hom =
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q + 1) • (K.X p).d (q + 1) q := by
  dsimp [horizontalDirectColumnCochain, horizontalDirectColumnCochainXIso]
  rw [HomologicalComplex.extend_d_eq
    (i := q + 1) (j := q)
    (hi := by simp only [ComplexShape.embeddingUpIntLE_f]; omega)
    (hj := by simp only [ComplexShape.embeddingUpIntLE_f])]
  simp
  congr 1

/-- Canonical projection component in bidegree `(p,q)` for the direct column
presentation. -/
noncomputable def horizontalDirectColumnProjectionComponent (p q : ℕ) :
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex p)).X (-(p : ℤ) - q) ⟶
        (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) :=
  (horizontalCompleteFiltrationCochainUpperIso K p).hom.f (-(p : ℤ) - q) ≫
    ((horizontalFilteredTotalComplex K p).extendXIso
      ComplexShape.embeddingDownNat
      (i := p + q) (i' := -(p : ℤ) - q) (by simp; omega)).hom ≫
    horizontalFilteredTopProjection K p q ≫
    (horizontalDirectColumnCochainXIso K p q).inv

/-- Degreewise projection from filtration stage `p` to the direct column. -/
noncomputable def horizontalDirectColumnProjection (p : ℕ) (i : ℤ) :
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex p)).X i ⟶
        (horizontalDirectColumnCochain K p).X i := by
  by_cases hi : i ≤ -(p : ℤ)
  · exact eqToHom (congrArg
      (fun j => ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p)).X j)
          (horizontalColumnDegree_spec p i hi)) ≫
      horizontalDirectColumnProjectionComponent K p (horizontalColumnDegree p i) ≫
      eqToHom (congrArg
        (fun j => (horizontalDirectColumnCochain K p).X j)
          (horizontalColumnDegree_spec p i hi).symm)
  · exact 0

theorem horizontalDirectColumnProjection_eq_of_le (p : ℕ) (i : ℤ)
    (hi : i ≤ -(p : ℤ)) :
    horizontalDirectColumnProjection K p i =
      eqToHom (congrArg
        (fun j => ((horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex p)).X j)
            (horizontalColumnDegree_spec p i hi)) ≫
        horizontalDirectColumnProjectionComponent K p (horizontalColumnDegree p i) ≫
        eqToHom (congrArg
          (fun j => (horizontalDirectColumnCochain K p).X j)
            (horizontalColumnDegree_spec p i hi).symm) := by
  unfold horizontalDirectColumnProjection
  rw [dite_eq_left hi]

theorem horizontalDirectColumnProjection_eq_zero_of_lt (p : ℕ) (i : ℤ)
    (hi : -(p : ℤ) < i) :
    horizontalDirectColumnProjection K p i = 0 := by
  unfold horizontalDirectColumnProjection
  rw [dite_eq_right (by lia)]

theorem horizontalDirectColumnProjection_eq_component (p q : ℕ) :
    horizontalDirectColumnProjection K p (-(p : ℤ) - q) =
      horizontalDirectColumnProjectionComponent K p q := by
  unfold horizontalDirectColumnProjection
  rw [dite_eq_left (show -(p : ℤ) - q ≤ -(p : ℤ) by omega)]
  simp [horizontalColumnDegree]

theorem horizontalDirectColumnProjectionComponent_comm (p q : ℕ) :
    horizontalDirectColumnProjectionComponent K p (q + 1) ≫
        (horizontalDirectColumnCochain K p).d (-(p : ℤ) - (q + 1))
          (-(p : ℤ) - q) =
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p)).d (-(p : ℤ) - (q + 1))
          (-(p : ℤ) - q) ≫
        horizontalDirectColumnProjectionComponent K p q := by
  apply (cancel_mono (horizontalDirectColumnCochainXIso K p q).hom).1
  dsimp [horizontalDirectColumnProjectionComponent]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [horizontalDirectColumnCochainXIso_inv_d_hom]
  have hU := (horizontalCompleteFiltrationCochainUpperIso K p).hom.comm
    (-(p : ℤ) - (q + 1)) (-(p : ℤ) - q)
  have hExt := (horizontalFilteredTotalComplex K p).extend_d_eq
    ComplexShape.embeddingDownNat
    (i := p + q + 1) (j := p + q)
    (i' := -(p : ℤ) - (q + 1)) (j' := -(p : ℤ) - q)
    (hi := by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)
    (hj := by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)
  change ((horizontalFilteredTotalComplex K p).extend
      ComplexShape.embeddingDownNat).d (-(p : ℤ) - (q + 1))
        (-(p : ℤ) - q) =
    ((horizontalFilteredTotalComplex K p).extendXIso
      ComplexShape.embeddingDownNat
      (i := p + q + 1) (i' := -(p : ℤ) - (q + 1))
      (by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)).hom ≫
      horizontalFilteredTotalD K p (p + q + 1) (p + q) ≫
      ((horizontalFilteredTotalComplex K p).extendXIso
        ComplexShape.embeddingDownNat
        (i := p + q) (i' := -(p : ℤ) - q)
        (by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)).inv at hExt
  conv_rhs =>
    rw [← Category.assoc, ← hU, hExt]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [horizontalFilteredTotalD_topProjection]

/-- The top-column projections form a cochain map to the direct graded-piece
presentation. -/
noncomputable def horizontalDirectColumnProjectionMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      horizontalDirectColumnCochain K p where
  f := horizontalDirectColumnProjection K p
  comm' := by
    intro i j hij
    by_cases hj : -(p : ℤ) < j
    · exact (horizontalDirectColumnCochain_isZero_X_of_lt K p j hj).eq_of_tgt _ _
    · have hjle : j ≤ -(p : ℤ) := by lia
      have hiRel : i + 1 = j := by simpa only [ComplexShape.up_Rel] using hij
      have hile : i ≤ -(p : ℤ) := by lia
      obtain ⟨q, hjEq⟩ : ∃ q : ℕ, j = -(p : ℤ) - q :=
        ⟨horizontalColumnDegree p j,
          horizontalColumnDegree_spec p j hjle⟩
      have hiEq : i = -(p : ℤ) - ((q + 1 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hiEq, hjEq]
      rw [horizontalDirectColumnProjection_eq_component K p (q + 1),
        horizontalDirectColumnProjection_eq_component K p q]
      exact horizontalDirectColumnProjectionComponent_comm K p q

end HomologicalComplex₂

end
