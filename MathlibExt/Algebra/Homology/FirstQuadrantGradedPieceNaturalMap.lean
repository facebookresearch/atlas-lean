/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernel

/-!
# Natural finite-stage cochain projections to direct columns

Let `K` be a first-quadrant bicomplex in a preadditive category with a zero object and finite
coproducts. Extend finite stage `F_p` to cochain degrees and project its top bidegree `(p,q)`
to the direct signed column at degree `-p-q`.

The components commute with the filtered total differential and the vertical differential
signed by `(-1)^p`, and are zero above degree `-p`. They form a cochain map. The extended
stage inclusion `F_p → F_(p+1)` has zero composite with the new direct-column projection.
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

/-- The direct-column component projection of an extended finite stage.

At degree `-p-q`, use the finite top-column projection and the inverse direct-column object
comparison. -/
noncomputable def horizontalNaturalDirectColumnProjectionComponent (p q : ℕ) :
    ((horizontalFilteredTotalComplex K p).extend
      ComplexShape.embeddingDownNat).X (-(p : ℤ) - q) ⟶
        (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) :=
  ((horizontalFilteredTotalComplex K p).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + q) (i' := -(p : ℤ) - q) (by simp; omega)).hom ≫
    horizontalFilteredTopProjection K p q ≫
    (horizontalDirectColumnCochainXIso K p q).inv

/-- The finite-stage direct-column projection in every cochain degree.

Use the supported component when `i ≤ -p` and zero when `i>-p`. -/
noncomputable def horizontalNaturalDirectColumnProjection (p : ℕ) (i : ℤ) :
    ((horizontalFilteredTotalComplex K p).extend
      ComplexShape.embeddingDownNat).X i ⟶
        (horizontalDirectColumnCochain K p).X i := by
  by_cases hi : i ≤ -(p : ℤ)
  · exact eqToHom (congrArg
      (fun j => ((horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat).X j)
          (horizontalColumnDegree_spec p i hi)) ≫
      horizontalNaturalDirectColumnProjectionComponent K p
        (horizontalColumnDegree p i) ≫
      eqToHom (congrArg
        (fun j => (horizontalDirectColumnCochain K p).X j)
          (horizontalColumnDegree_spec p i hi).symm)
  · exact 0

/-- The supported component formula for finite-stage column projection.

At degree `-p-q`, the arbitrary-degree finite-stage projection equals its `(p,q)` component. -/
theorem horizontalNaturalDirectColumnProjection_eq_component (p q : ℕ) :
    horizontalNaturalDirectColumnProjection K p (-(p : ℤ) - q) =
      horizontalNaturalDirectColumnProjectionComponent K p q := by
  unfold horizontalNaturalDirectColumnProjection
  rw [dite_eq_left (show -(p : ℤ) - q ≤ -(p : ℤ) by omega)]
  simp [horizontalColumnDegree]

/-- The finite-stage column projection above support.

In cochain degree `i>-p`, the projection to direct column `p` is zero. -/
theorem horizontalNaturalDirectColumnProjection_eq_zero_of_lt
    (p : ℕ) (i : ℤ) (hi : -(p : ℤ) < i) :
    horizontalNaturalDirectColumnProjection K p i = 0 := by
  unfold horizontalNaturalDirectColumnProjection
  rw [dite_eq_right (by lia)]

/-- Differential compatibility of finite-stage direct-column components.

The supported components commute with the extended filtered differential and the direct-column
signed vertical differential. -/
theorem horizontalNaturalDirectColumnProjectionComponent_comm (p q : ℕ) :
    horizontalNaturalDirectColumnProjectionComponent K p (q + 1) ≫
        (horizontalDirectColumnCochain K p).d (-(p : ℤ) - (q + 1))
          (-(p : ℤ) - q) =
      ((horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat).d (-(p : ℤ) - (q + 1))
          (-(p : ℤ) - q) ≫
        horizontalNaturalDirectColumnProjectionComponent K p q := by
  apply (cancel_mono (horizontalDirectColumnCochainXIso K p q).hom).1
  dsimp [horizontalNaturalDirectColumnProjectionComponent]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [horizontalDirectColumnCochainXIso_inv_d_hom]
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
  rw [hExt]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [horizontalFilteredTotalD_topProjection]

/-- The finite-stage cochain projection onto its direct column.

Assemble the supported component maps and zero unsupported components into a cochain map. -/
noncomputable def horizontalNaturalDirectColumnProjectionMap (p : ℕ) :
    (horizontalFilteredTotalComplex K p).extend
        ComplexShape.embeddingDownNat ⟶
      horizontalDirectColumnCochain K p where
  f := horizontalNaturalDirectColumnProjection K p
  comm' := by
    intro i j hij
    by_cases hj : -(p : ℤ) < j
    · exact (horizontalDirectColumnCochain_isZero_X_of_lt K p j hj).eq_of_tgt _ _
    · have hjle : j ≤ -(p : ℤ) := by lia
      have hiRel : i + 1 = j := by simpa only [ComplexShape.up_Rel] using hij
      obtain ⟨q, hjEq⟩ : ∃ q : ℕ, j = -(p : ℤ) - q :=
        ⟨horizontalColumnDegree p j,
          horizontalColumnDegree_spec p j hjle⟩
      have hiEq : i = -(p : ℤ) - ((q + 1 : ℕ) : ℤ) := by
        push_cast
        omega
      rw [hiEq, hjEq]
      rw [horizontalNaturalDirectColumnProjection_eq_component K p (q + 1),
        horizontalNaturalDirectColumnProjection_eq_component K p q]
      exact horizontalNaturalDirectColumnProjectionComponent_comm K p q

/-- The preceding-stage vanishing identity in a supported new-column degree.

At degree `-(p+1)-q`, the extended inclusion from stage `p` into `p+1` followed by the new-
column component projection is zero. -/
theorem horizontalNaturalDirectColumnProjectionComponent_stageMap_zero
    (p q : ℕ) :
    ((ComplexShape.embeddingDownNat.extendFunctor C).map
      (horizontalFilteredTotalComplexMap K (Nat.le_succ p))).f
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalNaturalDirectColumnProjectionComponent K (p + 1) q = 0 := by
  dsimp [horizontalNaturalDirectColumnProjectionComponent]
  change (HomologicalComplex.extendMap
      (horizontalFilteredTotalComplexMap K (Nat.le_succ p))
      ComplexShape.embeddingDownNat).f (-((p : ℤ) + 1) - q) ≫ _ = 0
  rw [HomologicalComplex.extendMap_f _ _
    (i := p + 1 + q) (i' := -((p : ℤ) + 1) - q)
    (by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ horizontalFilteredTotalMap K (Nat.le_succ p) (p + 1 + q) ≫
      horizontalFilteredTopProjection K (p + 1) q ≫ _ = 0
  rw [horizontalFilteredTotalMap_succ_topProjection_assoc]
  simp

/-- The zero-composite chain identity for consecutive finite stages.

The extended stage inclusion `F_p → F_(p+1)` followed by projection to direct column `p+1` is
the zero cochain map. -/
theorem horizontalNaturalDirectColumnProjectionMap_stageMap_zero (p : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor C).map
        (horizontalFilteredTotalComplexMap K (Nat.le_succ p)) ≫
      horizontalNaturalDirectColumnProjectionMap K (p + 1) = 0 := by
  ext i
  change ((ComplexShape.embeddingDownNat.extendFunctor C).map
      (horizontalFilteredTotalComplexMap K (Nat.le_succ p))).f i ≫
        horizontalNaturalDirectColumnProjection K (p + 1) i = 0
  by_cases hi : -((p + 1 : ℕ) : ℤ) < i
  · rw [horizontalNaturalDirectColumnProjection_eq_zero_of_lt K (p + 1) i hi,
      comp_zero]
  · have hile : i ≤ -((p + 1 : ℕ) : ℤ) := by lia
    obtain ⟨q, hiEq⟩ : ∃ q : ℕ, i = -((p + 1 : ℕ) : ℤ) - q :=
      ⟨horizontalColumnDegree (p + 1) i,
        horizontalColumnDegree_spec (p + 1) i hile⟩
    rw [hiEq,
      horizontalNaturalDirectColumnProjection_eq_component]
    exact horizontalNaturalDirectColumnProjectionComponent_stageMap_zero K p q

end HomologicalComplex₂

end
