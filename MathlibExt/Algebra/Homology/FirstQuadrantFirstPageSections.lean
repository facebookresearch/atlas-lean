/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageConnecting

/-!
# Degreewise sections of first-page column projections

The projection from a filtration stage to its new direct column has a
canonical section in every supported degree.  These sections need not form a
cochain map; they are the degreewise lifts used in the connecting-homomorphism
calculation.
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
/-- The top-column inclusion is a section of the top-column projection. -/
theorem horizontalFilteredTopInclusion_projection (p q : ℕ) :
    horizontalFilteredTopInclusion K p q ≫
      horizontalFilteredTopProjection K p q = 𝟙 _ := by
  simpa [horizontalFilteredTopInclusion, horizontalFilteredTopIndex] using
    horizontalFilteredTopι_topProjection K p q

/-- Section of the direct-column projection component expressed through the
complete filtration stage. -/
noncomputable def horizontalCompleteDirectColumnSectionComponent (p q : ℕ) :
    (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) ⟶
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p)).X (-(p : ℤ) - q) :=
  (horizontalDirectColumnCochainXIso K p q).hom ≫
    horizontalFilteredTopInclusion K p q ≫
    ((horizontalFilteredTotalComplex K p).extendXIso
      ComplexShape.embeddingDownNat
      (i := p + q) (i' := -(p : ℤ) - q) (by simp; omega)).inv ≫
    (horizontalCompleteFiltrationCochainUpperIso K p).inv.f (-(p : ℤ) - q)

/-- The complete-stage section is a right inverse of the corresponding
direct-column projection component. -/
theorem horizontalCompleteDirectColumnSectionComponent_projection
    (p q : ℕ) :
    horizontalCompleteDirectColumnSectionComponent K p q ≫
      horizontalDirectColumnProjectionComponent K p q = 𝟙 _ := by
  let n : ℤ := -(p : ℤ) - q
  let eC := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapIso
    (horizontalCompleteFiltrationCochainUpperIso K p)
  let eE := (horizontalFilteredTotalComplex K p).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + q) (i' := n) (by dsimp [n]; simp; omega)
  let eD := horizontalDirectColumnCochainXIso K p q
  dsimp [horizontalCompleteDirectColumnSectionComponent,
    horizontalDirectColumnProjectionComponent]
  simp only [Category.assoc]
  change eD.hom ≫ horizontalFilteredTopInclusion K p q ≫ eE.inv ≫
      eC.inv ≫ eC.hom ≫ eE.hom ≫
      horizontalFilteredTopProjection K p q ≫ eD.inv = 𝟙 _
  simp only [Iso.inv_hom_id_assoc]
  have htop := horizontalFilteredTopInclusion_projection K p q
  calc
    _ = eD.hom ≫
        (horizontalFilteredTopInclusion K p q ≫
          horizontalFilteredTopProjection K p q) ≫ eD.inv := by
      simp only [Category.assoc]
    _ = eD.hom ≫ 𝟙 _ ≫ eD.inv := by rw [htop]
    _ = _ := by simp

/-- Section of the actual complete-filtration projection onto the positive
column `p+1`. -/
noncomputable def horizontalCompleteSuccDirectColumnSection (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).X
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1))).X
          (-((p + 1 : ℕ) : ℤ) - q) :=
  (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
    horizontalFilteredTopInclusion K (p + 1) q ≫
    ((horizontalFilteredTotalComplex K (p + 1)).extendXIso
      ComplexShape.embeddingDownNat
      (i := p + 1 + q) (i' := -((p + 1 : ℕ) : ℤ) - q)
      (by simp; omega)).inv ≫
    (horizontalNaturalStageCochainIso K (p + 1)).inv.f
      (-((p + 1 : ℕ) : ℤ) - q) ≫
    (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).inv.f
      (-((p + 1 : ℕ) : ℤ) - q)

/-- The positive-column section is a right inverse of the projection map in
the supported degree. -/
theorem horizontalCompleteSuccDirectColumnSection_projection (p q : ℕ) :
    horizontalCompleteSuccDirectColumnSection K p q ≫
        (horizontalCompleteDirectColumnProjectionMap K (p + 1)).f
          (-((p + 1 : ℕ) : ℤ) - q) =
      𝟙 _ := by
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  let eM := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapIso
    (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p)
  let eN := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapIso
    (horizontalNaturalStageCochainIso K (p + 1))
  let eE := (horizontalFilteredTotalComplex K (p + 1)).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + 1 + q) (i' := n) (by dsimp [n]; simp; omega)
  let eD := horizontalDirectColumnCochainXIso K (p + 1) q
  dsimp [horizontalCompleteSuccDirectColumnSection,
    horizontalCompleteDirectColumnProjectionMap,
    horizontalCompleteSuccDirectColumnProjectionMap,
    horizontalMonoStageDirectColumnProjectionMap,
    horizontalNaturalDirectColumnProjectionMap]
  simp only [Category.assoc]
  change eD.hom ≫ horizontalFilteredTopInclusion K (p + 1) q ≫
      eE.inv ≫ eN.inv ≫ eM.inv ≫ eM.hom ≫ eN.hom ≫
      horizontalNaturalDirectColumnProjection K (p + 1) n = 𝟙 _
  simp only [Iso.inv_hom_id_assoc]
  rw [horizontalNaturalDirectColumnProjection_eq_component]
  dsimp [horizontalNaturalDirectColumnProjectionComponent]
  change eD.hom ≫ horizontalFilteredTopInclusion K (p + 1) q ≫
      eE.inv ≫ eE.hom ≫ horizontalFilteredTopProjection K (p + 1) q ≫
      eD.inv = 𝟙 _
  simp only [Iso.inv_hom_id_assoc]
  have htop := horizontalFilteredTopInclusion_projection K (p + 1) q
  calc
    _ = eD.hom ≫
        (horizontalFilteredTopInclusion K (p + 1) q ≫
          horizontalFilteredTopProjection K (p + 1) q) ≫ eD.inv := by
      simp only [Category.assoc]
    _ = eD.hom ≫ 𝟙 _ ≫ eD.inv := by rw [htop]
    _ = _ := by simp

end HomologicalComplex₂

end
