/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageFiniteBoundary

/-!
# Complete-filtration boundaries of first-page column sections

Let `K` be a first-quadrant bicomplex in an abelian category. Finite filtration stage `p`
retains columns through `p`. A direct column at `(p,q)` is represented in total degree `p+q`
and cochain degree `-p-q`.

On vertical cycles, the differential of a top-column inclusion is its horizontal bicomplex
differential followed by the preceding-column inclusion. Transport through the finite-to-
complete filtration comparisons gives the corresponding complete-stage section formula. For
the section of column `p+2`, the target is column `p+1`, followed by that column's section and
next filtration map.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The top-column inclusion into a finite filtered complex term.

Include `K_(p,q)` into total degree `p+q` of filtration stage `p`, with the target written as
the bundled filtered complex term. -/
noncomputable def horizontalFilteredTopInclusionComplex (p q : ℕ) :
    (K.X p).X q ⟶ (horizontalFilteredTotalComplex K p).X (p + q) := by
  change (K.X p).X q ⟶ horizontalFilteredTotalObj K p (p + q)
  exact horizontalFilteredTopInclusion K p q

/-- The differential between finite filtered-complex terms.

For stage `k`, use its filtered total differential from total degree `n` to degree `m`. -/
noncomputable def horizontalFilteredTotalDComplex (k n m : ℕ) :
    (horizontalFilteredTotalComplex K k).X n ⟶
      (horizontalFilteredTotalComplex K k).X m := by
  change horizontalFilteredTotalObj K k n ⟶ horizontalFilteredTotalObj K k m
  exact horizontalFilteredTotalD K k n m

/-- The preceding-column inclusion into the next finite stage.

Include `K_(p,q)` into total degree `p+q` of filtration stage `p+1`. -/
noncomputable def horizontalFilteredPreviousColumnInclusionComplex
    (p q : ℕ) :
    (K.X p).X q ⟶ (horizontalFilteredTotalComplex K (p + 1)).X (p + q) := by
  change (K.X p).X q ⟶ horizontalFilteredTotalObj K (p + 1) (p + q)
  exact horizontalFilteredPreviousColumnInclusion K p q

/-- The finite-stage top-column boundary on vertical cycles.

For cycles in column `p+1` at vertical degree `q`, top inclusion followed by the filtered
differential from `p+1+q` to `p+q` equals the horizontal map to column `p` followed by its
preceding-column inclusion. -/
theorem horizontalDirectColumnTopInclusionComplex_d_eq_previous
    (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      horizontalFilteredTopInclusionComplex K (p + 1) q ≫
      horizontalFilteredTotalDComplex K (p + 1) (p + 1 + q) (p + q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      (K.d (p + 1) p).f q ≫
      horizontalFilteredPreviousColumnInclusionComplex K p q := by
  change (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      horizontalFilteredTopInclusion K (p + 1) q ≫
      horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) = _
  exact horizontalDirectColumnTopInclusion_d_eq_previous K p q

/-- The finite-total formula for a complete-stage section boundary.

The complete section of column `p+1` on direct-column cycles at cochain degree `-(p+1)-q` has
differential equal to the finite-stage top inclusion and filtered total boundary, followed by
the extension and complete-stage comparisons. -/
theorem horizontalCompleteSuccSection_d_eq_filtered (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1))).d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      horizontalFilteredTopInclusionComplex K (p + 1) q ≫
      horizontalFilteredTotalDComplex K (p + 1) (p + 1 + q) (p + q) ≫
      ((horizontalFilteredTotalComplex K (p + 1)).extendXIso
        ComplexShape.embeddingDownNat
        (i := p + q) (i' := -(p : ℤ) - q)
        (by simp; omega)).inv ≫
      (horizontalNaturalStageCochainIso K (p + 1)).inv.f
        (-(p : ℤ) - q) ≫
      (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).inv.f
        (-(p : ℤ) - q) := by
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  let j : ℤ := -(p : ℤ) - q
  let eM := horizontalCompleteFiltrationCochainMonoUpperSuccIso K p
  let eN := horizontalNaturalStageCochainIso K (p + 1)
  let eEn := (horizontalFilteredTotalComplex K (p + 1)).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + 1 + q) (i' := n) (by dsimp [n]; simp; omega)
  let eEj := (horizontalFilteredTotalComplex K (p + 1)).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + q) (i' := j) (by dsimp [j]; simp; omega)
  let eD := horizontalDirectColumnCochainXIso K (p + 1) q
  dsimp [horizontalCompleteSuccDirectColumnSection]
  simp only [Category.assoc]
  change (horizontalDirectColumnCochain K (p + 1)).iCycles n ≫
    eD.hom ≫ horizontalFilteredTopInclusionComplex K (p + 1) q ≫ eEn.inv ≫
    eN.inv.f n ≫ eM.inv.f n ≫
    ((horizontalCompleteFiltrationCochainDiagram K).obj
      (horizontalFirstPageUpperIndex (p + 1))).d n j =
    (horizontalDirectColumnCochain K (p + 1)).iCycles n ≫
      eD.hom ≫ horizontalFilteredTopInclusionComplex K (p + 1) q ≫
      horizontalFilteredTotalDComplex K (p + 1) (p + 1 + q) (p + q) ≫
      eEj.inv ≫ eN.inv.f j ≫ eM.inv.f j
  rw [eM.inv.comm n j]
  rw [reassoc_of% eN.inv.comm n j]
  have hExt := (horizontalFilteredTotalComplex K (p + 1)).extend_d_eq
    ComplexShape.embeddingDownNat
    (i := p + 1 + q) (j := p + q) (i' := n) (j' := j)
    (hi := by dsimp [n]; rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)
    (hj := by dsimp [j]; rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)
  change ((horizontalFilteredTotalComplex K (p + 1)).extend
      ComplexShape.embeddingDownNat).d n j =
    eEn.hom ≫ horizontalFilteredTotalDComplex K (p + 1)
      (p + 1 + q) (p + q) ≫ eEj.inv at hExt
  have hCancel : eEn.inv ≫
      (eEn.hom ≫ horizontalFilteredTotalDComplex K (p + 1)
        (p + 1 + q) (p + q) ≫ eEj.inv) ≫
      eN.inv.f j ≫ eM.inv.f j =
    horizontalFilteredTotalDComplex K (p + 1) (p + 1 + q) (p + q) ≫
      eEj.inv ≫ eN.inv.f j ≫ eM.inv.f j := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hExt]
  rw [hCancel]

/-- The next-filtration formula for a complete-stage section.

The complete section of column `p+1` followed by the next filtration map is its finite
inclusion into stage `p+2`, transported to cochain degree `-(p+1)-q`. -/
theorem horizontalCompleteSuccSection_nextMap_eq_filtered (p q : ℕ) :
    (horizontalDirectColumnCochainXIso K (p + 1) q).inv ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      (horizontalFirstPageNextFiltrationMap K (p + 1)).f
        (-((p + 1 : ℕ) : ℤ) - q) =
    horizontalFilteredPreviousColumnInclusionComplex K (p + 1) q ≫
      ((horizontalFilteredTotalComplex K (p + 2)).extendXIso
        ComplexShape.embeddingDownNat
        (i := p + 1 + q) (i' := -((p + 1 : ℕ) : ℤ) - q)
        (by simp; omega)).inv ≫
      (horizontalNaturalStageCochainIso K (p + 2)).inv.f
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalCompleteFiltrationCochainMonoUpperSuccIso K (p + 1)).inv.f
        (-((p + 1 : ℕ) : ℤ) - q) := by
  let j : ℤ := -((p + 1 : ℕ) : ℤ) - q
  let eMt := horizontalCompleteFiltrationCochainMonoUpperSuccIso K p
  let eNt := horizontalNaturalStageCochainIso K (p + 1)
  let eEt := (horizontalFilteredTotalComplex K (p + 1)).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + 1 + q) (i' := j) (by dsimp [j]; simp; omega)
  let eMs := horizontalCompleteFiltrationCochainMonoUpperSuccIso K (p + 1)
  let eNs := horizontalNaturalStageCochainIso K (p + 2)
  let eEs := (horizontalFilteredTotalComplex K (p + 2)).extendXIso
    ComplexShape.embeddingDownNat
    (i := p + 1 + q) (i' := j) (by dsimp [j]; simp; omega)
  let eMtX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eMt
  let eNtX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eNt
  let eMsX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eMs
  let eNsX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eNs
  let eL := horizontalCompleteFiltrationCochainMonoLowerSuccIso K (p + 1)
  let eLX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eL
  let eMidX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso
    (horizontalFirstPageMiddleStageIso K (p + 1))
  let t := eMsX.hom ≫ eNsX.hom ≫ eEs.hom
  have ht : IsIso t := by dsimp [t]; infer_instance
  let _ := ht
  apply (cancel_mono t).1
  dsimp [t, horizontalCompleteSuccDirectColumnSection]
  rw [horizontalFirstPageNextFiltrationMap_eq_middle K (p + 1)]
  simp only [HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc]
  change horizontalFilteredTopInclusionComplex K (p + 1) q ≫
      eEt.inv ≫ eNtX.inv ≫ eMtX.inv ≫
      (horizontalFirstPageMiddleStageIso K (p + 1)).hom.f j ≫
      (horizontalFirstPageFiltrationMap K (p + 2)).f j ≫
      eMsX.hom ≫ eNsX.hom ≫ eEs.hom =
    horizontalFilteredPreviousColumnInclusionComplex K (p + 1) q ≫
      eEs.inv ≫ eNsX.inv ≫ eMsX.inv ≫
      eMsX.hom ≫ eNsX.hom ≫ eEs.hom
  simp only [Iso.inv_hom_id_assoc]
  rw [eEs.inv_hom_id, Category.comp_id]
  have hPage := HomologicalComplex.congr_hom
    (horizontalFirstPageFiltrationMap_succ_monoIso K (p + 1)) j
  change (horizontalFirstPageFiltrationMap K (p + 2)).f j ≫ eMsX.hom =
    eLX.hom ≫
      ((ComplexShape.embeddingDownNat.extendFunctor C).map
        ((horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ (p + 1)))).hom.left).f j at hPage
  rw [reassoc_of% hPage]
  have hMiddle : eMtX.inv ≫ eMidX.hom ≫ eLX.hom = 𝟙 _ := by
    exact horizontalFirstPageMiddleStageTriangle_f K p j
  change horizontalFilteredTopInclusionComplex K (p + 1) q ≫
      eEt.inv ≫ eNtX.inv ≫ eMtX.inv ≫ eMidX.hom ≫ eLX.hom ≫
      ((ComplexShape.embeddingDownNat.extendFunctor C).map
        ((horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ (p + 1)))).hom.left).f j ≫
      eNsX.hom ≫ eEs.hom = _
  rw [reassoc_of% hMiddle]
  have hNat := HomologicalComplex.congr_hom
    (horizontalNaturalStageCochainIso_naturality K
      (Nat.le_succ (p + 1))) j
  change ((ComplexShape.embeddingDownNat.extendFunctor C).map
      ((horizontalTotalFiltration K).toMonoOver.map
        (homOfLE (Nat.le_succ (p + 1)))).hom.left).f j ≫ eNsX.hom =
    eNtX.hom ≫
      (HomologicalComplex.extendMap
        (horizontalFilteredTotalComplexMap K (Nat.le_succ (p + 1)))
        ComplexShape.embeddingDownNat).f j at hNat
  rw [reassoc_of% hNat]
  simp only [Iso.inv_hom_id_assoc]
  have hExt := HomologicalComplex.extendMap_f
    (horizontalFilteredTotalComplexMap K (Nat.le_succ (p + 1)))
    ComplexShape.embeddingDownNat
    (i := p + 1 + q) (i' := j) (by dsimp [j]; simp; omega)
  change (HomologicalComplex.extendMap
      (horizontalFilteredTotalComplexMap K (Nat.le_succ (p + 1)))
      ComplexShape.embeddingDownNat).f j =
    eEt.hom ≫ horizontalFilteredTotalMap K (Nat.le_succ (p + 1))
      (p + 1 + q) ≫ eEs.inv at hExt
  rw [reassoc_of% hExt]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change horizontalFilteredTotalι K (p + 1) (p + 1 + q)
      (horizontalFilteredTopIndex (p + 1) q) ≫
        horizontalFilteredTotalMap K (Nat.le_succ (p + 1)) (p + 1 + q) =
    horizontalFilteredTotalι K (p + 2) (p + 1 + q)
      (horizontalFilteredTotalIndexMap (Nat.le_succ (p + 1))
        (horizontalFilteredTopIndex (p + 1) q))
  exact horizontalFilteredTotalι_map K (Nat.le_succ (p + 1))
    (p + 1 + q) (horizontalFilteredTopIndex (p + 1) q)

/-- The horizontal boundary formula for successive complete-stage sections.

On direct-column cycles from column `p+2`, the complete-stage differential is the horizontal
map to column `p+1`, followed by that column's section and next complete filtration map. The
cochain degrees are `-(p+2)-q` and `-(p+1)-q`. -/
theorem horizontalCompleteSuccDirectColumnSection_d (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 2)).iCycles
        (-((p + 2 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K (p + 1) q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 2))).d
          (-((p + 2 : ℕ) : ℤ) - q) (-((p + 1 : ℕ) : ℤ) - q) =
    (horizontalDirectColumnCochain K (p + 2)).iCycles
        (-((p + 2 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 2) q).hom ≫
      (K.d (p + 2) (p + 1)).f q ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).inv ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      (horizontalFirstPageNextFiltrationMap K (p + 1)).f
        (-((p + 1 : ℕ) : ℤ) - q) := by
  rw [horizontalCompleteSuccSection_d_eq_filtered K (p + 1) q]
  rw [reassoc_of%
    horizontalDirectColumnTopInclusionComplex_d_eq_previous K (p + 1) q]
  rw [← horizontalCompleteSuccSection_nextMap_eq_filtered K p q]

end HomologicalComplex₂

end
