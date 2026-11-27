/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Totalizing homotopies of bicomplex maps

A homotopy in the horizontal complex direction induces a homotopy between
the corresponding maps of total complexes.  The vertical construction is
obtained by flipping the bicomplex, applying the horizontal construction, and
conjugating by the canonical total-flip isomorphisms.

The horizontal component includes the homotopy map into the shifted
bidegree with the total-complex sign `ε₁`.  Cross-direction terms cancel by
the bicomplex sign identity and the fact that every homotopy component is a
map in the other complex direction.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

open HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K L : HomologicalComplex₂ C c₁ c₂} {f g : K ⟶ L}
  (h : Homotopy f g) (c : ComplexShape J) [DecidableEq J]
  [TotalComplexShape c₁ c₂ c] [K.HasTotal c] [L.HasTotal c]

/-- Degreewise components of the totalized horizontal homotopy. -/
noncomputable def totalHomotopy₁Hom (j j' : J) :
    (K.total c).X j ⟶ (L.total c).X j' :=
  K.totalDesc fun i₁ i₂ _ =>
    ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
      ((h.hom i₁ (c₁.prev i₁)).f i₂ ≫
        L.ιTotalOrZero c (c₁.prev i₁) i₂ j')

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a horizontal total-homotopy component to one bidegree. -/
@[reassoc]
theorem ιTotal_totalHomotopy₁Hom
    (i₁ i₁' : I₁) (i₂ : I₂) (j j' : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁', i₂) = j)
    (hi : c₁.prev i₁' = i₁) :
    K.ιTotal c i₁' i₂ j hj ≫ totalHomotopy₁Hom h c j j' =
      ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
        ((h.hom i₁' i₁).f i₂ ≫ L.ιTotalOrZero c i₁ i₂ j') := by
  subst hi
  simp [totalHomotopy₁Hom]

set_option backward.isDefEq.respectTransparency false in
theorem totalHomotopy₁Hom_zero (j j' : J) (hrel : ¬c.Rel j' j) :
    totalHomotopy₁Hom h c j j' = 0 := by
  ext i₁ i₂ hj
  dsimp [totalHomotopy₁Hom]
  rw [comp_zero, HomologicalComplex₂.ι_totalDesc]
  by_cases hi : c₁.Rel (c₁.prev i₁) i₁
  · rw [ιTotalOrZero_eq_zero, comp_zero, smul_zero]
    intro hπ
    apply hrel
    rw [← hj, ← hπ]
    exact ComplexShape.rel_π₁ c₂ c hi i₂
  · rw [h.zero _ _ hi, HomologicalComplex.zero_f, zero_comp,
      smul_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem totalHomotopy₁_comm_aux
    {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁')
    {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') (j : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) :
    ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
        ((h.hom i₁' i₁).f i₂ ≫ L.d₂ c i₁ i₂ j) =
      -(K.d₂ c i₁' i₂ (c.next j) ≫
        totalHomotopy₁Hom h c (c.next j) j) := by
  have hj' : ComplexShape.π c₁ c₂ c (i₁, i₂') = j := by
    rw [← hj, ← ComplexShape.next_π₂ c₁ c i₁ hi₂,
      ComplexShape.next_π₁ c₂ c hi₁ i₂]
  rw [HomologicalComplex₂.d₂_eq L c i₁ hi₂ j hj',
    HomologicalComplex₂.d₂_eq K c i₁' hi₂ _
      (by rw [← c.next_eq' (ComplexShape.rel_π₂ c₁ c i₁' hi₂), hj])]
  rw [Linear.comp_units_smul, smul_smul]
  simp only [Linear.units_smul_comp]
  simp_rw [Category.assoc]
  rw [ιTotal_totalHomotopy₁Hom h c _ i₁' _ _ _ _
    (c₁.prev_eq' hi₁)]
  rw [ιTotalOrZero_eq L c i₁ i₂' j hj']
  rw [HomologicalComplex.Hom.comm_assoc]
  rw [ComplexShape.ε₁_ε₂ c hi₁ hi₂, neg_mul,
    Units.neg_smul]
  simp only [Linear.comp_units_smul, smul_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The totalized horizontal components satisfy the chain-homotopy equation. -/
theorem totalHomotopy₁_comm (j : J) :
    (HomologicalComplex₂.total.map f c).f j =
      (K.total c).d j (c.next j) ≫
          totalHomotopy₁Hom h c (c.next j) j +
        totalHomotopy₁Hom h c j (c.prev j) ≫
          (L.total c).d (c.prev j) j +
      (HomologicalComplex₂.total.map g c).f j := by
  ext i₁ i₂ hj
  simp only [ιTotal_map, h.comm i₁,
    dNext_eq_dFrom_fromNext, dFrom, fromNext,
    prevD_eq_toPrev_dTo, toPrev, dTo, AddMonoidHom.mk'_apply,
    HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    Preadditive.add_comp,
    HomologicalComplex₂.total_d,
    Preadditive.comp_add, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc, add_left_inj]
  have hsum : ∀ {X Y : C} (a b c' d e f' : X ⟶ Y),
      a = c' → b = e → f' = -d → a + b = c' + d + (e + f') := by
    rintro X Y a b _ d _ _ rfl rfl rfl
    abel
  apply hsum
  · by_cases hi₁ : c₁.Rel i₁ (c₁.next i₁)
    · rw [HomologicalComplex₂.d₁_eq K c hi₁ i₂ _
          (by rw [← hj, ComplexShape.next_π₁ c₂ c hi₁])]
      rw [Linear.units_smul_comp]
      simp_rw [Category.assoc]
      rw [ιTotal_totalHomotopy₁Hom h c i₁ _ i₂ _ _ _
        (c₁.prev_eq' hi₁)]
      rw [ιTotalOrZero_eq L c i₁ i₂ j hj]
      simp only [Linear.comp_units_smul,
        smul_smul, Int.units_mul_self, one_smul]
    · simp only [K.shape _ _ hi₁, HomologicalComplex.zero_f,
        CategoryTheory.Limits.zero_comp,
        HomologicalComplex₂.d₁_eq_zero K c i₁ i₂ _ hi₁]
  · rw [ιTotal_totalHomotopy₁Hom_assoc h c (c₁.prev i₁) i₁ i₂ j
      (c.prev j) hj rfl]
    by_cases hi₁ : c₁.Rel (c₁.prev i₁) i₁
    · rw [ιTotalOrZero_eq L c (c₁.prev i₁) i₂ (c.prev j)
          (by rw [← ComplexShape.prev_π₁ c₂ c hi₁, hj])]
      simp only [Linear.units_smul_comp]
      simp_rw [Category.assoc]
      rw [HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.d₁_eq L c hi₁ i₂ _ hj]
      simp only [Linear.comp_units_smul, smul_smul,
        Int.units_mul_self, one_smul]
    · simp only [h.zero _ _ hi₁, HomologicalComplex.zero_f,
        CategoryTheory.Limits.zero_comp, smul_zero]
  · rw [ιTotal_totalHomotopy₁Hom_assoc h c (c₁.prev i₁) i₁ i₂ j
      (c.prev j) hj rfl]
    by_cases hi₁ : c₁.Rel (c₁.prev i₁) i₁
    · rw [ιTotalOrZero_eq L c (c₁.prev i₁) i₂ (c.prev j)
          (by rw [← ComplexShape.prev_π₁ c₂ c hi₁, hj])]
      simp only [Linear.units_smul_comp]
      simp_rw [Category.assoc]
      rw [HomologicalComplex₂.ι_D₂]
      by_cases hi₂ : c₂.Rel i₂ (c₂.next i₂)
      · exact totalHomotopy₁_comm_aux h c hi₁ hi₂ j hj
      · simp only [HomologicalComplex₂.d₂_eq_zero L c _ _ _ hi₂,
          HomologicalComplex₂.d₂_eq_zero K c _ _ _ hi₂,
          CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp,
          smul_zero, neg_zero]
    · rw [h.zero _ _ hi₁, HomologicalComplex.zero_f, zero_comp,
        smul_zero, zero_comp, zero_eq_neg]
      by_cases hi₂ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases hjnext : c.Rel j (c.next j)
        · rw [HomologicalComplex₂.d₂_eq K c i₁ hi₂ _
              (by rw [← ComplexShape.next_π₂ c₁ c i₁ hi₂, hj]),
            Linear.units_smul_comp, Category.assoc,
            ιTotal_totalHomotopy₁Hom h c _ _ _ _ _ _ rfl,
            h.zero _ _ hi₁, HomologicalComplex.zero_f,
            zero_comp, smul_zero, CategoryTheory.Limits.comp_zero,
            smul_zero]
        · rw [totalHomotopy₁Hom_zero h c _ _ hjnext,
            CategoryTheory.Limits.comp_zero]
      · simp only [HomologicalComplex₂.d₂_eq_zero K c _ _ _ hi₂,
          CategoryTheory.Limits.zero_comp]

/-- A horizontal homotopy of bicomplex maps induces a homotopy of their
total-complex maps. -/
noncomputable def totalMapHomotopy₁ :
    Homotopy (HomologicalComplex₂.total.map f c)
      (HomologicalComplex₂.total.map g c) where
  hom := totalHomotopy₁Hom h c
  zero := totalHomotopy₁Hom_zero h c
  comm := totalHomotopy₁_comm h c

/-- The morphism induced between flipped bicomplexes. -/
noncomputable def flipMap (φ : K ⟶ L) : K.flip ⟶ L.flip where
  f i :=
    { f := fun j => (φ.f j).f i
      comm' := by
        intro j j' _
        exact congrArg (fun k => k.f i) (φ.comm j j') }
  comm' := by
    intro i i' _
    ext j
    exact (φ.f j).comm i i'

section Flip

variable [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]
  [K.flip.HasTotal c] [L.flip.HasTotal c]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the total-flip isomorphism. -/
@[reassoc]
theorem totalFlipIso_hom_naturality (φ : K ⟶ L) :
    HomologicalComplex₂.total.map
          (flipMap φ) c ≫
        (L.totalFlipIso c).hom =
      (K.totalFlipIso c).hom ≫ HomologicalComplex₂.total.map φ c := by
  ext j i₂ i₁ hj
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc]
  change (φ.f i₁).f i₂ ≫
      (ComplexShape.σ c₁ c₂ c i₁ i₂ • L.ιTotal c i₁ i₂ j _) =
    (ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j _) ≫
      (HomologicalComplex₂.total.map φ c).f j
  rw [Linear.comp_units_smul, Linear.units_smul_comp,
    HomologicalComplex₂.ιTotal_map]

/-- Conjugating the flipped total map recovers the original total map. -/
theorem flipConjugate_eq_totalMap (φ : K ⟶ L) :
    (K.totalFlipIso c).inv ≫
        (HomologicalComplex₂.total.map (flipMap φ) c ≫
          (L.totalFlipIso c).hom) =
      HomologicalComplex₂.total.map φ c := by
  rw [totalFlipIso_hom_naturality]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A horizontal homotopy after flipping the bicomplex induces a vertical
homotopy of the original total-complex maps. -/
noncomputable def totalMapHomotopy₂
    (hflip : Homotopy (flipMap f) (flipMap g)) :
    Homotopy (HomologicalComplex₂.total.map f c)
      (HomologicalComplex₂.total.map g c) :=
  let H := totalMapHomotopy₁ hflip c
  let Hconj := (H.compRight (L.totalFlipIso c).hom).compLeft
    (K.totalFlipIso c).inv
  (Homotopy.ofEq (flipConjugate_eq_totalMap c f).symm).trans
    (Hconj.trans (Homotopy.ofEq (flipConjugate_eq_totalMap c g)))

end Flip

end HomologicalComplex₂
