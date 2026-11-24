/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.MixedBicomplex
public import MathlibExt.Algebra.Homology.TotalComplexFirstColumn
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

public meta import Lean.Elab.Tactic.Omega

/-!
# Degree one of the actual (b,B) total complex

The native mixed bicomplex has one supported summand in degrees zero and one,
and two supported summands in degree two. Its degree-one short complex is
therefore K₂ ⊞ K₀ → K₁ → K₀, with first arrow [b₂,B₀] and second arrow b₁.
The object comparisons below are constructed from the actual coprojections
and their universal property. No comparison or isomorphism is a caller input.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace ChainComplex

universe u v

/-- Native Abelian homology applies to every designated zero-morphism view. -/
private theorem mixedHomologyOneCategoryWithHomology
    {C₀ : Type u} [hCategory : Category.{v} C₀] [hAbelian : Abelian C₀]
    (z : HasZeroMorphisms C₀) : @CategoryWithHomology C₀ hCategory z := by
  let zAbelian : HasZeroMorphisms C₀ :=
    @Preadditive.preadditiveHasZeroMorphisms C₀ hCategory hAbelian.toPreadditive
  have hNative : @CategoryWithHomology C₀ hCategory zAbelian :=
    @CategoryTheory.categoryWithHomology_of_abelian C₀ hCategory hAbelian
  have hz : zAbelian = z := Subsingleton.elim _ _
  exact Eq.mp (congrArg
    (fun z' : HasZeroMorphisms C₀ => @CategoryWithHomology C₀ hCategory z') hz) hNative

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
  (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)

local notation "B" => mixedBicomplex K H hSquare
local notation "T" => HomologicalComplex₂.total
  (mixedBicomplex K H hSquare) (ComplexShape.down ℕ)

variable [hTotal : HomologicalComplex₂.HasTotal
  (mixedBicomplex K H hSquare) (ComplexShape.down ℕ)]

/-- The actual degree-zero total object is its sole supported original term. -/
def mixedTotalZeroIso : (T).X 0 ≅ K.X 0 where
  hom := (B).totalDesc (fun p q hpq => by
    have hp : p = 0 := by change p + q = 0 at hpq; omega
    have hq : q = 0 := by change p + q = 0 at hpq; omega
    subst p
    subst q
    exact (mixedColumnIso K 0 0 0 rfl).hom)
  inv := (mixedColumnIso K 0 0 0 rfl).inv ≫
    (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hp : p = 0 := by change p + q = 0 at hpq; omega
    have hq : q = 0 := by change p + q = 0 at hpq; omega
    subst p
    subst q
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    let e : ((B).X 0).X 0 ≅ K.X 0 := mixedColumnIso K 0 0 0 rfl
    change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl) =
      (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫ 𝟙 _
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl) e.hom_inv_id
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    let e : ((B).X 0).X 0 ≅ K.X 0 := mixedColumnIso K 0 0 0 rfl
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id

/-- The actual degree-zero coprojection is retained by the object comparison. -/
@[reassoc]
lemma mixedTotalZeroIso_ι :
    (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫ (mixedTotalZeroIso K H hSquare).hom =
      (mixedColumnIso K 0 0 0 rfl).hom := by
  dsimp only [mixedTotalZeroIso]
  rw [HomologicalComplex₂.ι_totalDesc]

/-- The actual degree-one total object has only the supported original degree-one term. -/
def mixedTotalOneIso : (T).X 1 ≅ K.X 1 where
  hom := (B).totalDesc (fun p q hpq => if hp : p = 0 then by
    subst p
    have hq : q = 1 := by change 0 + q = 1 at hpq; omega
    subst q
    exact (mixedColumnIso K 0 1 1 rfl).hom
    else 0)
  inv := (mixedColumnIso K 0 1 1 rfl).inv ≫
    (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 1 := by change 0 + q = 1 at hpq; omega
      subst q
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      let e : ((B).X 0).X 1 ≅ K.X 1 := mixedColumnIso K 0 1 1 rfl
      change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) =
        (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) e.hom_inv_id
    · exact (mixedBicomplex_isZero_cell K H hSquare p q
        (by change p + q = 1 at hpq; omega)).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    let e : ((B).X 0).X 1 ≅ K.X 1 := mixedColumnIso K 0 1 1 rfl
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id

/-- The actual first-column degree-one coprojection is retained by the comparison. -/
@[reassoc]
lemma mixedTotalOneIso_ι :
    (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl ≫ (mixedTotalOneIso K H hSquare).hom =
      (mixedColumnIso K 0 1 1 rfl).hom := by
  dsimp only [mixedTotalOneIso]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

variable [HasBinaryBiproduct (K.X 2) (K.X 0)]

/-- Degree two is the biproduct of the original b₂ and B₀ source terms. -/
def mixedTotalTwoIso : (T).X 2 ≅ K.X 2 ⊞ K.X 0 where
  hom := (B).totalDesc (fun p q hpq => if hp : p = 0 then by
    subst p
    have hq : q = 2 := by change 0 + q = 2 at hpq; omega
    subst q
    exact (mixedColumnIso K 0 2 2 rfl).hom ≫ biprod.inl
    else if hp' : p = 1 then by
      subst p
      have hq : q = 1 := by change 1 + q = 2 at hpq; omega
      subst q
      exact (mixedColumnIso K 1 0 1 rfl).hom ≫ biprod.inr
    else 0)
  inv := biprod.desc
    ((mixedColumnIso K 0 2 2 rfl).inv ≫
      (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
    ((mixedColumnIso K 1 0 1 rfl).inv ≫
      (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl)
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 2 := by change 0 + q = 2 at hpq; omega
      subst q
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      change ((mixedColumnIso K 0 2 2 rfl).hom ≫ biprod.inl) ≫
          biprod.desc
            ((mixedColumnIso K 0 2 2 rfl).inv ≫
              (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
            ((mixedColumnIso K 1 0 1 rfl).inv ≫
              (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) =
        (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl ≫ 𝟙 _
      rw [Category.assoc, biprod.inl_desc]
      let e : ((B).X 0).X 2 ≅ K.X 2 := mixedColumnIso K 0 2 2 rfl
      change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl) =
        (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl) e.hom_inv_id
    · by_cases hp' : p = 1
      · subst p
        have hq : q = 1 := by change 1 + q = 2 at hpq; omega
        subst q
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        change ((mixedColumnIso K 1 0 1 rfl).hom ≫ biprod.inr) ≫
            biprod.desc
              ((mixedColumnIso K 0 2 2 rfl).inv ≫
                (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
              ((mixedColumnIso K 1 0 1 rfl).inv ≫
                (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) =
          (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫ 𝟙 _
        rw [Category.assoc, biprod.inr_desc]
        let e : ((B).X 1).X 1 ≅ K.X 0 := mixedColumnIso K 1 0 1 rfl
        change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) =
          (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫ 𝟙 _
        simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
          congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) e.hom_inv_id
      · exact (mixedBicomplex_isZero_cell K H hSquare p q
          (by change p + q = 2 at hpq; omega)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, Category.assoc,
        HomologicalComplex₂.ι_totalDesc]
      let e : ((B).X 0).X 2 ≅ K.X 2 := mixedColumnIso K 0 2 2 rfl
      change e.inv ≫ (e.hom ≫ biprod.inl) = biprod.inl ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m : K.X 2 ⟶ K.X 2 => m ≫
          (biprod.inl : K.X 2 ⟶ K.X 2 ⊞ K.X 0)) e.inv_hom_id
    · rw [← Category.assoc, biprod.inr_desc, Category.assoc,
        HomologicalComplex₂.ι_totalDesc]
      let e : ((B).X 1).X 1 ≅ K.X 0 := mixedColumnIso K 1 0 1 rfl
      change e.inv ≫ (e.hom ≫ biprod.inr) = biprod.inr ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m : K.X 0 ⟶ K.X 0 => m ≫
          (biprod.inr : K.X 0 ⟶ K.X 2 ⊞ K.X 0)) e.inv_hom_id

/-- The actual vertical boundary source becomes the first biproduct inclusion. -/
@[reassoc]
lemma mixedTotalTwoIso_ι_b :
    (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl ≫ (mixedTotalTwoIso K H hSquare).hom =
      (mixedColumnIso K 0 2 2 rfl).hom ≫ biprod.inl := by
  dsimp only [mixedTotalTwoIso]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

/-- The actual horizontal boundary source becomes the second biproduct inclusion. -/
@[reassoc]
lemma mixedTotalTwoIso_ι_B :
    (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫ (mixedTotalTwoIso K H hSquare).hom =
      (mixedColumnIso K 1 0 1 rfl).hom ≫ biprod.inr := by
  dsimp only [mixedTotalTwoIso]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

omit hTotal in
/-- The actual b₂/B₀ presentation is a short complex by d²=0 and the bottom mixed identity. -/
def mixedHomologyOneShortComplex : ShortComplex C :=
  ShortComplex.mk (biprod.desc (K.d 2 1) (H.hom 0 1)) (K.d 1 0) (by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, comp_zero]
      exact K.d_comp_d 2 1 0
    · rw [← Category.assoc, biprod.inr_desc, comp_zero]
      have h := H.comm 0
      rw [HomologicalComplex.zero_f_apply, add_zero,
        dNext_eq_zero H.hom 0 (by simp [ComplexShape.down_Rel]),
        prevD_eq H.hom (by show (ComplexShape.down ℕ).Rel 1 0; rfl), zero_add] at h
      exact h.symm)

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
private lemma firstColumn_d (n : ℕ) :
    (B).ιTotal (ComplexShape.down ℕ) 0 (n + 1) (n + 1) (Nat.zero_add (n + 1)) ≫ (T).d (n + 1) n =
      (mixedColumnIso K 0 (n + 1) (n + 1) rfl).hom ≫ K.d (n + 1) n ≫
        (mixedColumnIso K 0 n n rfl).inv ≫
          (B).ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) := by
  have hd : ((B).X 0).d (n + 1) n =
      (mixedColumnIso K 0 (n + 1) (n + 1) rfl).hom ≫ K.d (n + 1) n ≫
        (mixedColumnIso K 0 n n rfl).inv := by
    simpa only [ComplexShape.ε_zero, one_smul] using
      mixedBicomplex_total_vertical K H hSquare 0 (n + 1) n (n + 1) n rfl rfl
  have hNative := HomologicalComplex₂.ιTotal_firstColumn_d B n
  rw [hd] at hNative
  simpa only [Category.assoc] using hNative

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- The actual first column gives a chain map from the original b-complex to its mixed total. -/
def mixedColumnZeroInclusion : K ⟶ T :=
  (mixedColumnZeroIso K).inv ≫ HomologicalComplex₂.firstColumnTotalInclusion B

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- The chain map retains the original first-column coprojection in every degree. -/
lemma mixedColumnZeroInclusion_f (n : ℕ) :
    (mixedColumnZeroInclusion K H hSquare).f n =
      (mixedColumnIso K 0 n n rfl).inv ≫
        (B).ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) := rfl

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- The original mixed inclusion is its native zero-column transport followed by the total map. -/
lemma mixedColumnZeroInclusion_eq_firstColumn :
    mixedColumnZeroInclusion K H hSquare =
      (mixedColumnZeroIso K).inv ≫ HomologicalComplex₂.firstColumnTotalInclusion B := rfl

omit hTotal in
/-- The original short complex maps to the actual mixed presentation by the first b-source. -/
def mixedColumnZeroShortComplexMap : K.sc' 2 1 0 ⟶ mixedHomologyOneShortComplex K H :=
  ShortComplex.homMk (biprod.inl : K.X 2 ⟶ K.X 2 ⊞ K.X 0)
    (𝟙 (K.X 1)) (𝟙 (K.X 0)) (by
    change biprod.inl ≫ biprod.desc (K.d 2 1) (H.hom 0 1) = K.d 2 1 ≫ 𝟙 _
    rw [biprod.inl_desc, Category.comp_id]) (by
    change 𝟙 (K.X 1) ≫ K.d 1 0 = K.d 1 0 ≫ 𝟙 (K.X 0)
    rw [Category.id_comp, Category.comp_id])

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
private lemma horizontalBottom_d :
    (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫ (T).d 2 1 =
      (mixedColumnIso K 1 0 1 rfl).hom ≫ H.hom 0 1 ≫
        (mixedColumnIso K 0 1 1 rfl).inv ≫
          (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl := by
  have hε : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (1, 1) = 1 := rfl
  have hι : (B).ιTotal (ComplexShape.down ℕ) 1 0 1 rfl = 0 :=
    (mixedBicomplex_isZero_cell K H hSquare 1 0 (by omega)).eq_of_src _ _
  have hd : (B).d 1 0 = mixedHorizontalMap K H 0 := by
    change ChainComplex.of.d (mixedColumn K) (mixedHorizontalMap K H) 1 0 = _
    exact ChainComplex.of_d _ _ _
  change (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫
    ((B).D₁ (ComplexShape.down ℕ) 2 1 + (B).D₂ (ComplexShape.down ℕ) 2 1) = _
  rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    (B).d₂_eq (ComplexShape.down ℕ) 1
      (by show (ComplexShape.down ℕ).Rel 1 0; rfl) 1 rfl,
    hι, comp_zero, smul_zero, add_zero,
    (B).d₁_eq (ComplexShape.down ℕ)
      (by show (ComplexShape.down ℕ).Rel 1 0; rfl) 1 1 rfl,
    hε, one_smul, hd, mixedHorizontalMap_f,
    mixedHorizontalComponent_eq K H 0 0 1 rfl]
  simp only [Category.assoc]

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- The actual degree-one total differential is the original b₁ under the canonical objects. -/
lemma mixedTotalOneIso_inv_d :
    (mixedTotalOneIso K H hSquare).inv ≫ (T).d 1 0 ≫
      (mixedTotalZeroIso K H hSquare).hom = K.d 1 0 := by
  change ((mixedColumnIso K 0 1 1 rfl).inv ≫
      (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) ≫
        ((T).d 1 0 ≫ (mixedTotalZeroIso K H hSquare).hom) = _
  rw [Category.assoc]
  rw [← Category.assoc ((B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl),
    firstColumn_d K H hSquare 0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [mixedTotalZeroIso_ι, Iso.inv_hom_id, Category.comp_id]

/-- The actual total boundary is [b₂,B₀], with the native vertical sign already canceled. -/
lemma mixedTotalTwoIso_inv_d :
    (mixedTotalTwoIso K H hSquare).inv ≫ (T).d 2 1 ≫
      (mixedTotalOneIso K H hSquare).hom =
        biprod.desc (K.d 2 1) (H.hom 0 1) := by
  apply biprod.hom_ext'
  · change biprod.inl ≫
        (biprod.desc
          ((mixedColumnIso K 0 2 2 rfl).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
          ((mixedColumnIso K 1 0 1 rfl).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) ≫
          (T).d 2 1 ≫ (mixedTotalOneIso K H hSquare).hom) = _
    rw [biprod.inl_desc_assoc, biprod.inl_desc, Category.assoc]
    rw [← Category.assoc ((B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl),
      firstColumn_d K H hSquare 1]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [mixedTotalOneIso_ι, Iso.inv_hom_id, Category.comp_id]
  · change biprod.inr ≫
        (biprod.desc
          ((mixedColumnIso K 0 2 2 rfl).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
          ((mixedColumnIso K 1 0 1 rfl).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) ≫
          (T).d 2 1 ≫ (mixedTotalOneIso K H hSquare).hom) = _
    rw [biprod.inr_desc_assoc, biprod.inr_desc, Category.assoc]
    rw [← Category.assoc ((B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl),
      horizontalBottom_d K H hSquare]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [mixedTotalOneIso_ι, Iso.inv_hom_id, Category.comp_id]

/-- The actual total short complex is canonically the original b₂/B₀ presentation. -/
def mixedHomologyOneShortComplexIso :
    (T).sc' 2 1 0 ≅ mixedHomologyOneShortComplex K H :=
  ShortComplex.isoMk (mixedTotalTwoIso K H hSquare) (mixedTotalOneIso K H hSquare)
    (mixedTotalZeroIso K H hSquare) (by
      apply (cancel_epi (mixedTotalTwoIso K H hSquare).inv).1
      change (mixedTotalTwoIso K H hSquare).inv ≫
          ((mixedTotalTwoIso K H hSquare).hom ≫
            biprod.desc (K.d 2 1) (H.hom 0 1)) =
        (mixedTotalTwoIso K H hSquare).inv ≫
          ((T).d 2 1 ≫ (mixedTotalOneIso K H hSquare).hom)
      rw [Iso.inv_hom_id_assoc]
      exact (mixedTotalTwoIso_inv_d K H hSquare).symm) (by
      apply (cancel_epi (mixedTotalOneIso K H hSquare).inv).1
      change (mixedTotalOneIso K H hSquare).inv ≫
          ((mixedTotalOneIso K H hSquare).hom ≫ K.d 1 0) =
        (mixedTotalOneIso K H hSquare).inv ≫
          ((T).d 1 0 ≫ (mixedTotalZeroIso K H hSquare).hom)
      rw [Iso.inv_hom_id_assoc]
      exact (mixedTotalOneIso_inv_d K H hSquare).symm)

/-- The computed low-degree comparison keeps the actual first-column chain map. -/
lemma mixedColumnZeroShortComplexMap_eq :
    (shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0).map
        (mixedColumnZeroInclusion K H hSquare) ≫
      (mixedHomologyOneShortComplexIso K H hSquare).hom =
        mixedColumnZeroShortComplexMap K H := by
  apply ShortComplex.hom_ext
  · change (mixedColumnZeroInclusion K H hSquare).f 2 ≫
      (mixedTotalTwoIso K H hSquare).hom = biprod.inl
    rw [mixedColumnZeroInclusion_f, Category.assoc, mixedTotalTwoIso_ι_b,
      Iso.inv_hom_id_assoc]
  · change (mixedColumnZeroInclusion K H hSquare).f 1 ≫
      (mixedTotalOneIso K H hSquare).hom = 𝟙 (K.X 1)
    rw [mixedColumnZeroInclusion_f, Category.assoc, mixedTotalOneIso_ι,
      Iso.inv_hom_id]
  · change (mixedColumnZeroInclusion K H hSquare).f 0 ≫
      (mixedTotalZeroIso K H hSquare).hom = 𝟙 (K.X 0)
    rw [mixedColumnZeroInclusion_f, Category.assoc, mixedTotalZeroIso_ι,
      Iso.inv_hom_id]

section Abelian

variable [Abelian C]

/-- The goal selects its original zero dictionary as the ordinary indexed argument. -/
local instance mixedHomologyOneOriginalHomology (z : HasZeroMorphisms C) :
    @CategoryWithHomology C _ z := mixedHomologyOneCategoryWithHomology z

/-- Degree-one homology of the mixed total is the actual b₂/B₀ presentation homology. -/
def mixedHomologyOneIso : (T).homology 1 ≅ (mixedHomologyOneShortComplex K H).homology :=
  (T).homologyIsoSc' 2 1 0
    ((ComplexShape.down ℕ).prev_eq' (by show (ComplexShape.down ℕ).Rel 2 1; rfl))
    ((ComplexShape.down ℕ).next_eq' (by show (ComplexShape.down ℕ).Rel 1 0; rfl)) ≪≫
      ShortComplex.homologyMapIso (mixedHomologyOneShortComplexIso K H hSquare)

/-- The degree-one comparison identifies the actual inclusion-induced homology map. -/
lemma mixedColumnZeroInclusion_homology :
    homologyMap (mixedColumnZeroInclusion K H hSquare) 1 ≫
      (mixedHomologyOneIso K H hSquare).hom =
        (K.homologyIsoSc' 2 1 0
          ((ComplexShape.down ℕ).prev_eq' (by show (ComplexShape.down ℕ).Rel 2 1; rfl))
          ((ComplexShape.down ℕ).next_eq' (by show (ComplexShape.down ℕ).Rel 1 0; rfl))).hom ≫
            ShortComplex.homologyMap (mixedColumnZeroShortComplexMap K H) := by
  let m : K ⟶ T := mixedColumnZeroInclusion K H hSquare
  let hp : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (by show (ComplexShape.down ℕ).Rel 2 1; rfl)
  let hn : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (by show (ComplexShape.down ℕ).Rel 1 0; rfl)
  let e : shortComplexFunctor C (ComplexShape.down ℕ) 1 ≅
      shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0 :=
    natIsoSc' C (ComplexShape.down ℕ) 2 1 0 hp hn
  let eK : K.homology 1 ≅ (K.sc' 2 1 0).homology := K.homologyIsoSc' 2 1 0 hp hn
  let eT : (T).homology 1 ≅ ((T).sc' 2 1 0).homology := (T).homologyIsoSc' 2 1 0 hp hn
  let φ : K.sc' 2 1 0 ⟶ (T).sc' 2 1 0 :=
    (shortComplexFunctor' C (ComplexShape.down ℕ) 2 1 0).map m
  let ψ : (T).sc' 2 1 0 ⟶ mixedHomologyOneShortComplex K H :=
    (mixedHomologyOneShortComplexIso K H hSquare).hom
  have hSc : (shortComplexFunctor C (ComplexShape.down ℕ) 1).map m ≫ (e.app T).hom =
      (e.app K).hom ≫ φ := e.hom.naturality m
  have hH : homologyMap m 1 ≫ eT.hom = eK.hom ≫ ShortComplex.homologyMap φ := by
    change ShortComplex.homologyMap
        ((shortComplexFunctor C (ComplexShape.down ℕ) 1).map m) ≫
          ShortComplex.homologyMap (e.app T).hom =
      ShortComplex.homologyMap (e.app K).hom ≫ ShortComplex.homologyMap φ
    rw [← ShortComplex.homologyMap_comp, hSc, ShortComplex.homologyMap_comp]
  have hP : φ ≫ ψ = mixedColumnZeroShortComplexMap K H :=
    mixedColumnZeroShortComplexMap_eq K H hSquare
  have hPH : ShortComplex.homologyMap φ ≫ ShortComplex.homologyMap ψ =
      ShortComplex.homologyMap (mixedColumnZeroShortComplexMap K H) := by
    rw [← ShortComplex.homologyMap_comp, hP]
  change homologyMap m 1 ≫ (eT.hom ≫ ShortComplex.homologyMap ψ) =
    eK.hom ≫ ShortComplex.homologyMap (mixedColumnZeroShortComplexMap K H)
  exact (Category.assoc (homologyMap m 1) eT.hom (ShortComplex.homologyMap ψ)).symm.trans
    ((congrArg (fun f => f ≫ ShortComplex.homologyMap ψ) hH).trans
      ((Category.assoc eK.hom (ShortComplex.homologyMap φ)
        (ShortComplex.homologyMap ψ)).trans (congrArg (fun f => eK.hom ≫ f) hPH)))

omit hTotal [HasZeroObject C] in
/-- When b₁ is zero, the original quotient class maps to the actual mixed quotient class. -/
lemma mixedColumnZeroShortComplexMap_quotient (h0 : K.d 1 0 = 0) :
    (K.sc' 2 1 0).pOpcycles ≫ ((K.sc' 2 1 0).asIsoHomologyι h0).inv ≫
      ShortComplex.homologyMap (mixedColumnZeroShortComplexMap K H) =
        (mixedHomologyOneShortComplex K H).pOpcycles ≫
          ((mixedHomologyOneShortComplex K H).asIsoHomologyι h0).inv := by
  let P := K.sc' 2 1 0
  let S := mixedHomologyOneShortComplex K H
  let φ : P ⟶ S := mixedColumnZeroShortComplexMap K H
  apply (cancel_mono (S.asIsoHomologyι h0).hom).1
  change (P.pOpcycles ≫ (P.asIsoHomologyι h0).inv ≫ ShortComplex.homologyMap φ) ≫
      S.homologyι = (S.pOpcycles ≫ (S.asIsoHomologyι h0).inv) ≫ S.homologyι
  simp only [Category.assoc]
  rw [ShortComplex.homologyι_naturality,
    P.asIsoHomologyι_inv_comp_homologyι_assoc h0,
    S.asIsoHomologyι_inv_comp_homologyι h0, Category.comp_id,
    ShortComplex.p_opcyclesMap]
  change 𝟙 (K.X 1) ≫ S.pOpcycles = S.pOpcycles
  exact Category.id_comp _

end Abelian

end ChainComplex
