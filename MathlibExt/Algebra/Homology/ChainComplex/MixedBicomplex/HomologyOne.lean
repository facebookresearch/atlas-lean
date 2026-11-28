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
# Degree-one homology of a mixed-complex total

Let K be a nonnegative chain complex in a preadditive category with a zero object. A homotopy
H between its zero endomorphisms gives degree-raising maps B_n : K_n → K_(n+1) satisfying the
mixed relation with the boundary b. If B² = 0 and the mixed bicomplex has a total T, its first
three total objects are canonically K₀, K₁ and K₂ ⊞ K₀, with the last comparison requiring
that biproduct.

Under these comparisons, the degree-one short complex is K₂ ⊞ K₀ → K₁ → K₀, with arrows [b₂,
B₀] and b₁. Both summand coefficients in the first arrow are positive. The first-column chain
map K → T corresponds to the short-complex map with components biprod.inl, identity and
identity.

When the category is abelian, these maps identify H₁(T) with the homology of that short
complex. In module terms this is ker b₁/(im b₂ + im B₀); when b₁ = 0, the first-column
homology map sends a class modulo im b₂ to its class modulo im b₂ + im B₀.

See Weibel, *An Introduction to Homological Algebra*, Chapter 9, for mixed complexes.
-/

@[expose] public section


noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace ChainComplex

universe u v

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
  (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)

local notation "B" => mixedBicomplex K H hSquare
local notation "T" => HomologicalComplex₂.total
  (mixedBicomplex K H hSquare) (ComplexShape.down ℕ)

variable [hTotal : HomologicalComplex₂.HasTotal
  (mixedBicomplex K H hSquare) (ComplexShape.down ℕ)]

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. The unique supported cell in
total degree zero gives an isomorphism mixedTotalZeroIso : T.X 0 ≅ K.X 0. Its inverse is the
supported-cell comparison followed by the total coprojection from bidegree (0, 0). -/
def mixedTotalZeroIso : (T).X 0 ≅ K.X 0 where
  hom := (B).totalDesc (fun p q hpq => by
    have hp : p = 0 := by change p + q = 0 at hpq; omega
    have hq : q = 0 := by change p + q = 0 at hpq; omega
    subst p
    subst q
    exact (mixedBicomplexCellIso K H hSquare 0 0 (Nat.zero_le 0)).hom)
  inv := (mixedBicomplexCellIso K H hSquare 0 0 (Nat.zero_le 0)).inv ≫
    (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hp : p = 0 := by change p + q = 0 at hpq; omega
    have hq : q = 0 := by change p + q = 0 at hpq; omega
    subst p
    subst q
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    let e : ((B).X 0).X 0 ≅ K.X 0 := mixedBicomplexCellIso K H hSquare 0 0 (Nat.zero_le 0)
    change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl) =
      (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫ 𝟙 _
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl) e.hom_inv_id
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    let e : ((B).X 0).X 0 ≅ K.X 0 := mixedBicomplexCellIso K H hSquare 0 0 (Nat.zero_le 0)
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. The coprojection from cell (0,
0), followed by mixedTotalZeroIso.hom, equals
(mixedBicomplexCellIso K H hSquare 0 0 (Nat.zero_le 0)).hom :
(mixedBicomplex.X 0).X 0 ⟶ K.X 0. -/
@[reassoc]
lemma mixedTotalZeroIso_ι :
    (B).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫ (mixedTotalZeroIso K H hSquare).hom =
      (mixedBicomplexCellIso K H hSquare 0 0 (Nat.zero_le 0)).hom := by
  dsimp only [mixedTotalZeroIso]
  rw [HomologicalComplex₂.ι_totalDesc]

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. The only supported cell in
total degree one is (0, 1). It gives an isomorphism mixedTotalOneIso : T.X 1 ≅ K.X 1, with
inverse the cell comparison followed by its total coprojection. -/
def mixedTotalOneIso : (T).X 1 ≅ K.X 1 where
  hom := (B).totalDesc (fun p q hpq => if hp : p = 0 then by
    subst p
    have hq : q = 1 := by change 0 + q = 1 at hpq; omega
    subst q
    exact (mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).hom
    else 0)
  inv := (mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).inv ≫
    (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 1 := by change 0 + q = 1 at hpq; omega
      subst q
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      let e : ((B).X 0).X 1 ≅ K.X 1 := mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)
      change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) =
        (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) e.hom_inv_id
    · exact (mixedBicomplex_isZero_cell K H hSquare p q
        (by change p + q = 1 at hpq; omega)).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    let e : ((B).X 0).X 1 ≅ K.X 1 := mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. The total coprojection from
cell (0, 1), followed by mixedTotalOneIso.hom, equals
(mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).hom, the supported-cell comparison
to K.X 1. -/
@[reassoc]
lemma mixedTotalOneIso_ι :
    (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl ≫ (mixedTotalOneIso K H hSquare).hom =
      (mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).hom := by
  dsimp only [mixedTotalOneIso]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

variable [HasBinaryBiproduct (K.X 2) (K.X 0)]

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Assume the biproduct K₂ ⊞ K₀
exists. The supported cells (0, 2) and (1, 1) give an isomorphism mixedTotalTwoIso : T.X 2 ≅
K.X 2 ⊞ K.X 0. The first cell maps through its comparison to biprod.inl, and the second
through its comparison to biprod.inr. -/
def mixedTotalTwoIso : (T).X 2 ≅ K.X 2 ⊞ K.X 0 where
  hom := (B).totalDesc (fun p q hpq => if hp : p = 0 then by
    subst p
    have hq : q = 2 := by change 0 + q = 2 at hpq; omega
    subst q
    exact (mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).hom ≫ biprod.inl
    else if hp' : p = 1 then by
      subst p
      have hq : q = 1 := by change 1 + q = 2 at hpq; omega
      subst q
      exact (mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫ biprod.inr
    else 0)
  inv := biprod.desc
    ((mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).inv ≫
      (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
    ((mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).inv ≫
      (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl)
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 2 := by change 0 + q = 2 at hpq; omega
      subst q
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      change ((mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).hom ≫ biprod.inl) ≫
          biprod.desc
            ((mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).inv ≫
              (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
            ((mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).inv ≫
              (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) =
        (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl ≫ 𝟙 _
      rw [Category.assoc, biprod.inl_desc]
      let e : ((B).X 0).X 2 ≅ K.X 2 := mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)
      change e.hom ≫ (e.inv ≫ (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl) =
        (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m => m ≫ (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl) e.hom_inv_id
    · by_cases hp' : p = 1
      · subst p
        have hq : q = 1 := by change 1 + q = 2 at hpq; omega
        subst q
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        change ((mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫ biprod.inr) ≫
            biprod.desc
              ((mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).inv ≫
                (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
              ((mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).inv ≫
                (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) =
          (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫ 𝟙 _
        rw [Category.assoc, biprod.inr_desc]
        let e : ((B).X 1).X 1 ≅ K.X 0 := mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)
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
      let e : ((B).X 0).X 2 ≅ K.X 2 := mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)
      change e.inv ≫ (e.hom ≫ biprod.inl) = biprod.inl ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m : K.X 2 ⟶ K.X 2 => m ≫
          (biprod.inl : K.X 2 ⟶ K.X 2 ⊞ K.X 0)) e.inv_hom_id
    · rw [← Category.assoc, biprod.inr_desc, Category.assoc,
        HomologicalComplex₂.ι_totalDesc]
      let e : ((B).X 1).X 1 ≅ K.X 0 := mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)
      change e.inv ≫ (e.hom ≫ biprod.inr) = biprod.inr ≫ 𝟙 _
      simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
        congrArg (fun m : K.X 0 ⟶ K.X 0 => m ≫
          (biprod.inr : K.X 0 ⟶ K.X 2 ⊞ K.X 0)) e.inv_hom_id

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Assume the biproduct K₂ ⊞ K₀
exists. The total coprojection from (0, 2), followed by mixedTotalTwoIso.hom, is
(mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).hom ≫ biprod.inl. Thus this supported
cell is the K₂ summand. -/
@[reassoc]
lemma mixedTotalTwoIso_ι_b :
    (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl ≫ (mixedTotalTwoIso K H hSquare).hom =
      (mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).hom ≫ biprod.inl := by
  dsimp only [mixedTotalTwoIso]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Assume the biproduct K₂ ⊞ K₀
exists. The total coprojection from (1, 1), followed by mixedTotalTwoIso.hom, is
(mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫ biprod.inr. Thus this supported
cell is the K₀ summand. -/
@[reassoc]
lemma mixedTotalTwoIso_ι_B :
    (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫ (mixedTotalTwoIso K H hSquare).hom =
      (mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫ biprod.inr := by
  dsimp only [mixedTotalTwoIso]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

omit hTotal in
/-- In a preadditive category C, let K be an ℕ-indexed chain complex and H a homotopy between its
zero endomorphisms. Write b₂ = K.d 2 1, b₁ = K.d 1 0 and B₀ = H.hom 0 1, and assume K₂ ⊞ K₀
exists. The morphisms biprod.desc b₂ B₀ : K₂ ⊞ K₀ ⟶ K₁ and b₁ : K₁ ⟶ K₀ form a short complex.
The relation b₂ ≫ b₁ = 0 comes from the chain-complex law, and B₀ ≫ b₁ = 0 from the bottom
homotopy equation. -/
def mixedHomologyOneShortComplex : ShortComplex C :=
  ShortComplex.mk (biprod.desc (K.d 2 1) (H.hom 0 1)) (K.d 1 0) (by
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc, comp_zero]
      exact K.d_comp_d 2 1 0
    · rw [← Category.assoc, biprod.inr_desc, comp_zero]
      have h := H.comm 0
      rw [HomologicalComplex.zero_f_apply, add_zero,
        dNext_eq_zero H.hom 0 (by simp [ComplexShape.down_Rel]),
        prevD_eq H.hom (by rfl), zero_add] at h
      exact h.symm)

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
private lemma firstColumn_d (n : ℕ) :
    (B).ιTotal (ComplexShape.down ℕ) 0 (n + 1) (n + 1) (Nat.zero_add (n + 1)) ≫ (T).d (n + 1) n =
      (mixedBicomplexCellIso K H hSquare 0 (n + 1) (Nat.zero_le (n + 1))).hom ≫ K.d (n + 1) n ≫
        (mixedBicomplexCellIso K H hSquare 0 n (Nat.zero_le n)).inv ≫
          (B).ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) := by
  have hd : ((B).X 0).d (n + 1) n =
      (mixedBicomplexCellIso K H hSquare 0 (n + 1) (Nat.zero_le (n + 1))).hom ≫ K.d (n + 1) n ≫
        (mixedBicomplexCellIso K H hSquare 0 n (Nat.zero_le n)).inv := by
    have hSigned : (ComplexShape.down ℕ).ε 0 • ((B).X 0).d (n + 1) n =
        (mixedBicomplexCellIso K H hSquare 0 (n + 1) (Nat.zero_le (n + 1))).hom ≫
          K.d (n + 1) n ≫
            (mixedBicomplexCellIso K H hSquare 0 n (Nat.zero_le n)).inv :=
      mixedBicomplex_total_vertical K H hSquare 0 (n + 1) n (n + 1) n rfl rfl
    simpa only [ComplexShape.ε_zero, one_smul] using hSigned
  have hNative := HomologicalComplex₂.ιTotal_firstColumn_d B n
  rw [hd] at hNative
  simpa only [Category.assoc] using hNative

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Define
mixedColumnZeroInclusion : K ⟶ T as the inverse first-column isomorphism K ≅ mixedBicomplex.X
0 followed by the first-column total inclusion. -/
def mixedColumnZeroInclusion : K ⟶ T :=
  (mixedColumnZeroIso K).inv ≫ HomologicalComplex₂.firstColumnTotalInclusion B

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. For every n : ℕ,
mixedColumnZeroInclusion.f n = (mixedBicomplexCellIso K H hSquare 0 n (Nat.zero_le n)).inv ≫
  ιTotal (0, n). This maps K_n
into the first-column cell of total degree n. -/
lemma mixedColumnZeroInclusion_f (n : ℕ) :
    (mixedColumnZeroInclusion K H hSquare).f n =
      (mixedBicomplexCellIso K H hSquare 0 n (Nat.zero_le n)).inv ≫
        (B).ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) := rfl

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. The chain map
mixedColumnZeroInclusion equals (mixedColumnZeroIso K).inv ≫ firstColumnTotalInclusion
(mixedBicomplex K H hSquare). The first factor identifies K with column zero; the second is
assembled from its total coprojections. -/
lemma mixedColumnZeroInclusion_eq_firstColumn :
    mixedColumnZeroInclusion K H hSquare =
      (mixedColumnZeroIso K).inv ≫ HomologicalComplex₂.firstColumnTotalInclusion B := rfl

omit hTotal in
/-- In a preadditive category C, let K be an ℕ-indexed chain complex and H a homotopy between its
zero endomorphisms. Write b₂ = K.d 2 1, b₁ = K.d 1 0 and B₀ = H.hom 0 1, and assume K₂ ⊞ K₀
exists. The short complex K₂ ⟶ K₁ ⟶ K₀ maps to K₂ ⊞ K₀ ⟶ K₁ ⟶ K₀ by the three components
biprod.inl, 𝟙 K₁ and 𝟙 K₀. The target incoming arrow is [b₂, B₀] and its outgoing arrow is b₁. -/
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
      (mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫ H.hom 0 1 ≫
        (mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).inv ≫
          (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl := by
  have hε : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (1, 1) = 1 := rfl
  have hι : (B).ιTotal (ComplexShape.down ℕ) 1 0 1 rfl = 0 :=
    (mixedBicomplex_isZero_cell K H hSquare 1 0 (by omega)).eq_of_src _ _
  have hd : (B).d 1 0 = mixedHorizontalMap K H 0 := by
    change ChainComplex.of.d (mixedColumn K) (mixedHorizontalMap K H) 1 0 = _
    exact ChainComplex.of_d _ _ _
  have hComponent : ((B).d 1 0).f 1 =
      (mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫
        H.hom 0 1 ≫
          (mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).inv := by
    have hMap : ((B).d 1 0).f 1 = (mixedHorizontalMap K H 0).f 1 :=
      congrArg (fun f : (B).X 1 ⟶ (B).X 0 => f.f 1) hd
    have hNative : (mixedHorizontalMap K H 0).f 1 =
        (mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).hom ≫
          H.hom 0 1 ≫
            (mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).inv :=
      mixedHorizontalComponent_eq K H 0 0 1 rfl
    exact hMap.trans hNative
  change (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl ≫
    ((B).D₁ (ComplexShape.down ℕ) 2 1 + (B).D₂ (ComplexShape.down ℕ) 2 1) = _
  rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    (B).d₂_eq (ComplexShape.down ℕ) 1
      (by rfl) 1 rfl,
    hι, comp_zero, smul_zero, add_zero,
    (B).d₁_eq (ComplexShape.down ℕ)
      (by rfl) 1 1 rfl,
    hε, one_smul, hComponent]
  simp only [Category.assoc]

omit [HasBinaryBiproduct (K.X 2) (K.X 0)] in
/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. For e₁ = mixedTotalOneIso : T₁
≅ K₁ and e₀ = mixedTotalZeroIso : T₀ ≅ K₀, one has e₁.inv ≫ T.d 1 0 ≫ e₀.hom = K.d 1 0. -/
lemma mixedTotalOneIso_inv_d :
    (mixedTotalOneIso K H hSquare).inv ≫ (T).d 1 0 ≫
      (mixedTotalZeroIso K H hSquare).hom = K.d 1 0 := by
  change ((mixedBicomplexCellIso K H hSquare 0 1 (Nat.zero_le 1)).inv ≫
      (B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) ≫
        ((T).d 1 0 ≫ (mixedTotalZeroIso K H hSquare).hom) = _
  rw [Category.assoc]
  rw [← Category.assoc ((B).ιTotal (ComplexShape.down ℕ) 0 1 1 rfl),
    firstColumn_d K H hSquare 0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [mixedTotalZeroIso_ι, Iso.inv_hom_id, Category.comp_id]

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Assume the biproduct K₂ ⊞ K₀
exists. For e₂ = mixedTotalTwoIso and e₁ = mixedTotalOneIso, one has e₂.inv ≫ T.d 2 1 ≫ e₁.hom
= biprod.desc (K.d 2 1) B₀. The K₂ and K₀ summands contribute b₂ and B₀ with positive signs. -/
lemma mixedTotalTwoIso_inv_d :
    (mixedTotalTwoIso K H hSquare).inv ≫ (T).d 2 1 ≫
      (mixedTotalOneIso K H hSquare).hom =
        biprod.desc (K.d 2 1) (H.hom 0 1) := by
  apply biprod.hom_ext'
  · change biprod.inl ≫
        (biprod.desc
          ((mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
          ((mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) ≫
          (T).d 2 1 ≫ (mixedTotalOneIso K H hSquare).hom) = _
    rw [biprod.inl_desc_assoc, biprod.inl_desc, Category.assoc]
    rw [← Category.assoc ((B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl),
      firstColumn_d K H hSquare 1]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [mixedTotalOneIso_ι, Iso.inv_hom_id, Category.comp_id]
  · change biprod.inr ≫
        (biprod.desc
          ((mixedBicomplexCellIso K H hSquare 0 2 (Nat.zero_le 2)).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 0 2 2 rfl)
          ((mixedBicomplexCellIso K H hSquare 1 1 (Nat.le_refl 1)).inv ≫
            (B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl) ≫
          (T).d 2 1 ≫ (mixedTotalOneIso K H hSquare).hom) = _
    rw [biprod.inr_desc_assoc, biprod.inr_desc, Category.assoc]
    rw [← Category.assoc ((B).ιTotal (ComplexShape.down ℕ) 1 1 2 rfl),
      horizontalBottom_d K H hSquare]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [mixedTotalOneIso_ι, Iso.inv_hom_id, Category.comp_id]

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Assume the biproduct K₂ ⊞ K₀
exists. The comparisons e₂ : T₂ ≅ K₂ ⊞ K₀, e₁ : T₁ ≅ K₁ and e₀ : T₀ ≅ K₀ give an isomorphism
T.sc' 2 1 0 ≅ mixedHomologyOneShortComplex K H. The target arrows are [K.d 2 1, B₀] and K.d 1
0. -/
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

/-- Let C be preadditive with a zero object, K a chain complex indexed by ℕ, and H a homotopy
between the zero endomorphisms of K. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0 for
every n, and assume the mixed bicomplex has its down-ℕ total T. Assume the biproduct K₂ ⊞ K₀
exists. Applying the degree-(2,1,0) short-complex functor to mixedColumnZeroInclusion and then
the mixed short-complex comparison equals mixedColumnZeroShortComplexMap K H. Its three
components are biprod.inl, 𝟙 K₁ and 𝟙 K₀. -/
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

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
  (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)

local notation "T" => HomologicalComplex₂.total
  (mixedBicomplex K H hSquare) (ComplexShape.down ℕ)

variable [hTotal : HomologicalComplex₂.HasTotal
  (mixedBicomplex K H hSquare) (ComplexShape.down ℕ)]

/-- In an abelian category C, let K be an ℕ-indexed chain complex and H a homotopy between its
zero endomorphisms. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0, and assume the
mixed bicomplex has total T. The total-object comparisons induce an isomorphism H₁(T) ≅ H(K₂ ⊞
K₀ → K₁ → K₀), where the arrows are [K.d 2 1, B₀] and K.d 1 0. Equivalently, it identifies
total homology with the cycles of b₁ modulo the images of both incoming maps. -/
def mixedHomologyOneIso : (T).homology 1 ≅ (mixedHomologyOneShortComplex K H).homology :=
  (T).homologyIsoSc' 2 1 0
    ((ComplexShape.down ℕ).prev_eq' (by rfl))
    ((ComplexShape.down ℕ).next_eq' (by rfl)) ≪≫
      ShortComplex.homologyMapIso (mixedHomologyOneShortComplexIso K H hSquare)

/-- In an abelian category C, let K be an ℕ-indexed chain complex and H a homotopy between its
zero endomorphisms. Write B_n = H.hom n (n + 1), assume B_n ≫ B_(n+1) = 0, and assume the
mixed bicomplex has total T. Let m : K ⟶ T be the first-column inclusion, E_T the mixed
degree-one homology comparison, E_K : H₁(K) ≅ H(K.sc' 2 1 0) the canonical short-complex
comparison, and u the map with components biprod.inl, identity and identity into the mixed
presentation. Then H₁(m) ≫ E_T.hom = E_K.hom ≫ H(u). -/
lemma mixedColumnZeroInclusion_homology :
    homologyMap (mixedColumnZeroInclusion K H hSquare) 1 ≫
      (mixedHomologyOneIso K H hSquare).hom =
        (K.homologyIsoSc' 2 1 0
          ((ComplexShape.down ℕ).prev_eq' (by rfl))
          ((ComplexShape.down ℕ).next_eq' (by rfl))).hom ≫
            ShortComplex.homologyMap (mixedColumnZeroShortComplexMap K H) := by
  let m : K ⟶ T := mixedColumnZeroInclusion K H hSquare
  let hp : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (by rfl)
  let hn : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (by rfl)
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

omit hTotal in
/-- In an abelian category C, let K be an ℕ-indexed chain complex and H a homotopy between its
zero endomorphisms, and assume K.d 1 0 = 0. Write P = K.sc' 2 1 0 and S =
mixedHomologyOneShortComplex K H, and let u : P ⟶ S have components biprod.inl, identity and
identity. Their class maps c_P = P.pOpcycles ≫ (P.asIsoHomologyι h0).inv and c_S = S.pOpcycles
≫ (S.asIsoHomologyι h0).inv satisfy c_P ≫ H(u) = c_S. Thus the class of a degree-one element
modulo im b₂ maps to its class modulo im b₂ + im B₀. -/
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
