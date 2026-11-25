/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationNaturality
public import MathlibExt.Algebra.Homology.TotalHomotopy
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison
public import MathlibExt.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Vertical homotopies on the complete horizontal filtration

A homotopy of flipped first-quadrant bicomplex maps totalizes with sign
`(-1)^p` in horizontal degree `p`. Its components preserve that degree and
therefore restrict to each finite and complete horizontal-filtration stage.
The restrictions use the actual stage maps and commute with all transitions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  {f g : K ⟶ L}
  (h : _root_.Homotopy (flipMap f) (flipMap g))

local notation "c" => ComplexShape.down ℕ

/-- The actual signed total homotopy induced by a vertical bicomplex homotopy. -/
def verticalTotalHomotopy :
    _root_.Homotopy (total.map f c) (total.map g c) :=
  totalMapHomotopy₂ c h

omit [HasZeroObject C] in
/-- On a total summand the homotopy keeps the horizontal degree and has
exactly the canonical `(-1)^p` vertical totalization sign. -/
@[reassoc]
theorem ιTotal_verticalTotalHomotopy_hom (p q n : ℕ) (hn : p + q = n) :
    K.ιTotal c p q n hn ≫ (verticalTotalHomotopy h).hom n (n + 1) =
      (-1 : ℤˣ) ^ p • ((h.hom q (q + 1)).f p ≫
        L.ιTotal c p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  simp only [verticalTotalHomotopy, totalMapHomotopy₂, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Homotopy.compLeft_hom, Homotopy.compRight_hom,
    Pi.zero_apply, zero_add, add_zero, totalMapHomotopy₁]
  rw [← Category.assoc, ιTotal_totalFlipIso_f_inv]
  simp only [Linear.units_smul_comp]
  rw [ιTotal_totalHomotopy₁Hom_assoc (K := K.flip) (L := L.flip) h c
    (q + 1) q p n (n + 1) (by change q + p = n; omega)
      (ComplexShape.prev_eq' c (show ComplexShape.Rel c (q + 1) q from rfl))]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTotalOrZero_eq L.flip c (q + 1) p (n + 1)
      (by change (q + 1) + p = n + 1; omega),
    ιTotal_totalFlipIso_f_hom]
  simp only [Linear.comp_units_smul, smul_smul]
  congr 1
  have he : ComplexShape.ε₁ c c c (q + 1, p) = 1 := rfl
  rw [HomologicalComplex.ComplexShape.σ_down_ℕ, HomologicalComplex.ComplexShape.σ_down_ℕ,
    he, one_mul, Nat.mul_add, Nat.mul_one, pow_add, ← mul_assoc, Int.units_mul_self, one_mul]

/-- Raising the inner degree retains the allowed horizontal coordinate. -/
def horizontalFilteredTotalHomotopyIndex {k n : ℕ}
    (pq : DownNatHorizontalFilteredFiber n k) : DownNatHorizontalFilteredFiber (n + 1) k :=
  ⟨⟨(pq.val.val.1, pq.val.val.2 + 1), by
    have hs := pq.val.property
    change pq.val.val.1 + pq.val.val.2 = n at hs
    change pq.val.val.1 + (pq.val.val.2 + 1) = n + 1
    omega⟩, pq.property⟩

/-- The total vertical homotopy restricted to a finite horizontal stage. -/
def horizontalFilteredTotalHomotopyHom (k n m : ℕ) :
    horizontalFilteredTotalObj K k n ⟶ horizontalFilteredTotalObj L k m :=
  horizontalFilteredTotalToTotal K k n ≫ (verticalTotalHomotopy h).hom n m ≫
    totalToHorizontalFilteredTotal L k m

omit [HasZeroObject C] in
/-- The finite-stage prism keeps the horizontal coordinate, including at
the filtration boundary, and has the same totalization sign. -/
@[reassoc]
theorem horizontalFilteredTotalHomotopyHom_ι (k n : ℕ)
    (pq : DownNatHorizontalFilteredFiber n k) :
    horizontalFilteredTotalι K k n pq ≫ horizontalFilteredTotalHomotopyHom h k n (n + 1) =
      (-1 : ℤˣ) ^ pq.val.val.1 •
        ((h.hom pq.val.val.2 (pq.val.val.2 + 1)).f pq.val.val.1 ≫
          horizontalFilteredTotalι L k (n + 1) (horizontalFilteredTotalHomotopyIndex pq)) := by
  unfold horizontalFilteredTotalHomotopyHom
  rw [← Category.assoc, horizontalFilteredTotalι_toTotal]
  rw [ιTotal_verticalTotalHomotopy_hom_assoc h _ _ _ pq.val.property]
  rw [Linear.units_smul_comp, Category.assoc, ιTotal_totalToHorizontalFilteredTotal,
    dite_eq_left pq.property]
  rfl

omit [HasZeroObject C] in
/-- Finite-stage homotopy components vanish outside degree plus one. -/
theorem horizontalFilteredTotalHomotopyHom_zero (k n m : ℕ)
    (hrel : ¬ComplexShape.Rel c m n) : horizontalFilteredTotalHomotopyHom h k n m = 0 := by
  unfold horizontalFilteredTotalHomotopyHom
  rw [(verticalTotalHomotopy h).zero n m hrel]
  simp

omit [HasZeroObject C] in
/-- The finite-stage homotopy factors the actual total homotopy through
the same horizontal stage in every pair of degrees. -/
@[reassoc]
theorem horizontalFilteredTotalHomotopyHom_toTotal (k n m : ℕ) :
    horizontalFilteredTotalHomotopyHom h k n m ≫ horizontalFilteredTotalToTotal L k m =
      horizontalFilteredTotalToTotal K k n ≫ (verticalTotalHomotopy h).hom n m := by
  by_cases hnm : n + 1 = m
  · subst m
    apply Sigma.hom_ext
    intro pq
    change horizontalFilteredTotalι K k n pq ≫
        (horizontalFilteredTotalHomotopyHom h k n (n + 1) ≫
          horizontalFilteredTotalToTotal L k (n + 1)) =
      horizontalFilteredTotalι K k n pq ≫
        (horizontalFilteredTotalToTotal K k n ≫ (verticalTotalHomotopy h).hom n (n + 1))
    rw [horizontalFilteredTotalHomotopyHom_ι_assoc]
    rw [Linear.units_smul_comp, Category.assoc, horizontalFilteredTotalι_toTotal]
    rw [← Category.assoc, horizontalFilteredTotalι_toTotal,
      ιTotal_verticalTotalHomotopy_hom]
    rfl
  · rw [horizontalFilteredTotalHomotopyHom_zero h k n m hnm,
      (verticalTotalHomotopy h).zero n m hnm]
    simp

/-- A vertical bicomplex homotopy induces a chain homotopy between the
existing maps on each finite horizontal-filtration stage. -/
def horizontalFilteredTotalHomotopy (k : ℕ) :
    _root_.Homotopy (horizontalFilteredTotalComplexMapOfBicomplex f k)
      (horizontalFilteredTotalComplexMapOfBicomplex g k) where
  hom := horizontalFilteredTotalHomotopyHom h k
  zero n m hrel := horizontalFilteredTotalHomotopyHom_zero h k n m hrel
  comm n := by
    let iK := horizontalFilteredTotalComplexToTotal K k
    let iL := horizontalFilteredTotalComplexToTotal L k
    have hfac :
        (fun n m => horizontalFilteredTotalHomotopyHom h k n m ≫ iL.f m) =
          (fun n m => iK.f n ≫ (verticalTotalHomotopy h).hom n m) := by
      funext n m
      exact horizontalFilteredTotalHomotopyHom_toTotal h k n m
    have hd : dNext n (horizontalFilteredTotalHomotopyHom h k) ≫ iL.f n =
        iK.f n ≫ dNext n (verticalTotalHomotopy h).hom := by
      rw [← dNext_comp_right, hfac, dNext_comp_left]
    have hp : prevD n (horizontalFilteredTotalHomotopyHom h k) ≫ iL.f n =
        iK.f n ≫ prevD n (verticalTotalHomotopy h).hom := by
      rw [← prevD_comp_right, hfac, prevD_comp_left]
    have hf : (horizontalFilteredTotalComplexMapOfBicomplex f k).f n ≫ iL.f n =
        iK.f n ≫ (total.map f c).f n :=
      horizontalFilteredTotalMapOfBicomplex_toTotal f k n
    have hg : (horizontalFilteredTotalComplexMapOfBicomplex g k).f n ≫ iL.f n =
        iK.f n ≫ (total.map g c).f n :=
      horizontalFilteredTotalMapOfBicomplex_toTotal g k n
    apply (cancel_mono (horizontalFilteredTotalToTotal L k n)).mp
    change (horizontalFilteredTotalComplexMapOfBicomplex f k).f n ≫ iL.f n =
      (dNext n (horizontalFilteredTotalHomotopyHom h k) +
        prevD n (horizontalFilteredTotalHomotopyHom h k) +
        (horizontalFilteredTotalComplexMapOfBicomplex g k).f n) ≫ iL.f n
    rw [hf, (verticalTotalHomotopy h).comm n]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
    rw [hd, hp, hg]

omit [HasZeroObject C] in
/-- The finite-stage homotopy commutes with its canonical inclusion into the total. -/
@[reassoc]
theorem horizontalFilteredTotalHomotopy_toTotal (k n m : ℕ) :
    (horizontalFilteredTotalHomotopy h k).hom n m ≫
        (horizontalFilteredTotalComplexToTotal L k).f m =
      (horizontalFilteredTotalComplexToTotal K k).f n ≫ (verticalTotalHomotopy h).hom n m :=
  horizontalFilteredTotalHomotopyHom_toTotal h k n m

omit [HasZeroObject C] in
/-- The actual homotopies commute with every transition of finite
horizontal-filtration stages, on every homotopy component. -/
theorem horizontalFilteredTotalHomotopy_naturality {k l : ℕ} (hkl : k ≤ l) (n m : ℕ) :
    (horizontalFilteredTotalComplexMap K hkl).f n ≫
        (horizontalFilteredTotalHomotopy h l).hom n m =
      (horizontalFilteredTotalHomotopy h k).hom n m ≫
        (horizontalFilteredTotalComplexMap L hkl).f m := by
  change horizontalFilteredTotalMap K hkl n ≫ horizontalFilteredTotalHomotopyHom h l n m =
    horizontalFilteredTotalHomotopyHom h k n m ≫ horizontalFilteredTotalMap L hkl m
  apply (cancel_mono (horizontalFilteredTotalToTotal L l m)).mp
  rw [Category.assoc, horizontalFilteredTotalHomotopyHom_toTotal,
    ← Category.assoc, horizontalFilteredTotalMap_toTotal,
    Category.assoc, horizontalFilteredTotalMap_toTotal, horizontalFilteredTotalHomotopyHom_toTotal]

/-- Conjugating a finite-stage map by the canonical carrier isomorphisms
recovers exactly its complete-stage map. -/
theorem horizontalCompleteFilteredTotalComplexFiniteIso_conjugate_map
    (φ : K ⟶ L) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexMapOfBicomplex φ a.toNat ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex φ (a : EInt) := by
  rw [← Category.assoc, horizontalCompleteFilteredTotalComplexFiniteIso_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The finite-stage homotopy transported through the canonical complete-to-finite
isomorphisms, with the actual complete-stage maps as endpoints. -/
def horizontalCompleteFilteredTotalHomotopyOfNonneg (a : ℤ) (ha : 0 ≤ a) :
    _root_.Homotopy (horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt))
      (horizontalCompleteFilteredTotalComplexMapOfBicomplex g (a : EInt)) := by
  let H := ((horizontalFilteredTotalHomotopy h a.toNat).compRight
    (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv).compLeft
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom
  have hf : (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
      (horizontalFilteredTotalComplexMapOfBicomplex f a.toNat ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) := by
    exact horizontalCompleteFilteredTotalComplexFiniteIso_conjugate_map f a ha
  have hg : (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
      (horizontalFilteredTotalComplexMapOfBicomplex g a.toNat ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv) =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex g (a : EInt) := by
    exact horizontalCompleteFilteredTotalComplexFiniteIso_conjugate_map g a ha
  exact (Homotopy.ofEq hf.symm).trans (H.trans (Homotopy.ofEq hg))

/-- Nonnegative complete-stage components use the prescribed finite-stage
homotopy and the canonical carrier identifications. -/
theorem horizontalCompleteFilteredTotalHomotopyOfNonneg_hom (a : ℤ) (ha : 0 ≤ a)
    (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha).hom n m =
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalHomotopy h a.toNat).hom n m ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv.f m) := by
  simp only [horizontalCompleteFilteredTotalHomotopyOfNonneg, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Homotopy.compLeft_hom, Homotopy.compRight_hom,
    Pi.zero_apply, zero_add, add_zero]

/-- A vertical bicomplex homotopy induces the actual homotopy at every
complete horizontal-filtration stage: zero below zero, finite in the middle,
and the signed total homotopy at top. -/
def horizontalCompleteFilteredTotalHomotopy (i : EInt) :
    _root_.Homotopy (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i)
      (horizontalCompleteFilteredTotalComplexMapOfBicomplex g i) := by
  induction i using WithBotTop.rec with
  | bot =>
    change _root_.Homotopy (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
      HomologicalComplex.zero) 0
    exact Homotopy.refl 0
  | coe a =>
    by_cases ha : 0 ≤ a
    · exact horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha
    · have hz : IsZero (horizontalCompleteFilteredTotalComplex K (a : EInt)) := by
        rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a (lt_of_not_ge ha)]
        exact HomologicalComplex.isZero_zero
      exact Homotopy.ofEq (hz.eq_of_src _ _)
  | top =>
    change _root_.Homotopy (total.map f c) (total.map g c)
    exact verticalTotalHomotopy h

/-- The top stage is the actual signed total homotopy. -/
@[simp]
theorem horizontalCompleteFilteredTotalHomotopy_hom_top (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h ⊤).hom n m =
      (verticalTotalHomotopy h).hom n m := rfl

/-- The bottom stage has zero homotopy components. -/
@[simp]
theorem horizontalCompleteFilteredTotalHomotopy_hom_bot (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h ⊥).hom n m = 0 := rfl

/-- Every negative stage has zero homotopy components. -/
theorem horizontalCompleteFilteredTotalHomotopy_hom_coe_of_neg (a : ℤ) (ha : a < 0)
    (n m : ℕ) : (horizontalCompleteFilteredTotalHomotopy h (a : EInt)).hom n m = 0 := by
  simp only [horizontalCompleteFilteredTotalHomotopy, WithBotTop.rec_coe,
    dite_eq_right (not_le.mpr ha), Homotopy.ofEq_hom, Pi.zero_apply]

/-- A nonnegative complete-stage homotopy is its canonical finite-stage transport. -/
theorem horizontalCompleteFilteredTotalHomotopy_hom_coe_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h (a : EInt)).hom n m =
      (horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha).hom n m := by
  simp only [horizontalCompleteFilteredTotalHomotopy, WithBotTop.rec_coe, dite_eq_left ha]

private theorem completeOfNonneg_toTotal (a : ℤ) (ha : 0 ≤ a) (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopyOfNonneg h a ha).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal L (a : EInt)).f m =
      (horizontalCompleteFilteredTotalToTotal K (a : EInt)).f n ≫
        (verticalTotalHomotopy h).hom n m := by
  have hL : (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv ≫
      horizontalCompleteFilteredTotalToTotal L (a : EInt) =
        horizontalFilteredTotalComplexToTotal L a.toNat := by
    rw [← horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal L a ha,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hLf := congrArg (fun φ => φ.f m) hL
  have hKf := congrArg (fun φ => φ.f n)
    (horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha)
  simp only [HomologicalComplex.comp_f] at hLf hKf
  rw [horizontalCompleteFilteredTotalHomotopyOfNonneg_hom]
  calc
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalHomotopy h a.toNat).hom n m ≫
          ((horizontalCompleteFilteredTotalComplexFiniteIso L a ha).inv.f m ≫
            (horizontalCompleteFilteredTotalToTotal L (a : EInt)).f m)) := by
      simp only [Category.assoc]
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalHomotopy h a.toNat).hom n m ≫
          (horizontalFilteredTotalComplexToTotal L a.toNat).f m) := by rw [hLf]
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        ((horizontalFilteredTotalComplexToTotal K a.toNat).f n ≫
          (verticalTotalHomotopy h).hom n m) := by
      rw [horizontalFilteredTotalHomotopy_toTotal]
    _ = _ := by rw [← Category.assoc, hKf]

/-- At every complete filtration index the actual homotopy commutes with
inclusion into the total complex, on each pair of degrees. -/
@[reassoc]
theorem horizontalCompleteFilteredTotalHomotopy_toTotal (i : EInt) (n m : ℕ) :
    (horizontalCompleteFilteredTotalHomotopy h i).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal L i).f m =
      (horizontalCompleteFilteredTotalToTotal K i).f n ≫ (verticalTotalHomotopy h).hom n m := by
  induction i using WithBotTop.rec with
  | bot =>
    rw [horizontalCompleteFilteredTotalHomotopy_hom_bot]
    change 0 ≫ _ = (0 : (HomologicalComplex.zero : ChainComplex C ℕ).X n ⟶ _) ≫ _
    simp
  | coe a =>
    by_cases ha : 0 ≤ a
    · rw [horizontalCompleteFilteredTotalHomotopy_hom_coe_of_nonneg h a ha]
      exact completeOfNonneg_toTotal h a ha n m
    · have hz : IsZero (horizontalCompleteFilteredTotalComplex K (a : EInt)) := by
        rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a (lt_of_not_ge ha)]
        exact HomologicalComplex.isZero_zero
      have hi : horizontalCompleteFilteredTotalToTotal K (a : EInt) = 0 := hz.eq_of_src _ _
      rw [horizontalCompleteFilteredTotalHomotopy_hom_coe_of_neg h a (lt_of_not_ge ha), hi]
      simp
  | top =>
    rw [horizontalCompleteFilteredTotalHomotopy_hom_top]
    change (verticalTotalHomotopy h).hom n m ≫ 𝟙 _ = 𝟙 _ ≫ (verticalTotalHomotopy h).hom n m
    simp

/-- Every complete-stage inclusion is monic on each chain degree. -/
instance horizontalCompleteFilteredTotalToTotal_f_mono (i : EInt) (n : ℕ) :
    Mono ((horizontalCompleteFilteredTotalToTotal K i).f n) := by
  induction i using WithBotTop.rec with
  | bot =>
    change Mono (0 : (HomologicalComplex.zero : ChainComplex C ℕ).X n ⟶ (K.total c).X n)
    infer_instance
  | coe a =>
    by_cases ha : 0 ≤ a
    · have hs := congrArg (fun φ => φ.f n)
        (horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha)
      rw [← hs]
      change Mono ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom.f n ≫
        (horizontalFilteredTotalComplexToTotal K a.toNat).f n)
      let _ : Mono ((horizontalFilteredTotalComplexToTotal K a.toNat).f n) := by
        change Mono (horizontalFilteredTotalToTotal K a.toNat n)
        infer_instance
      infer_instance
    · have hz : IsZero ((horizontalCompleteFilteredTotalComplex K (a : EInt)).X n) := by
        rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a (lt_of_not_ge ha)]
        exact isZero_zero C
      exact { right_cancellation := fun g h _ => hz.eq_of_tgt g h }
  | top =>
    change Mono (𝟙 ((K.total c).X n))
    infer_instance

/-- The canonical homotopies commute with every inequality transition in
the complete horizontal filtration, on every homotopy component. -/
theorem horizontalCompleteFilteredTotalHomotopy_naturality
    {i j : EInt} (hij : i ≤ j) (n m : ℕ) :
    (horizontalCompleteFilteredTotalMap K hij).f n ≫
        (horizontalCompleteFilteredTotalHomotopy h j).hom n m =
      (horizontalCompleteFilteredTotalHomotopy h i).hom n m ≫
        (horizontalCompleteFilteredTotalMap L hij).f m := by
  have hK := congrArg (fun φ => φ.f n) (horizontalCompleteFilteredTotalMap_toTotal K hij)
  have hL := congrArg (fun φ => φ.f m) (horizontalCompleteFilteredTotalMap_toTotal L hij)
  simp only [HomologicalComplex.comp_f] at hK hL
  apply (cancel_mono ((horizontalCompleteFilteredTotalToTotal L j).f m)).mp
  rw [Category.assoc, horizontalCompleteFilteredTotalHomotopy_toTotal,
    ← Category.assoc, hK, Category.assoc, hL, horizontalCompleteFilteredTotalHomotopy_toTotal]

omit [HasZeroObject C] in
/-- The existing finite-stage map sends the identity bicomplex map to the identity. -/
@[simp]
theorem horizontalFilteredTotalComplexMapOfBicomplex_id (k : ℕ) :
    horizontalFilteredTotalComplexMapOfBicomplex (𝟙 K) k =
      𝟙 (horizontalFilteredTotalComplex K k) := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalTotalFilteredObjectFunctor (C := C)).map_id K)
  have hk := congr_app hs k
  change horizontalFilteredTotalComplexMapOfBicomplex (𝟙 K) k = 𝟙 _ at hk
  exact hk

omit [HasZeroObject C] in
/-- The existing finite-stage maps preserve composition of bicomplex maps. -/
@[simp]
theorem horizontalFilteredTotalComplexMapOfBicomplex_comp
    {M : HomologicalComplex₂ C c c} (φ : K ⟶ L) (ψ : L ⟶ M) (k : ℕ) :
    horizontalFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) k =
      horizontalFilteredTotalComplexMapOfBicomplex φ k ≫
        horizontalFilteredTotalComplexMapOfBicomplex ψ k := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalTotalFilteredObjectFunctor (C := C)).map_comp φ ψ)
  have hk := congr_app hs k
  change horizontalFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) k =
    horizontalFilteredTotalComplexMapOfBicomplex φ k ≫
      horizontalFilteredTotalComplexMapOfBicomplex ψ k at hk
  exact hk

/-- The existing complete-stage map sends the identity bicomplex map to the identity. -/
@[simp]
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_id (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex (𝟙 K) i =
      𝟙 (horizontalCompleteFilteredTotalComplex K i) := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalCompleteTotalFilteredObjectFunctor (C := C)).map_id K)
  have hi := congr_app hs i
  change horizontalCompleteFilteredTotalComplexMapOfBicomplex (𝟙 K) i = 𝟙 _ at hi
  exact hi

/-- The existing complete-stage maps preserve composition of bicomplex maps. -/
@[simp]
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp
    {M : HomologicalComplex₂ C c c} (φ : K ⟶ L) (ψ : L ⟶ M) (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex φ i ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex ψ i := by
  have hs := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    ((horizontalCompleteTotalFilteredObjectFunctor (C := C)).map_comp φ ψ)
  have hi := congr_app hs i
  change horizontalCompleteFilteredTotalComplexMapOfBicomplex (φ ≫ ψ) i =
    horizontalCompleteFilteredTotalComplexMapOfBicomplex φ i ≫
      horizontalCompleteFilteredTotalComplexMapOfBicomplex ψ i at hi
  exact hi

end HomologicalComplex₂

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K₀ K₁ L₀ L₁ : CochainComplex C ℤ}
  (uK : K₀ ⟶ K₁) (uL : L₀ ⟶ L₁)
  {f₀ g₀ : K₀ ⟶ L₀} {f₁ g₁ : K₁ ⟶ L₁}
  (h₀ : _root_.Homotopy f₀ g₀) (h₁ : _root_.Homotopy f₁ g₁)

/-- The componentwise cone homotopy uses the negative shifted lower
homotopy and the unshifted upper homotopy. -/
def mapCompatibleHomotopyHom (n m : ℤ) :
    (CochainComplex.mappingCone uK).X n ⟶ (CochainComplex.mappingCone uL).X m :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod uK n (n + 1) rfl).hom ≫
    biprod.map (-(h₀.hom (n + 1) (m + 1))) (h₁.hom n m) ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod uL m (m + 1) rfl).inv

/-- The lower cone coordinate retains its canonical inclusion and shift sign. -/
@[reassoc]
theorem mapCompatibleHomotopyHom_inl (n m : ℤ) :
    (inl uK).v (n + 1) n (by omega) ≫ mapCompatibleHomotopyHom uK uL h₀ h₁ n m =
      -(h₀.hom (n + 1) (m + 1)) ≫ (inl uL).v (m + 1) m (by omega) := by
  simp [mapCompatibleHomotopyHom, inl]

/-- The upper cone coordinate is the actual upper-stage homotopy component. -/
@[reassoc]
theorem mapCompatibleHomotopyHom_inr (n m : ℤ) :
    (inr uK).f n ≫ mapCompatibleHomotopyHom uK uL h₀ h₁ n m =
      h₁.hom n m ≫ (inr uL).f m := by
  simp [mapCompatibleHomotopyHom, inr]

/-- Cone homotopy components vanish outside the cochain homotopy degree. -/
theorem mapCompatibleHomotopyHom_zero (n m : ℤ)
    (hrel : ¬(ComplexShape.up ℤ).Rel m n) :
    mapCompatibleHomotopyHom uK uL h₀ h₁ n m = 0 := by
  have hshift : ¬(ComplexShape.up ℤ).Rel (m + 1) (n + 1) := by
    intro hs
    apply hrel
    change m + 1 = n
    change (m + 1) + 1 = n + 1 at hs
    omega
  have hz : biprod.map (0 : K₀.X (n + 1) ⟶ L₀.X (m + 1))
      (0 : K₁.X n ⟶ L₁.X m) = 0 := by
    ext <;> simp
  simp only [mapCompatibleHomotopyHom, h₀.zero (n + 1) (m + 1) hshift,
    h₁.zero n m hrel, neg_zero, hz, zero_comp, comp_zero]

private theorem inl_map_f (a : K₀ ⟶ L₀) (b : K₁ ⟶ L₁)
    (hc : uK ≫ b = a ≫ uL) (n : ℤ) :
    (inl uK).v (n + 1) n (by omega) ≫ (map uK uL a b hc).f n =
      a.f (n + 1) ≫ (inl uL).v (n + 1) n (by omega) := by
  simp [map]

private theorem inr_map_f (a : K₀ ⟶ L₀) (b : K₁ ⟶ L₁)
    (hc : uK ≫ b = a ≫ uL) (n : ℤ) :
    (inr uK).f n ≫ (map uK uL a b hc).f n = b.f n ≫ (inr uL).f n := by
  simp [map]

@[reassoc]
private theorem inl_hom_with_indices (n m i j : ℤ) (hi : n + 1 = i) (hj : m + 1 = j) :
    (inl uK).v i n (by omega) ≫ mapCompatibleHomotopyHom uK uL h₀ h₁ n m =
      -(h₀.hom i j) ≫ (inl uL).v j m (by omega) := by
  subst i
  subst j
  exact mapCompatibleHomotopyHom_inl uK uL h₀ h₁ n m

/-- Two compatible chain homotopies induce a genuine homotopy of their
canonical cone maps. The strict component square cancels the off-diagonal term. -/
def mapHomotopyOfCompatible
    (hf : uK ≫ f₁ = f₀ ≫ uL) (hg : uK ≫ g₁ = g₀ ≫ uL)
    (hn : ∀ n m, uK.f n ≫ h₁.hom n m = h₀.hom n m ≫ uL.f m) :
    _root_.Homotopy (map uK uL f₀ f₁ hf) (map uK uL g₀ g₁ hg) where
  hom := mapCompatibleHomotopyHom uK uL h₀ h₁
  zero n m hrel := mapCompatibleHomotopyHom_zero uK uL h₀ h₁ n m hrel
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from by change n - 1 + 1 = n; omega)]
    apply ext_from uK (n + 1) n rfl
    · have he := h₀.comm (n + 1)
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (n + 1) ((n + 1) + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)] at he
      have hsub : n - 1 + 1 = n := by omega
      have hhnext := mapCompatibleHomotopyHom_inl uK uL h₀ h₁ (n + 1) n
      simp only [Preadditive.comp_add]
      rw [inl_map_f uK uL f₀ f₁ hf n, inl_map_f uK uL g₀ g₁ hg n,
        inl_v_d_assoc uK (n + 1) n ((n + 1) + 1) (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [mapCompatibleHomotopyHom_inr, hhnext,
        inl_hom_with_indices_assoc uK uL h₀ h₁ n (n - 1) (n + 1) n rfl hsub]
      simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
      rw [inl_v_d uL n (n - 1) (n + 1) (by omega) (by omega)]
      simp only [Preadditive.comp_sub]
      have hn' : uK.f (n + 1) ≫ (h₁.hom (n + 1) n ≫ (inr uL).f n) =
          h₀.hom (n + 1) n ≫ (uL.f n ≫ (inr uL).f n) := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ (inr uL).f n) (hn (n + 1) n)
      rw [hn', he]
      simp only [Preadditive.add_comp, Category.assoc]
      abel
    · have he := h₁.comm n
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from
          by change n - 1 + 1 = n; omega)] at he
      simp only [Preadditive.comp_add]
      rw [inr_map_f uK uL f₀ f₁ hf n, inr_map_f uK uL g₀ g₁ hg n,
        inr_f_d_assoc, mapCompatibleHomotopyHom_inr,
        mapCompatibleHomotopyHom_inr_assoc, inr_f_d]
      rw [he]
      simp only [Preadditive.add_comp, Category.assoc]

end CochainComplex.mappingCone

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  {f g : K ⟶ L}
  (h : _root_.Homotopy (flipMap f) (flipMap g))

/-- The actual complete-stage homotopy under the existing chain-to-cochain
embedding used by the spectral object. -/
def horizontalCompleteFiltrationCochainHomotopy (i : EInt) :
    _root_.Homotopy ((horizontalCompleteFiltrationCochainDiagramNatTrans f).app i)
      ((horizontalCompleteFiltrationCochainDiagramNatTrans g).app i) :=
  (horizontalCompleteFilteredTotalHomotopy h i).extend ComplexShape.embeddingDownNat

/-- The cochain-stage homotopies commute with every actual filtration arrow. -/
theorem horizontalCompleteFiltrationCochainHomotopy_naturality
    {i j : EInt} (a : i ⟶ j) (n m : ℤ) :
    ((horizontalCompleteFiltrationCochainDiagram K).map a).f n ≫
        (horizontalCompleteFiltrationCochainHomotopy h j).hom n m =
      (horizontalCompleteFiltrationCochainHomotopy h i).hom n m ≫
        ((horizontalCompleteFiltrationCochainDiagram L).map a).f m := by
  have ha : homOfLE (leOfHom a) = a := Subsingleton.elim _ _
  rw [← ha]
  change (HomologicalComplex.extendMap (horizontalCompleteFilteredTotalMap K (leOfHom a))
      ComplexShape.embeddingDownNat).f n ≫
      ((horizontalCompleteFilteredTotalHomotopy h j).extend
        ComplexShape.embeddingDownNat).hom n m =
    ((horizontalCompleteFilteredTotalHomotopy h i).extend
      ComplexShape.embeddingDownNat).hom n m ≫
      (HomologicalComplex.extendMap (horizontalCompleteFilteredTotalMap L (leOfHom a))
        ComplexShape.embeddingDownNat).f m
  exact _root_.Homotopy.extend_hom_naturality
    (horizontalCompleteFilteredTotalHomotopy h i)
    (horizontalCompleteFilteredTotalHomotopy h j)
    (horizontalCompleteFilteredTotalMap K (leOfHom a))
    (horizontalCompleteFilteredTotalMap L (leOfHom a))
    (horizontalCompleteFilteredTotalHomotopy_naturality h (leOfHom a))
    ComplexShape.embeddingDownNat n m

/-- The complete filtered homotopy induces a genuine homotopy on every
actual interval cone in the chosen spectral-object construction. -/
def horizontalCompleteFiltrationMappingConeHomotopy (I : ComposableArrows EInt 1) :
    _root_.Homotopy ((horizontalCompleteFiltrationMappingConeNatTrans f).app I)
      ((horizontalCompleteFiltrationMappingConeNatTrans g).app I) :=
  CochainComplex.mappingCone.mapHomotopyOfCompatible
    ((horizontalCompleteFiltrationCochainDiagram K).map (I.map' 0 1))
    ((horizontalCompleteFiltrationCochainDiagram L).map (I.map' 0 1))
    (horizontalCompleteFiltrationCochainHomotopy h (I.obj 0))
    (horizontalCompleteFiltrationCochainHomotopy h (I.obj 1))
    ((horizontalCompleteFiltrationCochainDiagramNatTrans f).naturality (I.map' 0 1))
    ((horizontalCompleteFiltrationCochainDiagramNatTrans g).naturality (I.map' 0 1))
    (horizontalCompleteFiltrationCochainHomotopy_naturality h (I.map' 0 1))

/-- The lower interval-cone coordinate is the negative shifted homotopy of
the actual lower filtration stage. -/
@[reassoc]
theorem horizontalCompleteFiltrationMappingConeHomotopy_inl
    (I : ComposableArrows EInt 1) (n m : ℤ) :
    (CochainComplex.mappingCone.inl
        ((horizontalCompleteFiltrationCochainDiagram K).map (I.map' 0 1))).v
          (n + 1) n (by omega) ≫
        (horizontalCompleteFiltrationMappingConeHomotopy h I).hom n m =
      -((horizontalCompleteFiltrationCochainHomotopy h (I.obj 0)).hom (n + 1) (m + 1)) ≫
        (CochainComplex.mappingCone.inl
          ((horizontalCompleteFiltrationCochainDiagram L).map (I.map' 0 1))).v
            (m + 1) m (by omega) :=
  CochainComplex.mappingCone.mapCompatibleHomotopyHom_inl _ _ _ _ n m

/-- The upper interval-cone coordinate is the actual upper-stage homotopy. -/
@[reassoc]
theorem horizontalCompleteFiltrationMappingConeHomotopy_inr
    (I : ComposableArrows EInt 1) (n m : ℤ) :
    (CochainComplex.mappingCone.inr
        ((horizontalCompleteFiltrationCochainDiagram K).map (I.map' 0 1))).f n ≫
        (horizontalCompleteFiltrationMappingConeHomotopy h I).hom n m =
      (horizontalCompleteFiltrationCochainHomotopy h (I.obj 1)).hom n m ≫
        (CochainComplex.mappingCone.inr
          ((horizontalCompleteFiltrationCochainDiagram L).map (I.map' 0 1))).f m :=
  CochainComplex.mappingCone.mapCompatibleHomotopyHom_inr _ _ _ _ n m

/-- The actual interval-cone map of the identity bicomplex map is the identity. -/
theorem horizontalCompleteFiltrationMappingConeNatTrans_id
    (I : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationMappingConeNatTrans (𝟙 K)).app I =
      𝟙 ((horizontalCompleteFiltrationMappingConeFunctor K).obj I) := by
  simp only [horizontalCompleteFiltrationMappingConeNatTrans_app,
    horizontalCompleteFiltrationCochainDiagramNatTrans_app,
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_id, HomologicalComplex.extendMap_id]
  exact CochainComplex.mappingCone.map_id _

/-- The actual interval-cone maps preserve composition of bicomplex maps. -/
theorem horizontalCompleteFiltrationMappingConeNatTrans_comp
    {M : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (φ : K ⟶ L) (ψ : L ⟶ M) (I : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationMappingConeNatTrans (φ ≫ ψ)).app I =
      (horizontalCompleteFiltrationMappingConeNatTrans φ).app I ≫
        (horizontalCompleteFiltrationMappingConeNatTrans ψ).app I := by
  simp only [horizontalCompleteFiltrationMappingConeNatTrans_app,
    horizontalCompleteFiltrationCochainDiagramNatTrans_app,
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_comp, HomologicalComplex.extendMap_comp]
  apply CochainComplex.mappingCone.map_comp

end HomologicalComplex₂
