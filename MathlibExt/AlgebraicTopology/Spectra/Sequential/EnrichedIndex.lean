/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TensorPowers
public import MathlibExt.CategoryTheory.Monoidal.TensorInitial
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# An enriched indexing category for sequential spectra

In a braided closed monoidal category with an initial object, the natural-number
degrees form an enriched indexing category. A forward Hom object is a tensor power
of the suspension object, and a backward Hom object is initial.
Composition uses the reversed tensor-power pairing and its unit and associativity laws;
forward-degree composition is an isomorphism, and a successor Hom object is the suspension object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory

namespace CategoryTheory.SequentialSpectrum.EnrichedIndex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

private theorem reverseBraidWord (P Q R : C) :
    ((β_ P Q).hom ▷ R) ≫ (β_ (Q ⊗ P) R).hom ≫ (α_ R Q P).inv =
      (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫ (β_ P (R ⊗ Q)).hom := by
  rw [braiding_tensor_left_hom, braiding_tensor_right_hom]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun f => (α_ P Q R).hom ≫ f ≫ (α_ R Q P).inv)
      (yang_baxter P Q R)

/-- The literal reversed finite tensor-power product, with source-first degrees. -/
def reversePair (K : C) (p q : ℕ) :
    TensorPower.tensorPowObj K p ⊗ TensorPower.tensorPowObj K q ⟶
      TensorPower.tensorPowObj K (p + q) :=
  (β_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q)).hom ≫
    (TensorPower.tensorPowObj_add K q p).inv ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm q p))

/-- The zero-left product is the actual left unitor and degree transport. -/
theorem reversePair_zero_left (K : C) (p : ℕ) :
    reversePair K 0 p = (λ_ (TensorPower.tensorPowObj K p)).hom ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.zero_add p).symm) := by
  unfold reversePair
  change (β_ (𝟙_ C) (TensorPower.tensorPowObj K p)).hom ≫
    (TensorPower.tensorPowObj_add K p 0).inv ≫ _ = _
  rw [braiding_tensorUnit_left]
  have hAdd : (TensorPower.tensorPowObj_add K p 0).inv =
      (ρ_ (TensorPower.tensorPowObj K p)).hom :=
    (Iso.inv_eq_inv (TensorPower.tensorPowObj_add K p 0)
      (ρ_ (TensorPower.tensorPowObj K p)).symm).mpr
        (TensorPower.tensorPowObj_add_zero_right K p)
  rw [hAdd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The zero-right product is the actual right unitor. -/
theorem reversePair_zero_right (K : C) (p : ℕ) :
    reversePair K p 0 = (ρ_ (TensorPower.tensorPowObj K p)).hom := by
  unfold reversePair
  change (β_ (TensorPower.tensorPowObj K p) (𝟙_ C)).hom ≫
    (TensorPower.tensorPowObj_add K 0 p).inv ≫ _ = _
  rw [braiding_tensorUnit_right]
  change ((ρ_ (TensorPower.tensorPowObj K p)).hom ≫
    (λ_ (TensorPower.tensorPowObj K p)).inv) ≫
    (TensorPower.tensorPowObj_add K 0 p).inv ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm 0 p)) =
        (ρ_ (TensorPower.tensorPowObj K p)).hom
  have hAdd : (TensorPower.tensorPowObj_add K 0 p).inv ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.zero_add p)) =
        (λ_ (TensorPower.tensorPowObj K p)).hom := by
    let e := eqToIso (congrArg (TensorPower.tensorPowObj K) (Nat.zero_add p))
    have hUnit : (λ_ (TensorPower.tensorPowObj K p)).hom =
        (TensorPower.tensorPowObj_add K 0 p).inv ≫ e.hom :=
      (Iso.eq_inv_comp (TensorPower.tensorPowObj_add K 0 p)).mpr
        (TensorPower.tensorPowObj_add_zero_left K p)
    exact hUnit.symm
  have hTransport :
      (eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm 0 p)) :
        TensorPower.tensorPowObj K (0 + p) ⟶ TensorPower.tensorPowObj K p) =
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.zero_add p)) := by
    apply congrArg (fun h : TensorPower.tensorPowObj K (0 + p) =
      TensorPower.tensorPowObj K p => eqToHom h)
    exact Subsingleton.elim _ _
  calc
    _ = ((ρ_ (TensorPower.tensorPowObj K p)).hom ≫
        (λ_ (TensorPower.tensorPowObj K p)).inv) ≫
        (TensorPower.tensorPowObj_add K 0 p).inv ≫
        eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.zero_add p)) :=
      congrArg (fun f : TensorPower.tensorPowObj K (0 + p) ⟶
        TensorPower.tensorPowObj K p =>
          ((ρ_ (TensorPower.tensorPowObj K p)).hom ≫
            (λ_ (TensorPower.tensorPowObj K p)).inv) ≫
            (TensorPower.tensorPowObj_add K 0 p).inv ≫ f) hTransport
    _ = ((ρ_ (TensorPower.tensorPowObj K p)).hom ≫
        (λ_ (TensorPower.tensorPowObj K p)).inv) ≫
        (λ_ (TensorPower.tensorPowObj K p)).hom :=
      congrArg (fun f : 𝟙_ C ⊗ TensorPower.tensorPowObj K p ⟶
        TensorPower.tensorPowObj K p =>
          ((ρ_ (TensorPower.tensorPowObj K p)).hom ≫
            (λ_ (TensorPower.tensorPowObj K p)).inv) ≫ f) hAdd
    _ = _ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Reverse pairing is associative with the original source-first degree transport. -/
theorem reversePair_assoc (K : C) (p q r : ℕ) :
    (reversePair K p q ▷ TensorPower.tensorPowObj K r) ≫
        reversePair K (p + q) r ≫
        eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc p q r)) =
      (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q)
        (TensorPower.tensorPowObj K r)).hom ≫
        (TensorPower.tensorPowObj K p ◁ reversePair K q r) ≫
        reversePair K p (q + r) := by
  let P := TensorPower.tensorPowObj K p
  let Q := TensorPower.tensorPowObj K q
  let R := TensorPower.tensorPowObj K r
  let μ (a b : ℕ) := (TensorPower.tensorPowObj_add K a b).inv
  have hIdentity (a b : ℕ) : TensorPower.laxTensorPowerPairing (𝟭 C) K a b =
      μ a b := by
    change 𝟙 _ ≫ (TensorPower.tensorPowObj_add K a b).inv = _
    exact Category.id_comp _
  have hμ : (μ r q ▷ P) ≫ μ (r + q) p ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc r q p)) =
        (α_ R Q P).hom ≫ (R ◁ μ q p) ≫ μ r (q + p) := by
    simpa only [hIdentity, Functor.id_obj, tensorHom_id, id_tensorHom, P, Q, R] using
      TensorPower.laxTensorPowerPairing_assoc (𝟭 C) K r q p
  have hReverse :
      ((β_ P Q).hom ▷ R) ≫ (μ q p ▷ R) ≫
          (β_ (TensorPower.tensorPowObj K (q + p)) R).hom ≫ μ r (q + p) =
        (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫ (P ◁ μ r q) ≫
          (β_ P (TensorPower.tensorPowObj K (r + q))).hom ≫ μ (r + q) p ≫
          eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc r q p)) := by
    rw [braiding_naturality_left_assoc]
    rw [← (Iso.inv_comp_eq (α_ R Q P)).mpr hμ]
    have hWord := congrArg
      (fun f => f ≫ (μ r q ▷ P) ≫ μ (r + q) p ≫
        eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc r q p)))
      (reverseBraidWord P Q R)
    simpa only [P, Q, R, Category.assoc, braiding_naturality_right_assoc] using hWord
  have hLeftCast :
      (eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm q p)) ▷ R) ≫
          (β_ (TensorPower.tensorPowObj K (p + q)) R).hom ≫ μ r (p + q) ≫
          eqToHom (congrArg (TensorPower.tensorPowObj K)
            (show r + (p + q) = r + (q + p) by omega)) =
        (β_ (TensorPower.tensorPowObj K (q + p)) R).hom ≫ μ r (q + p) := by
    have h := eqToHom_naturality
      (fun n => (β_ (TensorPower.tensorPowObj K n) R).hom ≫ μ r n)
      (Nat.add_comm q p)
    have hPost := congrArg (fun f => f ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K)
        (show r + (p + q) = r + (q + p) by omega))) h.symm
    simpa only [eqToHom_whiskerRight, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id, μ, R] using hPost
  have hRightCast :
      (P ◁ eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm r q))) ≫
          (β_ P (TensorPower.tensorPowObj K (q + r))).hom ≫ μ (q + r) p ≫
          eqToHom (congrArg (TensorPower.tensorPowObj K)
            (show (q + r) + p = (r + q) + p by omega)) =
        (β_ P (TensorPower.tensorPowObj K (r + q))).hom ≫ μ (r + q) p := by
    have h := eqToHom_naturality
      (fun n => (β_ P (TensorPower.tensorPowObj K n)).hom ≫ μ n p)
      (Nat.add_comm r q)
    have hPost := congrArg (fun f => f ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K)
        (show (q + r) + p = (r + q) + p by omega))) h.symm
    simpa only [whiskerLeft_eqToHom, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id, μ, P] using hPost
  let e : p + (q + r) = r + (q + p) := by omega
  apply (cancel_mono (eqToHom (congrArg (TensorPower.tensorPowObj K) e))).mp
  have hL := congrArg
    (fun f => ((β_ P Q).hom ▷ R) ≫ (μ q p ▷ R) ≫ f) hLeftCast
  have hR := congrArg
    (fun f => (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫ (P ◁ μ r q) ≫ f ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc r q p)))
    hRightCast
  have hRightNormalized :
      (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫ (P ◁ μ r q) ≫
          (β_ P (TensorPower.tensorPowObj K (r + q))).hom ≫ μ (r + q) p ≫
          eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc r q p)) =
        (α_ P Q R).hom ≫ (P ◁ (β_ Q R).hom) ≫ (P ◁ μ r q) ≫
          (P ◁ eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm r q))) ≫
          (β_ P (TensorPower.tensorPowObj K (q + r))).hom ≫ μ (q + r) p ≫
          eqToHom (congrArg (TensorPower.tensorPowObj K)
            (show (q + r) + p = r + (q + p) by omega)) := by
    simpa only [Category.assoc, eqToHom_trans] using hR.symm
  simpa only [reversePair, P, Q, R, μ, e, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc, eqToHom_trans] using
      hL.trans (hReverse.trans hRightNormalized)


/-- The actual degree wrapper; its enrichment does not alter Nat instances. -/
@[ext]
structure Index (K : C) where
  /-- The natural-number degree of the sequential spectrum index. -/
  degree : ℕ

/-- The original natural degree as an object of the genuine indexing category. -/
def degree (K : C) (n : ℕ) : Index K := ⟨n⟩

variable [MonoidalClosed C] [HasInitial C]

/-- Actual forward tensor powers, with initial backward Hom objects. -/
abbrev indexHom (K : C) (a b : Index K) : C :=
  if a.degree ≤ b.degree then TensorPower.tensorPowObj K (b.degree - a.degree) else ⊥_ C

private abbrev tensorInitialLeft (X : C) : IsInitial (X ⊗ ⊥_ C) :=
  MonoidalCategory.tensorInitialLeft X

private abbrev tensorInitialRight (X : C) : IsInitial ((⊥_ C) ⊗ X) :=
  MonoidalCategory.tensorInitialRight X

private def tensorInitialOfFirst {A B : C} (hA : IsInitial A) : IsInitial (A ⊗ B) := by
  let _ : PreservesColimitsOfSize.{0, 0} (tensorLeft B) :=
    (ihom.adjunction B).leftAdjoint_preservesColimits
  let _ : PreservesColimit (Functor.empty.{0} C) (tensorRight B) :=
    preservesColimit_of_natIso (Functor.empty.{0} C) (tensorLeftIsoTensorRight B)
  exact IsInitial.isInitialObj (tensorRight B) A hA

private def tensorInitialOfSecond {A B : C} (hB : IsInitial B) : IsInitial (A ⊗ B) := by
  let _ : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
    (ihom.adjunction A).leftAdjoint_preservesColimits
  exact IsInitial.isInitialObj (tensorLeft A) B hB

/-- The degree-zero identity is the original monoidal unit map. -/
def indexId (K : C) (a : Index K) : 𝟙_ C ⟶ indexHom K a a :=
  eqToHom (by simp [indexHom, TensorPower.tensorPowObj_zero])

/-- Original source-first, late-power-first composition of complete Hom objects. -/
def indexComp (K : C) (a b c : Index K) :
    indexHom K a b ⊗ indexHom K b c ⟶ indexHom K a c := by
  by_cases hab : a.degree ≤ b.degree
  · by_cases hbc : b.degree ≤ c.degree
    · have hac : a.degree ≤ c.degree := hab.trans hbc
      rw [indexHom, ite_eq_left hab, indexHom, ite_eq_left hbc, indexHom, ite_eq_left hac]
      exact reversePair K (b.degree - a.degree) (c.degree - b.degree) ≫
        eqToHom (congrArg (TensorPower.tensorPowObj K)
          (show (b.degree - a.degree) + (c.degree - b.degree) =
            c.degree - a.degree by omega))
    · rw [indexHom, ite_eq_left hab, indexHom, ite_eq_right hbc]
      exact (tensorInitialLeft _).to _
  · rw [indexHom, ite_eq_right hab]
    exact (tensorInitialRight _).to _

omit [BraidedCategory C] [MonoidalClosed C] in
/-- Backward Hom objects are the actual selected initial object. -/
theorem indexHom_of_gt (K : C) (a b : Index K) (h : b.degree < a.degree) :
    indexHom K a b = ⊥_ C := ite_eq_right (Nat.not_le_of_gt h)

omit [BraidedCategory C] [MonoidalClosed C] in
/-- Forward Hom objects retain their literal degree difference. -/
theorem indexHom_of_le (K : C) (a b : Index K) (h : a.degree ≤ b.degree) :
    indexHom K a b = TensorPower.tensorPowObj K (b.degree - a.degree) := ite_eq_left h

omit [BraidedCategory C] [MonoidalClosed C] in
/-- The diagonal Hom is the original monoidal unit. -/
theorem indexHom_self (K : C) (a : Index K) : indexHom K a a = 𝟙_ C := by
  simp only [indexHom, le_refl, ite_true, Nat.sub_self, TensorPower.tensorPowObj_zero]

/-- The successor Hom is the original degree-one power of K. -/
def indexHomSuccessorIso (K : C) (n : ℕ) :
    indexHom K (degree K n) (degree K (n + 1)) ≅ K :=
  eqToIso (by simp [indexHom, degree, TensorPower.tensorPowObj_succ,
    TensorPower.tensorPowObj_zero]) ≪≫ λ_ K

/-- Forward-degree composition retains the original ordered power and exact degree casts. -/
theorem indexComp_of_le (K : C) (a b c : Index K)
    (hab : a.degree ≤ b.degree) (hbc : b.degree ≤ c.degree) :
    indexComp K a b c =
      eqToHom (congrArg₂ (fun X Y : C => X ⊗ Y)
        (indexHom_of_le K a b hab)
        (indexHom_of_le K b c hbc)) ≫
      reversePair K (b.degree - a.degree) (c.degree - b.degree) ≫
      eqToHom (congrArg (TensorPower.tensorPowObj K)
        (show (b.degree - a.degree) + (c.degree - b.degree) =
          c.degree - a.degree by omega)) ≫
      eqToHom (indexHom_of_le K a c (hab.trans hbc)).symm := by
  apply eq_of_heq
  simpa only [indexComp, dite_eq_left hab, dite_eq_left hbc, Eq.mpr, Eq.mp,
    eqRec_heq_iff, heq_eqRec_iff, eqToHom_trans, eqToHom_comp_heq_iff,
    heq_eqToHom_comp_iff, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff] using
      (HEq.refl (reversePair K (b.degree - a.degree) (c.degree - b.degree)))

theorem index_id_comp (K : C) (a b : Index K) :
    (λ_ (indexHom K a b)).inv ≫ (indexId K a ▷ indexHom K a b) ≫
      indexComp K a a b = 𝟙 (indexHom K a b) := by
  by_cases hab : a.degree ≤ b.degree
  · let H := indexHom K a b
    let p := b.degree - a.degree
    let P := TensorPower.tensorPowObj K p
    have hH : H = P := indexHom_of_le K a b hab
    have hD : indexHom K a a = 𝟙_ C := indexHom_self K a
    have hObj (F : C → Type v) (z : ∀ Z, F Z) {Z Z' : C} (h : Z = Z') :
        z Z ≍ z Z' := by cases h; rfl
    have hLambda : (λ_ H).inv ≍ (λ_ P).inv :=
      hObj (fun Z => Z ⟶ 𝟙_ C ⊗ Z) (fun Z => (λ_ Z).inv) hH
    have hWhisker : (indexId K a ▷ H) ≍ 𝟙 (𝟙_ C ⊗ P) := by
      unfold indexId
      rw [eqToHom_whiskerRight]
      exact (eqToHom_heq_id_dom _ _ _).trans
        (hObj (fun Z => Z ⟶ Z) (fun Z => 𝟙 Z)
          (congrArg (fun Z => 𝟙_ C ⊗ Z) hH))
    have hComp : indexComp K a a b ≍ reversePair K (a.degree - a.degree) p := by
      rw [indexComp_of_le K a a b (le_refl _) hab]
      simpa only [eqToHom_trans, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff] using
        (HEq.refl (reversePair K (a.degree - a.degree) p))
    have hNat (m n : ℕ) (h : m = n) : reversePair K m p ≍ reversePair K n p := by
      cases h
      rfl
    have hCompUnit : indexComp K a a b ≍ (λ_ P).hom :=
      hComp.trans ((hNat _ _ (Nat.sub_self a.degree)).trans
        ((heq_of_eq (reversePair_zero_left K p)).trans
          (comp_eqToHom_heq (λ_ P).hom
            (congrArg (TensorPower.tensorPowObj K) (Nat.zero_add p).symm))))
    have hTail : (indexId K a ▷ H) ≫ indexComp K a a b ≍
        𝟙 (𝟙_ C ⊗ P) ≫ (λ_ P).hom :=
      heq_comp (congrArg (fun Z => 𝟙_ C ⊗ Z) hH)
        (congrArg₂ (fun X Y : C => X ⊗ Y) hD hH) hH hWhisker hCompUnit
    have hAll : (λ_ H).inv ≫ (indexId K a ▷ H) ≫ indexComp K a a b ≍
        (λ_ P).inv ≫ 𝟙 (𝟙_ C ⊗ P) ≫ (λ_ P).hom :=
      heq_comp hH (congrArg (fun Z => 𝟙_ C ⊗ Z) hH) hH hLambda hTail
    have hCanonical : (λ_ P).inv ≫ 𝟙 (𝟙_ C ⊗ P) ≫ (λ_ P).hom = 𝟙 P := by
      rw [Category.id_comp]
      exact (λ_ P).inv_hom_id
    exact eq_of_heq (hAll.trans ((heq_of_eq hCanonical).trans
      (hObj (fun Z => Z ⟶ Z) (fun Z => 𝟙 Z) hH.symm)))
  · have hI : IsInitial (indexHom K a b) := by
      rw [indexHom, ite_eq_right hab]
      exact initialIsInitial
    exact hI.hom_ext _ _

theorem index_comp_id (K : C) (a b : Index K) :
    (ρ_ (indexHom K a b)).inv ≫ (indexHom K a b ◁ indexId K b) ≫
      indexComp K a b b = 𝟙 (indexHom K a b) := by
  by_cases hab : a.degree ≤ b.degree
  · let H := indexHom K a b
    let p := b.degree - a.degree
    let P := TensorPower.tensorPowObj K p
    have hH : H = P := indexHom_of_le K a b hab
    have hD : indexHom K b b = 𝟙_ C := indexHom_self K b
    have hObj (F : C → Type v) (z : ∀ Z, F Z) {Z Z' : C} (h : Z = Z') :
        z Z ≍ z Z' := by cases h; rfl
    have hRho : (ρ_ H).inv ≍ (ρ_ P).inv :=
      hObj (fun Z => Z ⟶ Z ⊗ 𝟙_ C) (fun Z => (ρ_ Z).inv) hH
    have hWhisker : (H ◁ indexId K b) ≍ 𝟙 (P ⊗ 𝟙_ C) := by
      unfold indexId
      rw [whiskerLeft_eqToHom]
      exact (eqToHom_heq_id_dom _ _ _).trans
        (hObj (fun Z => Z ⟶ Z) (fun Z => 𝟙 Z)
          (congrArg (fun Z => Z ⊗ 𝟙_ C) hH))
    have hComp : indexComp K a b b ≍ reversePair K p (b.degree - b.degree) := by
      rw [indexComp_of_le K a b b hab (le_refl _)]
      simpa only [eqToHom_trans, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff] using
        (HEq.refl (reversePair K p (b.degree - b.degree)))
    have hNat (m n : ℕ) (h : m = n) : reversePair K p m ≍ reversePair K p n := by
      cases h
      rfl
    have hCompUnit : indexComp K a b b ≍ (ρ_ P).hom :=
      hComp.trans ((hNat _ _ (Nat.sub_self b.degree)).trans
        (heq_of_eq (reversePair_zero_right K p)))
    have hTail : (H ◁ indexId K b) ≫ indexComp K a b b ≍
        𝟙 (P ⊗ 𝟙_ C) ≫ (ρ_ P).hom :=
      heq_comp (congrArg (fun Z => Z ⊗ 𝟙_ C) hH)
        (congrArg₂ (fun X Y : C => X ⊗ Y) hH hD) hH hWhisker hCompUnit
    have hAll : (ρ_ H).inv ≫ (H ◁ indexId K b) ≫ indexComp K a b b ≍
        (ρ_ P).inv ≫ 𝟙 (P ⊗ 𝟙_ C) ≫ (ρ_ P).hom :=
      heq_comp hH (congrArg (fun Z => Z ⊗ 𝟙_ C) hH) hH hRho hTail
    have hCanonical : (ρ_ P).inv ≫ 𝟙 (P ⊗ 𝟙_ C) ≫ (ρ_ P).hom = 𝟙 P := by
      rw [Category.id_comp]
      exact (ρ_ P).inv_hom_id
    exact eq_of_heq (hAll.trans ((heq_of_eq hCanonical).trans
      (hObj (fun Z => Z ⟶ Z) (fun Z => 𝟙 Z) hH.symm)))
  · have hI : IsInitial (indexHom K a b) := by
      rw [indexHom, ite_eq_right hab]
      exact initialIsInitial
    exact hI.hom_ext _ _

theorem index_assoc (K : C) (a b c d : Index K) :
    (α_ (indexHom K a b) (indexHom K b c) (indexHom K c d)).inv ≫
        (indexComp K a b c ▷ indexHom K c d) ≫ indexComp K a c d =
      (indexHom K a b ◁ indexComp K b c d) ≫ indexComp K a b d := by
  by_cases hab : a.degree ≤ b.degree
  · by_cases hbc : b.degree ≤ c.degree
    · by_cases hcd : c.degree ≤ d.degree
      · let p := b.degree - a.degree
        let q := c.degree - b.degree
        let r := d.degree - c.degree
        let P := TensorPower.tensorPowObj K p
        let Q := TensorPower.tensorPowObj K q
        let R := TensorPower.tensorPowObj K r
        have hac := hab.trans hbc
        have hbd := hbc.trans hcd
        have had := hac.trans hcd
        have hAB : indexHom K a b = P := indexHom_of_le K a b hab
        have hBC : indexHom K b c = Q := indexHom_of_le K b c hbc
        have hCD : indexHom K c d = R := indexHom_of_le K c d hcd
        have hPQ : c.degree - a.degree = p + q := by dsimp only [p, q]; omega
        have hQR : d.degree - b.degree = q + r := by dsimp only [q, r]; omega
        have hPQR : d.degree - a.degree = p + (q + r) := by
          dsimp only [p, q, r]
          omega
        have hAC : indexHom K a c = TensorPower.tensorPowObj K (p + q) :=
          (indexHom_of_le K a c hac).trans (congrArg (TensorPower.tensorPowObj K) hPQ)
        have hBD : indexHom K b d = TensorPower.tensorPowObj K (q + r) :=
          (indexHom_of_le K b d hbd).trans (congrArg (TensorPower.tensorPowObj K) hQR)
        have hAD : indexHom K a d = TensorPower.tensorPowObj K (p + (q + r)) :=
          (indexHom_of_le K a d had).trans (congrArg (TensorPower.tensorPowObj K) hPQR)
        have hComp (x y z : Index K) (hxy : x.degree ≤ y.degree)
            (hyz : y.degree ≤ z.degree) :
            indexComp K x y z ≍ reversePair K (y.degree - x.degree) (z.degree - y.degree) := by
          rw [indexComp_of_le K x y z hxy hyz]
          simpa only [eqToHom_trans, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff] using
            (HEq.refl (reversePair K (y.degree - x.degree) (z.degree - y.degree)))
        have hNat (m n m' n' : ℕ) (hm : m = m') (hn : n = n') :
            reversePair K m n ≍ reversePair K m' n' := by
          cases hm
          cases hn
          rfl
        have hABC : indexComp K a b c ≍ reversePair K p q := hComp a b c hab hbc
        have hBCD : indexComp K b c d ≍ reversePair K q r := hComp b c d hbc hcd
        have hACD : indexComp K a c d ≍ reversePair K (p + q) r ≫
            eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc p q r)) :=
          (hComp a c d hac hcd).trans ((hNat _ _ _ _ hPQ rfl).trans
            (comp_eqToHom_heq (reversePair K (p + q) r)
              (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc p q r))).symm)
        have hABD : indexComp K a b d ≍ reversePair K p (q + r) :=
          (hComp a b d hab hbd).trans (hNat _ _ _ _ rfl hQR)
        have hAssoc (X Y Z X' Y' Z' : C) (hx : X = X') (hy : Y = Y') (hz : Z = Z') :
            (α_ X Y Z).inv ≍ (α_ X' Y' Z').inv := by
          cases hx
          cases hy
          cases hz
          rfl
        have hRight {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
            (hx : X = X') (hy : Y = Y') (hf : f ≍ g) (Z Z' : C) (hz : Z = Z') :
            (f ▷ Z) ≍ (g ▷ Z') := by
          cases hx
          cases hy
          cases hz
          cases eq_of_heq hf
          rfl
        have hLeft {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
            (hx : X = X') (hy : Y = Y') (hf : f ≍ g) (Z Z' : C) (hz : Z = Z') :
            (Z ◁ f) ≍ (Z' ◁ g) := by
          cases hx
          cases hy
          cases hz
          cases eq_of_heq hf
          rfl
        have hSource := congrArg₂ (fun X Y : C => X ⊗ Y) hAB
          (congrArg₂ (fun X Y : C => X ⊗ Y) hBC hCD)
        have hMid := congrArg₂ (fun X Y : C => X ⊗ Y)
          (congrArg₂ (fun X Y : C => X ⊗ Y) hAB hBC) hCD
        have hAfter := congrArg₂ (fun X Y : C => X ⊗ Y) hAC hCD
        have hWhiskerRight : (indexComp K a b c ▷ indexHom K c d) ≍
            (reversePair K p q ▷ R) :=
          hRight _ _ (congrArg₂ (fun X Y : C => X ⊗ Y) hAB hBC) hAC hABC _ _ hCD
        have hTail : (indexComp K a b c ▷ indexHom K c d) ≫ indexComp K a c d ≍
            (reversePair K p q ▷ R) ≫ reversePair K (p + q) r ≫
              eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc p q r)) :=
          heq_comp hMid hAfter hAD hWhiskerRight hACD
        have hL : (α_ (indexHom K a b) (indexHom K b c) (indexHom K c d)).inv ≫
            (indexComp K a b c ▷ indexHom K c d) ≫ indexComp K a c d ≍
            (α_ P Q R).inv ≫ (reversePair K p q ▷ R) ≫ reversePair K (p + q) r ≫
              eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc p q r)) :=
          heq_comp hSource hMid hAD (hAssoc _ _ _ _ _ _ hAB hBC hCD) hTail
        have hWhiskerLeft : (indexHom K a b ◁ indexComp K b c d) ≍
            (P ◁ reversePair K q r) :=
          hLeft _ _ (congrArg₂ (fun X Y : C => X ⊗ Y) hBC hCD) hBD hBCD _ _ hAB
        have hR : (indexHom K a b ◁ indexComp K b c d) ≫ indexComp K a b d ≍
            (P ◁ reversePair K q r) ≫ reversePair K p (q + r) :=
          heq_comp hSource (congrArg₂ (fun X Y : C => X ⊗ Y) hAB hBD) hAD
            hWhiskerLeft hABD
        have hCanonical : (α_ P Q R).inv ≫ (reversePair K p q ▷ R) ≫
            reversePair K (p + q) r ≫
              eqToHom (congrArg (TensorPower.tensorPowObj K) (Nat.add_assoc p q r)) =
            (P ◁ reversePair K q r) ≫ reversePair K p (q + r) := by
          simpa only [P, Q, R, Category.assoc, Iso.inv_hom_id_assoc] using
            congrArg (fun f => (α_ P Q R).inv ≫ f) (reversePair_assoc K p q r)
        exact eq_of_heq (hL.trans ((heq_of_eq hCanonical).trans hR.symm))
      · have hLast : IsInitial (indexHom K c d) := by
          rw [indexHom, ite_eq_right hcd]
          exact initialIsInitial
        have hDomain : IsInitial (indexHom K a b ⊗
            (indexHom K b c ⊗ indexHom K c d)) :=
          tensorInitialOfSecond (tensorInitialOfSecond hLast)
        exact hDomain.hom_ext _ _
    · have hMiddle : IsInitial (indexHom K b c) := by
        rw [indexHom, ite_eq_right hbc]
        exact initialIsInitial
      have hDomain : IsInitial (indexHom K a b ⊗
          (indexHom K b c ⊗ indexHom K c d)) :=
        tensorInitialOfSecond (tensorInitialOfFirst hMiddle)
      exact hDomain.hom_ext _ _
  · have hFirst : IsInitial (indexHom K a b) := by
      rw [indexHom, ite_eq_right hab]
      exact initialIsInitial
    have hDomain : IsInitial (indexHom K a b ⊗
        (indexHom K b c ⊗ indexHom K c d)) := tensorInitialOfFirst hFirst
    exact hDomain.hom_ext _ _

/-- The genuine enriched sequential indexing category on the dedicated degree wrapper. -/
@[instance_reducible]
def enrichedCategory (K : C) : EnrichedCategory C (Index K) where
  Hom := indexHom K
  id := indexId K
  comp := indexComp K
  id_comp := index_id_comp K
  comp_id := index_comp_id K
  assoc := index_assoc K

end CategoryTheory.SequentialSpectrum.EnrichedIndex

namespace CategoryTheory.SequentialSpectrum.EnrichedPresentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasInitial C] {K : C}

/-- Actual composition along forward degrees is an isomorphism on full Hom objects. -/
theorem indexComp_isIso_of_le (K : C) (a b c : EnrichedIndex.Index K)
    (hab : a.degree ≤ b.degree) (hbc : b.degree ≤ c.degree) :
    IsIso (EnrichedIndex.indexComp K a b c) := by
  let p := b.degree - a.degree
  let q := c.degree - b.degree
  let P := TensorPower.tensorPowObj K p
  let Q := TensorPower.tensorPowObj K q
  let e : P ⊗ Q ≅ TensorPower.tensorPowObj K (p + q) :=
    (β_ P Q) ≪≫ (TensorPower.tensorPowObj_add K q p).symm ≪≫
      eqToIso (congrArg (TensorPower.tensorPowObj K) (Nat.add_comm q p))
  have hPair : IsIso (EnrichedIndex.reversePair K p q) := e.isIso_hom
  have hMap : EnrichedIndex.indexComp K a b c ≍ EnrichedIndex.reversePair K p q := by
    simpa only [EnrichedIndex.indexComp, dite_eq_left hab, dite_eq_left hbc,
      Eq.mpr, Eq.mp, eqRec_heq_iff, heq_eqRec_iff, eqToHom_trans,
      eqToHom_comp_heq_iff, heq_eqToHom_comp_iff, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff] using
        (HEq.refl (EnrichedIndex.reversePair K p q))
  have hSum : c.degree - a.degree = p + q := by
    dsimp only [p, q]
    omega
  have hSource : EnrichedIndex.indexHom K a b ⊗ EnrichedIndex.indexHom K b c = P ⊗ Q :=
    congrArg₂ (fun X Y : C => X ⊗ Y)
      (EnrichedIndex.indexHom_of_le K a b hab)
      (EnrichedIndex.indexHom_of_le K b c hbc)
  have hTarget : EnrichedIndex.indexHom K a c = TensorPower.tensorPowObj K (p + q) :=
    (EnrichedIndex.indexHom_of_le K a c (hab.trans hbc)).trans
      (congrArg (TensorPower.tensorPowObj K) hSum)
  have transport {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
      (hx : X = X') (hy : Y = Y') (hfg : f ≍ g) (hg : IsIso g) : IsIso f := by
    cases hx
    cases hy
    cases eq_of_heq hfg
    exact hg
  exact transport _ _ hSource hTarget hMap hPair

end CategoryTheory.SequentialSpectrum.EnrichedPresentation
