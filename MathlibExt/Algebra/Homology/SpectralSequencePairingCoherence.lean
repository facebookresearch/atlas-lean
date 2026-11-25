/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.SpectralSequencePairing
public import MathlibExt.CategoryTheory.Monoidal.PairingDescentCoherence
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Coherence through actual native page homology

The original cycle inclusions and homology quotient projections carry the
actual native page products to their actual cycle and homology products.
Coherence passes through these maps and the original successor isomorphism.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory.Abelian.SpectralObject.IntervalPairing

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]
  {X : SpectralObject C EInt} (P : IntervalPairing X X X)

/-- The original cycle product at an explicitly equal output bidegree. -/
def pageCyclesPairTo (r : ℤ) (hr : 1 ≤ r) (a b t : ℤ × ℤ) (ht : a + b = t) :
    ((X.skeletalSpectralSequence).page r).cycles a ⊗ ((X.skeletalSpectralSequence).page r).cycles b ⟶
      ((X.skeletalSpectralSequence).page r).cycles t := by
  subst t
  exact P.pageCyclesPair r hr a b

/-- The original homology product at an explicitly equal output bidegree. -/
def pageHomologyPairTo (r : ℤ) (hr : 1 ≤ r) (a b t : ℤ × ℤ) (ht : a + b = t) :
    ((X.skeletalSpectralSequence).page r).homology a ⊗ ((X.skeletalSpectralSequence).page r).homology b ⟶
      ((X.skeletalSpectralSequence).page r).homology t := by
  subst t
  exact P.pageHomologyPair r hr a b

/-- The original native cycle inclusion computes the equal-position cycle product. -/
lemma pageCyclesPairTo_i (r : ℤ) (hr : 1 ≤ r) (a b t : ℤ × ℤ) (ht : a + b = t) :
    P.pageCyclesPairTo r hr a b t ht ≫ ((X.skeletalSpectralSequence).page r).iCycles t =
      (((X.skeletalSpectralSequence).page r).iCycles a ⊗ₘ
        ((X.skeletalSpectralSequence).page r).iCycles b) ≫ P.pagePairTo r hr a b t ht := by
  subst t
  exact P.pageCyclesPair_i r hr a b

/-- The original native homology projection computes the equal-position homology product. -/
lemma pageHomologyPairTo_π (r : ℤ) (hr : 1 ≤ r) (a b t : ℤ × ℤ) (ht : a + b = t) :
    (((X.skeletalSpectralSequence).page r).homologyπ a ⊗ₘ
      ((X.skeletalSpectralSequence).page r).homologyπ b) ≫ P.pageHomologyPairTo r hr a b t ht =
      P.pageCyclesPairTo r hr a b t ht ≫ ((X.skeletalSpectralSequence).page r).homologyπ t := by
  subst t
  exact P.pageHomologyPair_π r hr a b

/-- The original successor isomorphism preserves the equal-position actual homology product. -/
lemma pageHomologyPairTo_successor (r : ℤ) (hr : 1 ≤ r) (a b t : ℤ × ℤ) (ht : a + b = t) :
    P.pageHomologyPairTo r hr a b t ht ≫ (X.skeletalSpectralSequence.iso r (r + 1) t rfl hr).hom =
      ((X.skeletalSpectralSequence.iso r (r + 1) a rfl hr).hom ⊗ₘ
        (X.skeletalSpectralSequence.iso r (r + 1) b rfl hr).hom) ≫
        P.pagePairTo (r + 1) (by omega) a b t ht := by
  subst t
  exact P.pagePair_successor r hr a b

/-- Associativity is an equality of the original native page cups at all bidegrees. -/
def pageAssociativity (r : ℤ) (hr : 1 ≤ r) : Prop :=
  ∀ a b c : ℤ × ℤ,
    (P.pagePair r hr a b ⊗ₘ 𝟙 (((X.skeletalSpectralSequence).page r).X c)) ≫
        P.pagePairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c) =
      (α_ (((X.skeletalSpectralSequence).page r).X a) (((X.skeletalSpectralSequence).page r).X b)
        (((X.skeletalSpectralSequence).page r).X c)).hom ≫
        (𝟙 _ ⊗ₘ P.pagePair r hr b c) ≫ P.pagePair r hr a (b + c)

/-- Actual cycle kernel inclusions retain the associativity of the original native page product. -/
lemma pageCyclesPair_associativity (r : ℤ) (hr : 1 ≤ r) (hP : P.pageAssociativity r hr) (a b c : ℤ × ℤ) :
    (P.pageCyclesPair r hr a b ⊗ₘ 𝟙 (((X.skeletalSpectralSequence).page r).cycles c)) ≫
        P.pageCyclesPairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c) =
      (α_ (((X.skeletalSpectralSequence).page r).cycles a) (((X.skeletalSpectralSequence).page r).cycles b)
        (((X.skeletalSpectralSequence).page r).cycles c)).hom ≫
        (𝟙 _ ⊗ₘ P.pageCyclesPair r hr b c) ≫ P.pageCyclesPair r hr a (b + c) := by
  let K := (X.skeletalSpectralSequence).page r
  have hc : 𝟙 _ ≫ K.iCycles (a + (b + c)) = K.iCycles (a + (b + c)) ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_associativity_of_mono_projection
    (K.iCycles a) (K.iCycles b) (K.iCycles c) (K.iCycles (a + b)) (K.iCycles (b + c))
    (K.iCycles (a + (b + c))) (K.iCycles (a + (b + c)))
    (P.pageCyclesPair r hr a b) (P.pageCyclesPairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pageCyclesPair r hr b c) (P.pageCyclesPair r hr a (b + c))
    (P.pagePair r hr a b) (P.pagePairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pagePair r hr b c) (P.pagePair r hr a (b + c)) (𝟙 _) (𝟙 _)
    (P.pageCyclesPair_i r hr a b) (P.pageCyclesPairTo_i r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pageCyclesPair_i r hr b c) (P.pageCyclesPair_i r hr a (b + c)) hc (by simpa using hP a b c)

/-- Actual homology quotient projections descend associativity of the original native page products. -/
lemma pageHomologyPair_associativity (r : ℤ) (hr : 1 ≤ r) (hP : P.pageAssociativity r hr) (a b c : ℤ × ℤ) :
    (P.pageHomologyPair r hr a b ⊗ₘ 𝟙 (((X.skeletalSpectralSequence).page r).homology c)) ≫
        P.pageHomologyPairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c) =
      (α_ (((X.skeletalSpectralSequence).page r).homology a) (((X.skeletalSpectralSequence).page r).homology b)
        (((X.skeletalSpectralSequence).page r).homology c)).hom ≫
        (𝟙 _ ⊗ₘ P.pageHomologyPair r hr b c) ≫ P.pageHomologyPair r hr a (b + c) := by
  let K := (X.skeletalSpectralSequence).page r
  letI : Epi (K.homologyπ a ⊗ₘ K.homologyπ b) := epi_tensorHom_of_preservesCokernels _ _
  letI : Epi ((K.homologyπ a ⊗ₘ K.homologyπ b) ⊗ₘ K.homologyπ c) := epi_tensorHom_of_preservesCokernels _ _
  have hc : 𝟙 _ ≫ K.homologyπ (a + (b + c)) = K.homologyπ (a + (b + c)) ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_associativity_of_epi_projection
    (K.homologyπ a) (K.homologyπ b) (K.homologyπ c) (K.homologyπ (a + b)) (K.homologyπ (b + c))
    (K.homologyπ (a + (b + c))) (K.homologyπ (a + (b + c)))
    (P.pageCyclesPair r hr a b) (P.pageCyclesPairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pageCyclesPair r hr b c) (P.pageCyclesPair r hr a (b + c))
    (P.pageHomologyPair r hr a b) (P.pageHomologyPairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pageHomologyPair r hr b c) (P.pageHomologyPair r hr a (b + c)) (𝟙 _) (𝟙 _)
    (P.pageHomologyPair_π r hr a b).symm
    (P.pageHomologyPairTo_π r hr (a + b) c (a + (b + c)) (add_assoc a b c)).symm
    (P.pageHomologyPair_π r hr b c).symm (P.pageHomologyPair_π r hr a (b + c)).symm hc
    (by simpa using P.pageCyclesPair_associativity r hr hP a b c)

omit [Abelian C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
private lemma inverse_pairing_square {A B D A' B' D' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D') (p : A ⊗ B ⟶ D) (p' : A' ⊗ B' ⟶ D')
    (hp : p ≫ eD.hom = (eA.hom ⊗ₘ eB.hom) ≫ p') :
    p' ≫ eD.inv = (eA.inv ⊗ₘ eB.inv) ≫ p := by
  apply (cancel_mono eD.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hp, tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- The inverse original successor comparison computes the actual homology product at equal positions. -/
lemma pagePairTo_successor_inv (r : ℤ) (hr : 1 ≤ r) (a b t : ℤ × ℤ) (ht : a + b = t) :
    P.pagePairTo (r + 1) (by omega) a b t ht ≫ (X.skeletalSpectralSequence.iso r (r + 1) t rfl hr).inv =
      ((X.skeletalSpectralSequence.iso r (r + 1) a rfl hr).inv ⊗ₘ
        (X.skeletalSpectralSequence.iso r (r + 1) b rfl hr).inv) ≫ P.pageHomologyPairTo r hr a b t ht :=
  inverse_pairing_square _ _ _ _ _ (P.pageHomologyPairTo_successor r hr a b t ht)

/-- The successor homology comparison preserves associativity. -/
theorem pageAssociativity_successor (r : ℤ) (hr : 1 ≤ r) (hP : P.pageAssociativity r hr) :
    P.pageAssociativity (r + 1) (by omega) := by
  intro a b c
  let S := X.skeletalSpectralSequence
  let eA := S.iso r (r + 1) a rfl hr
  let eB := S.iso r (r + 1) b rfl hr
  let eD := S.iso r (r + 1) c rfl hr
  let eX := S.iso r (r + 1) (a + b) rfl hr
  let eY := S.iso r (r + 1) (b + c) rfl hr
  let eQ := S.iso r (r + 1) (a + (b + c)) rfl hr
  have hc : 𝟙 _ ≫ eQ.inv = eQ.inv ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_associativity_of_mono_projection
    eA.inv eB.inv eD.inv eX.inv eY.inv eQ.inv eQ.inv
    (P.pagePair (r + 1) (by omega) a b)
    (P.pagePairTo (r + 1) (by omega) (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pagePair (r + 1) (by omega) b c) (P.pagePair (r + 1) (by omega) a (b + c))
    (P.pageHomologyPair r hr a b) (P.pageHomologyPairTo r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pageHomologyPair r hr b c) (P.pageHomologyPair r hr a (b + c)) (𝟙 _) (𝟙 _)
    (P.pagePairTo_successor_inv r hr a b (a + b) rfl)
    (P.pagePairTo_successor_inv r hr (a + b) c (a + (b + c)) (add_assoc a b c))
    (P.pagePairTo_successor_inv r hr b c (b + c) rfl)
    (P.pagePairTo_successor_inv r hr a (b + c) (a + (b + c)) rfl) hc
    (by simpa using P.pageHomologyPair_associativity r hr hP a b c)

/-- Associativity at an initial page is preserved at every later integer page. -/
theorem pageAssociativity_later (R : ℤ) (hR : 1 ≤ R) (hP : P.pageAssociativity R hR)
    (r : ℤ) (hRr : R ≤ r) : P.pageAssociativity r (by omega) := by
  let Q : ℤ → Prop := fun r => ∀ hr : 1 ≤ r, P.pageAssociativity r hr
  have h : ∀ n : ℕ, Q (R + (n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, add_zero] using (show Q R from fun _ => hP)
    | succ n ih =>
      have hs : Q ((R + (n : ℤ)) + 1) := by
        intro hr
        exact P.pageAssociativity_successor (R + (n : ℤ)) (by omega) (ih (by omega))
      exact (congrArg Q (by omega : (R + (n : ℤ)) + 1 = R + ((n + 1 : ℕ) : ℤ))).mp hs
  have he : R + ((r - R).toNat : ℤ) = r := by omega
  exact ((congrArg Q he).mp (h (r - R).toNat)) (by omega)

section SignedSymmetry

variable [BraidedCategory C]

/-- The signed swap concerns the actual native cup and its original total cohomological degrees. -/
def pageSignedSymmetry (r : ℤ) (hr : 1 ≤ r) : Prop :=
  ∀ a b : ℤ × ℤ,
    (β_ (((X.skeletalSpectralSequence).page r).X a) (((X.skeletalSpectralSequence).page r).X b)).hom ≫
      P.pagePair r hr b a = (((a.1 + a.2) * (b.1 + b.2)).negOnePow : ℤ) •
        P.pagePairTo r hr a b (b + a) (add_comm a b)

/-- Actual native cycle inclusion retains the original signed swap law. -/
lemma pageCyclesPair_signedSwap (r : ℤ) (hr : 1 ≤ r) (hP : P.pageSignedSymmetry r hr) (a b : ℤ × ℤ) :
    (β_ (((X.skeletalSpectralSequence).page r).cycles a) (((X.skeletalSpectralSequence).page r).cycles b)).hom ≫
      P.pageCyclesPair r hr b a = (((a.1 + a.2) * (b.1 + b.2)).negOnePow : ℤ) •
        P.pageCyclesPairTo r hr a b (b + a) (add_comm a b) := by
  let K := (X.skeletalSpectralSequence).page r
  have hc : 𝟙 _ ≫ K.iCycles (b + a) = K.iCycles (b + a) ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_signedSwap_of_mono_projection
    (K.iCycles a) (K.iCycles b) (K.iCycles (b + a)) (K.iCycles (b + a))
    (P.pageCyclesPairTo r hr a b (b + a) (add_comm a b)) (P.pageCyclesPair r hr b a)
    (P.pagePairTo r hr a b (b + a) (add_comm a b)) (P.pagePair r hr b a) (𝟙 _) (𝟙 _)
    (((a.1 + a.2) * (b.1 + b.2)).negOnePow : ℤ)
    (P.pageCyclesPairTo_i r hr a b (b + a) (add_comm a b)) (P.pageCyclesPair_i r hr b a) hc
    (by simpa using hP a b)

/-- The actual native homology projections descend the original total-degree signed swap. -/
lemma pageHomologyPair_signedSwap (r : ℤ) (hr : 1 ≤ r) (hP : P.pageSignedSymmetry r hr) (a b : ℤ × ℤ) :
    (β_ (((X.skeletalSpectralSequence).page r).homology a) (((X.skeletalSpectralSequence).page r).homology b)).hom ≫
      P.pageHomologyPair r hr b a = (((a.1 + a.2) * (b.1 + b.2)).negOnePow : ℤ) •
        P.pageHomologyPairTo r hr a b (b + a) (add_comm a b) := by
  let K := (X.skeletalSpectralSequence).page r
  letI : Epi (K.homologyπ a ⊗ₘ K.homologyπ b) := epi_tensorHom_of_preservesCokernels _ _
  have hc : 𝟙 _ ≫ K.homologyπ (b + a) = K.homologyπ (b + a) ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_signedSwap_of_epi_projection
    (K.homologyπ a) (K.homologyπ b) (K.homologyπ (b + a)) (K.homologyπ (b + a))
    (P.pageCyclesPairTo r hr a b (b + a) (add_comm a b)) (P.pageCyclesPair r hr b a)
    (P.pageHomologyPairTo r hr a b (b + a) (add_comm a b)) (P.pageHomologyPair r hr b a) (𝟙 _) (𝟙 _)
    (((a.1 + a.2) * (b.1 + b.2)).negOnePow : ℤ)
    (P.pageHomologyPairTo_π r hr a b (b + a) (add_comm a b)).symm
    (P.pageHomologyPair_π r hr b a).symm hc (by simpa using P.pageCyclesPair_signedSwap r hr hP a b)

/-- The successor homology comparison preserves the signed swap law. -/
theorem pageSignedSymmetry_successor (r : ℤ) (hr : 1 ≤ r) (hP : P.pageSignedSymmetry r hr) :
    P.pageSignedSymmetry (r + 1) (by omega) := by
  intro a b
  let S := X.skeletalSpectralSequence
  let eA := S.iso r (r + 1) a rfl hr
  let eB := S.iso r (r + 1) b rfl hr
  let eQ := S.iso r (r + 1) (b + a) rfl hr
  have hc : 𝟙 _ ≫ eQ.inv = eQ.inv ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_signedSwap_of_mono_projection
    eA.inv eB.inv eQ.inv eQ.inv
    (P.pagePairTo (r + 1) (by omega) a b (b + a) (add_comm a b)) (P.pagePair (r + 1) (by omega) b a)
    (P.pageHomologyPairTo r hr a b (b + a) (add_comm a b)) (P.pageHomologyPair r hr b a) (𝟙 _) (𝟙 _)
    (((a.1 + a.2) * (b.1 + b.2)).negOnePow : ℤ)
    (P.pagePairTo_successor_inv r hr a b (b + a) (add_comm a b))
    (P.pagePairTo_successor_inv r hr b a (b + a) rfl) hc
    (by simpa using P.pageHomologyPair_signedSwap r hr hP a b)

/-- The signed swap law is preserved from its initial page to every later integer page. -/
theorem pageSignedSymmetry_later (R : ℤ) (hR : 1 ≤ R) (hP : P.pageSignedSymmetry R hR)
    (r : ℤ) (hRr : R ≤ r) : P.pageSignedSymmetry r (by omega) := by
  let Q : ℤ → Prop := fun r => ∀ hr : 1 ≤ r, P.pageSignedSymmetry r hr
  have h : ∀ n : ℕ, Q (R + (n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, add_zero] using (show Q R from fun _ => hP)
    | succ n ih =>
      have hs : Q ((R + (n : ℤ)) + 1) := by
        intro hr
        exact P.pageSignedSymmetry_successor (R + (n : ℤ)) (by omega) (ih (by omega))
      exact (congrArg Q (by omega : (R + (n : ℤ)) + 1 = R + ((n + 1 : ℕ) : ℤ))).mp hs
  have he : R + ((r - R).toNat : ℤ) = r := by omega
  exact ((congrArg Q he).mp (h (r - R).toNat)) (by omega)

end SignedSymmetry

section Units

/-- The original native left unit law at all page bidegrees. -/
def pageLeftUnit (r : ℤ) (hr : 1 ≤ r) (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0) : Prop :=
  ∀ a : ℤ × ℤ, (u ⊗ₘ 𝟙 _) ≫ P.pagePairTo r hr 0 a a (zero_add a) = (λ_ _).hom

/-- The original native right unit law at all page bidegrees. -/
def pageRightUnit (r : ℤ) (hr : 1 ≤ r) (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0) : Prop :=
  ∀ a : ℤ × ℤ, (𝟙 _ ⊗ₘ u) ≫ P.pagePairTo r hr a 0 a (add_zero a) = (ρ_ _).hom

omit [Abelian C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
private lemma left_unit_apply {A B D : C} (u : 𝟙_ C ⟶ A) (v : D ⟶ B) (p : A ⊗ B ⟶ B)
    (hp : (u ⊗ₘ 𝟙 B) ≫ p = (λ_ B).hom) : (u ⊗ₘ v) ≫ p = (λ_ D).hom ≫ v := by
  have ht : (u ⊗ₘ v) = (𝟙 (𝟙_ C) ⊗ₘ v) ≫ (u ⊗ₘ 𝟙 B) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [ht, Category.assoc, hp]
  simpa only [MonoidalCategory.id_tensorHom] using leftUnitor_naturality v

omit [Abelian C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
private lemma right_unit_apply {A B D : C} (u : 𝟙_ C ⟶ A) (v : D ⟶ B) (p : B ⊗ A ⟶ B)
    (hp : (𝟙 B ⊗ₘ u) ≫ p = (ρ_ B).hom) : (v ⊗ₘ u) ≫ p = (ρ_ D).hom ≫ v := by
  have ht : (v ⊗ₘ u) = (v ⊗ₘ 𝟙 (𝟙_ C)) ≫ (𝟙 B ⊗ₘ u) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [ht, Category.assoc, hp]
  simpa only [MonoidalCategory.tensorHom_id] using rightUnitor_naturality v

omit [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)] in
private lemma unit_leibniz_zero {A B : C} (u : 𝟙_ C ⟶ A) (d : A ⟶ B)
    (p : A ⊗ A ⟶ A) (left : A ⊗ B ⟶ B) (right : B ⊗ A ⟶ B)
    (hp : (u ⊗ₘ 𝟙 A) ≫ p = (λ_ A).hom)
    (hl : (u ⊗ₘ 𝟙 B) ≫ left = (λ_ B).hom) (hr : (𝟙 B ⊗ₘ u) ≫ right = (ρ_ B).hom)
    (hd : p ≫ d = (d ⊗ₘ 𝟙 A) ≫ right + (𝟙 A ⊗ₘ d) ≫ left) : u ≫ d = 0 := by
  have h0 := left_unit_apply u u p hp
  have hL := left_unit_apply u (u ≫ d) left hl
  have hR := right_unit_apply u (u ≫ d) right hr
  have htL : (u ⊗ₘ u) ≫ (𝟙 A ⊗ₘ d) = u ⊗ₘ (u ≫ d) := by simp only [tensorHom_comp_tensorHom, Category.comp_id]
  have htR : (u ⊗ₘ u) ≫ (d ⊗ₘ 𝟙 A) = (u ≫ d) ⊗ₘ u := by simp only [tensorHom_comp_tensorHom, Category.comp_id]
  have h := congrArg (fun f => (u ⊗ₘ u) ≫ f) hd
  simp only [Preadditive.comp_add] at h
  rw [← Category.assoc (u ⊗ₘ u) p d, h0,
    ← Category.assoc (u ⊗ₘ u) (d ⊗ₘ 𝟙 A) right, htR, hR,
    ← Category.assoc (u ⊗ₘ u) (𝟙 A ⊗ₘ d) left, htL, hL, ← unitors_equal] at h
  simp only [Category.assoc] at h
  have hz : (λ_ (𝟙_ C)).hom ≫ u ≫ d = 0 :=
    add_left_cancel (h.symm.trans (add_zero ((λ_ (𝟙_ C)).hom ≫ u ≫ d)).symm)
  apply (cancel_epi (λ_ (𝟙_ C)).hom).mp
  simpa only [Category.assoc, comp_zero] using hz

/-- The original native Leibniz rule and both actual unit laws force the unit differential to vanish. -/
lemma pageUnit_d_zero (r : ℤ) (hr : 1 ≤ r) (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    u ≫ ((X.skeletalSpectralSequence).page r).d 0 (r, 1 - r) = 0 := by
  let K := (X.skeletalSpectralSequence).page r
  let j : ℤ × ℤ := (0 : ℤ × ℤ) + (r, 1 - r)
  have hd : P.pagePair r hr 0 0 ≫ K.d 0 j =
      (K.d 0 j ⊗ₘ 𝟙 (K.X 0)) ≫ P.pagePairTo r hr j 0 j (add_zero j) +
      (𝟙 (K.X 0) ⊗ₘ K.d 0 j) ≫ P.pagePairTo r hr 0 j j (zero_add j) := by
    have h := P.pagePair_leibniz r hr 0 0
    change P.pagePair r hr 0 0 ≫ K.d 0 j =
      (K.d 0 j ⊗ₘ 𝟙 (K.X 0)) ≫ P.pagePairTo r hr j 0 j (add_zero j) +
      (1 : ℤ) • ((𝟙 (K.X 0) ⊗ₘ K.d 0 j) ≫ P.pagePairTo r hr 0 j j (zero_add j)) at h
    simpa only [one_smul] using h
  have hz : u ≫ K.d 0 j = 0 := unit_leibniz_zero u (K.d 0 j) (P.pagePair r hr 0 0)
    (P.pagePairTo r hr 0 j j (zero_add j)) (P.pagePairTo r hr j 0 j (add_zero j))
    (by simpa only [pagePairTo] using hl 0) (hl j) (hu j) hd
  exact (congrArg (fun q : ℤ × ℤ => u ≫ K.d 0 q = 0) (zero_add (r, 1 - r))).mp hz

/-- Both original unit laws and Leibniz construct the actual native cycle unit. -/
def pageCycleUnit (r : ℤ) (hr : 1 ≤ r) (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).cycles 0 :=
  ((X.skeletalSpectralSequence).page r).liftCycles' u (r, 1 - r)
    (ComplexShape.up'_mk (r, 1 - r) 0 (r, 1 - r) (zero_add _)) (P.pageUnit_d_zero r hr u hl hu)

/-- The original native cycle inclusion retains the actual coefficient unit. -/
lemma pageCycleUnit_i (r : ℤ) (hr : 1 ≤ r) (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    P.pageCycleUnit r hr u hl hu ≫ ((X.skeletalSpectralSequence).page r).iCycles 0 = u := by
  dsimp only [pageCycleUnit, HomologicalComplex.liftCycles']
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The original coefficient unit descends through the actual homology quotient. -/
def pageHomologyUnit (r : ℤ) (hr : 1 ≤ r) (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).homology 0 :=
  P.pageCycleUnit r hr u hl hu ≫ ((X.skeletalSpectralSequence).page r).homologyπ 0

/-- The actual native cycle product retains the original left unit law. -/
lemma pageCycleUnit_left_unital (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) (a : ℤ × ℤ) :
    (P.pageCycleUnit r hr u hl hu ⊗ₘ 𝟙 _) ≫ P.pageCyclesPairTo r hr 0 a a (zero_add a) = (λ_ _).hom := by
  let K := (X.skeletalSpectralSequence).page r
  have hc : 𝟙 _ ≫ K.iCycles a = K.iCycles a ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_leftUnit_of_mono_projection
    (K.iCycles 0) (K.iCycles a) (K.iCycles a) (P.pageCycleUnit r hr u hl hu) u
    (P.pageCyclesPairTo r hr 0 a a (zero_add a)) (P.pagePairTo r hr 0 a a (zero_add a)) (𝟙 _) (𝟙 _)
    (P.pageCycleUnit_i r hr u hl hu) (P.pageCyclesPairTo_i r hr 0 a a (zero_add a)) hc
    (by simpa using hl a)

/-- The actual native cycle product retains the original right unit law. -/
lemma pageCycleUnit_right_unital (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) (a : ℤ × ℤ) :
    (𝟙 _ ⊗ₘ P.pageCycleUnit r hr u hl hu) ≫ P.pageCyclesPairTo r hr a 0 a (add_zero a) = (ρ_ _).hom := by
  let K := (X.skeletalSpectralSequence).page r
  have hc : 𝟙 _ ≫ K.iCycles a = K.iCycles a ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_rightUnit_of_mono_projection
    (K.iCycles 0) (K.iCycles a) (K.iCycles a) (P.pageCycleUnit r hr u hl hu) u
    (P.pageCyclesPairTo r hr a 0 a (add_zero a)) (P.pagePairTo r hr a 0 a (add_zero a)) (𝟙 _) (𝟙 _)
    (P.pageCycleUnit_i r hr u hl hu) (P.pageCyclesPairTo_i r hr a 0 a (add_zero a)) hc
    (by simpa using hu a)

/-- The actual homology quotient product retains the original left unit law. -/
lemma pageHomologyUnit_left_unital (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) (a : ℤ × ℤ) :
    (P.pageHomologyUnit r hr u hl hu ⊗ₘ 𝟙 _) ≫ P.pageHomologyPairTo r hr 0 a a (zero_add a) = (λ_ _).hom := by
  let K := (X.skeletalSpectralSequence).page r
  letI : Epi (𝟙 (𝟙_ C) ⊗ₘ K.homologyπ a) := epi_tensorHom_of_preservesCokernels _ _
  have hc : 𝟙 _ ≫ K.homologyπ a = K.homologyπ a ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_leftUnit_of_epi_projection
    (K.homologyπ 0) (K.homologyπ a) (K.homologyπ a)
    (P.pageCycleUnit r hr u hl hu) (P.pageHomologyUnit r hr u hl hu)
    (P.pageCyclesPairTo r hr 0 a a (zero_add a)) (P.pageHomologyPairTo r hr 0 a a (zero_add a)) (𝟙 _) (𝟙 _)
    rfl (P.pageHomologyPairTo_π r hr 0 a a (zero_add a)).symm hc
    (by simpa using P.pageCycleUnit_left_unital r hr u hl hu a)

/-- The actual homology quotient product retains the original right unit law. -/
lemma pageHomologyUnit_right_unital (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) (a : ℤ × ℤ) :
    (𝟙 _ ⊗ₘ P.pageHomologyUnit r hr u hl hu) ≫ P.pageHomologyPairTo r hr a 0 a (add_zero a) = (ρ_ _).hom := by
  let K := (X.skeletalSpectralSequence).page r
  letI : Epi (K.homologyπ a ⊗ₘ 𝟙 (𝟙_ C)) := epi_tensorHom_of_preservesCokernels _ _
  have hc : 𝟙 _ ≫ K.homologyπ a = K.homologyπ a ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_rightUnit_of_epi_projection
    (K.homologyπ 0) (K.homologyπ a) (K.homologyπ a)
    (P.pageCycleUnit r hr u hl hu) (P.pageHomologyUnit r hr u hl hu)
    (P.pageCyclesPairTo r hr a 0 a (add_zero a)) (P.pageHomologyPairTo r hr a 0 a (add_zero a)) (𝟙 _) (𝟙 _)
    rfl (P.pageHomologyPairTo_π r hr a 0 a (add_zero a)).symm hc
    (by simpa using P.pageCycleUnit_right_unital r hr u hl hu a)

/-- The original successor isomorphism carries the genuine homology unit to the next native page. -/
def pageSuccessorUnit (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    𝟙_ C ⟶ ((X.skeletalSpectralSequence).page (r + 1)).X 0 :=
  P.pageHomologyUnit r hr u hl hu ≫ (X.skeletalSpectralSequence.iso r (r + 1) 0 rfl hr).hom

/-- The actual successor comparison retains the original homology unit. -/
lemma pageSuccessorUnit_inv (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    P.pageSuccessorUnit r hr u hl hu ≫ (X.skeletalSpectralSequence.iso r (r + 1) 0 rfl hr).inv =
      P.pageHomologyUnit r hr u hl hu := by
  dsimp only [pageSuccessorUnit]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original successor comparison preserves the actual left unit law on every bidegree. -/
theorem pageSuccessorUnit_left_unital (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    P.pageLeftUnit (r + 1) (by omega) (P.pageSuccessorUnit r hr u hl hu) := by
  intro a
  let S := X.skeletalSpectralSequence
  let eA := S.iso r (r + 1) 0 rfl hr
  let eB := S.iso r (r + 1) a rfl hr
  have hc : 𝟙 _ ≫ eB.inv = eB.inv ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_leftUnit_of_mono_projection
    eA.inv eB.inv eB.inv (P.pageSuccessorUnit r hr u hl hu) (P.pageHomologyUnit r hr u hl hu)
    (P.pagePairTo (r + 1) (by omega) 0 a a (zero_add a)) (P.pageHomologyPairTo r hr 0 a a (zero_add a))
    (𝟙 _) (𝟙 _) (P.pageSuccessorUnit_inv r hr u hl hu)
    (P.pagePairTo_successor_inv r hr 0 a a (zero_add a)) hc
    (by simpa using P.pageHomologyUnit_left_unital r hr u hl hu a)

/-- The original successor comparison preserves the actual right unit law on every bidegree. -/
theorem pageSuccessorUnit_right_unital (r : ℤ) (hr : 1 ≤ r)
    (u : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0)
    (hl : P.pageLeftUnit r hr u) (hu : P.pageRightUnit r hr u) :
    P.pageRightUnit (r + 1) (by omega) (P.pageSuccessorUnit r hr u hl hu) := by
  intro a
  let S := X.skeletalSpectralSequence
  let eA := S.iso r (r + 1) 0 rfl hr
  let eB := S.iso r (r + 1) a rfl hr
  have hc : 𝟙 _ ≫ eB.inv = eB.inv ≫ 𝟙 _ := by simp
  simpa only [Category.comp_id] using pairing_rightUnit_of_mono_projection
    eA.inv eB.inv eB.inv (P.pageSuccessorUnit r hr u hl hu) (P.pageHomologyUnit r hr u hl hu)
    (P.pagePairTo (r + 1) (by omega) a 0 a (add_zero a)) (P.pageHomologyPairTo r hr a 0 a (add_zero a))
    (𝟙 _) (𝟙 _) (P.pageSuccessorUnit_inv r hr u hl hu)
    (P.pagePairTo_successor_inv r hr a 0 a (add_zero a)) hc
    (by simpa using P.pageHomologyUnit_right_unital r hr u hl hu a)

/-- An actual native page coefficient unit with its original two unit laws. -/
structure PageUnitData (r : ℤ) (hr : 1 ≤ r) where
  /-- The original native page unit at the zero bidegree. -/
  unit : 𝟙_ C ⟶ ((X.skeletalSpectralSequence).page r).X 0
  left : P.pageLeftUnit r hr unit
  right : P.pageRightUnit r hr unit

/-- The original homology quotient and successor comparison construct the actual next-page unit data. -/
def PageUnitData.successor (r : ℤ) (hr : 1 ≤ r) (D : P.PageUnitData r hr) :
    P.PageUnitData (r + 1) (by omega) where
  unit := P.pageSuccessorUnit r hr D.unit D.left D.right
  left := P.pageSuccessorUnit_left_unital r hr D.unit D.left D.right
  right := P.pageSuccessorUnit_right_unital r hr D.unit D.left D.right

/-- Equal integer notation transports only the page index of the same original unit data. -/
def PageUnitData.transport (r r' : ℤ) (hr : 1 ≤ r) (hr' : 1 ≤ r') (h : r = r')
    (D : P.PageUnitData r hr) : P.PageUnitData r' hr' := by
  cases h
  exact D

/-- Iterating the actual native successor constructs its coefficient unit after any number of pages. -/
def PageUnitData.addNat (R : ℤ) (hR : 1 ≤ R) (D : P.PageUnitData R hR) (n : ℕ) :
    P.PageUnitData (R + (n : ℤ)) (by omega) := by
  induction n with
  | zero => exact PageUnitData.transport P R (R + (0 : ℤ)) hR (by omega) (add_zero R).symm D
  | succ n ih =>
    exact PageUnitData.transport P ((R + (n : ℤ)) + 1) (R + ((n + 1 : ℕ) : ℤ))
      (by omega) (by omega) (by omega)
      (PageUnitData.successor P (R + (n : ℤ)) (by omega) ih)

/-- The unit identities are preserved from an initial page to every later integer page. -/
def PageUnitData.later (R : ℤ) (hR : 1 ≤ R) (D : P.PageUnitData R hR) (r : ℤ) (hRr : R ≤ r) :
    P.PageUnitData r (by omega) :=
  PageUnitData.transport P (R + ((r - R).toNat : ℤ)) r (by omega) (by omega) (by omega)
    (PageUnitData.addNat P R hR D (r - R).toNat)

end Units

end CategoryTheory.Abelian.SpectralObject.IntervalPairing
