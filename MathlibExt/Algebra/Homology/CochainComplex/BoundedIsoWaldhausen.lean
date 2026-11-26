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

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientWaldhausen
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Bounded complexes with isomorphism weak equivalences

Let E be a preadditive exact category with a zero object and binary biproducts.
On bounded integer-indexed cochain complexes, take degreewise admissible
monomorphisms as cofibrations and isomorphisms as weak equivalences.
A cofiber sequence X → Y → Z is an admissible map X → Y together with
a pushout description of Z along X → 0. Isomorphisms between the three
vertices of two admissible spans induce an isomorphism of their pushout apices.

For any additive functor F:E → A to an abelian category, the identity functor
on bounded complexes is Waldhausen exact from this structure to the one
whose weak equivalences are quasi-isomorphisms after applying F.
The object and morphism universes of E and A are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- In a preadditive exact category E with a zero object and binary
biproducts, the cofibration and weak-equivalence structure on bounded
integer-indexed cochain complexes with degreewise admissible monomorphisms
as cofibrations and isomorphisms as weak equivalences. Pushouts along
cofibrations exist, and their cobase-change legs are cofibrations. -/
@[instance_reducible, no_expose]
def isoWaldhausenCategory : WaldhausenCategoryWithoutGluing (Bounded E) where
  cofibrations := degreewiseAdmissibleMonomorphisms E
  weakEquivalences := MorphismProperty.isomorphisms (Bounded E)
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration := degreewiseAdmissibleMonomorphisms_zero
  cofibration_pushout i hi C f := by
    let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
    obtain ⟨P, inB, inC, hP, _, _, hadm, _⟩ := exists_boundedAdmissiblePushout E i f hi
    exact ⟨P, inC, inB, hP.flip, hadm⟩

/-- For bounded cochain complexes X and Y in a preadditive exact category E
with a zero object and binary biproducts, a map f:X → Y is a cofibration
in the isomorphism model if and only if every component fⱼ is an admissible
monomorphism in E. -/
theorem iso_isCofibration_iff {X Y : Bounded E} (f : X ⟶ Y) :
    letI := isoWaldhausenCategory E
    IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.f j) := Iff.rfl

/-- In the Waldhausen structure on bounded cochain complexes over a
preadditive exact category E with a zero object and binary biproducts,
whose weak equivalences are isomorphisms, a map f:X → Y is a weak
equivalence if and only if it is an isomorphism in the bounded category. -/
theorem iso_isWeakEquivalence_iff {X Y : Bounded E} (f : X ⟶ Y) :
    letI := isoWaldhausenCategory E
    IsWeakEquivalence f ↔ IsIso f := Iff.rfl

/-- Let E be a preadditive exact category with a zero object and binary
biproducts. Maps i:X → Y and p:Y → Z of bounded cochain complexes form a
cofiber sequence in the isomorphism Waldhausen model exactly when i is
degreewise admissible and there are maps X → 0 and 0 → Z making the
square with i and p a pushout. Thus Z is the cofiber of i in the bounded
category. -/
theorem iso_isCofiberSequence_iff {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z) :
    (letI := isoWaldhausenCategory E; IsCofiberSequence i p) ↔
      degreewiseAdmissibleMonomorphisms E i ∧
        ∃ (h : X ⟶ (0 : Bounded E)) (q : (0 : Bounded E) ⟶ Z), IsPushout h i q p := Iff.rfl

/-- For bounded cochain complexes in a preadditive exact category E with a
zero object and binary biproducts, a commuting map between two admissible
pushout squares that is an isomorphism on each of the three span vertices
is an isomorphism on the pushout apices. This gives the gluing axiom for
isomorphism weak equivalences. -/
theorem isoWaldhausen_gluing :
    letI := isoWaldhausenCategory E
    WaldhausenGluingAxiom (C := Bounded E) := by
  let _ := isoWaldhausenCategory E
  constructor
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p _ _ wi wf wY wZ hx hy hz
  let _ : IsIso x := hx
  let _ : IsIso y := hy
  let _ : IsIso z := hz
  have wiInv : i' ≫ inv y = inv x ≫ i := by
    apply (cancel_epi x).mp
    calc
      x ≫ (i' ≫ inv y) = (i ≫ y) ≫ inv y := by rw [← Category.assoc, ← wi]
      _ = i := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = x ≫ (inv x ≫ i) := by simp only [IsIso.hom_inv_id_assoc]
  have wfInv : f' ≫ inv z = inv x ≫ f := by
    apply (cancel_epi x).mp
    calc
      x ≫ (f' ≫ inv z) = (f ≫ z) ≫ inv z := by rw [← Category.assoc, ← wf]
      _ = f := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      _ = x ≫ (inv x ≫ f) := by simp only [IsIso.hom_inv_id_assoc]
  have w : i' ≫ (inv y ≫ inY) = f' ≫ (inv z ≫ inZ) := by
    calc
      i' ≫ (inv y ≫ inY) = (inv x ≫ i) ≫ inY := by rw [← Category.assoc, wiInv]
      _ = inv x ≫ (f ≫ inZ) := by rw [Category.assoc, hP.w]
      _ = f' ≫ (inv z ≫ inZ) := by rw [← Category.assoc, ← wfInv, Category.assoc]
  let q : P' ⟶ P := hP'.desc (inv y ≫ inY) (inv z ≫ inZ) w
  have qY : inY' ≫ q = inv y ≫ inY := hP'.inl_desc _ _ w
  have qZ : inZ' ≫ q = inv z ≫ inZ := hP'.inr_desc _ _ w
  refine ⟨⟨q, ?_, ?_⟩⟩
  · apply hP.hom_ext
    · calc
        inY ≫ (p ≫ q) = y ≫ (inY' ≫ q) := by rw [← Category.assoc, wY, Category.assoc]
        _ = y ≫ (inv y ≫ inY) := by rw [qY]
        _ = inY ≫ 𝟙 P := by simp only [IsIso.hom_inv_id_assoc, Category.comp_id]
    · calc
        inZ ≫ (p ≫ q) = z ≫ (inZ' ≫ q) := by rw [← Category.assoc, wZ, Category.assoc]
        _ = z ≫ (inv z ≫ inZ) := by rw [qZ]
        _ = inZ ≫ 𝟙 P := by simp only [IsIso.hom_inv_id_assoc, Category.comp_id]
  · apply hP'.hom_ext
    · calc
        inY' ≫ (q ≫ p) = inv y ≫ (inY ≫ p) := by rw [← Category.assoc, qY, Category.assoc]
        _ = inv y ≫ (y ≫ inY') := by rw [wY]
        _ = inY' ≫ 𝟙 P' := by simp only [IsIso.inv_hom_id_assoc, Category.comp_id]
    · calc
        inZ' ≫ (q ≫ p) = inv z ≫ (inZ ≫ p) := by rw [← Category.assoc, qZ, Category.assoc]
        _ = inv z ≫ (z ≫ inZ') := by rw [wZ]
        _ = inZ' ≫ 𝟙 P' := by simp only [IsIso.inv_hom_id_assoc, Category.comp_id]

variable {E}
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be a preadditive exact category with a zero object and binary
biproducts, A an abelian category, and F:E → A an additive functor.
The identity on bounded cochain complexes is a Waldhausen exact functor
from the structure with isomorphism weak equivalences to the structure with
F-detected quasi-isomorphism weak equivalences: it preserves zero objects,
degreewise admissible cofibrations, weak equivalences and pushouts along
cofibrations. -/
theorem isoToAmbient_isWaldhausenExact :
    @Functor.IsWaldhausenExact (Bounded E) _ _ (isoWaldhausenCategory E)
      (Bounded E) _ _ (ambientWaldhausenCategory F) (𝟭 (Bounded E)) := by
  refine @Functor.IsWaldhausenExact.mk (Bounded E) _ _ (isoWaldhausenCategory E)
    (Bounded E) _ _ (ambientWaldhausenCategory F) (𝟭 (Bounded E)) ?_ ?_ ?_ ?_
  · intro X hX
    exact hX
  · intro X Y f hi
    exact (ambient_isCofibration_iff F f).mpr ((iso_isCofibration_iff E f).mp hi)
  · intro X Y f hf
    let _ : IsIso f := hf
    apply (ambient_isWeakEquivalence_iff F f).mpr
    infer_instance
  · intro X Y X' P i f inl inr hi hP
    exact hP

end CochainComplex.Bounded

end
