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

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.Fibration.TrivialCofibration

/-!
# Acyclic objects with inherited Waldhausen morphism classes

Let C have a zero object and two Waldhausen cofibration/weak-equivalence
structures V,W with the same cofibrations. The full subcategory C^W
consists of objects whose map 0 → X is W-weak. Gluing for W makes it
closed under pushouts along V-cofibrations, so the V classes restrict
to Waldhausen cofibration, weak-equivalence and pushout data on C^W.

The inclusion into C with V is exact and preserves and reflects cofiber
sequences. If V-weak maps are W-weak, it is also exact into C with W,
and the identity from V to W is exact. If V additionally satisfies
gluing, the inherited V structure on C^W does as well.
The selected zero in C^W is canonically isomorphic, under inclusion,
to the ambient zero.

Reference: C. Weibel, The K-book, V.2.1, pp. 376–377.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped ZeroObject

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C]

section PushoutClosure

variable [WaldhausenCategoryWithoutGluing C]

/-- Let C have a zero object and Waldhausen cofibration/weak-equivalence
data satisfying gluing. For a pushout of i:X → Y and f:X → Z,
with i a cofibration, if 0 → X, 0 → Y and 0 → Z are weak equivalences,
then 0 → P is a weak equivalence for its pushout apex P. -/
theorem WaldhausenGluingAxiom.acyclicObjects_of_pushout
    (hG : WaldhausenGluingAxiom (C := C))
    {X Y Z P : C} (i : X ⟶ Y) (f : X ⟶ Z) (inY : Y ⟶ P) (inZ : Z ⟶ P)
    (hi : IsCofibration i) (hP : IsPushout i f inY inZ)
    (hX : WaldhausenCategoryWithoutGluing.acyclicObjects X)
    (hY : WaldhausenCategoryWithoutGluing.acyclicObjects Y)
    (hZ : WaldhausenCategoryWithoutGluing.acyclicObjects Z) :
    WaldhausenCategoryWithoutGluing.acyclicObjects P :=
  hG.gluing (IsPushout.of_id_fst (f := 𝟙 (0 : C))) hP
    ((isZero_zero C).to_ X) ((isZero_zero C).to_ Y)
    ((isZero_zero C).to_ Z) ((isZero_zero C).to_ P)
    (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso (𝟙 (0 : C))) hi
    ((isZero_zero C).eq_of_src _ _) ((isZero_zero C).eq_of_src _ _)
    ((isZero_zero C).eq_of_src _ _) ((isZero_zero C).eq_of_src _ _)
    hX hY hZ

end PushoutClosure

namespace Waldhausen

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The full category C^W has the W-acyclic objects and all ambient morphisms between them. -/
abbrev AcyclicSubcategory (W : WaldhausenCategoryWithoutGluing C) : Type u :=
  (@WaldhausenCategoryWithoutGluing.acyclicObjects C _ _ W).FullSubcategory

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The fully faithful inclusion ι:C^W → C retains the ambient objects and morphisms. -/
abbrev acyclicι (W : WaldhausenCategoryWithoutGluing C) : AcyclicSubcategory W ⥤ C :=
  (@WaldhausenCategoryWithoutGluing.acyclicObjects C _ _ W).ι

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The value of ι on an object of C^W is its underlying ambient object. -/
theorem acyclicι_obj (W : WaldhausenCategoryWithoutGluing C) (X : AcyclicSubcategory W) :
    (acyclicι W).obj X = X.obj := rfl

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The value of ι on a morphism of C^W is its ambient morphism in C. -/
theorem acyclicι_map (W : WaldhausenCategoryWithoutGluing C)
    {X Y : AcyclicSubcategory W} (f : X ⟶ Y) : (acyclicι W).map f = f.hom := rfl

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The ambient zero object, admitted as an object of C^W because its identity is W-weak. -/
def acyclicZero (W : WaldhausenCategoryWithoutGluing C) : AcyclicSubcategory W :=
  ⟨(0 : C), @WaldhausenCategoryWithoutGluing.zero_mem_acyclicObjects C _ _ W⟩

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The ambient zero admitted in C^W is a zero object of the full subcategory. -/
theorem acyclicZero_isZero (W : WaldhausenCategoryWithoutGluing C) : IsZero (acyclicZero W) :=
  IsZero.of_full_of_faithful_of_isZero (acyclicι W) (acyclicZero W) (isZero_zero C)

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The full subcategory C^W has a zero object, represented by the admitted ambient zero. -/
theorem acyclicHasZeroObject (W : WaldhausenCategoryWithoutGluing C) :
    HasZeroObject (AcyclicSubcategory W) :=
  (acyclicZero_isZero W).hasZeroObject

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The canonical isomorphism from the selected zero object of C^W to the ambient zero regarded as an
object of C^W. -/
def acyclicZeroIso (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (0 : AcyclicSubcategory W) ≅ acyclicZero W := by
  let := acyclicHasZeroObject W
  exact (isZero_zero (AcyclicSubcategory W)).iso (acyclicZero_isZero W)

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

Applying ι to the zero-object comparison gives the canonical isomorphism e_W:ι(0_{C^W}) ≅ 0_C. -/
def acyclicιZeroIso (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicι W).obj (0 : AcyclicSubcategory W) ≅ (0 : C) := by
  let := acyclicHasZeroObject W
  exact (acyclicι W).mapIso (acyclicZeroIso W)

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The forward map of e_W:ι(0_{C^W}) ≅ 0_C is the inclusion's image of the forward zero-object
isomorphism in C^W. -/
theorem acyclicιZeroIso_hom (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).hom = (acyclicι W).map (acyclicZeroIso W).hom := rfl

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The inverse map of e_W:ι(0_{C^W}) ≅ 0_C is the inclusion's image of the inverse zero-object
isomorphism in C^W. -/
theorem acyclicιZeroIso_inv (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).inv = (acyclicι W).map (acyclicZeroIso W).inv := rfl

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The forward map of e_W:ι(0_{C^W}) ≅ 0_C is the unique morphism from ι(0_{C^W}) to the ambient zero.
-/
theorem acyclicιZeroIso_hom_eq_from (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).hom =
      (isZero_zero C).from_ ((acyclicι W).obj (0 : AcyclicSubcategory W)) :=
  (isZero_zero C).eq_of_tgt _ _

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

The inverse map of e_W:ι(0_{C^W}) ≅ 0_C is the unique morphism from the ambient zero to ι(0_{C^W}).
-/
theorem acyclicιZeroIso_inv_eq_to (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).inv =
      (isZero_zero C).to_ ((acyclicι W).obj (0 : AcyclicSubcategory W)) :=
  (isZero_zero C).eq_of_src _ _

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

For X in C^W, X is a zero object of the full subcategory if and only if its underlying object ι(X)
is zero in C. -/
theorem acyclic_isZero_iff (W : WaldhausenCategoryWithoutGluing C) (X : AcyclicSubcategory W) :
    IsZero X ↔ IsZero X.obj := by
  constructor
  · intro hX
    let e : X ≅ acyclicZero W := hX.iso (acyclicZero_isZero W)
    exact (isZero_zero C).of_iso ((acyclicι W).mapIso e)
  · intro hX
    exact IsZero.of_full_of_faithful_of_isZero (acyclicι W) X hX

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

For a V-cofibration i:X → Y and f:X → Z in C^W, a pushout exists both in C^W and in C under
inclusion, with the induced map Z → P a V-cofibration. -/
theorem acyclic_cofibration_pushout (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y : AcyclicSubcategory W} (i : X ⟶ Y) (hi : V.cofibrations i.hom)
    (Z : AcyclicSubcategory W) (f : X ⟶ Z) :
    ∃ (P : AcyclicSubcategory W) (inl : Z ⟶ P) (inr : Y ⟶ P),
      IsPushout f i inl inr ∧ IsPushout f.hom i.hom inl.hom inr.hom ∧
        V.cofibrations inl.hom := by
  let := W
  obtain ⟨P, inl, inr, hP, hInl⟩ := V.cofibration_pushout i.hom hi Z.obj f.hom
  have hiW : IsCofibration i.hom := by
    change W.cofibrations i.hom
    rw [← hCof]
    exact hi
  have hAcyclic : WaldhausenCategoryWithoutGluing.acyclicObjects P :=
    hGW.acyclicObjects_of_pushout i.hom f.hom inr inl hiW hP.flip
      X.property Y.property Z.property
  let P' : AcyclicSubcategory W := ⟨P, hAcyclic⟩
  let inl' : Z ⟶ P' := ObjectProperty.homMk inl
  let inr' : Y ⟶ P' := ObjectProperty.homMk inr
  refine ⟨P', inl', inr', ?_, hP, hInl⟩
  exact IsPushout.of_map_of_faithful (acyclicι W) hP

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

Any pushout in C^W along a V-cofibration remains a pushout after applying the inclusion ι. -/
theorem acyclicι_map_isPushout (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y Z P : AcyclicSubcategory W}
    (i : X ⟶ Y) (f : X ⟶ Z) (inl : Z ⟶ P) (inr : Y ⟶ P)
    (hi : V.cofibrations i.hom) (hP : IsPushout f i inl inr) :
    IsPushout f.hom i.hom inl.hom inr.hom := by
  obtain ⟨Q, inlQ, inrQ, hQ, hQMapped, _⟩ :=
    acyclic_cofibration_pushout V W hCof hGW i hi Z f
  let : PreservesColimit (span f i) (acyclicι W) :=
    (hQ.preservesColimit_span_iff (F := acyclicι W)).mpr hQMapped
  exact hP.map (acyclicι W)

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

The restricted Waldhausen data on C^W use V-cofibrations and V-weak maps detected by ι, with the
pushouts admitted through W-acyclicity. -/
@[instance_reducible]
def acyclicWaldhausenCategory (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W) :
    letI := acyclicHasZeroObject W
    WaldhausenCategoryWithoutGluing (AcyclicSubcategory W) := by
  let := V
  let := acyclicHasZeroObject W
  refine {
    cofibrations := V.cofibrations.inverseImage (acyclicι W)
    weakEquivalences := V.weakEquivalences.inverseImage (acyclicι W)
    cofibrations_isMultiplicative := inferInstance
    cofibrations_respectsIso := inferInstance
    weakEquivalences_isMultiplicative := inferInstance
    weakEquivalences_respectsIso := inferInstance
    zero_isCofibration := ?_
    cofibration_pushout := ?_ }
  · intro X f
    change V.cofibrations f.hom
    let e := acyclicιZeroIso W
    have hZero : V.cofibrations (e.inv ≫ f.hom) := V.zero_isCofibration _ _
    have hPre := MorphismProperty.RespectsIso.precomp V.cofibrations e.hom _ hZero
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hPre
  · intro X Y i hi Z f
    obtain ⟨P, inl, inr, hP, _, hInl⟩ :=
      acyclic_cofibration_pushout V W hCof hGW i hi Z f
    exact ⟨P, inl, inr, hP, hInl⟩

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

A map f in the inherited structure on C^W is a cofibration exactly when ι(f) is a V-cofibration in
C. -/
theorem isCofibration_acyclicWaldhausenCategory_iff (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y : AcyclicSubcategory W} (f : X ⟶ Y) :
    (letI := acyclicHasZeroObject W;
      letI := acyclicWaldhausenCategory V W hCof hGW;
      IsCofibration f) ↔ V.cofibrations f.hom := Iff.rfl

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

A map f in the inherited structure on C^W is a weak equivalence exactly when ι(f) is V-weak in C. -/
theorem isWeakEquivalence_acyclicWaldhausenCategory_iff (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y : AcyclicSubcategory W} (f : X ⟶ Y) :
    (letI := acyclicHasZeroObject W;
      letI := acyclicWaldhausenCategory V W hCof hGW;
      IsWeakEquivalence f) ↔ V.weakEquivalences f.hom := Iff.rfl

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

The inclusion ι from the inherited V structure on C^W to C with structure V is Waldhausen exact. -/
theorem acyclicι_isWaldhausenExact (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W) :
    letI := V
    letI := acyclicHasZeroObject W
    letI := acyclicWaldhausenCategory V W hCof hGW
    (acyclicι W).IsWaldhausenExact := by
  let := V
  let := acyclicHasZeroObject W
  let := acyclicWaldhausenCategory V W hCof hGW
  refine {
    map_isZero := fun {X} hX => (acyclic_isZero_iff W X).mp hX
    map_cofibration := fun _ hf => hf
    map_weakEquivalence := fun _ hf => hf
    map_pushout := ?_ }
  intro X Y Z P i f inl inr hi hP
  exact acyclicι_map_isPushout V W hCof hGW i f inl inr hi hP

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

If every V-weak map is W-weak, the same inclusion ι is Waldhausen exact into C with structure W. -/
theorem acyclicι_toLarger_isWaldhausenExact (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hWeak : V.weakEquivalences ≤ W.weakEquivalences)
    (hGW : @WaldhausenGluingAxiom C _ _ W) :
    letI := W
    letI := acyclicHasZeroObject W
    letI := acyclicWaldhausenCategory V W hCof hGW
    (acyclicι W).IsWaldhausenExact := by
  let := W
  let := acyclicHasZeroObject W
  let := acyclicWaldhausenCategory V W hCof hGW
  refine {
    map_isZero := fun {X} hX => (acyclic_isZero_iff W X).mp hX
    map_cofibration := ?_
    map_weakEquivalence := fun f hf => hWeak f.hom hf
    map_pushout := ?_ }
  · intro X Y f hf
    change W.cofibrations f.hom
    rw [← hCof]
    exact hf
  · intro X Y Z P i f inl inr hi hP
    exact acyclicι_map_isPushout V W hCof hGW i f inl inr hi hP

/-- Let C have a zero object and V,W be Waldhausen cofibration,
weak-equivalence and pushout data with identical cofibrations.
If V-weak maps are W-weak, the identity functor C → C is
Waldhausen exact from V to W. -/
theorem changeWeakEquivalences_isWaldhausenExact (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hWeak : V.weakEquivalences ≤ W.weakEquivalences) :
    @Functor.IsWaldhausenExact C _ _ V C _ _ W (𝟭 C) := by
  refine @Functor.IsWaldhausenExact.mk C _ _ V C _ _ W (𝟭 C) ?_ ?_ ?_ ?_
  · intro X hX
    exact hX
  · intro X Y f hf
    change W.cofibrations f
    rw [← hCof]
    exact hf
  · intro X Y f hf
    change V.weakEquivalences f at hf
    change W.weakEquivalences f
    exact hWeak f hf
  · intro X Y Z P i f inl inr hi hP
    exact hP

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

For X in C^W and s:ι(X) → 0_C, the map X → 0_{C^W} whose ambient morphism is e_W⁻¹∘s, where
e_W:ι(0_{C^W}) ≅ 0_C is the canonical zero comparison. -/
def acyclicCofiberZeroMap (W : WaldhausenCategoryWithoutGluing C)
    {X : AcyclicSubcategory W} (s : X.obj ⟶ (0 : C)) :
    letI := acyclicHasZeroObject W
    X ⟶ (0 : AcyclicSubcategory W) := by
  let := acyclicHasZeroObject W
  exact ObjectProperty.homMk (s ≫ (acyclicιZeroIso W).inv)

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

For Q in C^W and z:0_C → ι(Q), the map 0_{C^W} → Q whose ambient morphism is z∘e_W, using
e_W:ι(0_{C^W}) ≅ 0_C. -/
def acyclicCofiberFromZeroMap (W : WaldhausenCategoryWithoutGluing C)
    {Q : AcyclicSubcategory W} (z : (0 : C) ⟶ Q.obj) :
    letI := acyclicHasZeroObject W
    (0 : AcyclicSubcategory W) ⟶ Q := by
  let := acyclicHasZeroObject W
  exact ObjectProperty.homMk ((acyclicιZeroIso W).hom ≫ z)

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

For s:ι(X) → 0_C, the ambient image of its map X → 0_{C^W} equals e_W⁻¹∘s. -/
theorem acyclicCofiberZeroMap_hom (W : WaldhausenCategoryWithoutGluing C)
    {X : AcyclicSubcategory W} (s : X.obj ⟶ (0 : C)) :
    letI := acyclicHasZeroObject W
    (acyclicCofiberZeroMap W s).hom = s ≫ (acyclicιZeroIso W).inv := rfl

/-- Let C have a zero object and let W be Waldhausen cofibration,
weak-equivalence and cofibration-pushout data on C.
Write C^W for the full subcategory of objects whose map 0 → X is
a W-weak equivalence, and ι:C^W → C for its inclusion.

For z:0_C → ι(Q), the ambient image of its map 0_{C^W} → Q equals z∘e_W. -/
theorem acyclicCofiberFromZeroMap_hom (W : WaldhausenCategoryWithoutGluing C)
    {Q : AcyclicSubcategory W} (z : (0 : C) ⟶ Q.obj) :
    letI := acyclicHasZeroObject W
    (acyclicCofiberFromZeroMap W z).hom = (acyclicιZeroIso W).hom ≫ z := rfl

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

For maps X —i→ Y —q→ Q in C^W, they form a cofiber sequence in the inherited V structure if and only
if ι(X) —ι(i)→ ι(Y) —ι(q)→ ι(Q) is a cofiber sequence in C with V. -/
theorem acyclic_isCofiberSequence_iff (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y Q : AcyclicSubcategory W} (i : X ⟶ Y) (q : Y ⟶ Q) :
    (letI := acyclicHasZeroObject W;
      letI := acyclicWaldhausenCategory V W hCof hGW;
      IsCofiberSequence i q) ↔ (@IsCofiberSequence C _ _ V _ _ _ i.hom q.hom) := by
  let := V
  let := acyclicHasZeroObject W
  let := acyclicWaldhausenCategory V W hCof hGW
  constructor
  · intro hS
    exact (acyclicι_isWaldhausenExact V W hCof hGW).map_cofibrationSequence hS
  · rintro ⟨hi, s, z, hP⟩
    have hP' : IsPushout (acyclicCofiberZeroMap W s).hom i.hom
        (acyclicCofiberFromZeroMap W z).hom q.hom := by
      change IsPushout (s ≫ (acyclicιZeroIso W).inv) i.hom
        ((acyclicιZeroIso W).hom ≫ z) q.hom
      apply hP.of_iso (Iso.refl _) (acyclicιZeroIso W).symm (Iso.refl _) (Iso.refl _)
      all_goals simp
    refine ⟨hi, acyclicCofiberZeroMap W s, acyclicCofiberFromZeroMap W z, ?_⟩
    exact IsPushout.of_map_of_faithful (acyclicι W) hP'

/-- Let C have a zero object and V,W Waldhausen cofibration,
weak-equivalence and pushout data with the same cofibration class.
Assume W satisfies gluing. Let C^W be the full subcategory of
W-acyclic objects, with cofibrations and weak equivalences inherited
from V, and inclusion ι:C^W → C.

If V also satisfies the gluing axiom, then the inherited V structure on C^W satisfies gluing. -/
theorem acyclicGluingAxiom (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    (hGV : @WaldhausenGluingAxiom C _ _ V) :
    letI := acyclicHasZeroObject W
    letI := acyclicWaldhausenCategory V W hCof hGW
    WaldhausenGluingAxiom (C := AcyclicSubcategory W) := by
  let := V
  let := acyclicHasZeroObject W
  let := acyclicWaldhausenCategory V W hCof hGW
  refine ⟨?_⟩
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p hi hi' hiSquare hfSquare hYFace hZFace hx hy hz
  have hMapP : IsPushout i.hom f.hom inY.hom inZ.hom :=
    (acyclicι_map_isPushout V W hCof hGW i f inZ inY hi hP.flip).flip
  have hMapP' : IsPushout i'.hom f'.hom inY'.hom inZ'.hom :=
    (acyclicι_map_isPushout V W hCof hGW i' f' inZ' inY' hi' hP'.flip).flip
  exact hGV.gluing hMapP hMapP' x.hom y.hom z.hom p.hom hi hi'
    (congrArg InducedCategory.Hom.hom hiSquare)
    (congrArg InducedCategory.Hom.hom hfSquare)
    (congrArg InducedCategory.Hom.hom hYFace)
    (congrArg InducedCategory.Hom.hom hZFace) hx hy hz

end Waldhausen

end CategoryTheory

end
