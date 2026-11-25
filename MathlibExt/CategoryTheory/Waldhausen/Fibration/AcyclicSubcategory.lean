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
# The original acyclic subcategory with the smaller weak structure

Two Waldhausen structures `V` and `W` share the original cofibrations on
the same category. The objects acyclic for `W` form the original full
subcategory. Gluing for `W` proves closure of the actual `V`-cofibration
pushouts. Those same pushouts construct the inherited `V` structure and
prove that its inclusion preserves the original cofiber sequences.

The chosen subcategory zero and the original ambient zero are connected
by their actual inclusion isomorphism. Both cofiber admission directions
retain this chart and the given quotient maps. Inclusion of the original
weak classes also gives exactness into `W` and of the identity `V → W`.

## References

* C. Weibel, *The K-book*, V.2.1, printed pages 376–377.
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

/-- Original gluing from the all-zero square proves acyclicity of the
given pushout apex from the three original acyclic span objects. -/
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

/-- The original full subcategory of objects acyclic for the specified
larger weak structure, with its inherited original morphisms. -/
abbrev AcyclicSubcategory (W : WaldhausenCategoryWithoutGluing C) : Type u :=
  (@WaldhausenCategoryWithoutGluing.acyclicObjects C _ _ W).FullSubcategory

/-- The original fully faithful inclusion of the acyclic full subcategory. -/
abbrev acyclicι (W : WaldhausenCategoryWithoutGluing C) : AcyclicSubcategory W ⥤ C :=
  (@WaldhausenCategoryWithoutGluing.acyclicObjects C _ _ W).ι

/-- The whole inclusion retains the original object. -/
theorem acyclicι_obj (W : WaldhausenCategoryWithoutGluing C) (X : AcyclicSubcategory W) :
    (acyclicι W).obj X = X.obj := rfl

/-- The whole inclusion retains the original morphism. -/
theorem acyclicι_map (W : WaldhausenCategoryWithoutGluing C)
    {X Y : AcyclicSubcategory W} (f : X ⟶ Y) : (acyclicι W).map f = f.hom := rfl

/-- The original ambient zero, admitted by its weak identity. -/
def acyclicZero (W : WaldhausenCategoryWithoutGluing C) : AcyclicSubcategory W :=
  ⟨(0 : C), @WaldhausenCategoryWithoutGluing.zero_mem_acyclicObjects C _ _ W⟩

/-- The admitted original zero is zero through the original full inclusion. -/
theorem acyclicZero_isZero (W : WaldhausenCategoryWithoutGluing C) : IsZero (acyclicZero W) :=
  IsZero.of_full_of_faithful_of_isZero (acyclicι W) (acyclicZero W) (isZero_zero C)

/-- The actual zero-object witness for the original acyclic category. -/
theorem acyclicHasZeroObject (W : WaldhausenCategoryWithoutGluing C) :
    HasZeroObject (AcyclicSubcategory W) :=
  (acyclicZero_isZero W).hasZeroObject

/-- The actual selected subcategory zero is compared with the admitted
original ambient zero, without replacing either selected object. -/
def acyclicZeroIso (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (0 : AcyclicSubcategory W) ≅ acyclicZero W := by
  let := acyclicHasZeroObject W
  exact (isZero_zero (AcyclicSubcategory W)).iso (acyclicZero_isZero W)

/-- The original inclusion's complete selected-zero chart. -/
def acyclicιZeroIso (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicι W).obj (0 : AcyclicSubcategory W) ≅ (0 : C) := by
  let := acyclicHasZeroObject W
  exact (acyclicι W).mapIso (acyclicZeroIso W)

/-- The zero chart's whole forward map is the original inclusion map. -/
theorem acyclicιZeroIso_hom (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).hom = (acyclicι W).map (acyclicZeroIso W).hom := rfl

/-- The zero chart's whole inverse map is the original inclusion map. -/
theorem acyclicιZeroIso_inv (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).inv = (acyclicι W).map (acyclicZeroIso W).inv := rfl

/-- The complete forward zero chart is the original unique map to zero. -/
theorem acyclicιZeroIso_hom_eq_from (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).hom =
      (isZero_zero C).from_ ((acyclicι W).obj (0 : AcyclicSubcategory W)) :=
  (isZero_zero C).eq_of_tgt _ _

/-- The complete inverse zero chart is the original unique map from zero. -/
theorem acyclicιZeroIso_inv_eq_to (W : WaldhausenCategoryWithoutGluing C) :
    letI := acyclicHasZeroObject W
    (acyclicιZeroIso W).inv =
      (isZero_zero C).to_ ((acyclicι W).obj (0 : AcyclicSubcategory W)) :=
  (isZero_zero C).eq_of_src _ _

/-- The original full inclusion preserves and reflects zero objects,
using the actual admitted ambient zero for the forward direction. -/
theorem acyclic_isZero_iff (W : WaldhausenCategoryWithoutGluing C) (X : AcyclicSubcategory W) :
    IsZero X ↔ IsZero X.obj := by
  constructor
  · intro hX
    let e : X ≅ acyclicZero W := hX.iso (acyclicZero_isZero W)
    exact (isZero_zero C).of_iso ((acyclicι W).mapIso e)
  · intro hX
    exact IsZero.of_full_of_faithful_of_isZero (acyclicι W) X hX

/-- Construct the same original smaller-structure cofibration pushout in
the acyclic full subcategory. Larger-structure gluing earns its apex. -/
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

/-- The constructed source and mapped pushout pair earns preservation of
every original source cofibration pushout by the full inclusion. -/
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

/-- The inherited smaller weak structure uses exactly the original
smaller cofibrations and weak maps under the original full inclusion. -/
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

/-- The source cofibration class is the literal original smaller class. -/
theorem isCofibration_acyclicWaldhausenCategory_iff (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y : AcyclicSubcategory W} (f : X ⟶ Y) :
    (letI := acyclicHasZeroObject W;
      letI := acyclicWaldhausenCategory V W hCof hGW;
      IsCofibration f) ↔ V.cofibrations f.hom := Iff.rfl

/-- The source weak class is the literal original smaller weak class. -/
theorem isWeakEquivalence_acyclicWaldhausenCategory_iff (V W : WaldhausenCategoryWithoutGluing C)
    (hCof : V.cofibrations = W.cofibrations)
    (hGW : @WaldhausenGluingAxiom C _ _ W)
    {X Y : AcyclicSubcategory W} (f : X ⟶ Y) :
    (letI := acyclicHasZeroObject W;
      letI := acyclicWaldhausenCategory V W hCof hGW;
      IsWeakEquivalence f) ↔ V.weakEquivalences f.hom := Iff.rfl

/-- The original acyclic inclusion into the original smaller weak
structure is exact on the constructed source structure and original maps. -/
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

/-- Inclusion of the actual weak classes makes the same acyclic
inclusion exact into the larger original weak structure. -/
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

/-- The original identity functor from the smaller to the larger weak
structure is exact, with the two actual structures separately supplied. -/
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

/-- The given original map to ambient zero, transported by the actual
inverse selected-zero chart, as a map to the selected subcategory zero. -/
def acyclicCofiberZeroMap (W : WaldhausenCategoryWithoutGluing C)
    {X : AcyclicSubcategory W} (s : X.obj ⟶ (0 : C)) :
    letI := acyclicHasZeroObject W
    X ⟶ (0 : AcyclicSubcategory W) := by
  let := acyclicHasZeroObject W
  exact ObjectProperty.homMk (s ≫ (acyclicιZeroIso W).inv)

/-- The given original map from ambient zero, transported by the actual
forward selected-zero chart, as a map from the selected subcategory zero. -/
def acyclicCofiberFromZeroMap (W : WaldhausenCategoryWithoutGluing C)
    {Q : AcyclicSubcategory W} (z : (0 : C) ⟶ Q.obj) :
    letI := acyclicHasZeroObject W
    (0 : AcyclicSubcategory W) ⟶ Q := by
  let := acyclicHasZeroObject W
  exact ObjectProperty.homMk ((acyclicιZeroIso W).hom ≫ z)

/-- The whole transported map retains the original map and inverse zero chart. -/
theorem acyclicCofiberZeroMap_hom (W : WaldhausenCategoryWithoutGluing C)
    {X : AcyclicSubcategory W} (s : X.obj ⟶ (0 : C)) :
    letI := acyclicHasZeroObject W
    (acyclicCofiberZeroMap W s).hom = s ≫ (acyclicιZeroIso W).inv := rfl

/-- The whole transported map retains the forward zero chart and original map. -/
theorem acyclicCofiberFromZeroMap_hom (W : WaldhausenCategoryWithoutGluing C)
    {Q : AcyclicSubcategory W} (z : (0 : C) ⟶ Q.obj) :
    letI := acyclicHasZeroObject W
    (acyclicCofiberFromZeroMap W z).hom = (acyclicιZeroIso W).hom ≫ z := rfl

/-- The same original cofiber row is admitted in both directions. The
reverse direction transports its given zero corner through the actual
selected-zero chart before reflecting the whole original pushout. -/
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

/-- The constructed acyclic category inherits the genuine smaller-class
gluing axiom from the original smaller weak structure, on the same maps. -/
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
