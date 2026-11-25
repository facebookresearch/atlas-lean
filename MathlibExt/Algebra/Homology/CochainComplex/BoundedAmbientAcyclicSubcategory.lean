/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedIsoWaldhausen
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientCofiberExactness
public import MathlibExt.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The original ambient-acyclic bounded subcategory

This is the full subcategory of the same bounded source cochains whose
actual image under the specified additive exact ambient functor is
acyclic. The original zero-to-object map tests precisely this property.
Ambient gluing earns closure of actual admissible pushouts.

The subcategory has inherited admissible cofibrations and isomorphism
weak maps. Its original inclusion is exact into both bounded weak
models. The chosen zeros and both original cofiber legs are retained.
Faithfulness, kernel closure and source homology are not needed for this
Waldhausen model; they enter the separate source-cycle dictionary.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- The property is acyclicity of the same original bounded cochain's actual ambient image. -/
def ambientAcyclicObjects : ObjectProperty (Bounded E) :=
  fun K => ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic

/-- The original full subcategory of actual ambient-acyclic bounded cochains. -/
abbrev AmbientAcyclic := (ambientAcyclicObjects F).FullSubcategory

/-- The original full inclusion forgets only the ambient-acyclicity proof. -/
abbrev ambientAcyclicι : AmbientAcyclic F ⥤ Bounded E := (ambientAcyclicObjects F).ι

/-- The whole underlying bounded object is unchanged by the acyclic inclusion. -/
theorem ambientAcyclicι_obj (K : AmbientAcyclic F) : (ambientAcyclicι F).obj K = K.obj := rfl

/-- The whole underlying bounded map is unchanged by the acyclic inclusion. -/
theorem ambientAcyclicι_map {K L : AmbientAcyclic F} (f : K ⟶ L) :
    (ambientAcyclicι F).map f = f.hom := rfl

instance ambientAcyclicObjects_isClosedUnderIsomorphisms :
    (ambientAcyclicObjects F).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    let J := F.mapHomologicalComplex (.up ℤ)
    let _ : QuasiIso (J.map e.hom.hom) := inferInstance
    intro j
    exact (exactAt_iff_of_quasiIsoAt (J.map e.hom.hom) j).mp (hK j)

variable [HasZeroObject E]

instance ambientAcyclicObjects_containsZero : (ambientAcyclicObjects F).ContainsZero where
  exists_zero := by
    let J := ι E ⋙ F.mapHomologicalComplex (.up ℤ)
    exact ⟨0, isZero_zero (Bounded E),
      (J.obj (0 : Bounded E)).acyclic_of_isZero (J.map_isZero (isZero_zero (Bounded E)))⟩

/-- The original chosen acyclic zero maps to the actual bounded zero through its canonical chart. -/
def ambientAcyclicZeroIso : (ambientAcyclicι F).obj (0 : AmbientAcyclic F) ≅ (0 : Bounded E) :=
  ((ambientAcyclicι F).map_isZero (isZero_zero (AmbientAcyclic F))).isoZero

/-- The zero chart has its actual whole forward/inverse cancellation. -/
theorem ambientAcyclicZeroIso_hom_inv :
    (ambientAcyclicZeroIso F).hom ≫ (ambientAcyclicZeroIso F).inv =
      𝟙 ((ambientAcyclicι F).obj (0 : AmbientAcyclic F)) := (ambientAcyclicZeroIso F).hom_inv_id

variable [HasBinaryBiproducts E] [ExactCategory E]

/-- The same original zero-to-object map is weak precisely for ambient-acyclic objects. -/
theorem ambientAcyclicObjects_iff_zeroWeak (K : Bounded E) (z : (0 : Bounded E) ⟶ K) :
    letI := ambientWaldhausenCategory F
    ambientAcyclicObjects F K ↔ IsWeakEquivalence z := by
  let _ := ambientWaldhausenCategory F
  let J := ι E ⋙ F.mapHomologicalComplex (.up ℤ)
  have hZero := (J.obj (0 : Bounded E)).acyclic_of_isZero
    (J.map_isZero (isZero_zero (Bounded E)))
  rw [ambient_isWeakEquivalence_iff F z]
  constructor
  · intro hK
    apply (quasiIso_iff (J.map z)).mpr
    intro j
    exact (quasiIsoAt_iff_exactAt (J.map z) j (hZero j)).mpr (hK j)
  · intro hz
    let _ : QuasiIso (J.map z) := hz
    intro j
    exact (quasiIsoAt_iff_exactAt (J.map z) j (hZero j)).mp inferInstance

/-- The geometric bounded object property is the same original canonical weak-zero property. -/
theorem ambientAcyclicCanonical_iff (K : Bounded E) :
    ambientAcyclicObjects F K ↔
      @WaldhausenCategoryWithoutGluing.acyclicObjects (Bounded E) _ _ (ambientWaldhausenCategory F) K := by
  let _ := ambientWaldhausenCategory F
  exact (ambientAcyclicObjects_iff_zeroWeak F K ((isZero_zero (Bounded E)).to_ K)).trans
    (WaldhausenCategoryWithoutGluing.acyclicObjects_iff_zero_to K ((isZero_zero (Bounded E)).to_ K)).symm

/-- The canonical acyclic category retains the same original bounded base and ambient weak value. -/
abbrev CanonicalAmbientAcyclic := Waldhausen.AcyclicSubcategory (ambientWaldhausenCategory F)

/-- Change only the proof of acyclicity, keeping every original bounded object and map. -/
def ambientAcyclicToCanonical : AmbientAcyclic F ⥤ CanonicalAmbientAcyclic F :=
  ObjectProperty.ιOfLE (fun K hK => (ambientAcyclicCanonical_iff F K).mp hK)

/-- The inverse changes only the proof, keeping every original bounded object and map. -/
def ambientAcyclicFromCanonical : CanonicalAmbientAcyclic F ⥤ AmbientAcyclic F :=
  ObjectProperty.ιOfLE (fun K hK => (ambientAcyclicCanonical_iff F K).mpr hK)

/-- Both original carrier functors are inverse on the same objects and whole maps. -/
def ambientAcyclicCanonicalEquivalence : AmbientAcyclic F ≌ CanonicalAmbientAcyclic F where
  functor := ambientAcyclicToCanonical F
  inverse := ambientAcyclicFromCanonical F
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    change (𝟙 ((ambientAcyclicToCanonical F).obj X)) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

instance ambientAcyclicToCanonical_isEquivalence : (ambientAcyclicToCanonical F).IsEquivalence :=
  (ambientAcyclicCanonicalEquivalence F).isEquivalence_functor

instance ambientAcyclicFromCanonical_isEquivalence : (ambientAcyclicFromCanonical F).IsEquivalence :=
  (ambientAcyclicCanonicalEquivalence F).symm.isEquivalence_functor

/-- The complete forward object remains the same original bounded cochain. -/
theorem ambientAcyclicToCanonical_obj (X : AmbientAcyclic F) :
    ((ambientAcyclicToCanonical F).obj X).obj = X.obj := rfl

/-- The complete forward map remains the same original bounded map. -/
theorem ambientAcyclicToCanonical_map {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    ((ambientAcyclicToCanonical F).map f).hom = f.hom := rfl

/-- The complete inverse object remains the same original bounded cochain. -/
theorem ambientAcyclicFromCanonical_obj (X : CanonicalAmbientAcyclic F) :
    ((ambientAcyclicFromCanonical F).obj X).obj = X.obj := rfl

/-- The complete inverse map remains the same original bounded map. -/
theorem ambientAcyclicFromCanonical_map {X Y : CanonicalAmbientAcyclic F} (f : X ⟶ Y) :
    ((ambientAcyclicFromCanonical F).map f).hom = f.hom := rfl

/-- The whole original forward inclusion composite is the unchanged geometric inclusion. -/
theorem ambientAcyclicToCanonical_comp_ι :
    ambientAcyclicToCanonical F ⋙ Waldhausen.acyclicι (ambientWaldhausenCategory F) =
      ambientAcyclicι F := rfl

/-- The whole original inverse inclusion composite is the unchanged canonical inclusion. -/
theorem ambientAcyclicFromCanonical_comp_ι :
    ambientAcyclicFromCanonical F ⋙ ambientAcyclicι F =
      Waldhausen.acyclicι (ambientWaldhausenCategory F) := rfl

/-- Compare the original geometric selected zero with the actual canonical selected zero. -/
def ambientAcyclicCanonicalZeroIso :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    (ambientAcyclicToCanonical F).obj (0 : AmbientAcyclic F) ≅ (0 : CanonicalAmbientAcyclic F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact ((Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) _).mpr
    ((ambientAcyclicι F).map_isZero (isZero_zero (AmbientAcyclic F)))).isoZero

/-- The whole mapped forward zero chart is the same original geometric inclusion zero chart. -/
theorem ambientAcyclicCanonicalZeroIso_hom :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    (Waldhausen.acyclicι (ambientWaldhausenCategory F)).map (ambientAcyclicCanonicalZeroIso F).hom ≫
        (Waldhausen.acyclicιZeroIso (ambientWaldhausenCategory F)).hom =
      (ambientAcyclicZeroIso F).hom := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact (isZero_zero (Bounded E)).eq_of_tgt _ _

/-- The whole mapped inverse zero chart is the same original geometric inclusion zero chart. -/
theorem ambientAcyclicCanonicalZeroIso_inv :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    (Waldhausen.acyclicιZeroIso (ambientWaldhausenCategory F)).inv ≫
        (Waldhausen.acyclicι (ambientWaldhausenCategory F)).map (ambientAcyclicCanonicalZeroIso F).inv =
      (ambientAcyclicZeroIso F).inv := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact (isZero_zero (Bounded E)).eq_of_src _ _

/-- Both bounded weak values have the same literal original cofibration property. -/
theorem ambientIsoCofibrations_eq :
    (isoWaldhausenCategory E).cofibrations = (ambientWaldhausenCategory F).cofibrations := by
  funext X Y f
  exact propext ((iso_isCofibration_iff E f).trans (ambient_isCofibration_iff F f).symm)

/-- The actual original isomorphism weak class lies in the ambient raw quasi-isomorphism class. -/
theorem ambientIsoWeakEquivalences_le :
    (isoWaldhausenCategory E).weakEquivalences ≤ (ambientWaldhausenCategory F).weakEquivalences := by
  intro X Y f hf
  let _ : IsIso f := (iso_isWeakEquivalence_iff E f).mp hf
  apply (ambient_isWeakEquivalence_iff F f).mpr
  infer_instance

variable [F.IsExact]

/-- Actual original admissible pushouts of ambient-acyclic objects are ambient-acyclic. -/
theorem ambientAcyclicObjects_pushout {X Y Z P : Bounded E}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : degreewiseAdmissibleMonomorphisms E i) (hP : IsPushout i f inY inZ)
    (hX : ambientAcyclicObjects F X) (hY : ambientAcyclicObjects F Y)
    (hZ : ambientAcyclicObjects F Z) : ambientAcyclicObjects F P := by
  let _ := ambientWaldhausenCategory F
  exact (ambientAcyclicCanonical_iff F P).mpr
    ((ambientWaldhausen_gluing F).acyclicObjects_of_pushout i f inY inZ
      ((ambient_isCofibration_iff F i).mpr hi) hP
      ((ambientAcyclicCanonical_iff F X).mp hX)
      ((ambientAcyclicCanonical_iff F Y).mp hY)
      ((ambientAcyclicCanonical_iff F Z).mp hZ))

/-- The actual canonical supplier for the original bounded isomorphism weak structure. -/
@[instance_reducible]
def ambientAcyclicCanonicalWaldhausenCategory :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    WaldhausenCategoryWithoutGluing (CanonicalAmbientAcyclic F) :=
  Waldhausen.acyclicWaldhausenCategory (isoWaldhausenCategory E) (ambientWaldhausenCategory F)
    (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)

omit [F.IsExact] in
/-- Cofibrations in the acyclic subcategory test the same literal original components. -/
def ambientAcyclicCofibrations : MorphismProperty (AmbientAcyclic F) :=
  (degreewiseAdmissibleMonomorphisms E).inverseImage (ambientAcyclicι F)

/-- The actual original bounded pushout lifts with its same apex, legs and every component UP. -/
theorem exists_ambientAcyclicAdmissiblePushout {X Y Z : AmbientAcyclic F}
    (i : X ⟶ Y) (f : X ⟶ Z) (hi : ambientAcyclicCofibrations F i) :
    letI := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom f.hom hi
    ∃ (P : AmbientAcyclic F) (inY : Y ⟶ P) (inZ : Z ⟶ P),
      IsPushout i f inY inZ ∧ IsPushout i.hom f.hom inY.hom inZ.hom ∧
      (∀ j : ℤ, IsPushout (i.hom.hom.f j) (f.hom.hom.f j)
        (inY.hom.hom.f j) (inZ.hom.hom.f j)) ∧ ambientAcyclicCofibrations F inZ ∧
      P.obj.obj = pushout i.hom.hom f.hom.hom := by
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom f.hom hi
  obtain ⟨P, inY, inZ, hP, _, hTerms, hadm, hRaw⟩ :=
    exists_boundedAdmissiblePushout E i.hom f.hom hi
  let Q : AmbientAcyclic F :=
    ⟨P, ambientAcyclicObjects_pushout F hi hP X.property Y.property Z.property⟩
  let inY' : Y ⟶ Q := ObjectProperty.homMk inY
  let inZ' : Z ⟶ Q := ObjectProperty.homMk inZ
  have hQ : IsPushout i f inY' inZ' := IsPushout.of_map_of_faithful (ambientAcyclicι F) hP
  exact ⟨Q, inY', inZ', hQ, hP, hTerms, hadm, hRaw⟩

/-- Every actual admissible pushout in the subcategory retains its original bounded UP. -/
theorem ambientAcyclicPushout_ι {X Y Z P : AmbientAcyclic F}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : ambientAcyclicCofibrations F i) (hP : IsPushout i f inY inZ) :
    IsPushout i.hom f.hom inY.hom inZ.hom := by
  let J := ambientAcyclicToCanonical F
  have hi₀ : (isoWaldhausenCategory E).cofibrations ((J.map i).hom) :=
    (iso_isCofibration_iff E i.hom).mpr hi
  have hCanon : IsPushout (J.map f) (J.map i) (J.map inZ) (J.map inY) := hP.flip.map J
  exact (Waldhausen.acyclicι_map_isPushout (isoWaldhausenCategory E)
    (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
    (J.map i) (J.map f) (J.map inZ) (J.map inY) hi₀ hCanon).flip

/-- The original acyclic subcategory inherits admissible cofibrations and isomorphism weak maps. -/
@[instance_reducible, no_expose]
def ambientAcyclicWaldhausenCategory : WaldhausenCategoryWithoutGluing (AmbientAcyclic F) where
  cofibrations := ambientAcyclicCofibrations F
  weakEquivalences := MorphismProperty.isomorphisms (AmbientAcyclic F)
  cofibrations_isMultiplicative := by
    dsimp only [ambientAcyclicCofibrations]
    infer_instance
  cofibrations_respectsIso := by
    dsimp only [ambientAcyclicCofibrations]
    infer_instance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration K f := by
    change degreewiseAdmissibleMonomorphisms E f.hom
    let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    let _ := ambientAcyclicCanonicalWaldhausenCategory F
    let J := ambientAcyclicToCanonical F
    have hZero : IsZero (J.obj (0 : AmbientAcyclic F)) :=
      (Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) _).mpr
        ((ambientAcyclicι F).map_isZero (isZero_zero (AmbientAcyclic F)))
    let e := hZero.isoZero
    have h : IsCofibration (e.inv ≫ J.map f) := WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
    have hcomp : IsCofibration (e.hom ≫ (e.inv ≫ J.map f)) :=
      WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _
        (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso e.hom) h
    have hf : IsCofibration (J.map f) := by simpa only [Iso.hom_inv_id_assoc] using hcomp
    exact (iso_isCofibration_iff E f.hom).mp
      ((Waldhausen.isCofibration_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
        (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
        (J.map f)).mp hf)
  cofibration_pushout i hi Z f := by
    let J := ambientAcyclicToCanonical F
    have hi₀ : (isoWaldhausenCategory E).cofibrations ((J.map i).hom) :=
      (iso_isCofibration_iff E i.hom).mpr hi
    obtain ⟨P, inZ, inY, _, hP, hadm⟩ :=
      Waldhausen.acyclic_cofibration_pushout (isoWaldhausenCategory E)
        (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
        (J.map i) hi₀ (J.obj Z) (J.map f)
    let Q := (ambientAcyclicFromCanonical F).obj P
    let inZ' : Z ⟶ Q := ObjectProperty.homMk inZ.hom
    let inY' : _ ⟶ Q := ObjectProperty.homMk inY.hom
    refine ⟨Q, inZ', inY', IsPushout.of_map_of_faithful (ambientAcyclicι F) hP, ?_⟩
    exact (iso_isCofibration_iff E inZ.hom).mp hadm

/-- All original component cofibration tests are retained by the inherited acyclic model. -/
theorem ambientAcyclic_isCofibration_iff {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicWaldhausenCategory F
    IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j) := Iff.rfl

/-- The whole weak map in the inherited acyclic model is precisely the same isomorphism. -/
theorem ambientAcyclic_isWeakEquivalence_iff {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicWaldhausenCategory F
    IsWeakEquivalence f ↔ IsIso f := Iff.rfl

/-- The actual forward carrier comparison is exact for the original smaller weak models. -/
theorem ambientAcyclicToCanonical_isWaldhausenExact :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
      (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
      (ambientAcyclicToCanonical F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  refine @Functor.IsWaldhausenExact.mk (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
    (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
    (ambientAcyclicToCanonical F) ?_ ?_ ?_ ?_
  · intro X hX
    exact (Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) _).mpr
      ((ambientAcyclicι F).map_isZero hX)
  · intro X Y f hf
    exact (Waldhausen.isCofibration_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
      ((ambientAcyclicToCanonical F).map f)).mpr
      ((iso_isCofibration_iff E f.hom).mpr ((ambientAcyclic_isCofibration_iff F f).mp hf))
  · intro X Y f hf
    let _ : IsIso f := (ambientAcyclic_isWeakEquivalence_iff F f).mp hf
    exact (Waldhausen.isWeakEquivalence_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
      ((ambientAcyclicToCanonical F).map f)).mpr
      ((iso_isWeakEquivalence_iff E _).mpr inferInstance)
  · intro X Y Z P i f inl inr hi hP
    exact hP.map (ambientAcyclicToCanonical F)

/-- The actual inverse carrier comparison is exact for the original smaller weak models. -/
theorem ambientAcyclicFromCanonical_isWaldhausenExact :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    @Functor.IsWaldhausenExact (CanonicalAmbientAcyclic F) _ _
      (ambientAcyclicCanonicalWaldhausenCategory F) (AmbientAcyclic F) _ _
      (ambientAcyclicWaldhausenCategory F) (ambientAcyclicFromCanonical F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  refine @Functor.IsWaldhausenExact.mk (CanonicalAmbientAcyclic F) _ _
    (ambientAcyclicCanonicalWaldhausenCategory F) (AmbientAcyclic F) _ _
    (ambientAcyclicWaldhausenCategory F) (ambientAcyclicFromCanonical F) ?_ ?_ ?_ ?_
  · intro X hX
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicι F)
      ((ambientAcyclicFromCanonical F).obj X)
      ((Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) X).mp hX)
  · intro X Y f hf
    exact (ambientAcyclic_isCofibration_iff F _).mpr
      ((iso_isCofibration_iff E f.hom).mp
        ((Waldhausen.isCofibration_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
          (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
          f).mp hf))
  · intro X Y f hf
    have hIso : IsIso f.hom := (iso_isWeakEquivalence_iff E f.hom).mp
      ((Waldhausen.isWeakEquivalence_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
        (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
        f).mp hf)
    let _ : IsIso f := (ObjectProperty.isIso_hom_iff f).mp hIso
    exact (ambientAcyclic_isWeakEquivalence_iff F _).mpr inferInstance
  · intro X Y Z P i f inl inr hi hP
    exact hP.map (ambientAcyclicFromCanonical F)

/-- The original full inclusion is exact into the isomorphism bounded model. -/
theorem ambientAcyclicι_iso_isWaldhausenExact :
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
      (Bounded E) _ _ (isoWaldhausenCategory E) (ambientAcyclicι F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact @Functor.IsWaldhausenExact.comp (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
    (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
    (Bounded E) _ _ (isoWaldhausenCategory E) (ambientAcyclicToCanonical F)
    (Waldhausen.acyclicι (ambientWaldhausenCategory F))
    (ambientAcyclicToCanonical_isWaldhausenExact F)
    (Waldhausen.acyclicι_isWaldhausenExact (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F))

/-- The same ambient inclusion is the original inclusion followed by the exact identity. -/
theorem ambientAcyclicι_ambient_isWaldhausenExact :
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
      (Bounded E) _ _ (ambientWaldhausenCategory F) (ambientAcyclicι F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact @Functor.IsWaldhausenExact.comp (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
    (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
    (Bounded E) _ _ (ambientWaldhausenCategory F) (ambientAcyclicToCanonical F)
    (Waldhausen.acyclicι (ambientWaldhausenCategory F))
    (ambientAcyclicToCanonical_isWaldhausenExact F)
    (Waldhausen.acyclicι_toLarger_isWaldhausenExact (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientIsoWeakEquivalences_le F)
      (ambientWaldhausen_gluing F))

/-- The same original quotient is ambient-acyclic precisely for the original trivial cofibration. -/
theorem ambientCofiber_quotient_mem_iff {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    ambientAcyclicObjects F Z ↔ IsWeakEquivalence i :=
  (ambientCofiber_isWeakEquivalence_iff_quotient_acyclic F i p hSeq).symm

omit [F.IsExact] in
/-- Both original bounded weak models have the same cofiber sequences and chosen zero legs. -/
theorem iso_isCofiberSequence_iff_ambient {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z) :
    @IsCofiberSequence (Bounded E) _ _ (isoWaldhausenCategory E) X Y Z i p ↔
      @IsCofiberSequence (Bounded E) _ _ (ambientWaldhausenCategory F) X Y Z i p :=
  and_congr ((iso_isCofibration_iff E i).trans (ambient_isCofibration_iff F i).symm) Iff.rfl

/-- The original acyclic inclusion reflects the same cofiber sequence, including both whole legs. -/
theorem ambientAcyclic_isCofiberSequence_iff {X Y Z : AmbientAcyclic F}
    (i : X ⟶ Y) (p : Y ⟶ Z) :
    @IsCofiberSequence (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F) X Y Z i p ↔
      @IsCofiberSequence (Bounded E) _ _ (isoWaldhausenCategory E)
        X.obj Y.obj Z.obj i.hom p.hom := by
  let _ := ambientAcyclicWaldhausenCategory F
  let _ := isoWaldhausenCategory E
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  let _ := ambientAcyclicCanonicalWaldhausenCategory F
  let J := ambientAcyclicToCanonical F
  have hCanon := Waldhausen.acyclic_isCofiberSequence_iff (isoWaldhausenCategory E)
    (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
    (J.map i) (J.map p)
  constructor
  · intro hS
    exact hCanon.mp ((ambientAcyclicToCanonical_isWaldhausenExact F).map_cofibrationSequence hS)
  · intro hS
    exact (ambientAcyclicFromCanonical_isWaldhausenExact F).map_cofibrationSequence (hCanon.mpr hS)

/-- The inherited isomorphism weak property has gluing on the same subcategory pushouts. -/
theorem ambientAcyclic_gluing :
    letI := ambientAcyclicWaldhausenCategory F
    WaldhausenGluingAxiom (C := AmbientAcyclic F) := by
  let _ := ambientAcyclicWaldhausenCategory F
  let _ := isoWaldhausenCategory E
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  let _ := ambientAcyclicCanonicalWaldhausenCategory F
  let J := ambientAcyclicToCanonical F
  let hJ := ambientAcyclicToCanonical_isWaldhausenExact F
  have hG := Waldhausen.acyclicGluingAxiom (isoWaldhausenCategory E)
    (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
    (isoWaldhausen_gluing E)
  constructor
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p hi hi' wi wf wY wZ hx hy hz
  have hp : IsWeakEquivalence (J.map p) := hG.gluing (hP.map J) (hP'.map J)
    (J.map x) (J.map y) (J.map z) (J.map p) (hJ.map_cofibration i hi) (hJ.map_cofibration i' hi')
    (by simpa only [← J.map_comp] using congrArg J.map wi)
    (by simpa only [← J.map_comp] using congrArg J.map wf)
    (by simpa only [← J.map_comp] using congrArg J.map wY)
    (by simpa only [← J.map_comp] using congrArg J.map wZ)
    (hJ.map_weakEquivalence x hx) (hJ.map_weakEquivalence y hy) (hJ.map_weakEquivalence z hz)
  exact (ambientAcyclicFromCanonical_isWaldhausenExact F).map_weakEquivalence (J.map p) hp

variable [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]

/-- The original embedding and kernel closure identify the same all-degree source cycles. -/
theorem ambientAcyclicObjects_iff_admissibleData (K : Bounded E)
    (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
      F.essImage U → F.essImage V → F.essImage (kernel f)) :
    ambientAcyclicObjects F K ↔ Nonempty (AmbientCycles.AdmissibleAcyclicData K) :=
  AmbientCycles.ambient_acyclic_iff_admissibleData F K hKernelClosure

end CochainComplex.Bounded

end
