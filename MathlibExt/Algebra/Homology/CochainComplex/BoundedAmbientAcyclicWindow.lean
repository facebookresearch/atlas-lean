/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicSubcategory
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowWaldhausen

/-!
# Acyclic bounded cochains in a fixed support window

Let E be preadditive, A abelian and F:E→A additive. For arbitrary integers a,b, consider bounded
E-cochains supported in [a,b] whose images under F are acyclic. Their full subcategory retains
the same cochain maps and has natural inclusions into the window, bounded and raw cochain
categories. It is closed under isomorphism; with a zero object in E it contains zero. A reversed
window b<a has only zero objects.

When E has an exact structure, zero and binary biproducts, and F is exact, degreewise admissible
monos define cofibrations. Pushouts along these maps stay in the same acyclic window and retain
their universal properties after forgetting support or evaluating in any degree. Together with
isomorphisms as weak maps, these give a Waldhausen model and the indicated exact inclusions.

The source and ambient object and Hom universes remain independent. The two bounds are arbitrary
integers.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. This object property tests
acyclicity of the F-image of a complex in the fixed support window. -/
def ambientAcyclicWindowObjects (a b : ℤ) : ObjectProperty (Window E a b) :=
  (ambientAcyclicObjects F).inverseImage (windowι E a b)

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Take the full subcategory
on that object property, retaining all cochain maps between its objects. -/
abbrev AmbientAcyclicWindow (a b : ℤ) := (ambientAcyclicWindowObjects F a b).FullSubcategory

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. The inclusion
C(a,b)→Window(E,a,b) retains the same supported cochain complex and every cochain map. -/
abbrev ambientAcyclicWindowι (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Window E a b :=
  (ambientAcyclicWindowObjects F a b).ι

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Forget the acyclicity and
support-window conditions to obtain the inclusion C(a,b)→Bounded(E). -/
abbrev ambientAcyclicWindowBounded (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ Bounded E :=
  ambientAcyclicWindowι F a b ⋙ windowι E a b

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Forget the bounded and
support conditions to obtain the inclusion C(a,b)→CochainComplex(E,ℤ). -/
abbrev ambientAcyclicWindowRaw (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ CochainComplex E ℤ :=
  ambientAcyclicWindowBounded F a b ⋙ ι E

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. The bounded inclusion sends
each K to the bounded complex underlying that same window object. -/
theorem ambientAcyclicWindowBounded_obj (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    (ambientAcyclicWindowBounded F a b).obj K = K.obj.obj := rfl

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. The raw inclusion sends
each K to its same integer-indexed cochain complex. -/
theorem ambientAcyclicWindowRaw_obj (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    (ambientAcyclicWindowRaw F a b).obj K = K.obj.obj.obj := rfl

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. The raw inclusion sends a
morphism f:K→L to its underlying whole cochain map, with all components unchanged. -/
theorem ambientAcyclicWindowRaw_map (a b : ℤ)
    {K L : AmbientAcyclicWindow F a b} (f : K ⟶ L) :
    (ambientAcyclicWindowRaw F a b).map f = f.hom.hom.hom := rfl

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. For every K in C(a,b), the
cochain complex obtained by applying F to K is acyclic. -/
theorem ambientAcyclicWindow_acyclic (a b : ℤ) (K : AmbientAcyclicWindow F a b) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K.obj.obj.obj).Acyclic := K.property

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. The same underlying bounded
complex defines an inclusion into the full category of all bounded F-acyclic complexes. -/
def ambientAcyclicWindowToAcyclic (a b : ℤ) : AmbientAcyclicWindow F a b ⥤ AmbientAcyclic F :=
  ObjectProperty.lift (ambientAcyclicObjects F) (ambientAcyclicWindowBounded F a b)
    (fun K => K.property)

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Including C(a,b) among all
bounded F-acyclic complexes and then forgetting acyclicity equals its bounded inclusion. -/
theorem ambientAcyclicWindowToAcyclic_comp_ι (a b : ℤ) :
    ambientAcyclicWindowToAcyclic F a b ⋙ ambientAcyclicι F =
      ambientAcyclicWindowBounded F a b := rfl

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. The F-acyclic object
property is invariant under isomorphism in the support-window category. -/
instance ambientAcyclicWindowObjects_isClosedUnderIsomorphisms (a b : ℤ) :
    (ambientAcyclicWindowObjects F a b).IsClosedUnderIsomorphisms := by
  dsimp only [ambientAcyclicWindowObjects]
  infer_instance

variable [HasZeroObject E]

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object.
A zero complex in the support-window category has acyclic F-image, so the object property
contains zero. -/
instance ambientAcyclicWindowObjects_containsZero (a b : ℤ) :
    (ambientAcyclicWindowObjects F a b).ContainsZero := by
  dsimp only [ambientAcyclicWindowObjects]
  infer_instance

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object.
The image of the selected zero of C(a,b) under its window inclusion is isomorphic to the
selected zero of Window(E,a,b). -/
def ambientAcyclicWindowZeroIso (a b : ℤ) :
    (ambientAcyclicWindowι F a b).obj (0 : AmbientAcyclicWindow F a b) ≅ (0 : Window E a b) :=
  ((ambientAcyclicWindowι F a b).map_isZero
    (isZero_zero (AmbientAcyclicWindow F a b))).isoZero

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object.
The selected zero of C(a,b), viewed as a bounded complex, is isomorphic to the selected zero of
Bounded(E). -/
def ambientAcyclicWindowBoundedZeroIso (a b : ℤ) :
    (ambientAcyclicWindowBounded F a b).obj (0 : AmbientAcyclicWindow F a b) ≅
      (0 : Bounded E) :=
  (windowι E a b).mapIso (ambientAcyclicWindowZeroIso F a b) ≪≫ windowZeroIso E a b

omit [HasZeroObject E] in
/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. If b<a, the support
condition forces every term of K to be zero, and every object K of C(a,b) is zero. -/
theorem ambientAcyclicWindow_isZero_of_reversed (a b : ℤ) (hba : b < a)
    (K : AmbientAcyclicWindow F a b) : IsZero K :=
  IsZero.of_full_of_faithful_of_isZero (ambientAcyclicWindowι F a b) K
    (window_isZero_of_reversed E a b hba K.obj)

variable [HasBinaryBiproducts E] [ExactCategory E] [F.IsExact]

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. A map in C(a,b) is a cofibration when
each of its integer-degree components is an admissible mono in E. -/
def ambientAcyclicWindowCofibrations (a b : ℤ) :
    MorphismProperty (AmbientAcyclicWindow F a b) :=
  (windowCofibrations E a b).inverseImage (ambientAcyclicWindowι F a b)

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. For a componentwise admissible mono
i:X→Y and any f:X→Z, there is a pushout P in C(a,b). Its same square is a pushout in the window
category, in bounded complexes and in every integer degree; the leg Z→P is again a cofibration.
The underlying cochain apex is the chosen raw pushout. -/
theorem exists_ambientAcyclicWindowPushout (a b : ℤ) {X Y Z : AmbientAcyclicWindow F a b}
    (i : X ⟶ Y) (f : X ⟶ Z) (hi : ambientAcyclicWindowCofibrations F a b i) :
    letI := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom.hom f.hom.hom hi
    ∃ (P : AmbientAcyclicWindow F a b) (inY : Y ⟶ P) (inZ : Z ⟶ P),
      IsPushout i f inY inZ ∧ IsPushout i.hom f.hom inY.hom inZ.hom ∧
      IsPushout i.hom.hom f.hom.hom inY.hom.hom inZ.hom.hom ∧
      (∀ j : ℤ, IsPushout (i.hom.hom.hom.f j) (f.hom.hom.hom.f j)
        (inY.hom.hom.hom.f j) (inZ.hom.hom.hom.f j)) ∧
      ambientAcyclicWindowCofibrations F a b inZ ∧
      P.obj.obj.obj = pushout i.hom.hom.hom f.hom.hom.hom := by
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom.hom f.hom.hom hi
  obtain ⟨P, inY, inZ, hP, hBounded, hTerms, hadm, hRaw⟩ :=
    exists_windowAdmissiblePushout E a b i.hom f.hom hi
  let Q : AmbientAcyclicWindow F a b :=
    ⟨P, ambientAcyclicObjects_pushout F hi hBounded X.property Y.property Z.property⟩
  let inY' : Y ⟶ Q := ObjectProperty.homMk inY
  let inZ' : Z ⟶ Q := ObjectProperty.homMk inZ
  have hQ : IsPushout i f inY' inZ' :=
    IsPushout.of_map_of_faithful (ambientAcyclicWindowι F a b) hP
  exact ⟨Q, inY', inZ', hQ, hP, hBounded, hTerms, hadm, hRaw⟩

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. A pushout square in C(a,b) along a
cofibration i retains its apex and both legs as a pushout square in Window(E,a,b). -/
theorem ambientAcyclicWindowPushout_window (a b : ℤ) {X Y Z P : AmbientAcyclicWindow F a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : ambientAcyclicWindowCofibrations F a b i) (hP : IsPushout i f inY inZ) :
    IsPushout i.hom f.hom inY.hom inZ.hom := by
  obtain ⟨Q, inY₀, inZ₀, hQ, hWindow, _, _, _, _⟩ :=
    exists_ambientAcyclicWindowPushout F a b i f hi
  let _ : PreservesColimit (span i f) (ambientAcyclicWindowι F a b) :=
    (hQ.preservesColimit_span_iff (F := ambientAcyclicWindowι F a b)).mpr hWindow
  exact hP.map (ambientAcyclicWindowι F a b)

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. A pushout square in C(a,b) along a
cofibration i remains a pushout of the same bounded complexes and maps. -/
theorem ambientAcyclicWindowPushout_bounded (a b : ℤ) {X Y Z P : AmbientAcyclicWindow F a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : ambientAcyclicWindowCofibrations F a b i) (hP : IsPushout i f inY inZ) :
    IsPushout i.hom.hom f.hom.hom inY.hom.hom inZ.hom.hom :=
  windowPushout_ι E a b hi (ambientAcyclicWindowPushout_window F a b hi hP)

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. A pushout square in C(a,b) along a
cofibration i evaluates to a pushout square in E at every integer degree j. -/
theorem ambientAcyclicWindowPushout_term (a b : ℤ) {X Y Z P : AmbientAcyclicWindow F a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : ambientAcyclicWindowCofibrations F a b i) (hP : IsPushout i f inY inZ) (j : ℤ) :
    IsPushout (i.hom.hom.hom.f j) (f.hom.hom.hom.f j)
      (inY.hom.hom.hom.f j) (inZ.hom.hom.hom.f j) :=
  windowPushout_term E a b hi (ambientAcyclicWindowPushout_window F a b hi hP) j

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. These classes, the chosen
zero and admissible pushouts give a Waldhausen structure on the acyclic support-window category. -/
@[instance_reducible, no_expose]
def ambientAcyclicWindowWaldhausenCategory (a b : ℤ) :
    WaldhausenCategoryWithoutGluing (AmbientAcyclicWindow F a b) where
  cofibrations := ambientAcyclicWindowCofibrations F a b
  weakEquivalences := MorphismProperty.isomorphisms (AmbientAcyclicWindow F a b)
  cofibrations_isMultiplicative := by
    dsimp only [ambientAcyclicWindowCofibrations]
    infer_instance
  cofibrations_respectsIso := by
    dsimp only [ambientAcyclicWindowCofibrations]
    infer_instance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration X f := by
    let _ := windowWaldhausenCategory E a b
    let e := ambientAcyclicWindowZeroIso F a b
    have h : IsCofibration (e.inv ≫ f.hom) := WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
    have hc := WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _
      (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso e.hom) h
    have hf : IsCofibration f.hom := by simpa only [Iso.hom_inv_id_assoc] using hc
    exact (window_isCofibration_iff E a b f.hom).mp hf
  cofibration_pushout i hi Z f := by
    obtain ⟨P, inY, inZ, hP, _, _, _, hadm, _⟩ :=
      exists_ambientAcyclicWindowPushout F a b i f hi
    exact ⟨P, inZ, inY, hP.flip, hadm⟩

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. A map f:K→L is a cofibration
exactly when each component fʲ is an admissible mono in E. -/
theorem ambientAcyclicWindow_isCofibration_iff (a b : ℤ)
    {X Y : AmbientAcyclicWindow F a b} (f : X ⟶ Y) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.hom.f j) := Iff.rfl

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. A map f:K→L is weak exactly
when it is an isomorphism in C(a,b). -/
theorem ambientAcyclicWindow_isWeakEquivalence_iff (a b : ℤ)
    {X Y : AmbientAcyclicWindow F a b} (f : X ⟶ Y) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    IsWeakEquivalence f ↔ IsIso f := Iff.rfl

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. The full inclusion into
Window(E,a,b) is Waldhausen exact for its componentwise admissible-mono and isomorphism-weak
structure. -/
theorem ambientAcyclicWindowι_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    letI := windowWaldhausenCategory E a b
    (ambientAcyclicWindowι F a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let _ := windowWaldhausenCategory E a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact (ambientAcyclicWindowι F a b).map_isZero hX
  · intro X Y f hf
    exact (window_isCofibration_iff E a b f.hom).mpr
      ((ambientAcyclicWindow_isCofibration_iff F a b f).mp hf)
  · intro X Y f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a b f).mp hf
    exact (window_isWeakEquivalence_iff E a b f.hom).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    exact (ambientAcyclicWindowPushout_window F a b hi hP.flip).flip

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. The bounded inclusion is
Waldhausen exact into Bounded(E) with componentwise admissible cofibrations and isomorphisms as
weak maps. -/
theorem ambientAcyclicWindowBounded_iso_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    letI := isoWaldhausenCategory E
    (ambientAcyclicWindowBounded F a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let _ := windowWaldhausenCategory E a b
  let _ := isoWaldhausenCategory E
  exact (ambientAcyclicWindowι_isWaldhausenExact F a b).comp (windowι_isWaldhausenExact E a b)

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. The inclusion into all
bounded F-acyclic complexes is Waldhausen exact for their isomorphism-weak model. -/
theorem ambientAcyclicWindowToAcyclic_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    letI := ambientAcyclicWaldhausenCategory F
    (ambientAcyclicWindowToAcyclic F a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let _ := ambientAcyclicWaldhausenCategory F
  let _ := isoWaldhausenCategory E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicι F) _
      ((ambientAcyclicWindowBounded_iso_isWaldhausenExact F a b).map_isZero hX)
  · intro X Y f hf
    exact (ambientAcyclic_isCofibration_iff F _).mpr
      ((ambientAcyclicWindow_isCofibration_iff F a b f).mp hf)
  · intro X Y f hf
    let _ : IsIso f := (ambientAcyclicWindow_isWeakEquivalence_iff F a b f).mp hf
    exact (ambientAcyclic_isWeakEquivalence_iff F _).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    apply IsPushout.of_map_of_faithful (ambientAcyclicι F)
    exact (ambientAcyclicWindowPushout_bounded F a b hi hP.flip).flip

/-- Let E be preadditive, A abelian and F:E→A additive, with integer bounds a,b. Let C(a,b) consist
of bounded E-cochains supported in [a,b] whose F-images are acyclic. Assume E has a zero object,
binary biproducts and an exact structure, and F is exact. Equip C(a,b) with componentwise
admissible-mono cofibrations and isomorphisms as weak equivalences. The bounded inclusion is
Waldhausen exact into the ambient model whose weak maps induce quasi-isomorphisms after F. -/
theorem ambientAcyclicWindowBounded_ambient_isWaldhausenExact (a b : ℤ) :
    letI := ambientAcyclicWindowWaldhausenCategory F a b
    letI := ambientWaldhausenCategory F
    (ambientAcyclicWindowBounded F a b).IsWaldhausenExact := by
  let _ := ambientAcyclicWindowWaldhausenCategory F a b
  let _ := ambientAcyclicWaldhausenCategory F
  let _ := ambientWaldhausenCategory F
  exact (ambientAcyclicWindowToAcyclic_isWaldhausenExact F a b).comp
    (ambientAcyclicι_ambient_isWaldhausenExact F)

end CochainComplex.Bounded

end
