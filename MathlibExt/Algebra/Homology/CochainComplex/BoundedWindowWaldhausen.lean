/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedIsoWaldhausen
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality

/-!
# Fixed windows of bounded cochain complexes

For a category `E` with zero morphisms and integers `a, b`, the category `Window E a b`
consists of bounded integer-indexed cochain complexes whose terms are zero whenever `j<a` or
`b<j`. It is a full subcategory of `Bounded E`; its inclusion and evaluation functors retain
the underlying complexes and degree components. If `b<a`, every object of the window is zero.

When `E` is preadditive and exact, with a zero object and binary biproducts, the window
cofibrations are degreewise admissible monomorphisms and the weak equivalences are
isomorphisms. Admissible pushouts remain in the window and are pushouts in every degree. The
inclusion into the bounded isomorphism model and evaluation into the exact category preserve
these structures and their S-construction diagrams.

See C. Weibel, *The K-book*, V.2.2.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E]

section Support

variable [HasZeroMorphisms E]

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a, b : ℤ`, `windowSupport E a
b` is the object property on `Bounded E` defined by
`∀ j : ℤ, j<a ∨ b<j → IsZero (K.obj.X j)`.
Thus the underlying cochain complex has zero terms outside the closed interval `[a,b]`. -/
def windowSupport (a b : ℤ) : ObjectProperty (Bounded E) :=
  fun K => ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a, b :
ℤ`, `Window E a b` is the full subcategory of `Bounded E` on complexes whose terms are zero
outside `[a,b]`. Its morphisms are bounded cochain maps between those complexes. -/
abbrev Window (a b : ℤ) := (windowSupport E a b).FullSubcategory

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a, b :
ℤ`, `windowι E a b : Window E a b ⥤ Bounded E` is the full inclusion of complexes supported in
`[a,b]` into the category of bounded integer-indexed cochain complexes. -/
abbrev windowι (a b : ℤ) : Window E a b ⥤ Bounded E := (windowSupport E a b).ι

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a, b :
ℤ`, the functor `windowRaw E a b : Window E a b ⥤ CochainComplex E ℤ` is `windowι E a b ⋙ ι
E`. It includes the fixed-window category into all integer-indexed cochain complexes. -/
abbrev windowRaw (a b : ℤ) : Window E a b ⥤ CochainComplex E ℤ := windowι E a b ⋙ ι E

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a, b, j :
ℤ`, `windowEval E a b j : Window E a b ⥤ E` is `windowι E a b ⋙ eval E j`. It takes a window
complex to its degree-`j` term and a cochain map to its degree-`j` component. -/
def windowEval (a b j : ℤ) : Window E a b ⥤ E := windowι E a b ⋙ eval E j

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a, b : ℤ`, and `K : Window E a b`,
`(windowRaw E a b).obj K = K.obj.obj`.
The underlying cochain complex is the same complex underlying the corresponding bounded object. -/
theorem windowRaw_obj (a b : ℤ) (K : Window E a b) : (windowRaw E a b).obj K = K.obj.obj := rfl

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a, b : ℤ`, and `f : K ⟶ L` in
`Window E a b`,
`(windowRaw E a b).map f = f.hom.hom`.
The full inclusions retain the underlying cochain map. -/
theorem windowRaw_map (a b : ℤ) {K L : Window E a b} (f : K ⟶ L) :
    (windowRaw E a b).map f = f.hom.hom := rfl

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a, b, j : ℤ`, and `K : Window E a
b`,
`(windowEval E a b j).obj K = K.obj.obj.X j`.
Evaluation returns the degree-`j` term of the underlying cochain complex. -/
theorem windowEval_obj (a b j : ℤ) (K : Window E a b) :
    (windowEval E a b j).obj K = K.obj.obj.X j := rfl

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a, b, j : ℤ`, and `f : K ⟶ L` in
`Window E a b`,
`(windowEval E a b j).map f = f.hom.hom.f j`.
The evaluated morphism is the degree-`j` cochain component. -/
theorem windowEval_map (a b j : ℤ) {K L : Window E a b} (f : K ⟶ L) :
    (windowEval E a b j).map f = f.hom.hom.f j := rfl

/-- Let `E` be a category with zero morphisms, `K : CochainComplex E ℤ`, and `a, b : ℤ`. Given `hK
: ∀ j, j<a ∨ b<j → IsZero (K.X j)`, the object `windowOf E K a b hK : Window E a b` represents
`K` with this support bound. The same witness makes `K` a bounded cochain complex. -/
def windowOf (K : CochainComplex E ℤ) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)) : Window E a b :=
  ⟨of E K a b hK, hK⟩

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `K : CochainComplex E ℤ`, `a, b :
ℤ`, and `hK : ∀ j, j<a ∨ b<j → IsZero (K.X j)`,
`(windowOf E K a b hK).obj.obj = K`.
The support-bound constructor retains the entire underlying cochain complex. -/
theorem windowOf_obj (K : CochainComplex E ℤ) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)) :
    (windowOf E K a b hK).obj.obj = K := rfl

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a, b :
ℤ`, the property `windowSupport E a b` is closed under isomorphisms in `Bounded E`. A cochain
isomorphism induces isomorphisms in every degree, so terms that are zero outside `[a,b]`
remain zero under that isomorphism. -/
instance windowSupport_isClosedUnderIsomorphisms (a b : ℤ) :
    (windowSupport E a b).IsClosedUnderIsomorphisms where
  of_iso e hK j hj := (hK j hj).of_iso ((eval E j).mapIso e).symm

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, integers `a,
b` with `b<a`, and `K : Window E a b`, the object `K` is zero. Every integer `j` satisfies
`j<a` or `b<j`, so the support condition makes every term of its cochain complex a zero
object. -/
theorem window_isZero_of_reversed (a b : ℤ) (hba : b < a) (K : Window E a b) : IsZero K := by
  have hRaw : IsZero K.obj.obj := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.hom_ext
    intro j
    exact (K.property j (by omega)).eq_of_src _ _
  exact IsZero.of_full_of_faithful_of_isZero (windowRaw E a b) K hRaw

variable [HasZeroObject E]

/-- Let `E` be a category with zero morphisms and a zero object. For every `a, b : ℤ`,
`windowSupport E a b` contains a zero object of `Bounded E`. Every term of the zero cochain
complex is zero, so it satisfies the support condition for any integer window. -/
instance windowSupport_containsZero (a b : ℤ) : (windowSupport E a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero (Bounded E), fun j _ =>
    (HomologicalComplex.eval E (.up ℤ) j).map_isZero
      ((ι E).map_isZero (isZero_zero (Bounded E)))⟩

/-- For a category `E` with zero morphisms and a zero object and for `a, b : ℤ`, there is an isomorphism
`(windowι E a b).obj (0 : Window E a b) ≅ (0 : Bounded E)`.
The full inclusion sends the selected zero window object to a zero bounded cochain complex. -/
def windowZeroIso (a b : ℤ) : (windowι E a b).obj (0 : Window E a b) ≅ (0 : Bounded E) :=
  ((windowι E a b).map_isZero (isZero_zero (Window E a b))).isoZero

end Support

variable [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a, b : ℤ`, `windowCofibrations E a b` is the morphism property on
`Window E a b` obtained by pulling back `degreewiseAdmissibleMonomorphisms E` along `windowι E
a b`. A window cochain map has this property exactly when every component is an admissible
monomorphism in `E`. -/
def windowCofibrations (a b : ℤ) : MorphismProperty (Window E a b) :=
  (degreewiseAdmissibleMonomorphisms E).inverseImage (windowι E a b)

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a, b : ℤ`, and `f : X ⟶ Y` in `Window E a b`,
`windowCofibrations E a b f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j)`.
The cofibration condition is precisely degreewise admissibility of the underlying cochain map. -/
theorem windowCofibrations_iff (a b : ℤ) {X Y : Window E a b} (f : X ⟶ Y) :
    windowCofibrations E a b f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j) := Iff.rfl

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a, b : ℤ`, the property `windowCofibrations E a b` contains
identity maps and is closed under composition. Both statements hold componentwise because
admissible monomorphisms in `E` have these properties. -/
instance windowCofibrations_isMultiplicative (a b : ℤ) :
    (windowCofibrations E a b).IsMultiplicative := by
  dsimp only [windowCofibrations]
  infer_instance

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a, b : ℤ`, `windowCofibrations E a b` respects isomorphisms of
arrows in `Window E a b`. Precomposition and postcomposition by cochain isomorphisms preserve
degreewise admissible monomorphisms. -/
instance windowCofibrations_respectsIso (a b : ℤ) : (windowCofibrations E a b).RespectsIso := by
  dsimp only [windowCofibrations]
  infer_instance

/-- Let `E` be a preadditive exact category with a zero object and binary biproducts. For `X,Y,Z :
Window E a b`, a window cofibration `i : X ⟶ Y`, and any `f : X ⟶ Z`, there exist `P : Window
E a b` and legs `inY, inZ` forming a pushout in the window category, in `Bounded E`, and in
every degree of `E`. The leg `inZ` is a window cofibration, and the underlying complex of `P`
is the chosen pushout of the underlying cochain maps. -/
theorem exists_windowAdmissiblePushout (a b : ℤ) {X Y Z : Window E a b}
    (i : X ⟶ Y) (f : X ⟶ Z) (hi : windowCofibrations E a b i) :
    letI := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom f.hom hi
    ∃ (P : Window E a b) (inY : Y ⟶ P) (inZ : Z ⟶ P),
      IsPushout i f inY inZ ∧ IsPushout i.hom f.hom inY.hom inZ.hom ∧
      (∀ j : ℤ, IsPushout (i.hom.hom.f j) (f.hom.hom.f j)
        (inY.hom.hom.f j) (inZ.hom.hom.f j)) ∧ windowCofibrations E a b inZ ∧
      P.obj.obj = pushout i.hom.hom f.hom.hom := by
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom f.hom hi
  obtain ⟨P, inY, inZ, hP, _, hTerms, hadm, hRaw⟩ :=
    exists_boundedAdmissiblePushout E i.hom f.hom hi
  have hWindow : windowSupport E a b P := by
    intro j hj
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (hTerms j).hom_ext
    · exact (Y.property j hj).eq_of_src _ _
    · exact (Z.property j hj).eq_of_src _ _
  let Q : Window E a b := ⟨P, hWindow⟩
  let inY' : Y ⟶ Q := ObjectProperty.homMk inY
  let inZ' : Z ⟶ Q := ObjectProperty.homMk inZ
  have hQ : IsPushout i f inY' inZ' := IsPushout.of_map_of_faithful (windowι E a b) hP
  exact ⟨Q, inY', inZ', hQ, hP, hTerms, hadm, hRaw⟩

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, and a pushout square `IsPushout i f inY inZ` in `Window E a b` with `windowCofibrations E a b i`,
`IsPushout i.hom f.hom inY.hom inZ.hom`
holds in `Bounded E`. Thus the full inclusion preserves this pushout along a degreewise admissible monomorphism. -/
theorem windowPushout_ι (a b : ℤ) {X Y Z P : Window E a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : windowCofibrations E a b i) (hP : IsPushout i f inY inZ) :
    IsPushout i.hom f.hom inY.hom inZ.hom := by
  obtain ⟨Q, inY₀, inZ₀, hQ, hBounded, _, _, _⟩ := exists_windowAdmissiblePushout E a b i f hi
  let _ : PreservesColimit (span i f) (windowι E a b) :=
    (hQ.preservesColimit_span_iff (F := windowι E a b)).mpr hBounded
  exact hP.map (windowι E a b)

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, a pushout `IsPushout i f inY inZ` in `Window E a b` with `windowCofibrations E a b i`, and `j : ℤ`,
`IsPushout (i.hom.hom.f j) (f.hom.hom.f j) (inY.hom.hom.f j) (inZ.hom.hom.f j)`
holds in `E`. Every degree component retains the pushout universal property. -/
theorem windowPushout_term (a b : ℤ) {X Y Z P : Window E a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : windowCofibrations E a b i) (hP : IsPushout i f inY inZ) (j : ℤ) :
    IsPushout (i.hom.hom.f j) (f.hom.hom.f j) (inY.hom.hom.f j) (inZ.hom.hom.f j) :=
  admissiblePushout_term E hi (windowPushout_ι E a b hi hP) j

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b : ℤ`, the fixed-window structure on `Window E a b` uses
`windowCofibrations E a b` as cofibrations and isomorphisms as weak equivalences.
Identity/composition and isomorphism invariance are inherited degreewise; maps from zero are
cofibrations, and pushouts along cofibrations remain in the same window with cofibration
cobase-change legs. -/
@[instance_reducible, no_expose]
def windowWaldhausenCategory (a b : ℤ) : WaldhausenCategoryWithoutGluing (Window E a b) where
  cofibrations := windowCofibrations E a b
  weakEquivalences := MorphismProperty.isomorphisms (Window E a b)
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration X f := by
    change degreewiseAdmissibleMonomorphisms E f.hom
    let e := windowZeroIso E a b
    have h : degreewiseAdmissibleMonomorphisms E (e.inv ≫ f.hom) :=
      degreewiseAdmissibleMonomorphisms_zero X.obj _
    have hComp := (degreewiseAdmissibleMonomorphisms E).comp_mem e.hom (e.inv ≫ f.hom)
      ((degreewiseAdmissibleMonomorphisms E).of_isIso e.hom) h
    simpa only [Iso.hom_inv_id_assoc] using hComp
  cofibration_pushout i hi Z f := by
    obtain ⟨P, inY, inZ, hP, _, _, hadm, _⟩ := exists_windowAdmissiblePushout E a b i f hi
    exact ⟨P, inZ, inY, hP.flip, hadm⟩

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, and `f : X ⟶ Y` in `Window E a b`, using `windowWaldhausenCategory E a b`,
`IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j)`.
Cofibrations are exactly the degreewise admissible monomorphisms. -/
theorem window_isCofibration_iff (a b : ℤ) {X Y : Window E a b} (f : X ⟶ Y) :
    letI := windowWaldhausenCategory E a b
    IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j) := Iff.rfl

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, and `f : X ⟶ Y` in `Window E a b`, using `windowWaldhausenCategory E a b`,
`IsWeakEquivalence f ↔ IsIso f`.
The weak-equivalence property of this fixed-window structure is the isomorphism property. -/
theorem window_isWeakEquivalence_iff (a b : ℤ) {X Y : Window E a b} (f : X ⟶ Y) :
    letI := windowWaldhausenCategory E a b
    IsWeakEquivalence f ↔ IsIso f := Iff.rfl

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b : ℤ`, `windowι E a b : Window E a b ⥤ Bounded E` is Waldhausen
exact from the fixed-window structure to `isoWaldhausenCategory E`. It preserves degreewise
admissible cofibrations, isomorphism weak equivalences, and pushout squares along
cofibrations. -/
theorem windowι_isWaldhausenExact (a b : ℤ) :
    letI := windowWaldhausenCategory E a b
    letI := isoWaldhausenCategory E
    (windowι E a b).IsWaldhausenExact := by
  let _ := windowWaldhausenCategory E a b
  let _ := isoWaldhausenCategory E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact (windowι E a b).map_isZero hX
  · intro X Y f hf
    exact (iso_isCofibration_iff E f.hom).mpr ((window_isCofibration_iff E a b f).mp hf)
  · intro X Y f hf
    let _ : IsIso f := (window_isWeakEquivalence_iff E a b f).mp hf
    exact (iso_isWeakEquivalence_iff E f.hom).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    exact (windowPushout_ι E a b (i := i) (f := f) (inY := inY) (inZ := inZ)
      ((window_isCofibration_iff E a b i).mp hi) hP.flip).flip

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b,j : ℤ`, `windowEval E a b j : Window E a b ⥤ E` is Waldhausen
exact from `windowWaldhausenCategory E a b` to `ExactCategory.waldhausenCategory E`.
Evaluation preserves zero objects, admissible cofibrations, isomorphism weak equivalences, and
pushout squares along cofibrations. -/
theorem windowEval_isWaldhausenExact (a b j : ℤ) :
    letI := windowWaldhausenCategory E a b
    letI := ExactCategory.waldhausenCategory E
    (windowEval E a b j).IsWaldhausenExact := by
  let _ := windowWaldhausenCategory E a b
  let _ := ExactCategory.waldhausenCategory E
  let _ : (windowEval E a b j).Additive := by
    dsimp only [windowEval, eval]
    infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact (windowEval E a b j).map_isZero hX
  · intro X Y f hf
    change ExactCategory.IsAdmissibleMono ((windowEval E a b j).map f)
    exact (window_isCofibration_iff E a b f).mp hf j
  · intro X Y f hf
    let _ : IsIso f := (window_isWeakEquivalence_iff E a b f).mp hf
    change IsIso ((windowEval E a b j).map f)
    infer_instance
  · intro X Y Z P i f inZ inY hi hP
    exact (windowPushout_term E a b (i := i) (f := f) (inY := inY) (inZ := inZ)
      ((window_isCofibration_iff E a b i).mp hi) hP.flip j).flip

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, `n : ℕ`, and `X : Stage (Window E a b) n`, using the fixed-window and bounded isomorphism
structures,
`(((windowι_isWaldhausenExact E a b).mapStage n).obj X).obj = X.obj ⋙ windowι E a b`.
The induced S-construction object is obtained by including each entry of the `Ar n`-diagram into `Bounded E`. -/
theorem windowι_mapStage_obj (a b : ℤ) (n : ℕ) :
    letI := windowWaldhausenCategory E a b
    letI := isoWaldhausenCategory E
    ∀ X : Stage (Window E a b) n, (((windowι_isWaldhausenExact E a b).mapStage n).obj X).obj =
      X.obj ⋙ windowι E a b := by
  let _ := windowWaldhausenCategory E a b
  let _ := isoWaldhausenCategory E
  intro X
  exact (windowι_isWaldhausenExact E a b).mapStage_obj n X

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, `n : ℕ`, and `f : X ⟶ Y` in `Stage (Window E a b) n`, with the fixed-window and bounded
isomorphism structures,
`(((windowι_isWaldhausenExact E a b).mapStage n).map f).hom = Functor.whiskerRight f.hom (windowι E a b)`.
The map retains every diagram component under the full inclusion. -/
theorem windowι_mapStage_map (a b : ℤ) (n : ℕ) :
    letI := windowWaldhausenCategory E a b
    letI := isoWaldhausenCategory E
    ∀ {X Y : Stage (Window E a b) n} (f : X ⟶ Y),
      (((windowι_isWaldhausenExact E a b).mapStage n).map f).hom =
        Functor.whiskerRight f.hom (windowι E a b) := by
  let _ := windowWaldhausenCategory E a b
  let _ := isoWaldhausenCategory E
  intro X Y f
  exact (windowι_isWaldhausenExact E a b).mapStage_map n f

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b,j : ℤ`, `n : ℕ`, and `X : Stage (Window E a b) n`, using the fixed-window and exact-category
structures,
`(((windowEval_isWaldhausenExact E a b j).mapStage n).obj X).obj = X.obj ⋙ windowEval E a b j`.
The evaluated S-construction diagram takes each window complex to its term in degree `j`. -/
theorem windowEval_mapStage_obj (a b j : ℤ) (n : ℕ) :
    letI := windowWaldhausenCategory E a b
    letI := ExactCategory.waldhausenCategory E
    ∀ X : Stage (Window E a b) n,
      (((windowEval_isWaldhausenExact E a b j).mapStage n).obj X).obj =
        X.obj ⋙ windowEval E a b j := by
  let _ := windowWaldhausenCategory E a b
  let _ := ExactCategory.waldhausenCategory E
  intro X
  exact (windowEval_isWaldhausenExact E a b j).mapStage_obj n X

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b,j : ℤ`, `n : ℕ`, and `f : X ⟶ Y` in `Stage (Window E a b) n`, using the fixed-window and exact-category
structures,
`(((windowEval_isWaldhausenExact E a b j).mapStage n).map f).hom = Functor.whiskerRight f.hom (windowEval E a b j)`.
Each evaluated component is the degree-`j` cochain component of the corresponding window-map entry. -/
theorem windowEval_mapStage_map (a b j : ℤ) (n : ℕ) :
    letI := windowWaldhausenCategory E a b
    letI := ExactCategory.waldhausenCategory E
    ∀ {X Y : Stage (Window E a b) n} (f : X ⟶ Y),
      (((windowEval_isWaldhausenExact E a b j).mapStage n).map f).hom =
        Functor.whiskerRight f.hom (windowEval E a b j) := by
  let _ := windowWaldhausenCategory E a b
  let _ := ExactCategory.waldhausenCategory E
  intro X Y f
  exact (windowEval_isWaldhausenExact E a b j).mapStage_map n f

end CochainComplex.Bounded

end
