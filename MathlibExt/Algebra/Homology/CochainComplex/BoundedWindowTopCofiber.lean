/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowWaldhausen
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedSingle
public import MathlibExt.CategoryTheory.Waldhausen.FunctorCategoryCofibrationPushout

/-!
# Top-term cofiber of a fixed-window cochain complex

Let `E` be a preadditive category with a zero object, and let `K` be supported in an integer
window `[a,b]`. Its degree-`b` term, placed in a single complex, includes naturally into `K`:
the outgoing differential vanishes by upper support. The inclusion is identified with the
identity of `K^b` through the single-term chart.

If `E` is exact and has binary biproducts, the inclusion is a degreewise admissible
cofibration. Its pushout along the zero map forms a natural top quotient. The quotient square
is a pushout in every degree, its degree-`b` term is zero, and it is supported in `[a,b−1]`.
This gives a quotient functor into the strictly smaller window and degreewise admissible exact
sequences, including reversed-window cases.

See C. Weibel, *The K-book*, V.2.2, for this filtration by top terms.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E] [HasZeroObject E]
variable (a b : ℤ)

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object, `a,b : ℤ`, and `K :
Window E a b`,
`windowSupport E a b ((single E b).obj (K.obj.obj.X b))`.
The single is supported at degree `b`; if that degree lies outside the window, the term is zero by the support of `K`.
-/
theorem windowTopSingle_support (K : Window E a b) :
    windowSupport E a b ((single E b).obj (K.obj.obj.X b)) := by
  intro j hj
  by_cases h : j = b
  · subst j
    exact (K.property b hj).of_iso (singleObjXSelf E b (K.obj.obj.X b))
  · exact single_isZero_X E b (K.obj.obj.X b) j h

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object and
`a,b : ℤ`, `windowTopSingleFunctor E a b : Window E a b ⥤ Window E a b` is the support lift of
`windowEval E a b b ⋙ single E b`. It sends a complex to the single complex on its degree-`b`
term and a map to its single degree-`b` component. -/
def windowTopSingleFunctor : Window E a b ⥤ Window E a b :=
  (windowSupport E a b).lift (windowEval E a b b ⋙ single E b)
    (windowTopSingle_support E a b)

omit [HasZeroObject E] in
/-- For a preadditive category `E`, `a,b : ℤ`, `K : Window E a b`, and `j : ℤ` with `(ComplexShape.up ℤ).Rel b j`,
`𝟙 (K.obj.obj.X b) ≫ K.obj.obj.d b j = 0`.
The relation means `j=b+1`, whose term is zero by the upper support bound. -/
theorem windowTop_outgoing_zero (K : Window E a b) (j : ℤ) (hj : (ComplexShape.up ℤ).Rel b j) :
    (𝟙 (K.obj.obj.X b)) ≫ K.obj.obj.d b j = 0 := by
  have hbj : b < j := by change b + 1 = j at hj; omega
  exact (K.property j (Or.inr hbj)).eq_of_tgt _ _

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object,
`a,b : ℤ`, and `K : Window E a b`, the cochain map from the single complex on `K^b` in degree
`b` to `K` is `HomologicalComplex.mkHomFromSingle (𝟙 (K.obj.obj.X b)) (windowTop_outgoing_zero
E a b K)`. The upper support condition supplies the vanishing outgoing differential. -/
def windowTopInclusionRaw (K : Window E a b) :
    ((single E b).obj (K.obj.obj.X b)).obj ⟶ K.obj.obj :=
  HomologicalComplex.mkHomFromSingle (𝟙 (K.obj.obj.X b)) (windowTop_outgoing_zero E a b K)

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object, `a,b : ℤ`, and `K :
Window E a b`,
`(windowTopInclusionRaw E a b K).f b = (singleObjXSelf E b (K.obj.obj.X b)).hom`.
The top-degree component identifies the single's supporting term with `K^b`. -/
theorem windowTopInclusionRaw_f_self (K : Window E a b) :
    (windowTopInclusionRaw E a b K).f b = (singleObjXSelf E b (K.obj.obj.X b)).hom := by
  rw [windowTopInclusionRaw, HomologicalComplex.mkHomFromSingle_f, Category.comp_id]
  rfl

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object and
`a,b : ℤ`, `windowTopInclusion E a b : windowTopSingleFunctor E a b ⟶ 𝟭 (Window E a b)` has
component the lifted cochain inclusion `windowTopInclusionRaw E a b K`. Its naturality
expresses commutation of each window map with the single of its top component. -/
def windowTopInclusion : windowTopSingleFunctor E a b ⟶ 𝟭 (Window E a b) where
  app K := ObjectProperty.homMk (ObjectProperty.homMk (windowTopInclusionRaw E a b K))
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.from_single_hom_ext
    change ((single E b).map (f.hom.hom.f b)).hom.f b ≫
        (windowTopInclusionRaw E a b L).f b =
      (windowTopInclusionRaw E a b K).f b ≫ f.hom.hom.f b
    rw [single_map_f_self, windowTopInclusionRaw_f_self, windowTopInclusionRaw_f_self]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object, `a,b : ℤ`, and `K :
Window E a b`,
`((windowTopInclusion E a b).app K).hom.hom = windowTopInclusionRaw E a b K`.
The natural transformation uses the cochain map from the degree-`b` single into `K`. -/
theorem windowTopInclusion_hom (K : Window E a b) :
    ((windowTopInclusion E a b).app K).hom.hom = windowTopInclusionRaw E a b K := rfl

/-- For a preadditive category `E : Type uE` with morphisms in universe `vE` and a zero object, `a,b : ℤ`, and `K :
Window E a b`,
`((windowTopInclusion E a b).app K).hom.hom.f b = (singleObjXSelf E b (K.obj.obj.X b)).hom`.
Thus the component at the top supporting degree is an isomorphism. -/
theorem windowTopInclusion_f_self (K : Window E a b) :
    ((windowTopInclusion E a b).app K).hom.hom.f b =
      (singleObjXSelf E b (K.obj.obj.X b)).hom := windowTopInclusionRaw_f_self E a b K

/-- For a preadditive category `E` with a zero object and `a,b : ℤ`, `windowTopZero E a b` is the
zero natural transformation from `windowTopSingleFunctor E a b` to the constant functor at the
selected zero of `Window E a b`. -/
def windowTopZero : windowTopSingleFunctor E a b ⟶
    (Functor.const (Window E a b)).obj (0 : Window E a b) := 0

variable [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`K : Window E a b`, `(windowTopInclusion E a b).app K` is a cofibration in the fixed-window
structure. Its top component is a single-term isomorphism; every other source component is
zero, so all components are admissible monomorphisms. -/
theorem windowTopInclusion_isCofibration (K : Window E a b) :
    letI := windowWaldhausenCategory E a b
    IsCofibration ((windowTopInclusion E a b).app K) := by
  let _ := windowWaldhausenCategory E a b
  apply (window_isCofibration_iff E a b _).mpr
  intro j
  by_cases hj : j = b
  · subst j
    rw [windowTopInclusion_f_self]
    let e := singleObjXSelf E b (K.obj.obj.X b)
    let _ : IsIso e.hom := e.isIso_hom
    exact ExactCategory.IsAdmissibleMono.of_isIso e.hom
  · let e := (single_isZero_X E b (K.obj.obj.X b) j hj).isoZero
    let m := ((windowTopInclusion E a b).app K).hom.hom.f j
    have h : ExactCategory.IsAdmissibleMono (e.inv ≫ m) := ExactCategory.IsAdmissibleMono.fromZero _
    have hComp := ExactCategory.admissibleMono_comp.comp_mem e.hom (e.inv ≫ m)
      (ExactCategory.IsAdmissibleMono.of_isIso e.hom) h
    change ExactCategory.IsAdmissibleMono m
    exact (e.hom_inv_id_assoc m) ▸ hComp

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
the natural transformations `windowTopZero E a b` and `windowTopInclusion E a b` have a
pushout in the functor category `Window E a b ⥤ Window E a b`. Objectwise admissibility of the
top inclusions supplies these zero pushouts. -/
theorem windowTopFunctorHasPushout : HasPushout (windowTopZero E a b) (windowTopInclusion E a b) := by
  let _ := windowWaldhausenCategory E a b
  exact Waldhausen.functorCategoryHasPushoutOfCofibrations (windowTopInclusion E a b)
    (windowTopZero E a b) (windowTopInclusion_isCofibration E a b)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopQuotientFunctor E a b : Window E a b ⥤ Window E a b` is the chosen functor-category
pushout of `windowTopZero E a b : Top→0` and `windowTopInclusion E a b : Top→𝟭`. Its object at
`K` is the cofiber quotient of the top single `Top(K)→K`. -/
def windowTopQuotientFunctor : Window E a b ⥤ Window E a b := by
  let _ := windowTopFunctorHasPushout E a b
  exact pushout (windowTopZero E a b) (windowTopInclusion E a b)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopQuotientProjection E a b : 𝟭 (Window E a b) ⟶ windowTopQuotientFunctor E a b` is the
chosen zero-pushout leg from the complex to its quotient by the top single. -/
def windowTopQuotientProjection : 𝟭 (Window E a b) ⟶ windowTopQuotientFunctor E a b := by
  let _ := windowTopFunctorHasPushout E a b
  exact pushout.inr (windowTopZero E a b) (windowTopInclusion E a b)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopQuotientFromZero E a b` is the natural transformation from the constant zero functor
to `windowTopQuotientFunctor E a b`, given by the other leg of the top-single zero pushout. -/
def windowTopQuotientFromZero : (Functor.const (Window E a b)).obj (0 : Window E a b) ⟶
    windowTopQuotientFunctor E a b := by
  let _ := windowTopFunctorHasPushout E a b
  exact pushout.inl (windowTopZero E a b) (windowTopInclusion E a b)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`K : Window E a b`, the square with top-left object `Top(K)`, maps to zero and to `K`, and
bottom-right object `(windowTopQuotientFunctor E a b).obj K` is a pushout. Its four arrows are
the components of `windowTopZero`, `windowTopInclusion`, `windowTopQuotientFromZero`, and
`windowTopQuotientProjection`. -/
theorem windowTopQuotient_isPushout (K : Window E a b) :
    IsPushout ((windowTopZero E a b).app K) ((windowTopInclusion E a b).app K)
      ((windowTopQuotientFromZero E a b).app K) ((windowTopQuotientProjection E a b).app K) := by
  let _ := windowWaldhausenCategory E a b
  exact Waldhausen.functorCategoryPushout_app_isPushout (windowTopInclusion E a b)
    (windowTopZero E a b) (windowTopInclusion_isCofibration E a b) K

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
the arrows
`(windowTopInclusion E a b).app K` and `(windowTopQuotientProjection E a b).app K`
form a cofiber sequence in the fixed-window structure. The first is a cofibration and the second is its selected
quotient map from the zero pushout. -/
theorem windowTopQuotient_isCofiberSequence (K : Window E a b) :
    letI := windowWaldhausenCategory E a b
    IsCofiberSequence ((windowTopInclusion E a b).app K)
      ((windowTopQuotientProjection E a b).app K) := by
  let _ := windowWaldhausenCategory E a b
  exact ⟨windowTopInclusion_isCofibration E a b K, (windowTopZero E a b).app K,
    (windowTopQuotientFromZero E a b).app K, windowTopQuotient_isPushout E a b K⟩

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `K :
Window E a b`, and `j : ℤ`, the degree-`j` components of the top-single zero square form a
pushout in `E`. The four maps are the components of `windowTopZero`, `windowTopInclusion`,
`windowTopQuotientFromZero`, and `windowTopQuotientProjection` at `K`. -/
theorem windowTopQuotient_term_isPushout (K : Window E a b) (j : ℤ) :
    IsPushout (((windowTopZero E a b).app K).hom.hom.f j)
      (((windowTopInclusion E a b).app K).hom.hom.f j)
      (((windowTopQuotientFromZero E a b).app K).hom.hom.f j)
      (((windowTopQuotientProjection E a b).app K).hom.hom.f j) := by
  let _ := windowWaldhausenCategory E a b
  exact (windowPushout_term E a b
    ((window_isCofibration_iff E a b _).mp (windowTopInclusion_isCofibration E a b K))
    (windowTopQuotient_isPushout E a b K).flip j).flip

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
`IsZero (((windowTopQuotientFunctor E a b).obj K).obj.obj.X b)`.
The top component of the single inclusion is an isomorphism, so its pushout along zero has a zero degree-`b` object. -/
theorem windowTopQuotient_isZero_X_top (K : Window E a b) :
    IsZero (((windowTopQuotientFunctor E a b).obj K).obj.obj.X b) := by
  have hP := windowTopQuotient_term_isPushout E a b K b
  let _ : IsIso (((windowTopInclusion E a b).app K).hom.hom.f b) := by
    rw [windowTopInclusion_f_self]
    exact (singleObjXSelf E b (K.obj.obj.X b)).isIso_hom
  let _ : IsIso (((windowTopQuotientFromZero E a b).app K).hom.hom.f b) := hP.isIso_inl_of_isIso
  have hZero : IsZero ((0 : Window E a b).obj.obj.X b) :=
    (HomologicalComplex.eval E (.up ℤ) b).map_isZero
      ((ι E).map_isZero ((windowι E a b).map_isZero (isZero_zero (Window E a b))))
  exact hZero.of_iso (asIso (((windowTopQuotientFromZero E a b).app K).hom.hom.f b)).symm

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
`windowSupport E a (b−1) ((windowTopQuotientFunctor E a b).obj K).obj`.
The quotient retains the lower support bound `a`, has zero term at `b`, and is zero in all degrees above `b−1`. -/
theorem windowTopQuotient_support (K : Window E a b) :
    windowSupport E a (b - 1) ((windowTopQuotientFunctor E a b).obj K).obj := by
  intro j hj
  rcases hj with hj | hj
  · exact ((windowTopQuotientFunctor E a b).obj K).property j (Or.inl hj)
  · by_cases h : j = b
    · subst j
      exact windowTopQuotient_isZero_X_top E a b K
    · exact ((windowTopQuotientFunctor E a b).obj K).property j (Or.inr (by omega))

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopQuotient E a b : Window E a b ⥤ Window E a (b−1)` is the support lift of
`windowTopQuotientFunctor E a b ⋙ windowι E a b`. It retains the chosen top quotient and its
maps while recording the proved upper cutoff `b−1`. -/
def windowTopQuotient : Window E a b ⥤ Window E a (b - 1) :=
  (windowSupport E a (b - 1)).lift (windowTopQuotientFunctor E a b ⋙ windowι E a b)
    (windowTopQuotient_support E a b)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `K : Window E a b`,
`((windowTopQuotient E a b).obj K).obj = ((windowTopQuotientFunctor E a b).obj K).obj`.
The strict support lift retains the same bounded cochain quotient object. -/
theorem windowTopQuotient_obj (K : Window E a b) :
    ((windowTopQuotient E a b).obj K).obj = ((windowTopQuotientFunctor E a b).obj K).obj := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `f:K→L` in `Window E a
b`,
`((windowTopQuotient E a b).map f).hom = ((windowTopQuotientFunctor E a b).map f).hom`.
The quotient map is retained when its target category is the smaller support window. -/
theorem windowTopQuotient_map {K L : Window E a b} (f : K ⟶ L) :
    ((windowTopQuotient E a b).map f).hom = ((windowTopQuotientFunctor E a b).map f).hom := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `K : Window E a b`, and `j
: ℤ`, the sequence
`Top(K)^j → K^j → Quotient(K)^j`
formed by the degree components of `windowTopInclusion E a b` and `windowTopQuotientProjection E a b` is admissible
exact in `E`. Their composite is zero by the cofiber-sequence equation, and evaluation preserves the admissible cofiber
sequence. -/
theorem windowTopQuotient_term_isAdmissibleExact (K : Window E a b) (j : ℤ) :
    letI := windowWaldhausenCategory E a b
    ExactCategory.IsAdmissibleExact (ShortComplex.mk
      (((windowTopInclusion E a b).app K).hom.hom.f j)
      (((windowTopQuotientProjection E a b).app K).hom.hom.f j) (by
        exact congrArg (fun t : (windowTopSingleFunctor E a b).obj K ⟶
          (windowTopQuotientFunctor E a b).obj K => t.hom.hom.f j)
          (windowTopQuotient_isCofiberSequence E a b K).comp_eq_zero)) := by
  let _ := windowWaldhausenCategory E a b
  let _ := ExactCategory.waldhausenCategory E
  exact ExactCategory.isAdmissibleExact_of_isCofibrationSequence
    ((windowEval_isWaldhausenExact E a b j).map_cofibrationSequence
      (windowTopQuotient_isCofiberSequence E a b K))

end CochainComplex.Bounded

end
