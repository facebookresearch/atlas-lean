/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowTopCofiber
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequence

/-!
# Exact top-term and quotient functors of a cochain window

Let `E` be a preadditive exact category with a zero object and binary biproducts, and fix `a,b
: ℤ`. The top-single functor and the quotient by that single are exact for the window
structure with degreewise admissible cofibrations and isomorphism weak equivalences. The
quotient projection is an isomorphism in every degree other than `b`, while its degree-`b`
target is zero.

For a source cofibration `f:X→Y`, the relative corner map `X ⊔_{Top(X)} Top(Y) → Y` is a
cofibration. Together with the objectwise cofiber sequences, this gives the Waldhausen cofiber
functor sequence `Top ⟶ 𝟭 ⟶ Quotient`.

The relative cofibration condition is the one in C. Weibel, *The K-book*, V.1.1(b).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (a b : ℤ)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `K : Window E a b`, and `j
: ℤ` with `j≠b`,
`IsIso (((windowTopQuotientProjection E a b).app K).hom.hom.f j)`.
Quotienting the single top term preserves every other degree up to this projection isomorphism. -/
theorem windowTopQuotientProjection_isIso_f (K : Window E a b) (j : ℤ) (hj : j ≠ b) :
    IsIso (((windowTopQuotientProjection E a b).app K).hom.hom.f j) := by
  have hP := windowTopQuotient_term_isPushout E a b K j
  have hSingle : IsZero (((windowTopSingleFunctor E a b).obj K).obj.obj.X j) :=
    single_isZero_X E b (K.obj.obj.X b) j hj
  have hZero : IsZero ((0 : Window E a b).obj.obj.X j) :=
    (HomologicalComplex.eval E (.up ℤ) j).map_isZero
      ((ι E).map_isZero ((windowι E a b).map_isZero (isZero_zero (Window E a b))))
  let _ : IsIso (((windowTopZero E a b).app K).hom.hom.f j) := hSingle.isIso hZero _
  exact hP.isIso_inr_of_isIso

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, a window map `f:K→L`, and
`j : ℤ`, let `π=windowTopQuotientProjection E a b` and `Q=windowTopQuotientFunctor E a b`. Then
`(π.app K).hom.hom.f j ≫ (Q.map f).hom.hom.f j = f.hom.hom.f j ≫ (π.app L).hom.hom.f j`. -/
theorem windowTopQuotientProjection_naturality_f {K L : Window E a b} (f : K ⟶ L) (j : ℤ) :
    ((windowTopQuotientProjection E a b).app K).hom.hom.f j ≫
        ((windowTopQuotientFunctor E a b).map f).hom.hom.f j =
      f.hom.hom.f j ≫ ((windowTopQuotientProjection E a b).app L).hom.hom.f j :=
  (congrArg (fun t : K ⟶ (windowTopQuotientFunctor E a b).obj L => t.hom.hom.f j)
    ((windowTopQuotientProjection E a b).naturality f)).symm

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopSingleFunctor E a b` is Waldhausen exact on `Window E a b`. It sends a complex to
the single of its degree-`b` term, and preserves zero objects, degreewise admissible
cofibrations, isomorphism weak equivalences, and admissible pushouts. -/
theorem windowTopSingleFunctor_isWaldhausenExact :
    letI := windowWaldhausenCategory E a b
    (windowTopSingleFunctor E a b).IsWaldhausenExact := by
  let _ := windowWaldhausenCategory E a b
  let _ := ExactCategory.waldhausenCategory E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    have hTerm := (windowEval_isWaldhausenExact E a b b).map_isZero hX
    have hSingle := (HomologicalComplex.single E (.up ℤ) b).map_isZero hTerm
    exact IsZero.of_full_of_faithful_of_isZero (windowRaw E a b)
      ((windowTopSingleFunctor E a b).obj X) hSingle
  · intro X Y f hf
    apply (window_isCofibration_iff E a b _).mpr
    intro j
    by_cases hj : j = b
    · subst j
      change ExactCategory.IsAdmissibleMono (((single E b).map (f.hom.hom.f b)).hom.f b)
      rw [single_map_f_self]
      exact ExactCategory.admissibleMono_comp.comp_mem _ _
        (ExactCategory.IsAdmissibleMono.of_isIso (singleObjXSelf E b (X.obj.obj.X b)).hom)
        (ExactCategory.admissibleMono_comp.comp_mem _ _
          ((window_isCofibration_iff E a b f).mp hf b)
          (ExactCategory.IsAdmissibleMono.of_isIso (singleObjXSelf E b (Y.obj.obj.X b)).inv))
    · let e := (single_isZero_X E b (X.obj.obj.X b) j hj).isoZero
      let m := ((windowTopSingleFunctor E a b).map f).hom.hom.f j
      have h : ExactCategory.IsAdmissibleMono (e.inv ≫ m) := ExactCategory.IsAdmissibleMono.fromZero _
      have hComp := ExactCategory.admissibleMono_comp.comp_mem e.hom (e.inv ≫ m)
        (ExactCategory.IsAdmissibleMono.of_isIso e.hom) h
      change ExactCategory.IsAdmissibleMono m
      exact (e.hom_inv_id_assoc m) ▸ hComp
  · intro X Y f hf
    let _ : IsIso f := (window_isWeakEquivalence_iff E a b f).mp hf
    exact (window_isWeakEquivalence_iff E a b _).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    have hEval := (windowEval_isWaldhausenExact E a b b).map_pushout i f inZ inY hi hP
    have hSingle := hEval.map (HomologicalComplex.single E (.up ℤ) b)
    exact IsPushout.of_map_of_faithful (windowRaw E a b) hSingle

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
a window cofibration `f:K→L`, the map `(windowTopQuotientFunctor E a b).map f` is a
cofibration. Away from degree `b`, its components are identified with those of `f` through the
quotient-projection isomorphisms; the degree-`b` quotient terms are zero. -/
theorem windowTopQuotientFunctor_map_isCofibration {K L : Window E a b} (f : K ⟶ L) :
    letI := windowWaldhausenCategory E a b
    IsCofibration f → IsCofibration ((windowTopQuotientFunctor E a b).map f) := by
  let _ := windowWaldhausenCategory E a b
  intro hf
  apply (window_isCofibration_iff E a b _).mpr
  intro j
  let m := ((windowTopQuotientFunctor E a b).map f).hom.hom.f j
  by_cases hj : j = b
  · subst j
    let e := (windowTopQuotient_isZero_X_top E a b K).isoZero
    have h : ExactCategory.IsAdmissibleMono (e.inv ≫ m) := ExactCategory.IsAdmissibleMono.fromZero _
    have hComp := ExactCategory.admissibleMono_comp.comp_mem e.hom (e.inv ≫ m)
      (ExactCategory.IsAdmissibleMono.of_isIso e.hom) h
    change ExactCategory.IsAdmissibleMono m
    exact (e.hom_inv_id_assoc m) ▸ hComp
  · let _ := windowTopQuotientProjection_isIso_f E a b K j hj
    let _ := windowTopQuotientProjection_isIso_f E a b L j hj
    let eK := asIso (((windowTopQuotientProjection E a b).app K).hom.hom.f j)
    let eL := asIso (((windowTopQuotientProjection E a b).app L).hom.hom.f j)
    have hChart : m = eK.inv ≫ f.hom.hom.f j ≫ eL.hom := by
      apply (cancel_epi eK.hom).mp
      exact (windowTopQuotientProjection_naturality_f E a b f j).trans
        (eK.hom_inv_id_assoc (f.hom.hom.f j ≫ eL.hom)).symm
    have hComp := ExactCategory.admissibleMono_comp.comp_mem eK.inv
      (f.hom.hom.f j ≫ eL.hom) (ExactCategory.IsAdmissibleMono.of_isIso eK.inv)
      (ExactCategory.admissibleMono_comp.comp_mem _ _
        ((window_isCofibration_iff E a b f).mp hf j)
        (ExactCategory.IsAdmissibleMono.of_isIso eL.hom))
    change ExactCategory.IsAdmissibleMono m
    exact hChart.symm ▸ hComp

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `X : Window E a b`
with `IsZero X`,
`IsZero ((windowTopQuotientFunctor E a b).obj X)`.
The top-single zero-pushout construction preserves the zero property. -/
theorem windowTopQuotientFunctor_obj_isZero {X : Window E a b} (hX : IsZero X) :
    IsZero ((windowTopQuotientFunctor E a b).obj X) := by
  let _ := windowWaldhausenCategory E a b
  have hT := (windowTopSingleFunctor_isWaldhausenExact E a b).map_isZero hX
  let _ : IsIso ((windowTopInclusion E a b).app X) := hT.isIso hX _
  have hP := windowTopQuotient_isPushout E a b X
  let _ : IsIso ((windowTopQuotientFromZero E a b).app X) := hP.isIso_inl_of_isIso
  exact (isZero_zero (Window E a b)).of_iso
    (asIso ((windowTopQuotientFromZero E a b).app X)).symm

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, a
pushout `IsPushout i f inY inZ` in `Window E a b` with `windowCofibrations E a b i`, and `j :
ℤ`, the degree-`j` components of its four images under `windowTopQuotientFunctor E a b` form a
pushout square in `E`. -/
theorem windowTopQuotientFunctor_map_term_isPushout {X Y Z P : Window E a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : windowCofibrations E a b i) (hP : IsPushout i f inY inZ) (j : ℤ) :
    IsPushout (((windowTopQuotientFunctor E a b).map i).hom.hom.f j)
      (((windowTopQuotientFunctor E a b).map f).hom.hom.f j)
      (((windowTopQuotientFunctor E a b).map inY).hom.hom.f j)
      (((windowTopQuotientFunctor E a b).map inZ).hom.hom.f j) := by
  let Q := windowTopQuotientFunctor E a b
  by_cases hj : j = b
  · subst j
    let _ : IsIso ((Q.map i).hom.hom.f b) :=
      (windowTopQuotient_isZero_X_top E a b X).isIso
        (windowTopQuotient_isZero_X_top E a b Y) _
    let _ : IsIso ((Q.map inZ).hom.hom.f b) :=
      (windowTopQuotient_isZero_X_top E a b Z).isIso
        (windowTopQuotient_isZero_X_top E a b P) _
    apply IsPushout.of_horiz_isIso
    constructor
    have h : Q.map i ≫ Q.map inY = Q.map f ≫ Q.map inZ := by
      simpa only [← Q.map_comp] using congrArg Q.map hP.w
    exact congrArg (fun t : Q.obj X ⟶ Q.obj P => t.hom.hom.f b) h
  · let _ := windowTopQuotientProjection_isIso_f E a b X j hj
    let _ := windowTopQuotientProjection_isIso_f E a b Y j hj
    let _ := windowTopQuotientProjection_isIso_f E a b Z j hj
    let _ := windowTopQuotientProjection_isIso_f E a b P j hj
    let eX := asIso (((windowTopQuotientProjection E a b).app X).hom.hom.f j)
    let eY := asIso (((windowTopQuotientProjection E a b).app Y).hom.hom.f j)
    let eZ := asIso (((windowTopQuotientProjection E a b).app Z).hom.hom.f j)
    let eP := asIso (((windowTopQuotientProjection E a b).app P).hom.hom.f j)
    apply (windowPushout_term E a b hi hP j).of_iso eX eY eZ eP
    · exact (windowTopQuotientProjection_naturality_f E a b i j).symm
    · exact (windowTopQuotientProjection_naturality_f E a b f j).symm
    · exact (windowTopQuotientProjection_naturality_f E a b inY j).symm
    · exact (windowTopQuotientProjection_naturality_f E a b inZ j).symm

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and a pushout square
`IsPushout i f inY inZ` in `Window E a b` with `windowCofibrations E a b i`,
`IsPushout (Q.map i) (Q.map f) (Q.map inY) (Q.map inZ)`
holds for `Q=windowTopQuotientFunctor E a b`. The quotient functor preserves this pushout along a cofibration. -/
theorem windowTopQuotientFunctor_map_isPushout {X Y Z P : Window E a b}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : windowCofibrations E a b i) (hP : IsPushout i f inY inZ) :
    IsPushout ((windowTopQuotientFunctor E a b).map i) ((windowTopQuotientFunctor E a b).map f)
      ((windowTopQuotientFunctor E a b).map inY) ((windowTopQuotientFunctor E a b).map inZ) := by
  let Q := windowTopQuotientFunctor E a b
  let R := windowRaw E a b
  have w : R.map (Q.map i) ≫ R.map (Q.map inY) = R.map (Q.map f) ≫ R.map (Q.map inZ) := by
    have h : Q.map i ≫ Q.map inY = Q.map f ≫ Q.map inZ := by
      simpa only [← Q.map_comp] using congrArg Q.map hP.w
    simpa only [← R.map_comp] using congrArg R.map h
  let c : PushoutCocone (R.map (Q.map i)) (R.map (Q.map f)) :=
    PushoutCocone.mk (R.map (Q.map inY)) (R.map (Q.map inZ)) w
  have hc : IsColimit c := HomologicalComplex.isColimitOfEval _ c (fun j =>
    (PushoutCocone.isColimitMapCoconeEquiv c (HomologicalComplex.eval E (.up ℤ) j)).symm
      (windowTopQuotientFunctor_map_term_isPushout E a b hi hP j).isColimit)
  exact IsPushout.of_map_of_faithful R (IsPushout.of_isColimit hc)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowTopQuotientFunctor E a b` is Waldhausen exact on the fixed-window structure. It
preserves zero objects, cofibrations, isomorphism weak equivalences, and admissible pushout
squares. -/
theorem windowTopQuotientFunctor_isWaldhausenExact :
    letI := windowWaldhausenCategory E a b
    (windowTopQuotientFunctor E a b).IsWaldhausenExact := by
  let _ := windowWaldhausenCategory E a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact windowTopQuotientFunctor_obj_isZero E a b
  · exact windowTopQuotientFunctor_map_isCofibration E a b
  · intro X Y f hf
    let _ : IsIso f := (window_isWeakEquivalence_iff E a b f).mp hf
    exact (window_isWeakEquivalence_iff E a b _).mpr inferInstance
  · intro X Y Z P i f inZ inY hi hP
    exact (windowTopQuotientFunctor_map_isPushout E a b
      ((window_isCofibration_iff E a b i).mp hi) hP.flip).flip

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
any window map `f:X→Y`, the pushout of `(windowTopInclusion E a b).app X : Top(X)→X` and
`(windowTopSingleFunctor E a b).map f : Top(X)→Top(Y)` exists. The top inclusion is a
cofibration, so this relative corner can be formed. -/
theorem windowTopBase_hasPushout {X Y : Window E a b} (f : X ⟶ Y) :
    HasPushout ((windowTopInclusion E a b).app X) ((windowTopSingleFunctor E a b).map f) := by
  let _ := windowWaldhausenCategory E a b
  obtain ⟨P, inT, inX, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
    ((windowTopInclusion E a b).app X) (windowTopInclusion_isCofibration E a b X)
    ((windowTopSingleFunctor E a b).obj Y) ((windowTopSingleFunctor E a b).map f)
  exact hP.flip.hasPushout

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
a window cofibration `f:X→Y`, the map `X ⊔_{Top(X)} Top(Y) → Y` induced by `f` and the top
inclusion at `Y` is a cofibration. It is the `pushout.desc` map with commutation supplied by
naturality of `windowTopInclusion E a b`. -/
theorem windowTopBaseCorner_isCofibration {X Y : Window E a b} (f : X ⟶ Y) :
    letI := windowWaldhausenCategory E a b
    IsCofibration f →
      letI := windowTopBase_hasPushout E a b f
      IsCofibration (pushout.desc f ((windowTopInclusion E a b).app Y)
        ((windowTopInclusion E a b).naturality f).symm) := by
  let _ := windowWaldhausenCategory E a b
  intro hf
  let _ := windowTopBase_hasPushout E a b f
  let i := (windowTopInclusion E a b).app X
  let u := (windowTopSingleFunctor E a b).map f
  let d := pushout.desc f ((windowTopInclusion E a b).app Y)
    ((windowTopInclusion E a b).naturality f).symm
  have hi : windowCofibrations E a b i :=
    (window_isCofibration_iff E a b i).mp (windowTopInclusion_isCofibration E a b X)
  apply (window_isCofibration_iff E a b d).mpr
  intro j
  let m := d.hom.hom.f j
  let l := (pushout.inl i u).hom.hom.f j
  let r := (pushout.inr i u).hom.hom.f j
  have hP := windowPushout_term E a b hi (IsPushout.of_hasPushout i u) j
  have hOld : l ≫ m = f.hom.hom.f j := congrArg (fun t : X ⟶ Y => t.hom.hom.f j)
    (pushout.inl_desc f ((windowTopInclusion E a b).app Y)
      ((windowTopInclusion E a b).naturality f).symm)
  have hNew : r ≫ m = ((windowTopInclusion E a b).app Y).hom.hom.f j :=
    congrArg (fun t : (windowTopSingleFunctor E a b).obj Y ⟶ Y => t.hom.hom.f j)
      (pushout.inr_desc f ((windowTopInclusion E a b).app Y)
        ((windowTopInclusion E a b).naturality f).symm)
  by_cases hj : j = b
  · subst j
    let _ : IsIso (i.hom.hom.f b) := by
      rw [windowTopInclusion_f_self]
      exact (singleObjXSelf E b (X.obj.obj.X b)).isIso_hom
    let _ : IsIso r := hP.isIso_inr_of_isIso
    have hI : IsIso (((windowTopInclusion E a b).app Y).hom.hom.f b) := by
      rw [windowTopInclusion_f_self]
      exact (singleObjXSelf E b (Y.obj.obj.X b)).isIso_hom
    have hComp : IsIso (r ≫ m) := hNew.symm ▸ hI
    let _ : IsIso m := (MorphismProperty.isomorphisms E).of_precomp
      (W' := MorphismProperty.isomorphisms E) r m (inferInstance : IsIso r) hComp
    exact ExactCategory.IsAdmissibleMono.of_isIso m
  · have hX : IsZero (((windowTopSingleFunctor E a b).obj X).obj.obj.X j) :=
      single_isZero_X E b (X.obj.obj.X b) j hj
    have hY : IsZero (((windowTopSingleFunctor E a b).obj Y).obj.obj.X j) :=
      single_isZero_X E b (Y.obj.obj.X b) j hj
    let _ : IsIso (u.hom.hom.f j) := hX.isIso hY _
    let _ : IsIso l := hP.isIso_inl_of_isIso
    let e := asIso l
    have hChart : m = e.inv ≫ f.hom.hom.f j := by
      apply (cancel_epi e.hom).mp
      exact hOld.trans (e.hom_inv_id_assoc (f.hom.hom.f j)).symm
    have hComp := ExactCategory.admissibleMono_comp.comp_mem e.inv (f.hom.hom.f j)
      (ExactCategory.IsAdmissibleMono.of_isIso e.inv)
      ((window_isCofibration_iff E a b f).mp hf j)
    change ExactCategory.IsAdmissibleMono m
    exact hChart.symm ▸ hComp

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
the exact functors `windowTopSingleFunctor E a b`, `𝟭 (Window E a b)`, and
`windowTopQuotientFunctor E a b`, with arrows `windowTopInclusion E a b` and
`windowTopQuotientProjection E a b`, form a Waldhausen cofiber functor sequence. Components
are cofiber sequences, and every source cofibration gives a cofibration `X ⊔_{Top(X)} Top(Y) →
Y` on the relative corner. -/
theorem windowTopCofiberFunctorSequence :
    letI := windowWaldhausenCategory E a b
    IsWaldhausenCofiberFunctorSequence (windowTopSingleFunctor E a b) (𝟭 (Window E a b))
      (windowTopQuotientFunctor E a b) (windowTopInclusion E a b)
      (windowTopQuotientProjection E a b) := by
  let _ := windowWaldhausenCategory E a b
  refine {
    sourceExact := windowTopSingleFunctor_isWaldhausenExact E a b
    middleExact := Functor.IsWaldhausenExact.id
    quotientExact := windowTopQuotientFunctor_isWaldhausenExact E a b
    objectwise := windowTopQuotient_isCofiberSequence E a b
    baseCofibration := ?_ }
  intro X Y f hf
  exact windowTopBaseCorner_isCofibration E a b f hf

end CochainComplex.Bounded

end
