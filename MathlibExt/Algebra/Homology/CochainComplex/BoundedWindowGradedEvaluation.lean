/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedSingleWaldhausen
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowTopIteration
public import MathlibExt.CategoryTheory.Waldhausen.Pi

/-!
# Finite graded evaluation and supported single complexes

For `a,b : ℤ`, set `L=(b−a+1).toNat` and `d_i=b−i` for `i : Fin L`. These degrees lie in
`[a,b]`, are distinct, and include every integer in that interval. For a category `E` with
zero morphisms, evaluating a window complex in these degrees gives a functor `Window E a b ⥤
(Fin L → E)`.

If `E` has a zero object, the single complex in any supported degree lifts to the window
category. Evaluating it in its supporting degree is naturally the identity of `E`; its other
graded terms and map components are zero. If `E` is preadditive and exact with binary
biproducts, the graded evaluation and supported-single functors preserve the fixed-window
cofibrations, isomorphism weak equivalences, and admissible pushouts. The definitions include
empty and reversed windows.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded

/-- For `a,b : ℤ`, `L=(b−a+1).toNat`, and `i : Fin L`,
`windowGradedDegree a b i = b−(i.val : ℤ)`.
The graded coordinates list the integer window in descending order. -/
def windowGradedDegree (a b : ℤ) (i : Fin (WindowTopIteration.length a b)) : ℤ :=
  b - (i.val : ℤ)

/-- For `a,b : ℤ` and `i : Fin ((b−a+1).toNat)`,
`a≤windowGradedDegree a b i ∧ windowGradedDegree a b i≤b`.
Thus the degree `b−i` lies in the closed interval `[a,b]`. -/
theorem windowGradedDegree_mem (a b : ℤ) (i : Fin (WindowTopIteration.length a b)) :
    a ≤ windowGradedDegree a b i ∧ windowGradedDegree a b i ≤ b := by
  have hi := i.isLt
  change i.val < (b - a + 1).toNat at hi
  dsimp only [windowGradedDegree]
  omega

/-- For `a,b : ℤ`, the map `windowGradedDegree a b : Fin ((b−a+1).toNat) → ℤ` is injective.
Equality of the degrees `b−i` and `b−j` forces equality of the finite indices. -/
theorem windowGradedDegree_injective (a b : ℤ) :
    Function.Injective (windowGradedDegree a b) := by
  intro i k h
  apply Fin.ext
  dsimp only [windowGradedDegree] at h
  omega

/-- For `a,b,j : ℤ` with `a≤j` and `j≤b`, there exists `i : Fin ((b−a+1).toNat)` such that
`windowGradedDegree a b i=j`. The coordinate has numerical value `b−j`. -/
theorem exists_windowGradedDegree (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) :
    ∃ i : Fin (WindowTopIteration.length a b), windowGradedDegree a b i = j := by
  have hi : (b - j).toNat < WindowTopIteration.length a b := by
    dsimp only [WindowTopIteration.length]
    omega
  refine ⟨⟨(b - j).toNat, hi⟩, ?_⟩
  dsimp only [windowGradedDegree]
  omega

variable (E : Type uE) [Category.{vE} E]

section Evaluation

variable [HasZeroMorphisms E]

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms and `a,b : ℤ`,
the functor `windowGradedEval E a b : Window E a b ⥤ (Fin ((b−a+1).toNat) → E)` evaluates a
complex in coordinate `i` at degree `windowGradedDegree a b i=b−i`. It applies the same
evaluation to cochain maps. -/
def windowGradedEval (a b : ℤ) :
    Window E a b ⥤ (Fin (WindowTopIteration.length a b) → E) :=
  Functor.pi' (fun i => windowEval E a b (windowGradedDegree a b i))

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a,b : ℤ`, and `K : Window E a b`,
`(windowGradedEval E a b).obj K = fun i => K.obj.obj.X (windowGradedDegree a b i)`.
The output family consists of the cochain terms in descending window degrees. -/
theorem windowGradedEval_obj (a b : ℤ) (K : Window E a b) :
    (windowGradedEval E a b).obj K =
      fun i => K.obj.obj.X (windowGradedDegree a b i) := rfl

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a,b : ℤ`, and a window map
`f:K→L`,
`(windowGradedEval E a b).map f = fun i => f.hom.hom.f (windowGradedDegree a b i)`.
Each family component is the cochain map component in its descending degree. -/
theorem windowGradedEval_map (a b : ℤ) {K L : Window E a b} (f : K ⟶ L) :
    (windowGradedEval E a b).map f =
      fun i => f.hom.hom.f (windowGradedDegree a b i) := rfl

/-- For a category `E : Type uE` with morphisms in universe `vE` and zero morphisms, `a,b : ℤ`, and `i : I=Fin
((b−a+1).toNat)`,
`windowGradedEval E a b ⋙ Pi.eval (fun _ : I => E) i = windowEval E a b (windowGradedDegree a b i)`.
Projection to a family coordinate is exactly evaluation in its corresponding integer degree. -/
theorem windowGradedEval_comp_eval (a b : ℤ) (i : Fin (WindowTopIteration.length a b)) :
    windowGradedEval E a b ⋙ Pi.eval (fun _ : Fin (WindowTopIteration.length a b) => E) i =
      windowEval E a b (windowGradedDegree a b i) := rfl

end Evaluation

section Single

variable [HasZeroMorphisms E] [HasZeroObject E]

/-- For a category `E` with zero morphisms and a zero object, `a,b,j : ℤ` with `a≤j≤b`, and `X :
E`, the bounded single complex `(single E j).obj X` satisfies `windowSupport E a b`. Its only
potentially nonzero term is in the supported degree `j`. -/
theorem windowSingle_support (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) (X : E) :
    windowSupport E a b ((single E j).obj X) := by
  intro i hi
  exact single_isZero_X E j X i (by omega)

/-- For a category `E` with zero morphisms and a zero object and `a,b,j : ℤ` with `a≤j≤b`,
`windowSingle E a b j ha hb : E ⥤ Window E a b` sends an object to its single cochain complex
in degree `j`. The degree inequalities provide its fixed-window support. -/
def windowSingle (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) : E ⥤ Window E a b :=
  ObjectProperty.lift (windowSupport E a b) (single E j) (windowSingle_support E a b j ha hb)

/-- For a category `E` with zero morphisms and a zero object and `a,b,j : ℤ` with `a≤j≤b`,
`windowSingle E a b j ha hb ⋙ windowι E a b = single E j`.
The full inclusion of the supported single is the same bounded single-degree embedding. -/
theorem windowSingle_comp_windowι (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) :
    windowSingle E a b j ha hb ⋙ windowι E a b = single E j := rfl

/-- For a category `E` with zero morphisms and a zero object, `a,b,j : ℤ` with `a≤j≤b`, and `X : E`,
`((windowSingle E a b j ha hb).obj X).obj.obj = (HomologicalComplex.single E (.up ℤ) j).obj X`.
The underlying complex is concentrated in degree `j` with value `X`. -/
theorem windowSingle_obj_obj (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) (X : E) :
    ((windowSingle E a b j ha hb).obj X).obj.obj =
      (HomologicalComplex.single E (.up ℤ) j).obj X := rfl

/-- For a category `E` with zero morphisms and a zero object, `a,b,j : ℤ` with `a≤j≤b`, and `f:X→Y` in `E`,
`((windowSingle E a b j ha hb).map f).hom.hom = (HomologicalComplex.single E (.up ℤ) j).map f`.
The source and target support lifts retain the single-degree cochain map. -/
theorem windowSingle_map_hom (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b)
    {X Y : E} (f : X ⟶ Y) :
    ((windowSingle E a b j ha hb).map f).hom.hom =
      (HomologicalComplex.single E (.up ℤ) j).map f := rfl

/-- For a category `E` with zero morphisms and a zero object and `a,b,j : ℤ` with `a≤j≤b`, there is a natural
isomorphism
`windowSingle E a b j ha hb ⋙ windowEval E a b j ≅ 𝟭 E`.
It identifies the supporting term of the single complex with its coefficient object. -/
def windowSingleCompEvalIsoSelf (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) :
    windowSingle E a b j ha hb ⋙ windowEval E a b j ≅ 𝟭 E :=
  singleCompEvalIsoSelf E j

/-- For a category `E` with zero morphisms and a zero object, `a,b,j : ℤ` with `a≤j≤b`, and `X : E`,
`(windowSingleCompEvalIsoSelf E a b j ha hb).hom.app X = (singleObjXSelf E j X).hom`.
The forward evaluation map is the supporting-term identification. -/
theorem windowSingleCompEvalIsoSelf_hom_app (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) (X : E) :
    (windowSingleCompEvalIsoSelf E a b j ha hb).hom.app X =
      (singleObjXSelf E j X).hom := rfl

/-- For a category `E` with zero morphisms and a zero object, `a,b,j : ℤ` with `a≤j≤b`, and `X : E`,
`(windowSingleCompEvalIsoSelf E a b j ha hb).inv.app X = (singleObjXSelf E j X).inv`.
The inverse places `X` into the supporting term of the single complex. -/
theorem windowSingleCompEvalIsoSelf_inv_app (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) (X : E) :
    (windowSingleCompEvalIsoSelf E a b j ha hb).inv.app X =
      (singleObjXSelf E j X).inv := rfl

/-- For a category `E` with zero morphisms and a zero object, `a,b,j : ℤ` with `a≤j≤b`, `X : E`, and `k : ℤ` with `k≠j`,
`IsZero (((windowSingle E a b j ha hb).obj X).obj.obj.X k)`.
The supported single has zero terms outside its specified degree. -/
theorem windowSingle_isZero_X (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b)
    (X : E) (k : ℤ) (hk : k ≠ j) :
    IsZero (((windowSingle E a b j ha hb).obj X).obj.obj.X k) :=
  single_isZero_X E j X k hk

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, and `i : Fin
((b−a+1).toNat)`, `windowGradedSingle E a b i : E ⥤ Window E a b` is the supported single
functor in degree `windowGradedDegree a b i=b−i`. The proved bounds on that graded degree
supply its support witness. -/
def windowGradedSingle (a b : ℤ) (i : Fin (WindowTopIteration.length a b)) : E ⥤ Window E a b :=
  windowSingle E a b (windowGradedDegree a b i)
    (windowGradedDegree_mem a b i).1 (windowGradedDegree_mem a b i).2

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, `I=Fin ((b−a+1).toNat)`, and `i : I`, there is
a natural isomorphism
`windowGradedSingle E a b i ⋙ windowGradedEval E a b ⋙ Pi.eval (fun _ : I => E) i ≅ 𝟭 E`.
The matching graded coordinate evaluates the single in its supporting degree `b−i`. -/
def windowGradedSingleCompEvalIsoSelf (a b : ℤ) (i : Fin (WindowTopIteration.length a b)) :
    windowGradedSingle E a b i ⋙ windowGradedEval E a b ⋙
      Pi.eval (fun _ : Fin (WindowTopIteration.length a b) => E) i ≅ 𝟭 E :=
  singleCompEvalIsoSelf E (windowGradedDegree a b i)

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, `i : Fin ((b−a+1).toNat)`, and `X : E`,
`(windowGradedSingleCompEvalIsoSelf E a b i).hom.app X = (singleObjXSelf E (windowGradedDegree a b i) X).hom`.
It is the single-term identification in degree `b−i`. -/
theorem windowGradedSingleCompEvalIsoSelf_hom_app (a b : ℤ)
    (i : Fin (WindowTopIteration.length a b)) (X : E) :
    (windowGradedSingleCompEvalIsoSelf E a b i).hom.app X =
      (singleObjXSelf E (windowGradedDegree a b i) X).hom := rfl

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, `i : Fin ((b−a+1).toNat)`, and `X : E`,
`(windowGradedSingleCompEvalIsoSelf E a b i).inv.app X = (singleObjXSelf E (windowGradedDegree a b i) X).inv`.
It inserts the coefficient object into its supporting graded term. -/
theorem windowGradedSingleCompEvalIsoSelf_inv_app (a b : ℤ)
    (i : Fin (WindowTopIteration.length a b)) (X : E) :
    (windowGradedSingleCompEvalIsoSelf E a b i).inv.app X =
      (singleObjXSelf E (windowGradedDegree a b i) X).inv := rfl

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, distinct indices `i,k : Fin ((b−a+1).toNat)`,
and `X : E`,
`IsZero (((windowGradedSingle E a b i).obj X).obj.obj.X (windowGradedDegree a b k))`.
Injectivity of descending degrees makes the degree `b−k` different from the supporting degree `b−i`. -/
theorem windowGradedSingle_isZero_X (a b : ℤ) (i k : Fin (WindowTopIteration.length a b))
    (hk : k ≠ i) (X : E) :
    IsZero (((windowGradedSingle E a b i).obj X).obj.obj.X (windowGradedDegree a b k)) :=
  single_isZero_X E (windowGradedDegree a b i) X (windowGradedDegree a b k)
    (fun h => hk (windowGradedDegree_injective a b h))

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, `i : Fin ((b−a+1).toNat)`, and `f:X→Y` in `E`,
`((windowGradedEval E a b).map ((windowGradedSingle E a b i).map f)) i = (singleObjXSelf E (windowGradedDegree a b i)
X).hom ≫ f ≫ (singleObjXSelf E (windowGradedDegree a b i) Y).inv`.
The supporting component is the coefficient map through its two term charts. -/
theorem windowGradedEval_map_windowGradedSingle_self (a b : ℤ)
    (i : Fin (WindowTopIteration.length a b)) {X Y : E} (f : X ⟶ Y) :
    ((windowGradedEval E a b).map ((windowGradedSingle E a b i).map f)) i =
      (singleObjXSelf E (windowGradedDegree a b i) X).hom ≫ f ≫
        (singleObjXSelf E (windowGradedDegree a b i) Y).inv :=
  single_map_f_self E (windowGradedDegree a b i) f

/-- For a category `E` with zero morphisms and a zero object, `a,b : ℤ`, distinct `i,k : Fin ((b−a+1).toNat)`, and
`f:X→Y` in `E`,
`((windowGradedEval E a b).map ((windowGradedSingle E a b i).map f)) k = 0`.
The off-coordinate source term is zero. -/
theorem windowGradedEval_map_windowGradedSingle_off (a b : ℤ)
    (i k : Fin (WindowTopIteration.length a b)) (hk : k ≠ i) {X Y : E} (f : X ⟶ Y) :
    ((windowGradedEval E a b).map ((windowGradedSingle E a b i).map f)) k = 0 :=
  (windowGradedSingle_isZero_X E a b i k hk X).eq_of_src _ _

end Single

section Exactness

variable [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b,j : ℤ`
with `a≤j≤b`, `windowSingle E a b j ha hb` is Waldhausen exact from the exact-category
structure on `E` to the fixed-window structure. It preserves zero objects, admissible
cofibrations, isomorphism weak equivalences, and admissible pushouts. -/
theorem windowSingle_isWaldhausenExact (a b j : ℤ) (ha : a ≤ j) (hb : j ≤ b) :
    letI := ExactCategory.waldhausenCategory E
    letI := windowWaldhausenCategory E a b
    (windowSingle E a b j ha hb).IsWaldhausenExact := by
  let _ := ExactCategory.waldhausenCategory E
  let _ := windowWaldhausenCategory E a b
  let _ : (single E j).Additive := by
    dsimp only [single]
    infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact IsZero.of_full_of_faithful_of_isZero (windowι E a b) _
      ((single E j).map_isZero hX)
  · intro X Y f hf
    apply (window_isCofibration_iff E a b _).mpr
    change IsAdmissibleMono f at hf
    exact single_map_degreewiseAdmissibleMonomorphisms j f hf
  · intro X Y f hf
    change IsIso f at hf
    let _ : IsIso f := hf
    apply (window_isWeakEquivalence_iff E a b _).mpr
    infer_instance
  · intro X Y Z P i f inZ inY _hi hP
    exact IsPushout.of_map_of_faithful (windowι E a b) (single_map_isPushout j hP)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and any `a,b :
ℤ`, `windowGradedEval E a b` is Waldhausen exact from the fixed-window structure to the
pointwise exact-category structure on `Fin ((b−a+1).toNat) → E`. Each coordinate is exact term
evaluation; the statement includes the empty family for a reversed window. -/
theorem windowGradedEval_isWaldhausenExact (a b : ℤ) :
    letI := windowWaldhausenCategory E a b
    letI := ExactCategory.waldhausenCategory E
    letI := piWaldhausen (fun _ : Fin (WindowTopIteration.length a b) => E)
    (windowGradedEval E a b).IsWaldhausenExact := by
  let _ := windowWaldhausenCategory E a b
  let _ := ExactCategory.waldhausenCategory E
  exact Functor.IsWaldhausenExact.pi'
    (fun _ : Fin (WindowTopIteration.length a b) => E)
    (fun i => windowEval E a b (windowGradedDegree a b i))
    (fun i => windowEval_isWaldhausenExact E a b (windowGradedDegree a b i))

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`i : Fin ((b−a+1).toNat)`, `windowGradedSingle E a b i` is Waldhausen exact from the
exact-category structure on `E` to the fixed-window structure. The inequalities `a≤b−i≤b`
supply the supported degree for its single embedding. -/
theorem windowGradedSingle_isWaldhausenExact (a b : ℤ)
    (i : Fin (WindowTopIteration.length a b)) :
    letI := ExactCategory.waldhausenCategory E
    letI := windowWaldhausenCategory E a b
    (windowGradedSingle E a b i).IsWaldhausenExact :=
  windowSingle_isWaldhausenExact E a b (windowGradedDegree a b i)
    (windowGradedDegree_mem a b i).1 (windowGradedDegree_mem a b i).2

end Exactness

end CochainComplex.Bounded

end
