/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowGradedEvaluation
public import MathlibExt.CategoryTheory.Waldhausen.FinCoproductFunctor
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowGluing

/-!
# Coproduct of the supported graded singles

Let `E` be a preadditive exact category with a zero object and binary biproducts. For `a,b :
ℤ`, set `L=(b−a+1).toNat`, `I=Fin L`, and `d_i=b−i`. The graded coproduct takes a family `X :
I → E` to the chosen finite coproduct of the complexes concentrated at degree `d_i` with value
`X_i`, all in `Window E a b`. Its cofan and injections are colimiting and preserve the window
support.

Evaluation in degree `d_j` leaves the matching single and zero objects at the other
coordinates. The evaluated cofan's map to `X_j` uses the matching single-term isomorphism and
zero maps; its inverse uses the matching injection. These maps give a natural isomorphism
`windowGradedCoproduct E a b ⋙ windowGradedEval E a b ≅ 𝟭 (I → E)`. The coproduct functor
preserves the fixed-window cofibrations, isomorphism weak equivalences, and admissible
pushouts.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen
open scoped ZeroObject

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts, the local coefficient structure has admissible monomorphisms as
cofibrations and isomorphisms as weak equivalences. It is `ExactCategory.waldhausenCategory
E`, used on the coefficient category of the graded coproduct. -/
@[instance_reducible]
local instance gradedCoproductExactModel : WaldhausenCategoryWithoutGluing E :=
  ExactCategory.waldhausenCategory E

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b : ℤ`, the local structure on `Window E a b` is
`windowWaldhausenCategory E a b`. Its cofibrations are degreewise admissible monomorphisms and
its weak equivalences are isomorphisms. -/
@[instance_reducible]
local instance gradedCoproductWindowModel (a b : ℤ) : WaldhausenCategoryWithoutGluing (Window E a b) :=
  windowWaldhausenCategory E a b

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b : ℤ`, put `I=Fin ((b−a+1).toNat)`. The local structure on the
family category `I → E` is the pointwise structure induced from the exact-category one:
cofibrations are componentwise admissible monomorphisms and weak equivalences are
componentwise isomorphisms. -/
@[instance_reducible]
local instance gradedCoproductPiSourceModel (a b : ℤ) :
    WaldhausenCategoryWithoutGluing (Fin (WindowTopIteration.length a b) → E) :=
  piWaldhausen (fun _ : Fin (WindowTopIteration.length a b) => E)

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b : ℤ`, put `I=Fin ((b−a+1).toNat)`. The local structure on `I →
Window E a b` is the pointwise fixed-window structure. Its cofibrations are componentwise
degreewise admissible monomorphisms and its weak equivalences are componentwise isomorphisms. -/
@[instance_reducible]
local instance gradedCoproductPiWindowModel (a b : ℤ) :
    WaldhausenCategoryWithoutGluing (Fin (WindowTopIteration.length a b) → Window E a b) :=
  piWaldhausen (fun _ : Fin (WindowTopIteration.length a b) => Window E a b)

/-- For a preadditive category `E` with a zero object and `a,b : ℤ`, put `I=Fin ((b−a+1).toNat)`
and `d_i=b−i`. The functor `windowGradedSingleFamily E a b : (I → E) ⥤ (I → Window E a b)`
sends `X` in coordinate `i` to the complex concentrated in degree `d_i` with value `X_i`, via
`windowGradedSingle E a b i`. -/
def windowGradedSingleFamily (a b : ℤ) :
    (Fin (WindowTopIteration.length a b) → E) ⥤
      (Fin (WindowTopIteration.length a b) → Window E a b) :=
  Functor.pi' (fun i => Pi.eval (fun _ : Fin (WindowTopIteration.length a b) => E) i ⋙
    windowGradedSingle E a b i)

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, and `X : Fin ((b−a+1).toNat) → E`,
`(windowGradedSingleFamily E a b).obj X = fun i => (windowGradedSingle E a b i).obj (X i)`.
Each coordinate is the supported single in degree `b−i`. -/
theorem windowGradedSingleFamily_obj (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E) :
    (windowGradedSingleFamily E a b).obj X =
      fun i => (windowGradedSingle E a b i).obj (X i) := rfl

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, families `X,Y : Fin ((b−a+1).toNat) → E`, and a
componentwise morphism `f : X ⟶ Y`,
`(windowGradedSingleFamily E a b).map f = fun i => (windowGradedSingle E a b i).map (f i)`.
Each component is the single-degree image of its coefficient morphism. -/
theorem windowGradedSingleFamily_map (a b : ℤ)
    {X Y : Fin (WindowTopIteration.length a b) → E} (f : X ⟶ Y) :
    (windowGradedSingleFamily E a b).map f =
      fun i => (windowGradedSingle E a b i).map (f i) := rfl

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object,
and binary biproducts and `a,b : ℤ`, put `I=Fin ((b−a+1).toNat)`. The functor
`windowGradedCoproduct E a b : (I → E) ⥤ Window E a b` is `windowGradedSingleFamily E a b`
followed by `waldhausenFinCoproductFunctor`. It takes the chosen finite coproduct of the
single complexes in degrees `b−i`, with values `X_i`. -/
def windowGradedCoproduct (a b : ℤ) :
    (Fin (WindowTopIteration.length a b) → E) ⥤ Window E a b :=
  windowGradedSingleFamily E a b ⋙
    waldhausenFinCoproductFunctor (Window E a b) (WindowTopIteration.length a b)

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, and `X : Fin ((b−a+1).toNat) → E`,
`(windowGradedCoproduct E a b).obj X = (waldhausenFinCoproductFunctor (Window E a b) ((b−a+1).toNat)).obj
((windowGradedSingleFamily E a b).obj X)`.
This is the selected finite coproduct of the supported single family. -/
theorem windowGradedCoproduct_obj (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E) :
    (windowGradedCoproduct E a b).obj X =
      (waldhausenFinCoproductFunctor (Window E a b) (WindowTopIteration.length a b)).obj
        ((windowGradedSingleFamily E a b).obj X) := rfl

/-- For a preadditive exact category `E : Type uE` with morphisms in universe `vE`, a zero object, and binary
biproducts, `a,b : ℤ`, and a morphism `f : X ⟶ Y` of `Fin ((b−a+1).toNat)`-indexed coefficient families,
`(windowGradedCoproduct E a b).map f = (waldhausenFinCoproductFunctor (Window E a b) ((b−a+1).toNat)).map
((windowGradedSingleFamily E a b).map f)`.
The finite coproduct acts on the componentwise supported-single maps. -/
theorem windowGradedCoproduct_map (a b : ℤ)
    {X Y : Fin (WindowTopIteration.length a b) → E} (f : X ⟶ Y) :
    (windowGradedCoproduct E a b).map f =
      (waldhausenFinCoproductFunctor (Window E a b) (WindowTopIteration.length a b)).map
        ((windowGradedSingleFamily E a b).map f) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`X : Fin ((b−a+1).toNat) → E`, the object `(windowGradedCoproduct E a b).obj X` is supported
in `[a,b]`. Its underlying complex has zero terms in every degree `j<a` or `b<j`. -/
theorem windowGradedCoproduct_support (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E) :
    windowSupport E a b ((windowGradedCoproduct E a b).obj X).obj :=
  ((windowGradedCoproduct E a b).obj X).property

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and a morphism `f : X ⟶ Y`
of families indexed by `Fin ((b−a+1).toNat)`, every `j : ℤ` with `j<a ∨ b<j` satisfies
`((windowGradedCoproduct E a b).map f).hom.hom.f j = 0`.
The source term in that degree is zero by the window support. -/
theorem windowGradedCoproduct_map_off (a b : ℤ)
    {X Y : Fin (WindowTopIteration.length a b) → E} (f : X ⟶ Y) (j : ℤ)
    (hj : j < a ∨ b < j) :
    ((windowGradedCoproduct E a b).map f).hom.hom.f j = 0 :=
  (windowGradedCoproduct_support E a b X j hj).eq_of_src _ _

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
`windowGradedSingleFamily E a b` is Waldhausen exact between the pointwise coefficient and
fixed-window structures. Each coordinate is coefficient evaluation followed by a supported
single-degree embedding; the functor preserves zero objects, cofibrations, isomorphism weak
equivalences, and admissible pushouts. -/
theorem windowGradedSingleFamily_isWaldhausenExact (a b : ℤ) :
    (windowGradedSingleFamily E a b).IsWaldhausenExact :=
  Functor.IsWaldhausenExact.pi'
    (fun _ : Fin (WindowTopIteration.length a b) => Window E a b)
    (fun i => Pi.eval (fun _ : Fin (WindowTopIteration.length a b) => E) i ⋙
      windowGradedSingle E a b i)
    (fun i =>
      let h := Pi.eval_isWaldhausenExact (fun _ : Fin (WindowTopIteration.length a b) => E) i
      h.comp (windowGradedSingle_isWaldhausenExact E a b i))

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
the functor `windowGradedCoproduct E a b` is Waldhausen exact from the pointwise
exact-category structure on `Fin ((b−a+1).toNat) → E` to the fixed-window structure. This uses
the supported-single family and the finite-coproduct functor with the gluing axiom
`windowGluing E a b`. -/
theorem windowGradedCoproduct_isWaldhausenExact (a b : ℤ) :
    (windowGradedCoproduct E a b).IsWaldhausenExact :=
  (windowGradedSingleFamily_isWaldhausenExact E a b).comp
    (waldhausenFinCoproductFunctor_isWaldhausenExact (Window E a b)
      (windowGluing E a b)
      (WindowTopIteration.length a b))

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`,
the image under `windowGradedCoproduct E a b` of the selected zero object in `Fin
((b−a+1).toNat) → E` is isomorphic to the selected zero of `Window E a b`. The isomorphism
identifies these two zero objects without requiring their choices to be equal. -/
def windowGradedCoproductZeroIso (a b : ℤ) :
    letI : Zero (Fin (WindowTopIteration.length a b) → E) :=
      HasZeroObject.zero' (Fin (WindowTopIteration.length a b) → E)
    (windowGradedCoproduct E a b).obj (0 : Fin (WindowTopIteration.length a b) → E) ≅
      (0 : Window E a b) := by
  letI : Zero (Fin (WindowTopIteration.length a b) → E) :=
    HasZeroObject.zero' (Fin (WindowTopIteration.length a b) → E)
  exact ((windowGradedCoproduct_isWaldhausenExact E a b).map_isZero
    (isZero_zero (Fin (WindowTopIteration.length a b) → E))).isoZero

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and
`X : Fin ((b−a+1).toNat) → E`, the cofan `windowGradedCoproductCofan E a b X` has summands
`(windowGradedSingle E a b i).obj (X i)` and apex `(windowGradedCoproduct E a b).obj X`. Its
legs are the chosen finite-coproduct injections in `Window E a b`. -/
@[implicit_reducible]
def windowGradedCoproductCofan (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E) :
    Cofan ((windowGradedSingleFamily E a b).obj X) :=
  waldhausenFinCoproductCofan (Window E a b) (WindowTopIteration.length a b)
    ((windowGradedSingleFamily E a b).obj X)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, and `X : Fin
((b−a+1).toNat) → E`,
`IsColimit (windowGradedCoproductCofan E a b X)`.
Thus `(windowGradedCoproduct E a b).obj X` is the coproduct of the supported single complexes with coefficient values
`X_i` in degrees `b−i`. -/
def windowGradedCoproductCofanIsColimit (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E) :
    IsColimit (windowGradedCoproductCofan E a b X) :=
  waldhausenFinCoproductCofanIsColimit (Window E a b) (WindowTopIteration.length a b)
    ((windowGradedSingleFamily E a b).obj X)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : Fin ((b−a+1).toNat) →
E`, and an index `i`, the map
`(windowGradedSingle E a b i).obj (X i) ⟶ (windowGradedCoproduct E a b).obj X`
is the `i`-th leg of `windowGradedCoproductCofan E a b X`. -/
def windowGradedCoproductInjection (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E)
    (i : Fin (WindowTopIteration.length a b)) :
    (windowGradedSingle E a b i).obj (X i) ⟶ (windowGradedCoproduct E a b).obj X :=
  (windowGradedCoproductCofan E a b X).inj i

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X :
Fin ((b−a+1).toNat) → E`, and an index `i`, `windowGradedCoproductInjection E a b X i` is a
cofibration in the fixed-window structure. Equivalently, its cochain components are admissible
monomorphisms in `E`. -/
theorem windowGradedCoproductInjection_isCofibration (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (i : Fin (WindowTopIteration.length a b)) :
    IsCofibration (windowGradedCoproductInjection E a b X i) :=
  waldhausenFinCoproductInjection_isCofibration (Window E a b) (WindowTopIteration.length a b)
    ((windowGradedSingleFamily E a b).obj X) i

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, a family morphism `f : X ⟶
Y` indexed by `Fin ((b−a+1).toNat)`, and an index `i`,
`windowGradedCoproductInjection E a b X i ≫ (windowGradedCoproduct E a b).map f = (windowGradedSingle E a b i).map (f i)
≫ windowGradedCoproductInjection E a b Y i`.
The injection square commutes with the componentwise single maps. -/
theorem windowGradedCoproductInjection_naturality (a b : ℤ)
    {X Y : Fin (WindowTopIteration.length a b) → E} (f : X ⟶ Y)
    (i : Fin (WindowTopIteration.length a b)) :
    windowGradedCoproductInjection E a b X i ≫ (windowGradedCoproduct E a b).map f =
      (windowGradedSingle E a b i).map (f i) ≫ windowGradedCoproductInjection E a b Y i :=
  waldhausenFinCoproductInjection_naturality (Window E a b) (WindowTopIteration.length a b)
    ((windowGradedSingleFamily E a b).obj X) ((windowGradedSingleFamily E a b).obj Y)
    ((windowGradedSingleFamily E a b).map f) i

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b,j : ℤ`,
and `X : I → E` with `I=Fin ((b−a+1).toNat)`, the cofan `windowGradedCoproductEvalCofan E a b
X j` has apex `(windowEval E a b j).obj ((windowGradedCoproduct E a b).obj X)`. Its `i`-th
summand is the degree-`j` evaluation of `(windowGradedSingle E a b i).obj (X i)`, and its leg
is evaluation of the corresponding coproduct injection. -/
@[implicit_reducible]
def windowGradedCoproductEvalCofan (a b : ℤ) (X : Fin (WindowTopIteration.length a b) → E)
    (j : ℤ) : Cofan (fun i => (windowEval E a b j).obj ((windowGradedSingle E a b i).obj (X i))) :=
  Cofan.mk ((windowEval E a b j).obj ((windowGradedCoproduct E a b).obj X))
    (fun i => (windowEval E a b j).map (windowGradedCoproductInjection E a b X i))

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b,j : ℤ`, `X : Fin ((b−a+1).toNat)
→ E`, and an index `i`,
`(windowGradedCoproductEvalCofan E a b X j).inj i = (windowEval E a b j).map (windowGradedCoproductInjection E a b X
i)`.
The evaluated cofan uses the degreewise images of the selected coproduct injections. -/
theorem windowGradedCoproductEvalCofan_inj (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : ℤ)
    (i : Fin (WindowTopIteration.length a b)) :
    (windowGradedCoproductEvalCofan E a b X j).inj i =
      (windowEval E a b j).map (windowGradedCoproductInjection E a b X i) := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b,j : ℤ`, and `X : Fin
((b−a+1).toNat) → E`,
`IsColimit (windowGradedCoproductEvalCofan E a b X j)`.
Evaluation preserves the selected finite cofan of supported singles, so its degree-`j` apex is their coproduct in `E`.
-/
def windowGradedCoproductEvalCofanIsColimit (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : ℤ) :
    IsColimit (windowGradedCoproductEvalCofan E a b X j) :=
  (windowEval_isWaldhausenExact E a b j).mapFinCofanIsColimit
    (windowGradedCoproductCofan E a b X) (windowGradedCoproductCofanIsColimit E a b X)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b,j : ℤ`, a family morphism `f : X
⟶ Y` indexed by `I=Fin ((b−a+1).toNat)`, and `i : I`, applying `windowEval E a b j` gives
`eval_j(β_i(X)) ≫ eval_j(R(f)) = eval_j(S_i(f_i)) ≫ eval_j(β_i(Y))`,
where `R=windowGradedCoproduct E a b`, `S_i=windowGradedSingle E a b i`, and `β_i` is `windowGradedCoproductInjection`.
-/
theorem windowGradedCoproductInjection_eval_naturality (a b : ℤ)
    {X Y : Fin (WindowTopIteration.length a b) → E} (f : X ⟶ Y) (j : ℤ)
    (i : Fin (WindowTopIteration.length a b)) :
    (windowEval E a b j).map (windowGradedCoproductInjection E a b X i) ≫
        (windowEval E a b j).map ((windowGradedCoproduct E a b).map f) =
      (windowEval E a b j).map ((windowGradedSingle E a b i).map (f i)) ≫
        (windowEval E a b j).map (windowGradedCoproductInjection E a b Y i) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (windowEval E a b j).map (windowGradedCoproductInjection_naturality E a b f i)

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, and `j : Fin ((b−a+1).toNat)`, put
`d_j=windowGradedDegree a b j`. There is a natural isomorphism
`windowGradedSingle E a b j ⋙ windowEval E a b d_j ≅ 𝟭 E`.
It identifies the supporting term of each single-degree complex with its coefficient object. -/
@[implicit_reducible]
def windowGradedCoproductSingleSelfNatIso (a b : ℤ)
    (j : Fin (WindowTopIteration.length a b)) :
    windowGradedSingle E a b j ⋙ windowEval E a b (windowGradedDegree a b j) ≅ 𝟭 E :=
  windowSingleCompEvalIsoSelf E a b (windowGradedDegree a b j)
    (windowGradedDegree_mem a b j).1 (windowGradedDegree_mem a b j).2

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `j : Fin ((b−a+1).toNat)`, and `X : E`, there is an
isomorphism
`(windowEval E a b (windowGradedDegree a b j)).obj ((windowGradedSingle E a b j).obj X) ≅ X`.
It is the component at `X` of the natural supporting-degree evaluation isomorphism. -/
@[implicit_reducible]
def windowGradedCoproductSingleSelfIso (a b : ℤ)
    (j : Fin (WindowTopIteration.length a b)) (X : E) :
    (windowEval E a b (windowGradedDegree a b j)).obj ((windowGradedSingle E a b j).obj X) ≅ X :=
  (windowGradedCoproductSingleSelfNatIso E a b j).app X

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `j : Fin ((b−a+1).toNat)`, and `X : E`,
`(windowGradedCoproductSingleSelfIso E a b j X).hom = (singleObjXSelf E (windowGradedDegree a b j) X).hom`.
The forward comparison is the single-term identification in degree `b−j`. -/
theorem windowGradedCoproductSingleSelfIso_hom (a b : ℤ)
    (j : Fin (WindowTopIteration.length a b)) (X : E) :
    (windowGradedCoproductSingleSelfIso E a b j X).hom =
      (singleObjXSelf E (windowGradedDegree a b j) X).hom := rfl

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `j : Fin ((b−a+1).toNat)`, and `X : E`,
`(windowGradedCoproductSingleSelfIso E a b j X).inv = (singleObjXSelf E (windowGradedDegree a b j) X).inv`.
The inverse inserts the coefficient object into the supporting term of its single complex. -/
theorem windowGradedCoproductSingleSelfIso_inv (a b : ℤ)
    (j : Fin (WindowTopIteration.length a b)) (X : E) :
    (windowGradedCoproductSingleSelfIso E a b j X).inv =
      (singleObjXSelf E (windowGradedDegree a b j) X).inv := rfl

/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `j : I`, the recovery legs go from the degree-`d_j` evaluations of the
supported singles to `X_j`, where `d_j=b−j`. At `i=j` the leg is
`(windowGradedCoproductSingleSelfIso E a b j (X j)).hom`; at `i≠j` it is zero. -/
def windowGradedCoproductEvaluationLegs (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    ∀ i : Fin (WindowTopIteration.length a b),
      (windowEval E a b (windowGradedDegree a b j)).obj
        ((windowGradedSingle E a b i).obj (X i)) ⟶ X j := by
  classical
  intro i
  by_cases h : i = j
  · subst i
    exact (windowGradedCoproductSingleSelfIso E a b j (X j)).hom
  · exact 0

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `X : Fin ((b−a+1).toNat) → E`, and an index `j`,
`windowGradedCoproductEvaluationLegs E a b X j j = (windowGradedCoproductSingleSelfIso E a b j (X j)).hom`.
The matching evaluated single is identified with its coefficient object. -/
theorem windowGradedCoproductEvaluationLegs_self (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    windowGradedCoproductEvaluationLegs E a b X j j =
      (windowGradedCoproductSingleSelfIso E a b j (X j)).hom := by
  classical
  simp [windowGradedCoproductEvaluationLegs]

omit [HasBinaryBiproducts E] [ExactCategory E] in
/-- For a preadditive category `E` with a zero object, `a,b : ℤ`, `X : I → E` with `I=Fin ((b−a+1).toNat)`, and distinct
`i,j : I`,
`windowGradedCoproductEvaluationLegs E a b X j i = 0`.
The single supported at `b−i` has zero term at `b−j`. -/
theorem windowGradedCoproductEvaluationLegs_off (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (i j : Fin (WindowTopIteration.length a b))
    (h : i ≠ j) : windowGradedCoproductEvaluationLegs E a b X j i = 0 := by
  classical
  simp [windowGradedCoproductEvaluationLegs, h]

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `j : I`, there is a map
`(windowEval E a b (windowGradedDegree a b j)).obj ((windowGradedCoproduct E a b).obj X) ⟶ X j`.
It is the descendant of the evaluated colimiting cofan with the matching single-term isomorphism as its `j`-th leg and
zero legs at all other indices. -/
def windowGradedCoproductEvaluationHom (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    (windowEval E a b (windowGradedDegree a b j)).obj ((windowGradedCoproduct E a b).obj X) ⟶
      X j :=
  Cofan.IsColimit.desc
    (windowGradedCoproductEvalCofanIsColimit E a b X (windowGradedDegree a b j))
    (windowGradedCoproductEvaluationLegs E a b X j)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `j : I`, the map from `X_j` into the evaluation of its graded coproduct in degree `d_j=b−j` is
`(windowGradedCoproductSingleSelfIso E a b j (X j)).inv ≫ (windowEval E a b d_j).map (windowGradedCoproductInjection E a
b X j)`.
It inserts the coefficient through the matching supported single and coproduct injection. -/
@[implicit_reducible]
def windowGradedCoproductEvaluationInv (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    X j ⟶ (windowEval E a b (windowGradedDegree a b j)).obj
      ((windowGradedCoproduct E a b).obj X) :=
  (windowGradedCoproductSingleSelfIso E a b j (X j)).inv ≫
    (windowEval E a b (windowGradedDegree a b j)).map (windowGradedCoproductInjection E a b X j)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `i,j : I`, put `d_j=b−j`. Then
`(windowEval E a b d_j).map (windowGradedCoproductInjection E a b X i) ≫ windowGradedCoproductEvaluationHom E a b X j =
windowGradedCoproductEvaluationLegs E a b X j i`.
The composite is the matching single-term isomorphism when `i=j` and zero otherwise. -/
theorem windowGradedCoproductEvaluation_fac (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (i j : Fin (WindowTopIteration.length a b)) :
    (windowEval E a b (windowGradedDegree a b j)).map (windowGradedCoproductInjection E a b X i) ≫
        windowGradedCoproductEvaluationHom E a b X j =
      windowGradedCoproductEvaluationLegs E a b X j i :=
  Cofan.IsColimit.fac
    (windowGradedCoproductEvalCofanIsColimit E a b X (windowGradedDegree a b j))
    (windowGradedCoproductEvaluationLegs E a b X j) i

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `j : I`,
`(windowEval E a b (windowGradedDegree a b j)).obj ((windowGradedCoproduct E a b).obj X) ≅ X j`.
Its forward map is `windowGradedCoproductEvaluationHom`; its inverse is the matching single-term inverse followed by the
evaluated coproduct injection. -/
def windowGradedCoproductEvaluationIso (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    (windowEval E a b (windowGradedDegree a b j)).obj ((windowGradedCoproduct E a b).obj X) ≅
      X j where
  hom := windowGradedCoproductEvaluationHom E a b X j
  inv := windowGradedCoproductEvaluationInv E a b X j
  hom_inv_id := by
    apply Cofan.IsColimit.hom_ext
      (windowGradedCoproductEvalCofanIsColimit E a b X (windowGradedDegree a b j))
    intro i
    rw [windowGradedCoproductEvalCofan_inj, ← Category.assoc,
      windowGradedCoproductEvaluation_fac]
    by_cases h : i = j
    · subst i
      rw [windowGradedCoproductEvaluationLegs_self]
      change _ ≫ (_ ≫ _) = _ ≫ 𝟙 _
      simp only [Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (windowGradedSingle_isZero_X E a b i j (Ne.symm h) (X i)).eq_of_src _ _
  inv_hom_id := by
    change (_ ≫ _) ≫ _ = 𝟙 _
    rw [Category.assoc, windowGradedCoproductEvaluation_fac,
      windowGradedCoproductEvaluationLegs_self, Iso.inv_hom_id]

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, a morphism `f : X ⟶ Y` of
families indexed by `I=Fin ((b−a+1).toNat)`, and `j : I`, put `d_j=b−j`. Then
`(windowEval E a b d_j).map ((windowGradedCoproduct E a b).map f) ≫ windowGradedCoproductEvaluationHom E a b Y j =
windowGradedCoproductEvaluationHom E a b X j ≫ f j`. -/
theorem windowGradedCoproductEvaluation_naturality (a b : ℤ)
    {X Y : Fin (WindowTopIteration.length a b) → E} (f : X ⟶ Y)
    (j : Fin (WindowTopIteration.length a b)) :
    (windowEval E a b (windowGradedDegree a b j)).map ((windowGradedCoproduct E a b).map f) ≫
        windowGradedCoproductEvaluationHom E a b Y j =
      windowGradedCoproductEvaluationHom E a b X j ≫ f j := by
  apply Cofan.IsColimit.hom_ext
    (windowGradedCoproductEvalCofanIsColimit E a b X (windowGradedDegree a b j))
  intro i
  rw [windowGradedCoproductEvalCofan_inj, ← Category.assoc,
    windowGradedCoproductInjection_eval_naturality, Category.assoc,
    windowGradedCoproductEvaluation_fac, ← Category.assoc, windowGradedCoproductEvaluation_fac]
  by_cases h : i = j
  · subst i
    rw [windowGradedCoproductEvaluationLegs_self, windowGradedCoproductEvaluationLegs_self]
    exact (windowGradedCoproductSingleSelfNatIso E a b j).hom.naturality (f j)
  · exact (windowGradedSingle_isZero_X E a b i j (Ne.symm h) (X i)).eq_of_src _ _

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `I=Fin ((b−a+1).toNat)`,
and `j : I`, there is a natural isomorphism
`windowGradedCoproduct E a b ⋙ windowGradedEval E a b ⋙ Pi.eval (fun _ : I => E) j ≅ Pi.eval (fun _ : I => E) j`.
Its component at a family `X` is the coefficient-recovery isomorphism in degree `b−j`. -/
def windowGradedCoproductCompEvalIso (a b : ℤ) (j : Fin (WindowTopIteration.length a b)) :
    windowGradedCoproduct E a b ⋙ windowGradedEval E a b ⋙
      Pi.eval (fun _ : Fin (WindowTopIteration.length a b) => E) j ≅
        Pi.eval (fun _ : Fin (WindowTopIteration.length a b) => E) j :=
  NatIso.ofComponents (fun X => windowGradedCoproductEvaluationIso E a b X j)
    (fun f => windowGradedCoproductEvaluation_naturality E a b f j)

/-- For a preadditive exact category `E` with a zero object and binary biproducts and `a,b : ℤ`, put `I=Fin
((b−a+1).toNat)`. The coordinate recovery isomorphisms assemble to
`windowGradedCoproduct E a b ⋙ windowGradedEval E a b ≅ 𝟭 (I → E)`.
Each coordinate of the graded evaluation of the supported-single coproduct is naturally isomorphic to its input
coefficient object. -/
def windowGradedCoproductCompGradedEvalIso (a b : ℤ) :
    windowGradedCoproduct E a b ⋙ windowGradedEval E a b ≅
      𝟭 (Fin (WindowTopIteration.length a b) → E) :=
  NatIso.pi' (fun j => windowGradedCoproductCompEvalIso E a b j)

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `j : I`,
`(windowGradedCoproductCompGradedEvalIso E a b).hom.app X j = windowGradedCoproductEvaluationHom E a b X j`.
The forward natural component is the evaluated cofan descendant recovering the `j`-th coefficient. -/
theorem windowGradedCoproductCompGradedEvalIso_hom_app (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    (windowGradedCoproductCompGradedEvalIso E a b).hom.app X j =
      windowGradedCoproductEvaluationHom E a b X j := rfl

/-- For a preadditive exact category `E` with a zero object and binary biproducts, `a,b : ℤ`, `X : I → E` with `I=Fin
((b−a+1).toNat)`, and `j : I`, put `d_j=b−j`. Then
`(windowGradedCoproductCompGradedEvalIso E a b).inv.app X j = (windowGradedCoproductSingleSelfIso E a b j (X j)).inv ≫
(windowEval E a b d_j).map (windowGradedCoproductInjection E a b X j)`.
The inverse uses the matching single and its coproduct injection. -/
theorem windowGradedCoproductCompGradedEvalIso_inv_app (a b : ℤ)
    (X : Fin (WindowTopIteration.length a b) → E) (j : Fin (WindowTopIteration.length a b)) :
    (windowGradedCoproductCompGradedEvalIso E a b).inv.app X j =
      (windowGradedCoproductSingleSelfIso E a b j (X j)).inv ≫
        (windowEval E a b (windowGradedDegree a b j)).map
          (windowGradedCoproductInjection E a b X j) := rfl

end CochainComplex.Bounded

end
