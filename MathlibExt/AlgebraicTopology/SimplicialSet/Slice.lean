/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexQuasicategory

/-!
# Path (arrow) slices and path mapping spaces (exponential model)

For a simplicial set `X` and a vertex `x : Δ[0] ⟶ X`, this file provides
*path-object* over/under slices and left/right path mapping spaces:
pullbacks and fibers of the endpoint evaluations on the path object
`X^{Δ[1]}`. These are the arrow-category slices, together with
functoriality in `X` and the quasicategory closure results that follow
from the landed inner-fibration theory. They are **not** the
join slices `X_{/x}`, `X_{x/}` of Lurie and Kerodon, nor the
`Hom^L`/`Hom^R` mapping spaces built from them, and they are
deliberately given `path`-prefixed names
(`SSet.pathSliceOver`, `SSet.pathSliceUnder`,
`SSet.pathMappingSpaceLeft`, `SSet.pathMappingSpaceRight`) so that
the unprefixed over/under slice and left/right mapping-space names
remain free for the genuine join slices, which are defined in
[JoinSlice.lean](JoinSlice.lean) as `SSet.sliceOver`,
`SSet.sliceUnder`, `SSet.mappingSpaceRight` and
`SSet.mappingSpaceLeft`. Nothing in this file should be cited as a
join slice, and no comparison map between the two models is
constructed yet (see the TODO section below); arguments that
require join slices on the nose should cite `JoinSlice.lean`
instead.

## Choice of definition (read before using)

The classical slices of Lurie (HTT §1.2.9) and Kerodon (§4.3.5;
joins in §4.3.3) are
defined using the join: an `n`-simplex of `X_{/x}` is a map
`Δ[n] ⋆ Δ[0] ⟶ X` whose restriction to the right factor is `x`, and
dually for `X_{x/}`. Those join slices are constructed directly in
[JoinSlice.lean](JoinSlice.lean), using the endpoint inclusions
`SSet.joinInl`/`SSet.joinInr`, connected-colimit preservation and
the representable computation `SSet.joinStdSimplexIso` from
[Join.lean](Join.lean) and [JoinProperties.lean](JoinProperties.lean).
What the join API still lacks — and what keeps the two models
uncompared for now — is pushout-product/anodyne lemmas for the
join and a comparison map between the path and join models.

This file uses the equivalent *path-object* (exponential)
model, which the landed internal-hom API supports completely. The
path object itself is **reused**, not redefined: it is
`SSet.pathSpace X := (ihom Δ[1]).obj X` with endpoint evaluations
`SSet.eval₀, SSet.eval₁ : pathSpace X ⟶ X`, imported from
`MathlibExt/AlgebraicTopology/SimplicialSet/ModelCategory/PathSpace.lean`.
Importing that file here is layering-clean: it imports only Mathlib
(so there is no import cycle), and its `open SSet.modelCategoryQuillen`
is file-local — the Quillen `CategoryWithFibrations` instance is
scoped to that open and does not become globally available to
consumers of this file (its Kan-complex fibration instances for the
evaluations likewise stay dormant without that scope). The
evaluations imported there are precomposition with
`stdSimplex.δ 1`, resp. `stdSimplex.δ 0`, followed by evaluation at
`Δ[0]`; this is recorded here as `SSet.pathSpace_eval₀_eq` and
`SSet.pathSpace_eval₁_eq` (proved from the public
`comp_eval₀_eq_ι₀_braiding_uncurry` characterization, since the
bodies of `eval₀`/`eval₁` are not exposed across modules), and
naturality in `X` is `SSet.pathSpace_map_eval₀` /
`SSet.pathSpace_map_eval₁` from the same file. On top of that:

* the path over-slice `SSet.pathSliceOver x` is the pullback of
  `SSet.eval₁` along `x` (paths *ending* at `x`), with projection
  `pathSliceOver.proj` to `X` given by the free (source) endpoint;
* the path under-slice `SSet.pathSliceUnder x` is the pullback of
  `SSet.eval₀` along `x` (paths *starting* at `x`), with
  projection given by the free (target) endpoint;
* the right mapping space `SSet.pathMappingSpaceRight x y` is the fiber
  of `pathSliceOver.proj y` over `x`, and the left mapping space
  `SSet.pathMappingSpaceLeft x y` is the fiber of `pathSliceUnder.proj x`
  over `y`. In this exponential model the two are *canonically
  isomorphic* (not just equivalent), both computing the fiber of the
  endpoint pair map `SSet.pathPair X : pathSpace X ⟶ X ⨯ X`; see
  `SSet.pathMappingSpaceLeftIsoRight` and `SSet.pathMappingSpaceRightIsoFiber`.
  `SSet.pathMappingSpace x y` abbreviates the right one.

These objects are *not* the join slices on the nose: an
`n`-simplex of `pathSliceOver x` is a map `Δ[n] ⟶ pathSpace X`, i.e. a map
`Δ[n] ⊗ Δ[1] ⟶ X` constant at `x` on the target edge, whereas an
`n`-simplex of the join slice `X_{/x}` is an `(n+1)`-simplex of `X`
with last vertex `x`. The two models are equivalent for
quasicategories (both model the same mapping spaces; compare Kerodon
§4.6 and Dugger--Spivak), but no comparison map is constructed here.

## What is proved

* naturality of the evaluations in `X`, and functoriality of
  slices and mapping spaces in `X` (`pathSliceOver.map` and companions,
  characterized by their projections);
* universal-property characterizations of maps into slices and
  mapping spaces (`pathSliceOver.homEquiv`, `pathMappingSpaceRight.homEquiv`
  and companions);
* for a quasicategory `X`: `eval₀`, `eval₁` and the pair map
  `pathPair` are inner fibrations. The key point is the identification
  `(ihom ∂Δ[1]).obj X ≅ X ⨯ X` (`SSet.ihomBoundaryOneIso`, the
  composite of the tensor-form isomorphism `SSet.boundaryOneIhomIso`
  from `PathSpace.lean` with Mathlib's tensor-to-product comparison
  `CartesianMonoidalCategory.tensorLeftIsoProd`), under which
  `pathPair` is `(pre ∂Δ[1].ι).app X`, an inner fibration by the
  landed pushout-product instance;
* consequently, for a quasicategory `X`, the slices and both mapping
  spaces are quasicategories (base change of inner fibrations to
  `Δ[0]`);
* the slices are identified with base changes of `pathPair` along
  the graphs of vertices (`pathSliceOverIsoPairPullback`,
  `pathSliceUnderIsoPairPullback`), so for a quasicategory `X` the slice
  projections `pathSliceOver.proj` and `pathSliceUnder.proj` are inner
  fibrations.

## TODO

* Kan-ness of mapping spaces. For a quasicategory `X`, the mapping
  spaces above *are* Kan complexes mathematically, but this does not
  follow from inner fibrations alone: an inner fibration to `Δ[0]`
  only gives a quasicategory. The standard proofs use either Joyal's
  special outer horn filling (fillers for `Λ[n, 0]`/`Λ[n, n]` whose
  outer edge is an equivalence; no such API exists in the pinned
  Mathlib), or that the *join* slice projections in
  [JoinSlice.lean](JoinSlice.lean) are left/right fibrations, which
  needs join anodyne lemmas that are not yet available. This file
  proves the quasicategory statement and explicitly does not assert
  `KanComplex` for mapping spaces.
* The comparison between the path slices here and the join slices
  `SSet.sliceOver`/`SSet.sliceUnder` of
  [JoinSlice.lean](JoinSlice.lean) — in particular the
  identifications of the `Hom^L`/`Hom^R` mapping-space fibers of
  the join slices with the path mapping spaces here. The missing
  inputs are the join anodyne/pushout-product lemmas above; the
  join slices themselves and their fibers already exist.
* That `pathSliceOver.proj`/`pathSliceUnder.proj` are right/left fibrations
  for a quasicategory `X` (same missing input as Kan-ness).

## References

- J. Lurie, *Higher Topos Theory*, §§1.2.8, 1.2.9 (joins, slices) and
  §1.2.2 (mapping spaces `Hom^R` and `Hom^L`).
- *Kerodon*, §4.3.3 (joins), §4.3.5 (slices) and §4.6 (mapping
  spaces).
- D. Dugger and D. Spivak, *Mapping spaces in quasi-categories*,
  Algebraic & Geometric Topology 11 (2011) (comparison of models).
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Precomposition with an isomorphism, as an isomorphism of internal
homs: `(ihom B).obj X ≅ (ihom A).obj X` for `e : A ≅ B`. -/
def preIso {A B : SSet.{u}} (e : A ≅ B) (X : SSet.{u}) :
    (ihom B).obj X ≅ (ihom A).obj X where
  hom := (pre e.hom).app X
  inv := (pre e.inv).app X
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id]
    rfl
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id]
    rfl

/-- Evaluation at `Δ[0]`: the canonical isomorphism
`(ihom Δ[0]).obj X ≅ X`. -/
def evalDeltaZeroIso (X : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj X ≅ X :=
  preIso Δ0IsoUnit.symm X ≪≫ unitIsoSelf X

lemma evalDeltaZeroIso_hom (X : SSet.{u}) :
    (evalDeltaZeroIso X).hom =
      (pre Δ0IsoUnit.inv).app X ≫ (unitIsoSelf X).hom :=
  rfl

/-- Evaluation at `Δ[0]` is natural in `X`. -/
lemma evalDeltaZeroIso_hom_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom (Δ[0] : SSet.{u})).map f ≫ (evalDeltaZeroIso Y).hom =
      (evalDeltaZeroIso X).hom ≫ f := by
  have hunit : (ihom (𝟙_ SSet.{u})).map f ≫ (unitIsoSelf Y).hom =
      (unitIsoSelf X).hom ≫ f := by
    exact NatTrans.naturality unitNatIso.inv f
  have hpre := (pre Δ0IsoUnit.inv).naturality f
  rw [evalDeltaZeroIso_hom, evalDeltaZeroIso_hom, ← Category.assoc, hpre,
    Category.assoc, hunit, ← Category.assoc]

/-- The landed source evaluation `SSet.eval₀` on `pathSpace X` is
precomposition with `stdSimplex.δ 1 : Δ[0] ⟶ Δ[1]` (the inclusion
of vertex `0`), followed by evaluation at `Δ[0]`. The body of
`eval₀` is not exposed across modules, so this is proved from its
public characterization `comp_eval₀_eq_ι₀_braiding_uncurry`. -/
lemma pathSpace_eval₀_eq (X : SSet.{u}) :
    (eval₀ : pathSpace X ⟶ X) =
      (pre (stdSimplex.δ (1 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom := by
  have h : ∀ {A : SSet.{u}} (f : A ⟶ pathSpace X),
      f ≫ ((pre (stdSimplex.δ (1 : Fin 2))).app X ≫
        (evalDeltaZeroIso X).hom) = f ≫ (eval₀ : pathSpace X ⟶ X) := by
    intro A f
    rw [comp_eval₀_eq_ι₀_braiding_uncurry, evalDeltaZeroIso_hom]
    rw [← MonoidalClosed.curry_uncurry f]
    rw [MonoidalClosed.curry_pre_app_assoc,
      MonoidalClosed.curry_pre_app_assoc]
    rw [curry_unitIsoSelf]
    change (SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom) ≫
        MonoidalClosed.uncurry f = _
    rw [MonoidalClosed.uncurry_curry, Category.assoc]
  have hid := h (𝟙 (pathSpace X))
  simpa using hid.symm

/-- The landed target evaluation `SSet.eval₁` on `pathSpace X` is
precomposition with `stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]` (the inclusion
of vertex `1`), followed by evaluation at `Δ[0]`. -/
lemma pathSpace_eval₁_eq (X : SSet.{u}) :
    (eval₁ : pathSpace X ⟶ X) =
      (pre (stdSimplex.δ (0 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom := by
  have h : ∀ {A : SSet.{u}} (f : A ⟶ pathSpace X),
      f ≫ ((pre (stdSimplex.δ (0 : Fin 2))).app X ≫
        (evalDeltaZeroIso X).hom) = f ≫ (eval₁ : pathSpace X ⟶ X) := by
    intro A f
    rw [comp_eval₁_eq_ι₁_braiding_uncurry, evalDeltaZeroIso_hom]
    rw [← MonoidalClosed.curry_uncurry f]
    rw [MonoidalClosed.curry_pre_app_assoc,
      MonoidalClosed.curry_pre_app_assoc]
    rw [curry_unitIsoSelf]
    change (SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom) ≫
        MonoidalClosed.uncurry f = _
    rw [MonoidalClosed.uncurry_curry, Category.assoc]
  have hid := h (𝟙 (pathSpace X))
  simpa using hid.symm

/-- The unique map to `Δ[0]` from any simplicial set, through the
terminality of `Δ[0]`. Bundled here because the fibers defining
slices and mapping spaces are taken over `Δ[0]`. -/
abbrev toDeltaZero (Z : SSet.{u}) : Z ⟶ (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.from Z

lemma toDeltaZero_eq {Z : SSet.{u}} (g : Z ⟶ (Δ[0] : SSet.{u})) :
    g = toDeltaZero Z :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

variable {X : SSet.{u}}

/-- The over-category slice at a vertex `x : Δ[0] ⟶ X`, in the
path-object model: the pullback of target evaluation
`(eval₁ (X := X)) : pathSpace X ⟶ X` along `x`. Its simplices are paths in
`X` ending at `x`. See the file header for the comparison with the
join slice `X_{/x}`. -/
def pathSliceOver (x : (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  pullback ((eval₁ (X := X))) x

namespace pathSliceOver

variable (x : (Δ[0] : SSet.{u}) ⟶ X)

/-- The underlying path of a point of the over-slice. -/
def fst : pathSliceOver x ⟶ pathSpace X := pullback.fst _ _

/-- The (unique) map from the over-slice to `Δ[0]`. -/
def snd : pathSliceOver x ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

@[reassoc (attr := simp)]
lemma condition : fst x ≫ (eval₁ (X := X)) = snd x ≫ x :=
  pullback.condition

/-- The projection from the over-slice to `X`, given by the free
(source) endpoint of the path. -/
def proj : pathSliceOver x ⟶ X := fst x ≫ (eval₀ (X := X))

lemma snd_eq : snd x = toDeltaZero (pathSliceOver x) := toDeltaZero_eq _

/-- A map into the over-slice from a path whose target is
constantly `x`. -/
def lift {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ x) : Z ⟶ pathSliceOver x :=
  pullback.lift f (toDeltaZero Z) hf

@[reassoc (attr := simp)]
lemma lift_fst {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ x) :
    lift x f hf ≫ fst x = f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_snd {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ x) :
    lift x f hf ≫ snd x = toDeltaZero Z :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma lift_proj {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ x) :
    lift x f hf ≫ proj x = f ≫ (eval₀ (X := X)) := by
  rw [proj, ← Category.assoc, lift_fst]

/-- Maps into the over-slice are determined by the underlying path. -/
@[ext]
lemma hom_ext {Z : SSet.{u}} {f g : Z ⟶ pathSliceOver x}
    (h : f ≫ fst x = g ≫ fst x) : f = g :=
  pullback.hom_ext h (stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- Maps into the over-slice are exactly the paths whose target is
constantly `x`. -/
def homEquiv (Z : SSet.{u}) :
    (Z ⟶ pathSliceOver x) ≃
      {f : Z ⟶ pathSpace X // f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ x} where
  toFun f := ⟨f ≫ fst x, by
    rw [Category.assoc, condition, ← Category.assoc,
      toDeltaZero_eq (f ≫ snd x)]⟩
  invFun f := lift x f.1 f.2
  left_inv f := hom_ext x (lift_fst x _ _)
  right_inv f := Subtype.ext (lift_fst x f.1 f.2)

variable {Y : SSet.{u}} (f : X ⟶ Y)

/-- Functoriality of the over-slice in `X`: a map `f : X ⟶ Y`
sends paths ending at `x` to paths ending at `x ≫ f`. -/
def map : pathSliceOver x ⟶ pathSliceOver (x ≫ f) :=
  lift (x ≫ f) (fst x ≫ (ihom (Δ[1] : SSet.{u})).map f) (by
    rw [Category.assoc, pathSpace_map_eval₁, ← Category.assoc, condition,
      Category.assoc, toDeltaZero_eq (snd x)])

@[reassoc (attr := simp)]
lemma map_fst : map x f ≫ fst (x ≫ f) =
    fst x ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_proj : map x f ≫ proj (x ≫ f) = proj x ≫ f := by
  rw [proj, proj, ← Category.assoc, map_fst, Category.assoc,
    pathSpace_map_eval₀, ← Category.assoc]

end pathSliceOver

/-- The under-category slice at a vertex `x : Δ[0] ⟶ X`, in the
path-object model: the pullback of source evaluation
`(eval₀ (X := X)) : pathSpace X ⟶ X` along `x`. Its simplices are paths in
`X` starting at `x`. See the file header for the comparison with
the join slice `X_{x/}`. -/
def pathSliceUnder (x : (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  pullback ((eval₀ (X := X))) x

namespace pathSliceUnder

variable (x : (Δ[0] : SSet.{u}) ⟶ X)

/-- The underlying path of a point of the under-slice. -/
def fst : pathSliceUnder x ⟶ pathSpace X := pullback.fst _ _

/-- The (unique) map from the under-slice to `Δ[0]`. -/
def snd : pathSliceUnder x ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

@[reassoc (attr := simp)]
lemma condition : fst x ≫ (eval₀ (X := X)) = snd x ≫ x :=
  pullback.condition

/-- The projection from the under-slice to `X`, given by the free
(target) endpoint of the path. -/
def proj : pathSliceUnder x ⟶ X := fst x ≫ (eval₁ (X := X))

lemma snd_eq : snd x = toDeltaZero (pathSliceUnder x) := toDeltaZero_eq _

/-- A map into the under-slice from a path whose source is
constantly `x`. -/
def lift {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x) : Z ⟶ pathSliceUnder x :=
  pullback.lift f (toDeltaZero Z) hf

@[reassoc (attr := simp)]
lemma lift_fst {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x) :
    lift x f hf ≫ fst x = f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_snd {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x) :
    lift x f hf ≫ snd x = toDeltaZero Z :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma lift_proj {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hf : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x) :
    lift x f hf ≫ proj x = f ≫ (eval₁ (X := X)) := by
  rw [proj, ← Category.assoc, lift_fst]

/-- Maps into the under-slice are determined by the underlying
path. -/
@[ext]
lemma hom_ext {Z : SSet.{u}} {f g : Z ⟶ pathSliceUnder x}
    (h : f ≫ fst x = g ≫ fst x) : f = g :=
  pullback.hom_ext h (stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- Maps into the under-slice are exactly the paths whose source is
constantly `x`. -/
def homEquiv (Z : SSet.{u}) :
    (Z ⟶ pathSliceUnder x) ≃
      {f : Z ⟶ pathSpace X // f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x} where
  toFun f := ⟨f ≫ fst x, by
    rw [Category.assoc, condition, ← Category.assoc,
      toDeltaZero_eq (f ≫ snd x)]⟩
  invFun f := lift x f.1 f.2
  left_inv f := hom_ext x (lift_fst x _ _)
  right_inv f := Subtype.ext (lift_fst x f.1 f.2)

variable {Y : SSet.{u}} (f : X ⟶ Y)

/-- Functoriality of the under-slice in `X`: a map `f : X ⟶ Y`
sends paths starting at `x` to paths starting at `x ≫ f`. -/
def map : pathSliceUnder x ⟶ pathSliceUnder (x ≫ f) :=
  lift (x ≫ f) (fst x ≫ (ihom (Δ[1] : SSet.{u})).map f) (by
    rw [Category.assoc, pathSpace_map_eval₀, ← Category.assoc, condition,
      Category.assoc, toDeltaZero_eq (snd x)])

@[reassoc (attr := simp)]
lemma map_fst : map x f ≫ fst (x ≫ f) =
    fst x ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_proj : map x f ≫ proj (x ≫ f) = proj x ≫ f := by
  rw [proj, proj, ← Category.assoc, map_fst, Category.assoc,
    pathSpace_map_eval₁, ← Category.assoc]

end pathSliceUnder

/-- The endpoint pair map of the path object:
`Fun(Δ[1], X) ⟶ X ⨯ X`. -/
def pathPair (X : SSet.{u}) : pathSpace X ⟶ X ⨯ X :=
  prod.lift ((eval₀ (X := X))) ((eval₁ (X := X)))

@[reassoc (attr := simp)]
lemma pathPair_fst (X : SSet.{u}) : pathPair X ≫ prod.fst = (eval₀ (X := X)) :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
lemma pathPair_snd (X : SSet.{u}) : pathPair X ≫ prod.snd = (eval₁ (X := X)) :=
  prod.lift_snd _ _

/-- The endpoint pair map is natural in `X`. -/
lemma pathPair_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫ pathPair Y =
      pathPair X ≫ prod.map f f := by
  apply prod.hom_ext <;>
    simp [pathSpace_map_eval₀ f, pathSpace_map_eval₁ f]

/-- The right mapping space between two vertices: the fiber of
the over-slice projection `pathSliceOver.proj y : pathSliceOver y ⟶ X` over
`x`, i.e. paths in `X` from `x` to `y`, organized by first fixing
the target. -/
def pathMappingSpaceRight (x y : (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  pullback (pathSliceOver.proj y) x

namespace pathMappingSpaceRight

variable (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The point of the over-slice at `y` underlying a path in the
right mapping space. -/
def fst : pathMappingSpaceRight x y ⟶ pathSliceOver y := pullback.fst _ _

/-- The (unique) map from the right mapping space to `Δ[0]`. -/
def snd : pathMappingSpaceRight x y ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

@[reassoc (attr := simp)]
lemma condition : fst x y ≫ pathSliceOver.proj y = snd x y ≫ x :=
  pullback.condition

/-- The underlying path in `X`. -/
def toPath : pathMappingSpaceRight x y ⟶ pathSpace X :=
  fst x y ≫ pathSliceOver.fst y

lemma toPath_src : toPath x y ≫ (eval₀ (X := X)) =
    toDeltaZero (pathMappingSpaceRight x y) ≫ x := by
  calc toPath x y ≫ (eval₀ (X := X)) = fst x y ≫ pathSliceOver.proj y := by
        rw [toPath, pathSliceOver.proj, Category.assoc]
    _ = snd x y ≫ x := condition x y
    _ = toDeltaZero (pathMappingSpaceRight x y) ≫ x := by
        rw [toDeltaZero_eq (snd x y)]

lemma toPath_tgt : toPath x y ≫ (eval₁ (X := X)) =
    toDeltaZero (pathMappingSpaceRight x y) ≫ y := by
  calc toPath x y ≫ (eval₁ (X := X))
      = fst x y ≫ (pathSliceOver.fst y ≫ (eval₁ (X := X))) := by
        rw [toPath, Category.assoc]
    _ = fst x y ≫ (pathSliceOver.snd y ≫ y) := by rw [pathSliceOver.condition]
    _ = (fst x y ≫ pathSliceOver.snd y) ≫ y := (Category.assoc _ _ _).symm
    _ = toDeltaZero (pathMappingSpaceRight x y) ≫ y := by
        rw [toDeltaZero_eq (fst x y ≫ pathSliceOver.snd y)]

/-- A map into the right mapping space from a path whose endpoints
are constantly `x` and `y`. -/
def lift {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    Z ⟶ pathMappingSpaceRight x y :=
  pullback.lift (pathSliceOver.lift y f ht) (toDeltaZero Z) (by
    rw [pathSliceOver.lift_proj]
    exact hs)

@[reassoc (attr := simp)]
lemma lift_fst {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    lift x y f hs ht ≫ fst x y = pathSliceOver.lift y f ht :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_toPath {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    lift x y f hs ht ≫ toPath x y = f := by
  rw [toPath, ← Category.assoc, lift_fst, pathSliceOver.lift_fst]

/-- Maps into the right mapping space are determined by the
underlying path. -/
@[ext]
lemma hom_ext {Z : SSet.{u}} {f g : Z ⟶ pathMappingSpaceRight x y}
    (h : f ≫ toPath x y = g ≫ toPath x y) : f = g := by
  apply pullback.hom_ext _ (stdSimplex.isTerminalObj₀.hom_ext _ _)
  apply pathSliceOver.hom_ext
  rw [toPath, ← Category.assoc] at h
  exact h

/-- Maps into the right mapping space are exactly the paths whose
endpoints are constantly `x` and `y`. -/
def homEquiv (Z : SSet.{u}) :
    (Z ⟶ pathMappingSpaceRight x y) ≃
      {f : Z ⟶ pathSpace X //
        f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x ∧
          f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y} where
  toFun f := ⟨f ≫ toPath x y, by
    constructor
    · rw [Category.assoc, toPath_src, ← Category.assoc,
        toDeltaZero_eq (f ≫ toDeltaZero (pathMappingSpaceRight x y))]
    · rw [Category.assoc, toPath_tgt, ← Category.assoc,
        toDeltaZero_eq (f ≫ toDeltaZero (pathMappingSpaceRight x y))]⟩
  invFun f := lift x y f.1 f.2.1 f.2.2
  left_inv f := hom_ext x y (lift_toPath x y _ _ _)
  right_inv f := Subtype.ext (lift_toPath x y f.1 f.2.1 f.2.2)

variable {Y : SSet.{u}} (f : X ⟶ Y)

/-- Functoriality of the right mapping space in `X`. -/
def map : pathMappingSpaceRight x y ⟶ pathMappingSpaceRight (x ≫ f) (y ≫ f) :=
  lift (x ≫ f) (y ≫ f) (toPath x y ≫ (ihom (Δ[1] : SSet.{u})).map f)
    (by
      rw [Category.assoc, pathSpace_map_eval₀, ← Category.assoc, toPath_src,
        Category.assoc, toDeltaZero_eq
          (toDeltaZero (pathMappingSpaceRight x y))])
    (by
      rw [Category.assoc, pathSpace_map_eval₁, ← Category.assoc, toPath_tgt,
        Category.assoc, toDeltaZero_eq
          (toDeltaZero (pathMappingSpaceRight x y))])

@[reassoc (attr := simp)]
lemma map_toPath : map x y f ≫ toPath (x ≫ f) (y ≫ f) =
    toPath x y ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  lift_toPath _ _ _ _ _

end pathMappingSpaceRight

/-- The left mapping space between two vertices: the fiber of
the under-slice projection `pathSliceUnder.proj x : pathSliceUnder x ⟶ X`
over `y`, i.e. paths in `X` from `x` to `y`, organized by first
fixing the source. -/
def pathMappingSpaceLeft (x y : (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  pullback (pathSliceUnder.proj x) y

namespace pathMappingSpaceLeft

variable (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The point of the under-slice at `x` underlying a path in the
left mapping space. -/
def fst : pathMappingSpaceLeft x y ⟶ pathSliceUnder x := pullback.fst _ _

/-- The (unique) map from the left mapping space to `Δ[0]`. -/
def snd : pathMappingSpaceLeft x y ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

@[reassoc (attr := simp)]
lemma condition : fst x y ≫ pathSliceUnder.proj x = snd x y ≫ y :=
  pullback.condition

/-- The underlying path in `X`. -/
def toPath : pathMappingSpaceLeft x y ⟶ pathSpace X :=
  fst x y ≫ pathSliceUnder.fst x

lemma toPath_tgt : toPath x y ≫ (eval₁ (X := X)) =
    toDeltaZero (pathMappingSpaceLeft x y) ≫ y := by
  calc toPath x y ≫ (eval₁ (X := X)) = fst x y ≫ pathSliceUnder.proj x := by
        rw [toPath, pathSliceUnder.proj, Category.assoc]
    _ = snd x y ≫ y := condition x y
    _ = toDeltaZero (pathMappingSpaceLeft x y) ≫ y := by
        rw [toDeltaZero_eq (snd x y)]

lemma toPath_src : toPath x y ≫ (eval₀ (X := X)) =
    toDeltaZero (pathMappingSpaceLeft x y) ≫ x := by
  calc toPath x y ≫ (eval₀ (X := X))
      = fst x y ≫ (pathSliceUnder.fst x ≫ (eval₀ (X := X))) := by
        rw [toPath, Category.assoc]
    _ = fst x y ≫ (pathSliceUnder.snd x ≫ x) := by rw [pathSliceUnder.condition]
    _ = (fst x y ≫ pathSliceUnder.snd x) ≫ x := (Category.assoc _ _ _).symm
    _ = toDeltaZero (pathMappingSpaceLeft x y) ≫ x := by
        rw [toDeltaZero_eq (fst x y ≫ pathSliceUnder.snd x)]

/-- A map into the left mapping space from a path whose endpoints
are constantly `x` and `y`. -/
def lift {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    Z ⟶ pathMappingSpaceLeft x y :=
  pullback.lift (pathSliceUnder.lift x f hs) (toDeltaZero Z) (by
    rw [pathSliceUnder.lift_proj]
    exact ht)

@[reassoc (attr := simp)]
lemma lift_fst {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    lift x y f hs ht ≫ fst x y = pathSliceUnder.lift x f hs :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_toPath {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    lift x y f hs ht ≫ toPath x y = f := by
  rw [toPath, ← Category.assoc, lift_fst, pathSliceUnder.lift_fst]

/-- Maps into the left mapping space are determined by the
underlying path. -/
@[ext]
lemma hom_ext {Z : SSet.{u}} {f g : Z ⟶ pathMappingSpaceLeft x y}
    (h : f ≫ toPath x y = g ≫ toPath x y) : f = g := by
  apply pullback.hom_ext _ (stdSimplex.isTerminalObj₀.hom_ext _ _)
  apply pathSliceUnder.hom_ext
  rw [toPath, ← Category.assoc] at h
  exact h

/-- Maps into the left mapping space are exactly the paths whose
endpoints are constantly `x` and `y`. -/
def homEquiv (Z : SSet.{u}) :
    (Z ⟶ pathMappingSpaceLeft x y) ≃
      {f : Z ⟶ pathSpace X //
        f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x ∧
          f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y} where
  toFun f := ⟨f ≫ toPath x y, by
    constructor
    · rw [Category.assoc, toPath_src, ← Category.assoc,
        toDeltaZero_eq (f ≫ toDeltaZero (pathMappingSpaceLeft x y))]
    · rw [Category.assoc, toPath_tgt, ← Category.assoc,
        toDeltaZero_eq (f ≫ toDeltaZero (pathMappingSpaceLeft x y))]⟩
  invFun f := lift x y f.1 f.2.1 f.2.2
  left_inv f := hom_ext x y (lift_toPath x y _ _ _)
  right_inv f := Subtype.ext (lift_toPath x y f.1 f.2.1 f.2.2)

variable {Y : SSet.{u}} (f : X ⟶ Y)

/-- Functoriality of the left mapping space in `X`. -/
def map : pathMappingSpaceLeft x y ⟶ pathMappingSpaceLeft (x ≫ f) (y ≫ f) :=
  lift (x ≫ f) (y ≫ f) (toPath x y ≫ (ihom (Δ[1] : SSet.{u})).map f)
    (by
      rw [Category.assoc, pathSpace_map_eval₀, ← Category.assoc, toPath_src,
        Category.assoc, toDeltaZero_eq
          (toDeltaZero (pathMappingSpaceLeft x y))])
    (by
      rw [Category.assoc, pathSpace_map_eval₁, ← Category.assoc, toPath_tgt,
        Category.assoc, toDeltaZero_eq
          (toDeltaZero (pathMappingSpaceLeft x y))])

@[reassoc (attr := simp)]
lemma map_toPath : map x y f ≫ toPath (x ≫ f) (y ≫ f) =
    toPath x y ≫ (ihom (Δ[1] : SSet.{u})).map f :=
  lift_toPath _ _ _ _ _

end pathMappingSpaceLeft

/-- The mapping space between two vertices, as the fiber of the
endpoint pair map `pathPair X` over `(x, y)`. The left and right
mapping spaces are both canonically isomorphic to this fiber. -/
def pathMappingSpaceFiber (x y : (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  pullback (pathPair X) (prod.lift x y)

namespace pathMappingSpaceFiber

variable (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The underlying path in `X`. -/
def fst : pathMappingSpaceFiber x y ⟶ pathSpace X := pullback.fst _ _

/-- The (unique) map from the mapping-space fiber to `Δ[0]`. -/
def snd : pathMappingSpaceFiber x y ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

@[reassoc (attr := simp)]
lemma condition : fst x y ≫ pathPair X = snd x y ≫ prod.lift x y :=
  pullback.condition

lemma fst_src : fst x y ≫ (eval₀ (X := X)) =
    toDeltaZero (pathMappingSpaceFiber x y) ≫ x := by
  calc fst x y ≫ (eval₀ (X := X)) = (fst x y ≫ pathPair X) ≫ prod.fst := by
        rw [Category.assoc, pathPair_fst]
    _ = (snd x y ≫ prod.lift x y) ≫ prod.fst := by rw [condition]
    _ = snd x y ≫ x := by rw [Category.assoc, prod.lift_fst]
    _ = toDeltaZero (pathMappingSpaceFiber x y) ≫ x := by
        rw [toDeltaZero_eq (snd x y)]

lemma fst_tgt : fst x y ≫ (eval₁ (X := X)) =
    toDeltaZero (pathMappingSpaceFiber x y) ≫ y := by
  calc fst x y ≫ (eval₁ (X := X)) = (fst x y ≫ pathPair X) ≫ prod.snd := by
        rw [Category.assoc, pathPair_snd]
    _ = (snd x y ≫ prod.lift x y) ≫ prod.snd := by rw [condition]
    _ = snd x y ≫ y := by rw [Category.assoc, prod.lift_snd]
    _ = toDeltaZero (pathMappingSpaceFiber x y) ≫ y := by
        rw [toDeltaZero_eq (snd x y)]

/-- A map into the mapping-space fiber from a path whose endpoints
are constantly `x` and `y`. -/
def lift {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    Z ⟶ pathMappingSpaceFiber x y :=
  pullback.lift f (toDeltaZero Z) (by
    apply prod.hom_ext <;>
      simp only [Category.assoc, pathPair_fst, pathPair_snd,
        prod.lift_fst, prod.lift_snd]
    · exact hs
    · exact ht)

@[reassoc (attr := simp)]
lemma lift_fst {Z : SSet.{u}} (f : Z ⟶ pathSpace X)
    (hs : f ≫ (eval₀ (X := X)) = toDeltaZero Z ≫ x)
    (ht : f ≫ (eval₁ (X := X)) = toDeltaZero Z ≫ y) :
    lift x y f hs ht ≫ fst x y = f :=
  pullback.lift_fst _ _ _

/-- Maps into the mapping-space fiber are determined by the
underlying path. -/
@[ext]
lemma hom_ext {Z : SSet.{u}} {f g : Z ⟶ pathMappingSpaceFiber x y}
    (h : f ≫ fst x y = g ≫ fst x y) : f = g :=
  pullback.hom_ext h (stdSimplex.isTerminalObj₀.hom_ext _ _)

end pathMappingSpaceFiber

variable (x y : (Δ[0] : SSet.{u}) ⟶ X)

/-- The right mapping space is canonically isomorphic to the fiber
of the endpoint pair map. -/
def pathMappingSpaceRightIsoFiber :
    pathMappingSpaceRight x y ≅ pathMappingSpaceFiber x y where
  hom := pathMappingSpaceFiber.lift x y (pathMappingSpaceRight.toPath x y)
    (pathMappingSpaceRight.toPath_src x y) (pathMappingSpaceRight.toPath_tgt x y)
  inv := pathMappingSpaceRight.lift x y (pathMappingSpaceFiber.fst x y)
    (pathMappingSpaceFiber.fst_src x y) (pathMappingSpaceFiber.fst_tgt x y)
  hom_inv_id := pathMappingSpaceRight.hom_ext x y (by simp)
  inv_hom_id := pathMappingSpaceFiber.hom_ext x y (by simp)

/-- The left mapping space is canonically isomorphic to the fiber
of the endpoint pair map. -/
def pathMappingSpaceLeftIsoFiber :
    pathMappingSpaceLeft x y ≅ pathMappingSpaceFiber x y where
  hom := pathMappingSpaceFiber.lift x y (pathMappingSpaceLeft.toPath x y)
    (pathMappingSpaceLeft.toPath_src x y) (pathMappingSpaceLeft.toPath_tgt x y)
  inv := pathMappingSpaceLeft.lift x y (pathMappingSpaceFiber.fst x y)
    (pathMappingSpaceFiber.fst_src x y) (pathMappingSpaceFiber.fst_tgt x y)
  hom_inv_id := pathMappingSpaceLeft.hom_ext x y (by simp)
  inv_hom_id := pathMappingSpaceFiber.hom_ext x y (by simp)

/-- In the path-object model, the left and right mapping spaces
are canonically isomorphic: both compute the fiber of the endpoint
pair map. -/
def pathMappingSpaceLeftIsoRight :
    pathMappingSpaceLeft x y ≅ pathMappingSpaceRight x y :=
  pathMappingSpaceLeftIsoFiber x y ≪≫ (pathMappingSpaceRightIsoFiber x y).symm

/-- The mapping space between two vertices `x y : Δ[0] ⟶ X`, in
the path-object model. By definition this is the right mapping
space; it is canonically isomorphic to the left mapping space and
to the fiber of the endpoint pair map. -/
abbrev pathMappingSpace (x y : (Δ[0] : SSet.{u}) ⟶ X) : SSet.{u} :=
  pathMappingSpaceRight x y

/-- Being a quasicategory is invariant under isomorphism of
simplicial sets. -/
lemma quasicategory_of_iso {A B : SSet.{u}} (e : A ≅ B)
    [Quasicategory B] : Quasicategory A := by
  have hB : InnerFibration (terminal.from B) :=
    (quasicategory_iff_innerFibration B).1 inferInstance
  rw [quasicategory_iff_innerFibration]
  exact ⟨(innerFibrations.arrow_mk_iso_iff
    (Arrow.isoMk e (Iso.refl _))).2 hB.mem⟩

section InnerFibrations

variable [Quasicategory X]

/-- For a quasicategory `X`, source evaluation on the path object
is an inner fibration: it is precomposition with the monomorphism
`stdSimplex.δ 1`, followed by an isomorphism. -/
instance : InnerFibration ((eval₀ (X := X))) where
  mem := by
    rw [pathSpace_eval₀_eq]
    exact (MorphismProperty.cancel_right_of_respectsIso innerFibrations
      ((pre (stdSimplex.δ (1 : Fin 2))).app X)
      (evalDeltaZeroIso X).hom).2 (mem_innerFibrations _)

/-- For a quasicategory `X`, target evaluation on the path object
is an inner fibration. -/
instance : InnerFibration ((eval₁ (X := X))) where
  mem := by
    rw [pathSpace_eval₁_eq]
    exact (MorphismProperty.cancel_right_of_respectsIso innerFibrations
      ((pre (stdSimplex.δ (0 : Fin 2))).app X)
      (evalDeltaZeroIso X).hom).2 (mem_innerFibrations _)

/-- The defining map of the over-slice to `Δ[0]` is an inner
fibration (a base change of target evaluation). -/
instance (x : (Δ[0] : SSet.{u}) ⟶ X) :
    InnerFibration (pathSliceOver.snd x) where
  mem := MorphismProperty.pullback_snd _ _ (mem_innerFibrations _)

/-- The defining map of the under-slice to `Δ[0]` is an inner
fibration (a base change of source evaluation). -/
instance (x : (Δ[0] : SSet.{u}) ⟶ X) :
    InnerFibration (pathSliceUnder.snd x) where
  mem := MorphismProperty.pullback_snd _ _ (mem_innerFibrations _)

/-- The over-slice of a quasicategory at any vertex is a
quasicategory. -/
instance (x : (Δ[0] : SSet.{u}) ⟶ X) : Quasicategory (pathSliceOver x) :=
  quasicategory_of_innerFibration (pathSliceOver.snd x)

/-- The under-slice of a quasicategory at any vertex is a
quasicategory. -/
instance (x : (Δ[0] : SSet.{u}) ⟶ X) : Quasicategory (pathSliceUnder x) :=
  quasicategory_of_innerFibration (pathSliceUnder.snd x)

end InnerFibrations

lemma const_yonedaEquiv {Z : SSet.{u}} (f : (Δ[0] : SSet.{u}) ⟶ Z) :
    SSet.const (yonedaEquiv f) = f := by
  rw [← yonedaEquiv_symm_zero, Equiv.symm_apply_apply]

/-- The boundary of `Δ[1]` as the binary cofan of its two vertices:
the left inclusion is vertex `0` (that is, `boundary.ι 1`) and the
right inclusion is vertex `1` (that is, `boundary.ι 0`). -/
def boundaryOneCofan :
    BinaryCofan (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) :=
  BinaryCofan.mk (boundary.ι (1 : Fin 2)) (boundary.ι (0 : Fin 2))

/-- Evaluation of the internal hom out of `∂Δ[1]` at the source
vertex of the boundary. -/
def boundaryEvalSrc (X : SSet.{u}) :
    (ihom (∂Δ[1] : SSet.{u})).obj X ⟶ X :=
  (pre (boundary.ι (1 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom

/-- Evaluation of the internal hom out of `∂Δ[1]` at the target
vertex of the boundary. -/
def boundaryEvalTgt (X : SSet.{u}) :
    (ihom (∂Δ[1] : SSet.{u})).obj X ⟶ X :=
  (pre (boundary.ι (0 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom

/-- The `Δ[0]`-evaluation isomorphism of `PathSpace.lean` agrees
with `evalDeltaZeroIso` above. -/
lemma ihomZeroIso_hom_eq_evalDeltaZeroIso_hom (X : SSet.{u}) :
    (ihomZeroIso X).hom = (evalDeltaZeroIso X).hom := by
  rw [ihomZeroIso_hom, evalDeltaZeroIso_hom]

/-- The internal hom out of `∂Δ[1]` is the product of two copies
of `X`: a map out of the boundary is a pair of vertices. This is
the composite of the tensor-form isomorphism
`SSet.boundaryOneIhomIso` in `ModelCategory/PathSpace.lean` with
Mathlib's tensor-to-product comparison
`CartesianMonoidalCategory.tensorLeftIsoProd`. -/
def ihomBoundaryOneIso (X : SSet.{u}) :
    (ihom (∂Δ[1] : SSet.{u})).obj X ≅ X ⨯ X :=
  boundaryOneIhomIso X ≪≫
    (CartesianMonoidalCategory.tensorLeftIsoProd X).app X

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ihomBoundaryOneIso_hom_fst (X : SSet.{u}) :
    (ihomBoundaryOneIso X).hom ≫ prod.fst = boundaryEvalSrc X := by
  simp only [ihomBoundaryOneIso, Iso.trans_hom, Iso.app_hom]
  rw [Category.assoc, tensorLeftIsoProd_hom_fst,
    boundaryOneIhomIso_hom_fst, ihomZeroIso_hom_eq_evalDeltaZeroIso_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ihomBoundaryOneIso_hom_snd (X : SSet.{u}) :
    (ihomBoundaryOneIso X).hom ≫ prod.snd = boundaryEvalTgt X := by
  simp only [ihomBoundaryOneIso, Iso.trans_hom, Iso.app_hom]
  rw [Category.assoc, tensorLeftIsoProd_hom_snd,
    boundaryOneIhomIso_hom_snd, ihomZeroIso_hom_eq_evalDeltaZeroIso_hom]
  rfl

lemma pre_boundary_comp_boundaryEvalSrc (X : SSet.{u}) :
    (pre (boundary 1).ι).app X ≫ boundaryEvalSrc X = (eval₀ (X := X)) := by
  rw [pathSpace_eval₀_eq]
  change (pre (boundary 1).ι).app X ≫
      ((pre (boundary.ι (1 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom) =
    (pre (stdSimplex.δ (1 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom
  rw [← Category.assoc, ← NatTrans.comp_app, ← pre_map, boundary.ι_ι]

lemma pre_boundary_comp_boundaryEvalTgt (X : SSet.{u}) :
    (pre (boundary 1).ι).app X ≫ boundaryEvalTgt X = (eval₁ (X := X)) := by
  rw [pathSpace_eval₁_eq]
  change (pre (boundary 1).ι).app X ≫
      ((pre (boundary.ι (0 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom) =
    (pre (stdSimplex.δ (0 : Fin 2))).app X ≫ (evalDeltaZeroIso X).hom
  rw [← Category.assoc, ← NatTrans.comp_app, ← pre_map, boundary.ι_ι]

/-- Under `(ihom ∂Δ[1]).obj X ≅ X ⨯ X`, the endpoint pair map is
precomposition with the boundary inclusion `∂Δ[1].ι`. -/
lemma pathPair_eq (X : SSet.{u}) :
    pathPair X =
      (pre (boundary 1).ι).app X ≫ (ihomBoundaryOneIso X).hom := by
  apply prod.hom_ext <;>
    simp [pre_boundary_comp_boundaryEvalSrc X,
      pre_boundary_comp_boundaryEvalTgt X]

section PairInnerFibration

variable [Quasicategory X]

/-- For a quasicategory `X`, the endpoint pair map
`Fun(Δ[1], X) ⟶ X ⨯ X` is an inner fibration: it is
precomposition with the monomorphism `∂Δ[1].ι`, followed by the
isomorphism `ihomBoundaryOneIso`. -/
instance : InnerFibration (pathPair X) where
  mem := by
    rw [pathPair_eq]
    exact (MorphismProperty.cancel_right_of_respectsIso innerFibrations
      _ _).2 (mem_innerFibrations _)

/-- The defining map of the mapping-space fiber to `Δ[0]` is an
inner fibration (a base change of the endpoint pair map). -/
instance (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    InnerFibration (pathMappingSpaceFiber.snd x y) where
  mem := MorphismProperty.pullback_snd _ _ (mem_innerFibrations _)

/-- The mapping-space fiber in a quasicategory is a
quasicategory. -/
instance (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    Quasicategory (pathMappingSpaceFiber x y) :=
  quasicategory_of_innerFibration (pathMappingSpaceFiber.snd x y)

/-- The right mapping space in a quasicategory is a
quasicategory. See the file header for why this file does not
assert that it is a Kan complex. -/
instance (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    Quasicategory (pathMappingSpaceRight x y) :=
  quasicategory_of_iso (pathMappingSpaceRightIsoFiber x y)

/-- The left mapping space in a quasicategory is a
quasicategory. See the file header for why this file does not
assert that it is a Kan complex. -/
instance (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    Quasicategory (pathMappingSpaceLeft x y) :=
  quasicategory_of_iso (pathMappingSpaceLeftIsoFiber x y)

end PairInnerFibration

lemma pairPullbackOver_fst_src (x : (Δ[0] : SSet.{u}) ⟶ X) :
    pullback.fst (pathPair X) (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫
        (eval₀ (X := X)) =
      pullback.snd (pathPair X) (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) := by
  calc pullback.fst (pathPair X) (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫
          (eval₀ (X := X))
      = (pullback.fst (pathPair X) (prod.lift (𝟙 X)
          (toDeltaZero X ≫ x)) ≫ pathPair X) ≫ prod.fst := by
        rw [Category.assoc, pathPair_fst]
    _ = (pullback.snd (pathPair X) (prod.lift (𝟙 X)
          (toDeltaZero X ≫ x)) ≫
          prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫ prod.fst := by
        rw [pullback.condition]
    _ = pullback.snd (pathPair X) (prod.lift (𝟙 X)
          (toDeltaZero X ≫ x)) := by
        rw [Category.assoc, prod.lift_fst, Category.comp_id]

lemma pairPullbackOver_fst_tgt (x : (Δ[0] : SSet.{u}) ⟶ X) :
    pullback.fst (pathPair X) (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫
        (eval₁ (X := X)) =
      toDeltaZero (pullback (pathPair X)
        (prod.lift (𝟙 X) (toDeltaZero X ≫ x))) ≫ x := by
  calc pullback.fst (pathPair X) (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫
          (eval₁ (X := X))
      = (pullback.fst (pathPair X) (prod.lift (𝟙 X)
          (toDeltaZero X ≫ x)) ≫ pathPair X) ≫ prod.snd := by
        rw [Category.assoc, pathPair_snd]
    _ = (pullback.snd (pathPair X) (prod.lift (𝟙 X)
          (toDeltaZero X ≫ x)) ≫
          prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫ prod.snd := by
        rw [pullback.condition]
    _ = pullback.snd (pathPair X) (prod.lift (𝟙 X)
          (toDeltaZero X ≫ x)) ≫ (toDeltaZero X ≫ x) := by
        rw [Category.assoc, prod.lift_snd]
    _ = toDeltaZero (pullback (pathPair X)
          (prod.lift (𝟙 X) (toDeltaZero X ≫ x))) ≫ x := by
        rw [← Category.assoc,
          toDeltaZero_eq (pullback.snd (pathPair X)
            (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫ toDeltaZero X)]

/-- The over-slice is the base change of the endpoint pair map
along the graph of the vertex `x`: the slice projection is the
pullback projection. -/
def pathSliceOverIsoPairPullback (x : (Δ[0] : SSet.{u}) ⟶ X) :
    pathSliceOver x ≅
      pullback (pathPair X) (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) where
  hom := pullback.lift (pathSliceOver.fst x) (pathSliceOver.proj x) (by
    apply prod.hom_ext
    · calc (pathSliceOver.fst x ≫ pathPair X) ≫ prod.fst
          = pathSliceOver.fst x ≫ (eval₀ (X := X)) := by
            rw [Category.assoc, pathPair_fst]
        _ = pathSliceOver.proj x := rfl
        _ = (pathSliceOver.proj x ≫
              prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫ prod.fst := by
            rw [Category.assoc, prod.lift_fst, Category.comp_id]
    · calc (pathSliceOver.fst x ≫ pathPair X) ≫ prod.snd
          = pathSliceOver.fst x ≫ (eval₁ (X := X)) := by
            rw [Category.assoc, pathPair_snd]
        _ = pathSliceOver.snd x ≫ x := pathSliceOver.condition x
        _ = (pathSliceOver.proj x ≫
              prod.lift (𝟙 X) (toDeltaZero X ≫ x)) ≫ prod.snd := by
            rw [Category.assoc, prod.lift_snd, ← Category.assoc,
              toDeltaZero_eq (pathSliceOver.proj x ≫ toDeltaZero X),
              pathSliceOver.snd_eq])
  inv := pathSliceOver.lift x (pullback.fst _ _) (pairPullbackOver_fst_tgt x)
  hom_inv_id := pathSliceOver.hom_ext x (by
    simp only [Category.assoc, pathSliceOver.lift_fst, pullback.lift_fst,
      Category.id_comp])
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pathSliceOver.lift_fst,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd,
        pathSliceOver.lift_proj, Category.id_comp]
      exact pairPullbackOver_fst_src x

lemma pairPullbackUnder_fst_tgt (x : (Δ[0] : SSet.{u}) ⟶ X) :
    pullback.fst (pathPair X) (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫
        (eval₁ (X := X)) =
      pullback.snd (pathPair X) (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) := by
  calc pullback.fst (pathPair X) (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫
          (eval₁ (X := X))
      = (pullback.fst (pathPair X) (prod.lift (toDeltaZero X ≫ x)
          (𝟙 X)) ≫ pathPair X) ≫ prod.snd := by
        rw [Category.assoc, pathPair_snd]
    _ = (pullback.snd (pathPair X) (prod.lift (toDeltaZero X ≫ x)
          (𝟙 X)) ≫
          prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫ prod.snd := by
        rw [pullback.condition]
    _ = pullback.snd (pathPair X) (prod.lift (toDeltaZero X ≫ x)
          (𝟙 X)) := by
        rw [Category.assoc, prod.lift_snd, Category.comp_id]

lemma pairPullbackUnder_fst_src (x : (Δ[0] : SSet.{u}) ⟶ X) :
    pullback.fst (pathPair X) (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫
        (eval₀ (X := X)) =
      toDeltaZero (pullback (pathPair X)
        (prod.lift (toDeltaZero X ≫ x) (𝟙 X))) ≫ x := by
  calc pullback.fst (pathPair X) (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫
          (eval₀ (X := X))
      = (pullback.fst (pathPair X) (prod.lift (toDeltaZero X ≫ x)
          (𝟙 X)) ≫ pathPair X) ≫ prod.fst := by
        rw [Category.assoc, pathPair_fst]
    _ = (pullback.snd (pathPair X) (prod.lift (toDeltaZero X ≫ x)
          (𝟙 X)) ≫
          prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫ prod.fst := by
        rw [pullback.condition]
    _ = pullback.snd (pathPair X) (prod.lift (toDeltaZero X ≫ x)
          (𝟙 X)) ≫ (toDeltaZero X ≫ x) := by
        rw [Category.assoc, prod.lift_fst]
    _ = toDeltaZero (pullback (pathPair X)
          (prod.lift (toDeltaZero X ≫ x) (𝟙 X))) ≫ x := by
        rw [← Category.assoc,
          toDeltaZero_eq (pullback.snd (pathPair X)
            (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫ toDeltaZero X)]

/-- The under-slice is the base change of the endpoint pair map
along the graph of the vertex `x`. -/
def pathSliceUnderIsoPairPullback (x : (Δ[0] : SSet.{u}) ⟶ X) :
    pathSliceUnder x ≅
      pullback (pathPair X) (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) where
  hom := pullback.lift (pathSliceUnder.fst x) (pathSliceUnder.proj x) (by
    apply prod.hom_ext
    · calc (pathSliceUnder.fst x ≫ pathPair X) ≫ prod.fst
          = pathSliceUnder.fst x ≫ (eval₀ (X := X)) := by
            rw [Category.assoc, pathPair_fst]
        _ = pathSliceUnder.snd x ≫ x := pathSliceUnder.condition x
        _ = (pathSliceUnder.proj x ≫
              prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫ prod.fst := by
            rw [Category.assoc, prod.lift_fst, ← Category.assoc,
              toDeltaZero_eq (pathSliceUnder.proj x ≫ toDeltaZero X),
              pathSliceUnder.snd_eq]
    · calc (pathSliceUnder.fst x ≫ pathPair X) ≫ prod.snd
          = pathSliceUnder.fst x ≫ (eval₁ (X := X)) := by
            rw [Category.assoc, pathPair_snd]
        _ = pathSliceUnder.proj x := rfl
        _ = (pathSliceUnder.proj x ≫
              prod.lift (toDeltaZero X ≫ x) (𝟙 X)) ≫ prod.snd := by
            rw [Category.assoc, prod.lift_snd, Category.comp_id])
  inv := pathSliceUnder.lift x (pullback.fst _ _) (pairPullbackUnder_fst_src x)
  hom_inv_id := pathSliceUnder.hom_ext x (by
    simp only [Category.assoc, pathSliceUnder.lift_fst, pullback.lift_fst,
      Category.id_comp])
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pathSliceUnder.lift_fst,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd,
        pathSliceUnder.lift_proj, Category.id_comp]
      exact pairPullbackUnder_fst_tgt x

section ProjInnerFibration

variable [Quasicategory X]

/-- For a quasicategory `X`, the over-slice projection
`pathSliceOver.proj x : pathSliceOver x ⟶ X` is an inner fibration: under
`pathSliceOverIsoPairPullback` it is the base change of the endpoint
pair map along the graph of `x`. -/
instance (x : (Δ[0] : SSet.{u}) ⟶ X) :
    InnerFibration (pathSliceOver.proj x) where
  mem := by
    have h : pathSliceOver.proj x = (pathSliceOverIsoPairPullback x).hom ≫
        pullback.snd (pathPair X)
          (prod.lift (𝟙 X) (toDeltaZero X ≫ x)) :=
      (pullback.lift_snd _ _ _).symm
    rw [h]
    exact (MorphismProperty.cancel_left_of_respectsIso innerFibrations
      _ _).2 (MorphismProperty.pullback_snd _ _
        (mem_innerFibrations _))

/-- For a quasicategory `X`, the under-slice projection is an
inner fibration. -/
instance (x : (Δ[0] : SSet.{u}) ⟶ X) :
    InnerFibration (pathSliceUnder.proj x) where
  mem := by
    have h : pathSliceUnder.proj x = (pathSliceUnderIsoPairPullback x).hom ≫
        pullback.snd (pathPair X)
          (prod.lift (toDeltaZero X ≫ x) (𝟙 X)) :=
      (pullback.lift_snd _ _ _).symm
    rw [h]
    exact (MorphismProperty.cancel_left_of_respectsIso innerFibrations
      _ _).2 (MorphismProperty.pullback_snd _ _
        (mem_innerFibrations _))

end ProjInnerFibration

end SSet
