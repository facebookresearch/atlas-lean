/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexQuasicategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.Join
public import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex

/-!
# Pre-fibrant simplicial sets

This file formalizes Danny Stevenson's *pre-fibrant simplicial sets*
from §3 of *Notes on the Joyal model structure* (arXiv:1810.05233v1),
together with the basic examples from §3.1 and an inner-anodyne
replacement theorem. This is packet T19 of the Joyal model structure
blueprint (phase JY2).

## The definition implemented

Stevenson, Definition 3.1, verbatim:

> Definition 3.1. We will say that simplicial set S is pre-fibrant if
> it satisfies the following conditions:
> (i) every map Λ²₁ → S extends along the inclusion Λ²₁ ⊆ Δ².
> (ii) for every 0 < i < n, if f : Λⁿᵢ → S is a map such that d₀f is a
> constant (n−1)-simplex, then f extends along the inclusion
> Λⁿᵢ ⊆ Δⁿ.
> Here we will say that an n-simplex x ∈ S is constant if
> x = s₀ⁿ(v) for some vertex v of S.

Here `Λ²₁` is the inner horn `Λ[2, 1]`, `s₀ⁿ(v)` is the `n`-fold
iterate of the `0`-th degeneracy operator applied to the vertex `v`
(`SSet.constSimplex`, characterized recursively by
`SSet.constSimplex_zero` and `SSet.constSimplex_succ`), and `d₀f` is
the `0`-th face of the horn map `f`, i.e. the restriction of `f`
along the face inclusion `δ⁰ : Δ[n-1] ≅ Δ[{1, …, n}] ↪ Λ[n, i]`
(which lands in the horn because `i ≠ 0`). We formalize `d₀f` as the
simplex `SSet.hornFaceZero f h := f.app _ (horn.face i 0 h)`, and
`SSet.hornFaceZero_eq_yonedaEquiv` identifies it with the simplex
classified by the face map `horn.ι i 0 h ≫ f : Δ[n-1] ⟶ S`, which is
the form in which `d₀` appears in Stevenson's descent arguments
(e.g. the pullbacks `d₀(α)*Z` of §4). The predicate
`SSet.IsConstantSimplex` is Stevenson's "constant" and
`SSet.IsPreFibrant` is Definition 3.1, with the quantifiers in the
shifted form `Λ[n + 2, i]` used by the pinned
`SSet.Quasicategory.hornFilling'`.

Note that condition (i) is not redundant: condition (ii) at `n = 2`
only fills `Λ[2, 1]`-horns whose `0`-th face (the edge `1 → 2`) is
degenerate.

## Relation to slices and mapping spaces (read before using)

Stevenson's Definition 3.1 is purely a horn-filling condition: it
mentions **no** mapping-space or slice object, in either the naive
(join-slice) model of his §2.4 or any exponential (path-object)
model. Accordingly, the formal predicate `SSet.IsPreFibrant` in
this file is exactly that horn-filling condition and uses no slice
or mapping-space object of either model; its meaning does not
depend on any choice of mapping-space model, and this file does
not even import the path-slice API of [Slice.lean](Slice.lean).
(The instance that standard simplices are quasicategories, used
for the examples below, now comes from
[StdSimplexQuasicategory.lean](StdSimplexQuasicategory.lean).)
Slices enter Stevenson's §3 only through the *consequences* of
pre-fibrancy for (naive, join-slice) mapping spaces:

* Remark 3.3: if `S` is pre-fibrant, the *naive* mapping space
  `Homᴸ_S(x, y)` is a Kan complex;
* Proposition 3.5: if `S` is pre-fibrant, there exists an inner
  anodyne map `f : S → T` such that `T` is an `∞`-category and the
  induced map `S_{x/} ×_S {y} → T_{x/} ×_T {y}` is an isomorphism
  for every pair of vertices `x, y ∈ S`.

Stevenson's `Homᴸ_S(x, y) = S_{x/} ×_S {y}` (§2.4) is a fiber of a
*join* (under-)slice: its `n`-simplices are the maps `Δ[n+1] → S`
sending vertex `0` to `x` and `Δ[{1, …, n+1}]` to the constant
simplex at `y`. Both slice models are now landed. The exponential
(path-object) ones are in [Slice.lean](Slice.lean):
`SSet.pathMappingSpaceLeft x y` and `SSet.pathMappingSpaceRight x y`
are fibers of the endpoint evaluations `SSet.eval₀`/`SSet.eval₁` on
the path object `Fun(Δ[1], S)` (`SSet.pathSpace S`). The genuine
join slices are in [JoinSlice.lean](JoinSlice.lean) (packet F5):
`SSet.sliceUnder S x` (Stevenson's `S_{x/}`) and
`SSet.sliceOver S y`, with left/right mapping spaces
`SSet.mappingSpaceLeft S x y` — the fiber of
`SSet.sliceUnder.proj` at `y`, i.e. Stevenson's `Homᴸ` — and
`SSet.mappingSpaceRight S x y` (`Homᴿ`). Remark 3.3 and the
mapping-space-preservation part of Proposition 3.5 — Proposition
3.5(2) in Stevenson's numbering — are therefore now *statable*
faithfully, using `SSet.mappingSpaceLeft` for `Homᴸ`; their
*proofs* are still
missing, and they are neither stated nor proved in this file (which
does not import [JoinSlice.lean](JoinSlice.lean)). Two caveats for
anyone stating them: as documented in the header of
[Slice.lean](Slice.lean), the path slices are not the join slices
on the nose (hence their `path`-prefixed names), no comparison map
between the two models is landed, and restating Remark 3.3 or
Proposition 3.5(2) with `pathMappingSpaceLeft` in place of `Homᴸ`
would silently change their content; and as documented in the
header of [JoinSlice.lean](JoinSlice.lean), the endpoint condition
in the `(n+1)`-simplex description of the join slices is currently
phrased with the transported vertex maps `SSet.leftVertex` /
`SSet.rightVertex`, whose identification with the standard
vertex inclusions `Δ[0] ⟶ Δ[n+1]` is not yet proved. Nothing about
`SSet.IsPreFibrant` itself is affected by any of this, since
Definition 3.1 involves no mapping spaces.

## The replacement theorem, and how it differs from Stevenson's

Stevenson uses pre-fibrant objects through two distinct replacement
constructions:

* Proposition 4.12 takes an *arbitrary* simplicial set `S` to a
  pre-fibrant `T` by a *selective* small object argument: at each
  stage one attaches only the inner horns `Λⁿᵢ → S(m)` whose `d₀` is
  constant (no condition at `n = 2`). The resulting inner anodyne
  map `S → T` moreover satisfies inner-anodyne descent for every
  inner fibration over `S`. The target is in general only
  pre-fibrant, not an `∞`-category.
* Proposition 3.5 starts from an already pre-fibrant `S` and attaches
  only the horns whose `d₀` is *non*-constant, reaching an
  `∞`-category `T` without changing the naive mapping spaces.

The replacement proved here, `SSet.toPreFibrantReplacement`, is
neither of these selective constructions. It is the ordinary inner
horn small object argument already landed upstream
(`HasSmallObjectArgument SSet.innerHornInclusions`), applied to
`X → ⊤`: it produces an inner anodyne map to a *quasicategory*,
which is pre-fibrant by Stevenson's Example 3.2 (every
`∞`-category is pre-fibrant). This proves the mere existence
statement "every simplicial set admits an inner anodyne map to a
pre-fibrant simplicial set"
(`SSet.exists_innerAnodyneExtensions_and_isPreFibrant`), but the map
has neither the descent property of Proposition 4.12 nor the
mapping-space preservation of Proposition 3.5. Do not cite it for
either.

## TODO

* Remark 3.3 (`Homᴸ_S(x, y)` is a Kan complex when `S` is
  pre-fibrant) and Proposition 3.5 (in particular the
  mapping-space preservation, 3.5(2)). The naive mapping spaces
  themselves are landed as fibers of the genuine join slices in
  [JoinSlice.lean](JoinSlice.lean) (packet F5:
  `SSet.mappingSpaceLeft`), so both statements are now statable;
  the proofs are missing. They must not be restated using the
  exponential path mapping spaces of [Slice.lean](Slice.lean).
  Remaining inputs include the last/first-vertex identification
  for `SSet.rightVertex` / `SSet.leftVertex` recorded in
  [JoinSlice.lean](JoinSlice.lean),
  and for Proposition 3.5 a selective horn-attachment argument,
  not the bundled functorial factorization used here.
* The selective small object argument of Proposition 4.12 and its
  descent property (Stevenson §4). This needs a variant of the small
  object argument attaching only a designated family of horn maps;
  the landed `HasSmallObjectArgument` API attaches all of them.
* Lemma 3.8 (`π₀` of naive mapping spaces computes `h(S)`) and the
  rest of §3.3, which depend on Proposition 3.5.

## References

- D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233v1, §§2.4, 3, 4.
- J. Lurie, *Higher Topos Theory*, §1.2.8 (joins), §1.2.9
  (slices) and §1.2.2 (mapping spaces).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {S T X : SSet.{u}}

/-! ### Constant simplices -/

/-- The constant `n`-simplex of `S` at a vertex `v`: the image of
`v` under the (unique) map induced by `⦋n⦌ ⟶ ⦋0⦌`. By
`constSimplex_zero` and `constSimplex_succ` this is Stevenson's
`s₀ⁿ(v)`, the `n`-fold iterate of the `0`-th degeneracy. -/
def constSimplex (S : SSet.{u}) (n : ℕ) (v : S _⦋0⦌) : S _⦋n⦌ :=
  S.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op v

/-- The constant `0`-simplex at `v` is `v`. -/
@[simp]
lemma constSimplex_zero (v : S _⦋0⦌) : constSimplex S 0 v = v := by
  simp [constSimplex]

/-- The constant `(n+1)`-simplex at `v` is the `0`-th degeneracy of
the constant `n`-simplex at `v`; inductively,
`constSimplex S n v = s₀ⁿ(v)` in Stevenson's notation. -/
lemma constSimplex_succ (n : ℕ) (v : S _⦋0⦌) :
    constSimplex S (n + 1) v = S.σ (0 : Fin (n + 1)) (constSimplex S n v) := by
  have h : (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0) =
      SimplexCategory.σ (0 : Fin (n + 1)) ≫ SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 :=
    Subsingleton.elim _ _
  calc constSimplex S (n + 1) v
      = S.map (SimplexCategory.σ (0 : Fin (n + 1)) ≫
          SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op v := by rw [constSimplex, h]
    _ = S.σ (0 : Fin (n + 1)) (constSimplex S n v) := by
        simp [constSimplex, SimplicialObject.σ_def]

/-- The simplex classified by the constant map `Δ[n] ⟶ S` at a vertex
`v` is the constant `n`-simplex at `v`. -/
lemma yonedaEquiv_const_eq (n : ℕ) (v : S _⦋0⦌) :
    yonedaEquiv (SSet.const v : Δ[n] ⟶ S) = constSimplex S n v := by
  have h1 : (SSet.const v : Δ[n] ⟶ S) =
      stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) ≫
        (SSet.const v : Δ[0] ⟶ S) := by
    rw [SSet.comp_const]
  rw [h1, ← yonedaEquiv_naturality, yonedaEquiv_const]
  rfl

/-- A simplex is *constant* if it is `s₀ⁿ(v)` for some vertex `v`
(Stevenson's terminology before Definition 3.1). -/
def IsConstantSimplex {n : ℕ} (x : S _⦋n⦌) : Prop :=
  ∃ v : S _⦋0⦌, x = constSimplex S n v

/-- Constant simplices are constant. -/
lemma isConstantSimplex_constSimplex (n : ℕ) (v : S _⦋0⦌) :
    IsConstantSimplex (constSimplex S n v) :=
  ⟨v, rfl⟩

/-- Constant simplices are preserved by simplicial maps. -/
lemma IsConstantSimplex.map {n : ℕ} {x : S _⦋n⦌} (hx : IsConstantSimplex x)
    (p : S ⟶ T) : IsConstantSimplex (p.app _ x) := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨p.app _ v, ?_⟩
  exact NatTrans.naturality_apply p _ v

/-- A map out of a standard simplex classifies a constant simplex if
and only if it is a constant map at some vertex. -/
lemma isConstantSimplex_yonedaEquiv_iff {n : ℕ} (f : Δ[n] ⟶ S) :
    IsConstantSimplex (yonedaEquiv f) ↔ ∃ v : S _⦋0⦌, f = SSet.const v := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, yonedaEquiv.injective ?_⟩
    rw [hv, yonedaEquiv_const_eq]
  · rintro ⟨v, rfl⟩
    rw [yonedaEquiv_const_eq]
    exact isConstantSimplex_constSimplex n v

/-! ### The `0`-th face of a horn map -/

/-- The `0`-th face of a horn map `f : Λ[n+2, i] ⟶ S`, as an
`(n+1)`-simplex of `S`: Stevenson's `d₀f`. It is the image under
`f` of the `0`-th codimension-one face of the horn, which exists
because `i ≠ 0`. -/
def hornFaceZero {n : ℕ} {i : Fin (n + 3)} (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S)
    (h : (0 : Fin (n + 3)) ≠ i) : S _⦋n + 1⦌ :=
  f.app _ (horn.face i 0 h)

/-- The `0`-th face of a composite horn map is the image of the
`0`-th face. -/
@[simp]
lemma hornFaceZero_comp {n : ℕ} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (h : (0 : Fin (n + 3)) ≠ i)
    (p : S ⟶ T) : hornFaceZero (f ≫ p) h = p.app _ (hornFaceZero f h) :=
  rfl

/-- The `0`-th face of a horn map is the simplex classified by
restricting the horn map along the face inclusion
`Δ[n+1] ⟶ Λ[n+2, i]` opposite vertex `0`; this is `d₀f` as a map,
the form used in Stevenson's pullback arguments. -/
lemma hornFaceZero_eq_yonedaEquiv {n : ℕ} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (h : (0 : Fin (n + 3)) ≠ i) :
    hornFaceZero f h = yonedaEquiv (horn.ι i 0 h ≫ f) := by
  rw [hornFaceZero, yonedaEquiv_comp, horn.yonedaEquiv_ι]

/-! ### Pre-fibrant simplicial sets -/

/-- A simplicial set `S` is *pre-fibrant* (Stevenson, Definition 3.1)
if every `Λ[2, 1]`-horn in `S` fills, and every inner horn in `S`
whose `0`-th face is a constant simplex fills. -/
class IsPreFibrant (S : SSet.{u}) : Prop where
  hornFillingTwo' : ∀ (σ₀ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶ S),
    ∃ σ : Δ[2] ⟶ S, σ₀ = Λ[2, (1 : Fin 3)].ι ≫ σ
  hornFillingConst' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄
    (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (_h0 : 0 < i)
    (_hn : i < Fin.last (n + 2)),
    IsConstantSimplex (hornFaceZero σ₀ (ne_of_lt _h0)) →
      ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ

namespace IsPreFibrant

variable [IsPreFibrant S]

/-- In a pre-fibrant simplicial set, every `Λ[2, 1]`-horn fills
(Definition 3.1(i)). -/
lemma hornFillingTwo (σ₀ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶ S) :
    ∃ σ : Δ[2] ⟶ S, σ₀ = Λ[2, (1 : Fin 3)].ι ≫ σ :=
  hornFillingTwo' σ₀

/-- In a pre-fibrant simplicial set, every inner horn whose `0`-th
face is constant fills (Definition 3.1(ii)). -/
lemma hornFillingConst {n : ℕ} {i : Fin (n + 3)}
    (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (h0 : 0 < i)
    (hn : i < Fin.last (n + 2))
    (hconst : IsConstantSimplex (hornFaceZero σ₀ (ne_of_lt h0))) :
    ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ :=
  hornFillingConst' σ₀ h0 hn hconst

end IsPreFibrant

/-- Every quasicategory (Stevenson's `∞`-category) is pre-fibrant
(Stevenson, Example 3.2): both filling conditions are special cases
of inner horn filling. -/
instance (S : SSet.{u}) [Quasicategory S] : IsPreFibrant S where
  hornFillingTwo' σ₀ := Quasicategory.hornFilling (by decide) (by decide) σ₀
  hornFillingConst' n i σ₀ h0 hn _ := Quasicategory.hornFilling' σ₀ h0 hn

/-- Being pre-fibrant is invariant under isomorphism of simplicial
sets. -/
lemma isPreFibrant_of_iso {A B : SSet.{u}} (e : A ≅ B) [IsPreFibrant B] :
    IsPreFibrant A where
  hornFillingTwo' σ₀ := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingTwo (S := B) (σ₀ ≫ e.hom)
    exact ⟨σ ≫ e.inv, by
      rw [← Category.assoc, ← hσ, Category.assoc, e.hom_inv_id,
        Category.comp_id]⟩
  hornFillingConst' n i σ₀ h0 hn hconst := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingConst (S := B) (σ₀ ≫ e.hom)
      h0 hn (by rw [hornFaceZero_comp]; exact hconst.map e.hom)
    exact ⟨σ ≫ e.inv, by
      rw [← Category.assoc, ← hσ, Category.assoc, e.hom_inv_id,
        Category.comp_id]⟩

/-- If `p : X → S` is an inner fibration and `S` is pre-fibrant,
then `X` is pre-fibrant (Stevenson, Remark 3.4, first part): fill
the horn in `S` and lift the filler along `p`; constancy of the
`0`-th face is preserved by `p`. -/
lemma isPreFibrant_of_innerFibration (p : X ⟶ S) [InnerFibration p]
    [IsPreFibrant S] : IsPreFibrant X where
  hornFillingTwo' σ₀ := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingTwo (S := S) (σ₀ ≫ p)
    have : HasLiftingProperty Λ[2, (1 : Fin 3)].ι p :=
      InnerFibration.mem _
        (horn_ι_mem_innerHornInclusions (by decide) (by decide))
    let sq : CommSq σ₀ Λ[2, (1 : Fin 3)].ι p σ := CommSq.mk hσ
    exact ⟨sq.lift, sq.fac_left.symm⟩
  hornFillingConst' n i σ₀ h0 hn hconst := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingConst (S := S) (σ₀ ≫ p)
      h0 hn (by rw [hornFaceZero_comp]; exact hconst.map p)
    have : HasLiftingProperty Λ[n + 2, i].ι p :=
      InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
    let sq : CommSq σ₀ Λ[n + 2, i].ι p σ := CommSq.mk hσ
    exact ⟨sq.lift, sq.fac_left.symm⟩

/-- A full subcomplex of a pre-fibrant simplicial set is pre-fibrant
(Stevenson, Remark 3.4, second part), since the inclusion of a full
subcomplex is an inner fibration. -/
instance (S : Set (X _⦋0⦌)) [IsPreFibrant X] :
    IsPreFibrant (Subcomplex.full S : SSet.{u}) :=
  isPreFibrant_of_innerFibration (Subcomplex.full S).ι

/-- The join of two standard simplices is pre-fibrant, since
`Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]` is a quasicategory. -/
instance (m n : ℕ) : IsPreFibrant ((Δ[m] : SSet.{u}) ⋆ Δ[n]) :=
  isPreFibrant_of_iso (joinStdSimplexIso m n)

/-! ### Inner-anodyne replacement by a pre-fibrant simplicial set -/

/-- The functorial factorization of `X → ⊤` produced by the inner
horn small object argument: an inner anodyne map (in
`innerHornInclusions.rlp.llp = innerAnodyneExtensions`) followed by
an inner fibration (in `innerHornInclusions.rlp =
innerFibrations`). -/
noncomputable def preFibrantReplacementData (X : SSet.{u}) :
    MorphismProperty.MapFactorizationData innerHornInclusions.rlp.llp
      innerHornInclusions.rlp (terminal.from X) :=
  MorphismProperty.factorizationData _ _ _

/-- The replacement target of `X`: the middle object of
`preFibrantReplacementData X`. It is a quasicategory (hence
pre-fibrant), reached from `X` by an inner anodyne map. This is the
full small-object replacement, not Stevenson's selective
constructions in Propositions 3.5 and 4.12; see the file header. -/
noncomputable abbrev preFibrantReplacement (X : SSet.{u}) : SSet.{u} :=
  (preFibrantReplacementData X).Z

/-- The replacement map from a simplicial set to its (quasicategory,
hence pre-fibrant) replacement. -/
noncomputable def toPreFibrantReplacement (X : SSet.{u}) :
    X ⟶ preFibrantReplacement X :=
  (preFibrantReplacementData X).i

/-- The replacement map is inner anodyne. -/
lemma innerAnodyneExtensions_toPreFibrantReplacement (X : SSet.{u}) :
    innerAnodyneExtensions (toPreFibrantReplacement X) := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact (preFibrantReplacementData X).hi

/-- The map from the replacement to the terminal object is an inner
fibration. -/
instance : InnerFibration (preFibrantReplacementData X).p :=
  ⟨(preFibrantReplacementData X).hp⟩

/-- The replacement of any simplicial set is a quasicategory. -/
instance (X : SSet.{u}) : Quasicategory (preFibrantReplacement X) :=
  (quasicategory_iff_of_isTerminal _ terminalIsTerminal).mpr
    ⟨(preFibrantReplacementData X).hp⟩

/-- Every simplicial set admits an inner anodyne map to a
pre-fibrant simplicial set. The target here is in fact a
quasicategory, by the full inner horn small object argument;
Stevenson's Proposition 4.12 constructs a smaller merely
pre-fibrant target with a descent property, which this map does not
have (see the file header). -/
theorem exists_innerAnodyneExtensions_and_isPreFibrant (X : SSet.{u}) :
    ∃ (T : SSet.{u}) (f : X ⟶ T), innerAnodyneExtensions f ∧ IsPreFibrant T :=
  ⟨preFibrantReplacement X, toPreFibrantReplacement X,
    innerAnodyneExtensions_toPreFibrantReplacement X, inferInstance⟩

/-- Every simplicial set admits an inner anodyne map to a
quasicategory (the replacement actually constructed here). -/
theorem exists_innerAnodyneExtensions_and_quasicategory (X : SSet.{u}) :
    ∃ (T : SSet.{u}) (f : X ⟶ T), innerAnodyneExtensions f ∧ Quasicategory T :=
  ⟨preFibrantReplacement X, toPreFibrantReplacement X,
    innerAnodyneExtensions_toPreFibrantReplacement X, inferInstance⟩

end SSet

end
