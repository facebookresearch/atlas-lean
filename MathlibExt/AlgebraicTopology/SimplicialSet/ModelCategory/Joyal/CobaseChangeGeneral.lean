/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeMono
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoFunctorCategorical
public import
  MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-! # Cobase change along monomorphisms into general quasicategories (packet T34)

This module attacks the two inputs left open by packets T30/T31,
TODO(T31-A) and TODO(T31-B) in the header of `CobaseChangeMono.lean`,
towards the unconditional stability statement

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}).
```

Methodologically, this header first gives a complete informal proof
with every definition unfolded and every reduction named. The formal
content below then proves the largest subset that the landed API
supports: the pointwise/core analysis (including a formal
counterexample showing that the naive core route to (A) has a gap),
the fullness half of (B) unconditionally, the `0`-dimensional cell
of (A), and the resulting conditional assemblies. The parts of the
informal proof that are
*not* formalized here are isolated at the end as precise blockers
TODO(T34-A) (prism triangulation and the pointwise criterion) and
TODO(T34-B2) (correction of `2`-simplices). Nothing in this module
claims (A) for a general quasicategory target, and the unconditional
stability instance above is *not* proved here: by
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`
(packet T30) it still requires TODO(T34-A) and TODO(T34-B2).

## 0. The statements, unfolded

Fix a pushout square `sq : IsPushout i f f' j` of simplicial sets

```text
A --i--> B
|        |
f        f'
v        v
X --j--> Y
```

with `[Mono i]` and `hf : SSet.categoricalEquivalences f`. By
`SSet.categoricalEquivalences.mem_iff`, `hf` says: for every
quasicategory `C`, the functor
`hFun(f, C) := (SSet.hoFunctor.map ((MonoidalClosed.pre f).app C)).toFunctor :
h((ihom X).obj C) ⥤ h((ihom A).obj C)` is an equivalence of ordinary
categories, and the goal `categoricalEquivalences f'` is the same
statement for `hFun(f', C) : h Fun(Y, C) ⥤ h Fun(B, C)`. Here
`Fun(W, C) := (ihom W).obj C`, `(pre g).app C` is precomposition with
`g`, and `h = SSet.hoFunctor.obj`. Objects of `h Fun(W, C)` are the
vertices of `Fun(W, C)` (through `SSet.HomotopyCategory.mk` and
`SSet.HomotopyCategory.objEquiv`), i.e. by `SSet.ihomVertexEquiv`
the maps `W ⟶ C`; every morphism is `(HomotopyCategory.homMk e)` for an edge
`e : SSet.Edge x₀ x₁` (`SSet.Edge.exists_homMk_eq`, packet T08),
and `e.IsEquivalence` means `IsIso (HomotopyCategory.homMk e)`
(`SSet.Edge.isEquivalence_iff`).

Precomposition turns `sq` into a pullback
`SSet.isPullback_pre_app_of_isPushout sq C` (packet T30), with
gluing interface `SSet.exists_pre_lift_of_isPushout`: maps
`W ⟶ Fun(Y, C)` are pairs of maps into `Fun(B, C)` and `Fun(X, C)`
agreeing *on the nose* in `Fun(A, C)`. By the T30 assembly
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`,
the goal follows from:

* (A) for every quasicategory `C`,
  `hFun(i, C).IsIsofibration`. By
  `SSet.hoFunctor_pre_isIsofibration_iff` (packet T26) this is
  `SSet.HoPreEquivalenceEdgeLifting i C`: every equivalence edge
  `e` of `Fun(A, C)` out of a restricted vertex
  `((pre i).app C).app _ b` lifts to an equivalence edge `e'` of
  `Fun(B, C)` out of `b` with strict target restriction and
  `(HomotopyCategory.homMk (e'.map ((pre i).app C))) ≫ eqToHom _ = (HomotopyCategory.homMk e)`. By
  `SSet.hoPreEquivalenceEdgeLifting_of_strict_lift` it suffices to
  lift strictly at the simplex level,
  `(e'.map ((pre i).app C)).edge = e.edge`, and by
  `SSet.hoPrePrismStrictExtension_iff_strict_lift` /
  `SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`
  (packet T30) it suffices to prove
  `SSet.HoPrePrismStrictExtension i C`: through the prism
  dictionary `SSet.ihomSimplexOfPrism`/`SSet.ihomPrismOfSimplex`
  (`IhomPrism.lean`), the prism
  `ihomPrismOfSimplex e.edge : A ⊗ Δ[1] ⟶ C` extends along
  `i ▷ Δ[1]` to a prism `F : B ⊗ Δ[1] ⟶ C` with source vertex `b`
  (`δ_one_ihomSimplexOfPrism`), strict target restriction
  (`δ_zero_ihomSimplexOfPrism`, `ihomSimplexOfPrism_pre_app`), and
  `(edgeOfPrism F _ _).IsEquivalence`. Essential surjectivity of
  `hFun(f', C)` then follows from (A) alone by
  `SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration` (T30).
* (B) for every quasicategory `C`, `hFun(f', C)` is full and
  faithful. Packet T31 proved the key correction step
  `SSet.exists_edge_correction_of_innerFibration`: through an inner
  fibration `p` (here `p = (pre i).app C`, an inner fibration by
  `SSet.innerFibration_pre_app_of_mono`), an edge can be corrected
  within its `HomotopyCategory.homMk` class so that its strict image is a
  prescribed edge representing the same downstairs morphism; the
  lift is against the inner horn `Λ[2, 1]`.

## 1. The core route to (A), and its precise gap

Recall `SSet.core C` (`Core.lean`): the subcomplex of simplices all
of whose edges are equivalences
(`SSet.mem_core_obj_iff_forall_edge`); a `1`-simplex lies in it iff
its edge is an equivalence (`SSet.mem_core_obj_one_iff`); it has all
vertices (`SSet.mem_core_obj_zero`); maps restrict to cores
(`SSet.core.map`, `SSet.core.map_ι`); and for `[Quasicategory C]`
the core is a Kan complex
(`SSet.kanComplex_core_of_quasicategory`, packet T21, from Joyal's
special outer horn filling
`SSet.hasSpecialOuterHornFilling_of_quasicategory`). Packet T31
proved (A) when the target is a Kan complex:
`SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex`, by strict
lifting along the Kan fibration `(pre i).app K` against the anodyne
vertex inclusions of `Δ[1]`.

The proposed core route runs: an equivalence edge `e` of
`Fun(A, C)` has all vertex evaluations equivalences in `C`, hence
`e` factors through `Fun(A, core C)`, and lifting reduces to the
Kan-target case at `core C`. Two sub-claims are needed:

(i) (TRUE, formalized below as
`SSet.isEquivalence_mk'_app_of_ihomVertex_lift_core`.) A vertex of
`Fun(A, C)` lifting along postcomposition
`((ihom A).map (core C).ι).app _` is classified by a map
`A ⟶ core C` (`SSet.ihomVertexEquiv_ihom_map`), i.e. by a map
`g : A ⟶ C` every `1`-simplex of whose image is an equivalence:
`g = G ≫ (core C).ι`, `g.app _ s = (G.app _ s).1` with
`(G.app _ s).2 : _ ∈ (core C).obj _`, concluded by
`SSet.mem_core_obj_one_iff`.

(ii) (FALSE as stated.) The two endpoint vertices of an equivalence
edge `e` need *not* lift to `Fun(A, core C)`. Counterexample,
formalized below as
`SSet.exists_equivalence_edge_endpoint_not_lift_core`: let `e₀` be
any non-equivalence edge of `C` (e.g. in `C = nerve [1]` the edge
`ComposableArrows.mk₁ (0 ⟶ 1)`, a non-equivalence by
`SSet.Edge.isEquivalence_nerve_edgeMk_iff`), let
`b := ihomVertexEquiv Δ[1] C (yonedaEquiv.symm e₀.edge)`, the vertex
of `Fun(Δ[1], C)` classifying `e₀` itself. The identity edge
`Edge.id b` is an equivalence (`SSet.Edge.isEquivalence_id`), but
`b` does not lift to `Fun(Δ[1], core C)`: by (i) a lift would make
the image of the fundamental simplex `yonedaEquiv (𝟙 Δ[1])`, which
is `e₀.edge`, an equivalence. In particular the source vertex `b`
in the lifting problem of (A) is an arbitrary map `B ⟶ C`; nothing
forces its edges to be equivalences.

The vertex evaluations are indeed equivalences (formalized as
`SSet.Edge.IsEquivalence.eval_vertex`): evaluation at a vertex
`v : Δ[0] ⟶ A` is the composite simplicial map
`Fun(A, C) --(pre v).app C--> Fun(Δ[0], C) --(evalDeltaZeroIso C).hom--> C`,
and simplicial maps preserve equivalences
(`SSet.Edge.IsEquivalence.map`). But pointwise data does not repair
(ii). Transposing, `e` is a prism `H : A ⊗ Δ[1] ⟶ C`; for `H` to
factor through `core C` *every* edge of `A ⊗ Δ[1]` must land on an
equivalence, including the horizontal edges
`(edge of A) ⊗ {0}` and `(edge of A) ⊗ {1}`, which are the edges of
the endpoint maps — arbitrary by (ii). The diagonal edges of the
naturality squares (one for each edge `α : x ⟶ y` of `A`, with sides
the two endpoint images of `α` and the two pointwise equivalences at
`x`, `y`) are composites, in either triangulation of the square, of
one pointwise equivalence with one arbitrary endpoint edge; they are
therefore not equivalences in general, and composition closure of
equivalences (`SSet.Edge.IsEquivalence.of_compStruct`,
`SSet.Edge.isEquivalence_iff_nonempty_invStruct`) does not apply.
What `e.IsEquivalence` *does* give is
`e.edge ∈ (core (Fun(A, C))).obj _` (by
`SSet.mem_core_obj_one_iff`; formalized as
`SSet.Edge.IsEquivalence.mem_core_edge_ihom`), i.e. factorization of
`Δ[1] ⟶ Fun(A, C)` through `core (Fun(A, C))` — a different object
from `Fun(A, core C)`. Lifting through
`SSet.core.map ((pre i).app C) : core Fun(B, C) ⟶ core Fun(A, C)`
would need this map of Kan complexes to be a Kan fibration; for an
inner fibration between quasicategories, that condition is
equivalent to the map being a categorical fibration (HTT §2.3: it is
special outer horn lifting for `(pre i).app C` restated on cores),
i.e. to (A) itself. The core route is therefore circular as a proof
of (A): the Kan property of `core C` is consumed by T31 only in the
form `(pre i).app (core C)`, to which the vertices of the lifting
problem do not belong. The correct proof of (A) is the skeletal one
of §2, where pointwise equivalences enter as the special edges of
special outer horns, not as a factorization through `core C`.

## 2. Proof of (A) by skeletal induction (mathematical proof)

We prove `SSet.HoPrePrismStrictExtension i C` for `[Mono i]` and
`[Quasicategory C]`; (A) follows by the reductions of §0. Write
`P(i)` for this property at fixed `C`.

*Saturation.* Every monomorphism of simplicial sets is a retract of
a transfinite composite of pushouts of coproducts of boundary
inclusions `∂Δ[n].ι : (∂Δ[n] : SSet) ⟶ Δ[n]` (the relative skeletal
filtration; in the pinned Mathlib the generating cofibrations of
`SSet.modelCategoryQuillen` are the boundary inclusions and its
cofibrations are the monomorphisms). The property `P` is closed
under these operations: under composition by
`SSet.HoPrePrismStrictExtension.comp` (packet T31: extend the prism
in two steps, using `((pre (i ≫ j)).app C) = ((pre j).app C) ≫
((pre i).app C)` from `MonoidalClosed.pre_map`); under coproducts
componentwise (`⊗` and `ihomVertexEquiv` commute with coproducts in
the source variable in the evident sense); under pushout, because
`(pushout) ⊗ Δ[1]` is the pushout of the prisms (`⊗` preserves
colimits in each variable), so two strictly agreeing prism
extensions glue by `IsPushout.desc`, the glued target vertex glues
by `SSet.ihomVertexEquiv` exactly as in
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`, and the
glued edge is an equivalence by the pointwise criterion below (its
vertex evaluations are those of the pieces); under transfinite
composition by iterating the composition step along the filtration
(the prisms form a compatible tower with colimit the required
prism, strictness being what makes the tower compatible); and under
retracts by transport along the retract diagrams through
`SSet.ihomSimplexOfPrism_pre_app`. It therefore suffices to prove
`P(∂Δ[n].ι)` for every `n`.

*The cell step.* Let `n ≥ 1`, let `b : Δ[n] ⟶ C` be the classifying
map of the prescribed source vertex, and let
`H : ∂Δ[n] ⊗ Δ[1] ⟶ C` be the prism of `e`; together they are a map
out of the subcomplex
`P₋₁ := ∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` of the prism `Δ[n] ⊗ Δ[1]`
(bottom face `Δ[n] ⊗ {0}` mapping by `b`, sides by `H`, agreeing on
`∂Δ[n] ⊗ {0}` because the source of `e` is the restriction of `b`,
via `SSet.δ_one_ihomSimplexOfPrism` and
`SSet.prismSectionZero_whiskerLeft_δ_one`). Vertices of `Δ[n] ⊗ Δ[1]`
are pairs `(i, ε)`, `i : Fin (n+1)`, `ε ∈ {0, 1}`. The prism is
triangulated by the `n + 1` nondegenerate `(n+1)`-simplices
`τₖ = ((0,0), …, (k,0), (k,1), …, (n,1))` for `k = 0, …, n`
(positions `0, …, k` are `(i, 0)`, position `k + 1` is `(k, 1)`,
positions `k + 2, …, n + 1` are `(i, 1)`). Attach them in decreasing
order `k = n, n - 1, …, 0`. When `τₖ` is attached to
`Pₖ₊₁ := P₋₁ ∪ τₙ ∪ … ∪ τₖ₊₁`, its faces are: `d_{k+1}` (omitting
`(k, 1)`), which is the face shared with `τₖ₊₁` — for `k = n` this
is `d_{n+1}`, the bottom face `Δ[n] ⊗ {0}`, already in `P₋₁`;
`dⱼ` for `j ∉ {k, k + 1}`, which lies in `∂Δ[n] ⊗ Δ[1]` (it misses
the vertex `(j', ε)` for some `j'` in both rows, or is contained in
a proper face of `Δ[n]` tensored with `Δ[1]`); and the single
missing face `dₖ` (omitting `(k, 0)`), the diagonal face that will
be shared with `τₖ₋₁` (for `k = 0`, `d₀` is the top face
`Δ[n] ⊗ {1}`, the target cell being constructed). Hence `τₖ` is
attached along the horn `Λ[n + 1, k]`:

* for `1 ≤ k ≤ n` this is an *inner* horn (`0 < k < n + 1`), filled
  because `C` is a quasicategory
  (`SSet.horn.IsCompatible.exists_lift_of_quasicategory` of
  `CoreKan.lean`, i.e. `Quasicategory.hornFilling`);
* for `k = 0` this is the *left outer* horn `Λ[n + 1, 0]`, whose
  `(0, 1)`-edge in the sense of `SSet.leftHornEdge` is the edge from
  vertex `(0, 0)` to vertex `(0, 1)` of `τ₀`, i.e. the evaluation of
  `e` at vertex `0` of `∂Δ[n]` (all vertices of `Δ[n]` lie in
  `∂Δ[n]` as `n ≥ 1`), which is an equivalence by §1. It is filled
  by Joyal's special outer horn theorem in all dimensions,
  `SSet.exists_fill_horn_left_of_isEquivalence` (packet T21).

For `n = 0` the prism is `Δ[1]` itself, `P₋₁` is its `0`-vertex
(the vertex `b` evaluated at the unique vertex of `Δ[0]`), there is
no restriction condition over `∂Δ[0] = ⊥`, and the degenerate prism
of the identity edge at that vertex is the required extension
(formalized below as
`SSet.hoPrePrismStrictExtension_boundary_zero`, with isofibration
and raw inner/isofibration corollaries; this is the one cell of the
induction that needs no triangulation). The
filled prism `F : Δ[n] ⊗ Δ[1] ⟶ C` restricts along `i ▷ Δ[1]` to
`H` by construction, its source vertex is `b` and its target vertex
restricts to the target of `e` (both read off by
`SSet.δ_one_ihomSimplexOfPrism`, `SSet.δ_zero_ihomSimplexOfPrism`),
and every vertical edge `{i} ⊗ Δ[1]` of `F` is the prescribed
pointwise equivalence, since `{i} ⊗ Δ[1] ⊆ ∂Δ[n] ⊗ Δ[1]` was part
of the given data. The target-prescribed variant (needed for
inverse data below) attaches the `τₖ` in increasing order along
`Λ[n + 1, k + 1]`, ending in the right outer horn `Λ[n + 1, n + 1]`
whose last edge is the vertical at vertex `n`, filled by
`SSet.exists_fill_horn_right_of_isEquivalence`.

*The lifted edge is an equivalence (pointwise criterion).* It
remains to see `(edgeOfPrism F _ _).IsEquivalence` in `Fun(B, C)`
after all cells are attached; equivalently: an edge `ε` of
`Fun(B, C)` all of whose vertex evaluations in `C` are equivalences
is an equivalence. We exhibit `ε.InvStruct`
(`SSet.Edge.isEquivalence_iff_nonempty_invStruct`, then
`SSet.Edge.InvStruct.isEquivalence`). Start from inverse data of
`e` in `Fun(A, C)` (`SSet.Edge.IsEquivalence.nonempty_invStruct`):
an edge `e⁻¹` and `CompStruct` `2`-simplices witnessing
`e ≫ e⁻¹ = id`, `e⁻¹ ≫ e = id` at the level of `HomotopyCategory.homMk`
(`HomotopyCategory.homMk_comp_homMk`, `HomotopyCategory.homMk_id`). Lift `e⁻¹`
along `(pre i).app C` with prescribed target `b` and strict source
restriction by the target-prescribed prism argument above, giving
`f : Edge b' b` in `Fun(B, C)`; pointwise, `f` evaluates to inverse
edges. The two `CompStruct` witnesses are prisms over `Δ[2]`, i.e.
extension problems for `B ⊗ Δ[2] ⟶ C` with data prescribed on
`B ⊗ ∂Δ[2]` (the three face prisms of `ε`, `f`, and an identity
edge, the latter being the degenerate prism `fst B Δ[?] ≫ _` of
`SSet.Homotopy.reflH` form) and on `A ⊗ Δ[2]` (the given
`CompStruct` prisms). Cell by cell, `Δ[n] ⊗ Δ[2]` is triangulated
by the `(n + 2)`-simplices indexed by shuffles of the two rows;
attaching them in the analogous monotone order presents each
attachment as an inner horn except for the two extremal ones, which
are special outer horns `Λ[n + 2, 0]` resp. `Λ[n + 2, n + 2]` whose
special edges are vertical `Δ[1]`-edges of the face prisms of `ε`
resp. `f` — pointwise equivalences by §1, the evaluations of `f`
being composites of inverse edges with identity edges, hence
equivalences by `SSet.Edge.IsEquivalence.of_compStruct`. Filling
(inner horns in `C`, special horns by T21) gives the two
`CompStruct` prisms, hence `f` is inverse data for `ε`. This
completes `P(i)`, hence (A) for every monomorphism and every
quasicategory. (This is Joyal's extension theorem in prism form:
HTT Proposition 2.3.4.5 and §2.3; Stevenson §2; Kerodon §4.5.)

## 3. Proof of (B): fullness (formalized) and faithfulness (blocker)

*Fullness* of `F' := hFun(f', C)` — formalized below as
`SSet.hoFunctor_pre_full_of_isPushout` — is the assembly of T31's
edge correction along the T30 pullback. Given vertices `y₁ y₂` of
`Fun(Y, C)` and `φ : F'.obj (mk y₁) ⟶ F'.obj (mk y₂)`, write
`bₖ := ((pre f').app C).app _ yₖ`, `xₖ := ((pre j).app C).app _ yₖ`,
`aₖ := ((pre i).app C).app _ bₖ`; the pullback commutativity
`(isPullback_pre_app_of_isPushout sq C).w` gives the vertex
equalities `hvₖ : ((pre f).app C).app _ xₖ = aₖ` by
`MonoidalClosed.pre_map` and `sq.w : i ≫ f' = f ≫ j`. Represent
`φ` (transported through the definitional equality
`F'.obj (mk yₖ) = mk bₖ`) by an edge `uB : Edge b₁ b₂` of
`Fun(B, C)` with `(HomotopyCategory.homMk uB) = φ`
(`SSet.Edge.exists_homMk_eq`). Its image edge
`uB.map ((pre i).app C)` in `Fun(A, C)` represents
`hFun(i, C).map φ` (`SSet.mapHomotopyCategory_map_homMk`). Since `hFun(f, C)` is
an equivalence (`hf` through
`SSet.categoricalEquivalences.mem_iff`), hence full, the morphism
`ψ := eqToHom (congrArg mk hv₁) ≫ (HomotopyCategory.homMk (uB.map _)) ≫
eqToHom (congrArg mk hv₂.symm)` in `h Fun(A, C)` (with
`hvₖ : ((pre f).app C).app _ xₖ = aₖ`, so `ψ` goes from
`mk (((pre f).app C).app _ x₁)` to `mk (((pre f).app C).app _ x₂)`,
definitionally the objects `hFun(f, C).obj (mk xₖ)`) has a preimage
`ξ : mk x₁ ⟶ mk x₂` under `hFun(f, C)`
(`CategoryTheory.Functor.map_surjective` at the explicit objects
`mk x₁`, `mk x₂`); represent `ξ` by an edge `uX : Edge x₁ x₂` of
`Fun(X, C)`. Set
`w := (uX.map ((pre f).app C)).ofEq hv₁ hv₂ : Edge a₁ a₂`
(`SSet.Edge.ofEq` does not change the underlying simplex; its
`HomotopyCategory.homMk` is computed by the private `cobaseGen_toHoHom_ofEq`
lemma below:
`(HomotopyCategory.homMk w) = eqToHom (congrArg mk hv₁.symm) ≫ (HomotopyCategory.homMk (uX.map _)) ≫
eqToHom (congrArg mk hv₂)`, by `subst` on abstract vertices). Then
`(HomotopyCategory.homMk w) = (HomotopyCategory.homMk (uB.map ((pre i).app C)))`:
`(HomotopyCategory.homMk (uX.map _)) = ψ` by `← mapHomotopyCategory_map_homMk` and the choice of
`ξ`, and the `eqToHom` factors cancel in pairs
(`eqToHom_trans`, `eqToHom_refl`). Apply
`SSet.exists_edge_correction_of_innerFibration` to
`p := (pre i).app C` (inner fibration by
`SSet.innerFibration_pre_app_of_mono`), `u := uB`, and this `w`:
the output `uB' : Edge b₁ b₂` satisfies `(HomotopyCategory.homMk uB') = (HomotopyCategory.homMk uB)`
and `(uB'.map p).edge = w.edge = (uX.map ((pre f).app C)).edge`.
The Yoneda names `yonedaEquiv.symm uB'.edge : Δ[1] ⟶ Fun(B, C)` and
`yonedaEquiv.symm uX.edge : Δ[1] ⟶ Fun(X, C)` therefore agree after
composing with `(pre i).app C` resp. `(pre f).app C`
(`yonedaEquiv_comp`, `SSet.Edge.map_edge`), so
`SSet.exists_pre_lift_of_isPushout sq C` at `W = Δ[1]` glues them
to `Wmap : Δ[1] ⟶ Fun(Y, C)`. Its faces are `y₁`, `y₂`: for
`δ₁`, the two maps `Δ[0] ⟶ Fun(Y, C)` named by
`Fun(Y, C).δ 1 (yonedaEquiv Wmap)` and by `y₁` have the same
projections to `Fun(B, C)` and `Fun(X, C)` (by
`stdSimplex.yonedaEquiv_δ_comp`, `IsPullback.lift_fst`/`lift_snd`
packaged in `exists_pre_lift_of_isPushout`, and the definitions of
`b₁, x₁`), hence are equal by
`(isPullback_pre_app_of_isPushout sq C).hom_ext`
(`CategoryTheory.IsPullback.hom_ext`); `δ₀` is identical. The
resulting edge `eY := Edge.mk (yonedaEquiv Wmap) _ _ : Edge y₁ y₂`
satisfies `(eY.map ((pre f').app C)).edge = uB'.edge`
(`yonedaEquiv_comp`, `Edge.map_edge`), hence
`F'.map (HomotopyCategory.homMk eY) = (HomotopyCategory.homMk (eY.map _)) = (HomotopyCategory.homMk
uB') =
(HomotopyCategory.homMk uB) = φ` (`← mapHomotopyCategory_map_homMk`, `SSet.Edge.ext`). This is
`Functor.Full` in the form `Full.map_surjective`. No special horns
are used: only the inner horn `Λ[2, 1]` inside T31's correction.

*Faithfulness* would need the one-dimension-higher correction:
given edges `e₁ e₂` of `Fun(Y, C)` with equal images in
`h Fun(B, C)`, represent the equality downstairs by a `CompStruct`
`2`-simplex `sB` in `Fun(B, C)`
(`SSet.Edge.nonempty_compStruct_of_homMk_comp_eq` against an
identity edge), the equality of the `X`-images (faithfulness of the
equivalence `hFun(f, C)`) by a `2`-simplex `sX` in `Fun(X, C)`;
their images in `Fun(A, C)` are two `2`-simplices with the *same*
boundary simplices (strictly, by functoriality of `pre`), and one
must correct `sB` through the inner fibration `(pre i).app C` to a
`2`-simplex `sB'` with the same three faces as `sB` and strict
image the image of `sX`, then glue by
`exists_pre_lift_of_isPushout` at `W = Δ[2]`. The naive
`Λ[3, 1]` attempt fails for a precise reason: with
`Δ[3]` vertices sent to `(v₀, v₁, v₁, v₂)`, the compatible faces
`d₀ = σ₀`-degenerate on the second edge, `d₂ = p(sB)`,
`d₃ = σ₁`-degenerate on the first edge form an inner horn
`Λ[3, 1]` in `Fun(A, C)`, but its quasicategory filler has
`d₁`-face *some* `2`-simplex with the common boundary, not the
prescribed image of `sX`; prescribing both `d₁` and `d₂` is a
`∂Δ[3]`-extension problem, not an inner horn. The correct input is
a `3`-simplex with two prescribed faces, i.e. a `CompStruct` in an
arrow/slice quasicategory over the common boundary, or equivalently
Kan-ness and the fibration property of mapping spaces (the
Stevenson §2.4 route through right properness of the Kan model
structure). Both are exactly the missing inputs TODO(T32-kan) and
TODO(T32-trivial-fibration-case) recorded in
`MappingSpaceCategorical.lean` (packet T32): no left/right
fibration API for the join slices, no slice base-change API. We
therefore record faithfulness as TODO(T34-B2): the missing lemma is
"correction of `2`-simplices through an inner fibration rel
boundary", stated precisely above; fullness does not depend on it.

## 4. Assembly, formalized content, and remaining blockers

Granting (A) and faithfulness, `categoricalEquivalences f'` is
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`
with fullness supplied by §3; this is formalized below as
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful`,
together with the per-target package
`SSet.hoFunctor_pre_essSurj_full_of_isPushout_of_isIsofibration`
(essential surjectivity from T30 plus fullness from §3) and the
raw inner/isofibration form
`SSet.innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension`
of the prism reduction. Combined with the landed cases of (A)
(Kan targets in T31, inner anodyne and isomorphism left legs in
T26/T30), the unconditional stability instance is reduced, with no
further formal steps, to:

* TODO(T34-A): `SSet.HoPrePrismStrictExtension i C` for `[Mono i]`,
  `[Quasicategory C]`, i.e. the formalization of §2. Missing API,
  in order: (1) for `n ≥ 1`, the triangulation of `Δ[n] ⊗ Δ[1]`
  (and `Δ[n] ⊗ Δ[2]`) as iterated horn attachments — no prism
  triangulation or shuffle API is landed, and maps out of
  `Δ[n] ⊗ Δ[1]` cannot currently be built simplex-by-simplex (the
  case `n = 0` is formalized here);
  (2) closure of `HoPrePrismStrictExtension` under pushouts,
  coproducts, transfinite compositions and retracts (only
  composition is landed, T31), together with the presentation of a
  monomorphism by its relative skeletal filtration in a usable
  form; (3) the pointwise criterion / `Δ[2]`-prism step. The horn
  fillers themselves (`exists_fill_horn_left/right_of_isEquivalence`,
  inner horn filling) are landed (T21). Note §2 also subsumes
  TODO(T15) of `CoherentIsoExtension.lean` (the case `A = Δ[0]` of
  the pointwise criterion applied in `Fun` categories gives
  coherent-isomorphism extensions), whose skeletal induction over
  the alternating simplices of `SSet.coherentIso` is likewise not
  formalized.
* TODO(T34-B2): faithfulness of `hFun(f', C)`, via correction of
  `2`-simplices rel boundary through `(pre i).app C` (§3), blocked
  on slice/mapping-space API as in TODO(T32-kan).

Formalized in this module, unconditionally: vertex evaluations of
equivalence edges are equivalences
(`SSet.Edge.IsEquivalence.eval_vertex`); equivalence edges of
`Fun(A, C)` are `1`-simplices of `core (Fun(A, C))`
(`SSet.Edge.IsEquivalence.mem_core_edge_ihom`); sub-claim (i)
(`SSet.isEquivalence_mk'_app_of_ihomVertex_lift_core`); the failure
of (ii) (`SSet.exists_equivalence_edge_endpoint_not_lift_core`);
fullness (`SSet.hoFunctor_pre_full_of_isPushout`); the
`0`-dimensional cell of (A)
(`SSet.hoPrePrismStrictExtension_boundary_zero`,
`SSet.hoFunctor_pre_isIsofibration_boundary_zero`,
`SSet.innerIsoFibrations_pre_app_boundary_zero`); and the
conditional assemblies above. The core route to (A) does *not*
close: §1 is a disproof of its step (ii), not a gap in
formalization effort.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.2.4.3 (special outer
  horns), Corollary 2.3.2.5 (internal Homs of quasicategories), and
  Corollary 2.4.6.5 (the fibration criterion with a quasicategory codomain).
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233, §2 (pushout stability of categorical
  equivalences), §2.4 (Dwyer–Kan equivalences, Lemma 2.17).
* *Kerodon*, Corollary 4.5.4.14 (stability under pushout along
  monomorphisms), §4.5 (categorical fibrations and cores).
* D. Dugger, D. Spivak, *Mapping spaces in quasi-categories*,
  Appendix B.9 (the filtration proof of special outer horn filling
  formalized in packet T21).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

/-! ## Pointwise evaluations and core membership (§1 of the header) -/

/-- **Vertex evaluations of an equivalence edge are equivalences.**
For an equivalence edge `e` of `Fun(A, C)` and a vertex map
`v : Δ[0] ⟶ A`, the edge of `C` obtained by precomposing with `v`
and evaluating at `Δ[0]` through `SSet.evalDeltaZeroIso` is an
equivalence in `C`. These are the pointwise equivalences that occur
as the special edges of the special outer horns in §2 of the
header. -/
theorem Edge.IsEquivalence.eval_vertex {C : SSet.{u}}
    {a₀ a₁ : ((ihom A).obj C) _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsEquivalence) (v : (Δ[0] : SSet.{u}) ⟶ A) :
    ((e.map ((pre v).app C)).map (evalDeltaZeroIso C).hom).IsEquivalence :=
  (he.map ((pre v).app C)).map _

/-- An equivalence edge of `Fun(A, C)` is a `1`-simplex of the core
of the functor object: `e.edge ∈ core (Fun(A, C))` by
`SSet.mem_core_obj_one_iff`. This is the factorization that
`e.IsEquivalence` actually gives; it must not be confused with a
factorization of the endpoint vertices through `Fun(A, core C)`
(§1 of the header). -/
theorem Edge.IsEquivalence.mem_core_edge_ihom {C : SSet.{u}}
    {a₀ a₁ : ((ihom A).obj C) _⦋0⦌} {e : Edge a₀ a₁}
    (he : e.IsEquivalence) :
    e.edge ∈ (core ((ihom A).obj C)).obj (Opposite.op ⦋1⦌) :=
  mem_core_obj_one_iff.2 (he.of_edge_eq rfl)

/-- **Sub-claim (i) of §1.** If the vertex of `Fun(A, C)` classified
by `g : A ⟶ C` lifts along postcomposition with `(core C).ι` to a
vertex of `Fun(A, core C)`, then every `1`-simplex image
`g.app _ s` is an equivalence edge of `C`: the lift is classified
by a map `G : A ⟶ (core C : SSet)` with `G ≫ (core C).ι = g`
(`SSet.ihomVertexEquiv_ihom_map`), and membership of `G.app _ s`
in the core is `SSet.mem_core_obj_one_iff`. -/
theorem isEquivalence_mk'_app_of_ihomVertex_lift_core {C : SSet.{u}}
    {g : A ⟶ C}
    (hlift : ∃ bt : ((ihom A).obj (core C : SSet.{u})) _⦋0⦌,
      ((ihom A).map (core C).ι).app (Opposite.op ⦋0⦌) bt =
        ihomVertexEquiv A C g)
    (s : A _⦋1⦌) : (Edge.mk' (g.app (Opposite.op ⦋1⦌) s)).IsEquivalence := by
  obtain ⟨bt, hbt⟩ := hlift
  set G : A ⟶ (core C : SSet.{u}) :=
    (ihomVertexEquiv A (core C : SSet.{u})).symm bt with hG
  have hGg : G ≫ (core C).ι = g := by
    apply (ihomVertexEquiv A C).injective
    rw [← ihomVertexEquiv_ihom_map, hG, Equiv.apply_symm_apply]
    exact hbt
  have happ : g.app (Opposite.op ⦋1⦌) s = (G.app (Opposite.op ⦋1⦌) s).1 := by
    rw [← hGg]
    rfl
  rw [happ]
  exact mem_core_obj_one_iff.mp (G.app (Opposite.op ⦋1⦌) s).2

/-- **Failure of sub-claim (ii) of §1 (the core-route gap).** For
every non-equivalence edge `e₀` of `C` there is a vertex `b` of
`Fun(Δ[1], C)` — the one classifying `e₀` itself — such that the
identity edge at `b` is an equivalence of `Fun(Δ[1], C)` but `b`
does not lift along postcomposition with `(core C).ι` to
`Fun(Δ[1], core C)`: by
`SSet.isEquivalence_mk'_app_of_ihomVertex_lift_core` at the
fundamental simplex `yonedaEquiv (𝟙 Δ[1])`, a lift would make
`e₀` an equivalence. Hence the endpoint vertices in the lifting
problem (A) do not in general belong to `Fun(-, core C)`, and (A)
does not reduce to the Kan-target case of packet T31 at `core C`. -/
theorem exists_equivalence_edge_endpoint_not_lift_core {C : SSet.{u}}
    {x₀ x₁ : C _⦋0⦌} (e₀ : Edge x₀ x₁) (h₀ : ¬ e₀.IsEquivalence) :
    ∃ b : ((ihom (Δ[1] : SSet.{u})).obj C) _⦋0⦌,
      (Edge.id b).IsEquivalence ∧
        ¬ ∃ bt : ((ihom (Δ[1] : SSet.{u})).obj (core C : SSet.{u})) _⦋0⦌,
          ((ihom (Δ[1] : SSet.{u})).map (core C).ι).app (Opposite.op ⦋0⦌) bt = b := by
  refine ⟨ihomVertexEquiv (Δ[1] : SSet.{u}) C (yonedaEquiv.symm e₀.edge),
    Edge.isEquivalence_id _, fun hlift => h₀ ?_⟩
  have key := isEquivalence_mk'_app_of_ihomVertex_lift_core
    (g := yonedaEquiv.symm e₀.edge) hlift (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  have happ : (yonedaEquiv.symm e₀.edge).app (Opposite.op ⦋1⦌)
        (yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = e₀.edge :=
    yonedaEquiv_symm_app_id _
  rw [happ] at key
  exact key.of_edge_eq rfl

/-! ## Fullness of the cobase change (§3 of the header) -/

/-- The morphism represented by a transported edge: transporting
the endpoints along vertex equalities conjugates `HomotopyCategory.homMk` by the
corresponding `eqToHom` morphisms. Proved by `subst` on abstract
vertices, where `Edge.ofEq` with `rfl` proofs is the original edge
(`SSet.Edge.ext`). -/
private lemma cobaseGen_toHoHom_ofEq {W : SSet.{u}} {a b a' b' : W _⦋0⦌}
    (e : Edge a b) (h₀ : a = a') (h₁ : b = b') :
    (HomotopyCategory.homMk (e.ofEq h₀ h₁)) =
      eqToHom (congrArg HomotopyCategory.mk h₀.symm) ≫ (HomotopyCategory.homMk e) ≫
        eqToHom (congrArg HomotopyCategory.mk h₁) := by
  subst h₀
  subst h₁
  have hEq : e.ofEq rfl rfl = e := Edge.ext rfl
  rw [hEq]
  change (HomotopyCategory.homMk e) = eqToHom (rfl : HomotopyCategory.mk a =
    HomotopyCategory.mk a) ≫ (HomotopyCategory.homMk e) ≫
      eqToHom (rfl : HomotopyCategory.mk b = HomotopyCategory.mk b)
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **Fullness of precomposition with a cobase change
(TODO(T31-B)(1), unconditional).** In a pushout square
`IsPushout i f f' j` with `i` a monomorphism and `f` a categorical
equivalence, precomposition with `f'` induces a full functor on
homotopy categories of functor objects into every quasicategory
`C`. The proof is §3 of the module header: represent the given
morphism by an edge of `Fun(B, C)`, take a preimage edge in
`Fun(X, C)` through the equivalence `hFun(f, C)`, correct the first
edge by `SSet.exists_edge_correction_of_innerFibration` (packet
T31, inner horn `Λ[2, 1]` through the inner fibration
`(pre i).app C`) so the two edges agree strictly in `Fun(A, C)`,
and glue along `SSet.isPullback_pre_app_of_isPushout` (packet
T30). -/
theorem hoFunctor_pre_full_of_isPushout
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre f').app C)).toFunctor.Full := by
  have hFf : (hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
    (categoricalEquivalences.mem_iff f).1 hf C inferInstance
  have hFf' : (mapHomotopyCategory ((pre f).app C)).IsEquivalence := hFf
  have := hFf'
  change (mapHomotopyCategory ((pre f').app C)).Full
  constructor
  intro P Q φ
  obtain ⟨y₁, rfl⟩ : ∃ y, HomotopyCategory.mk y = P :=
    ⟨_, HomotopyCategory.objEquiv.left_inv P⟩
  obtain ⟨y₂, rfl⟩ : ∃ y, HomotopyCategory.mk y = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  obtain ⟨uB, huB⟩ := Edge.exists_homMk_eq (show
    (HomotopyCategory.mk (((pre f').app C).app _ y₁) :
      hoFunctor.obj ((ihom B).obj C)) ⟶
      HomotopyCategory.mk (((pre f').app C).app _ y₂) from φ)
  have hv : ∀ y : ((ihom Y).obj C) _⦋0⦌,
      ((pre f).app C).app _ (((pre j).app C).app _ y) =
        ((pre i).app C).app _ (((pre f').app C).app _ y) := by
    intro y
    have key1 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
      rw [pre_map]; rfl
    have key2 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
      rw [pre_map]; rfl
    change (((pre j).app C ≫ (pre f).app C).app _ y) =
      (((pre f').app C ≫ (pre i).app C).app _ y)
    rw [key1, key2, sq.w]
  obtain ⟨ξ, hξ⟩ := (mapHomotopyCategory ((pre f).app C)).map_surjective
    (X := HomotopyCategory.mk (((pre j).app C).app _ y₁))
    (Y := HomotopyCategory.mk (((pre j).app C).app _ y₂))
    (eqToHom (congrArg HomotopyCategory.mk (hv y₁)) ≫
      (HomotopyCategory.homMk (uB.map ((pre i).app C))) ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm))
  obtain ⟨uX, huX⟩ := Edge.exists_homMk_eq ξ
  have hstep : (HomotopyCategory.homMk (uX.map ((pre f).app C))) =
      eqToHom (congrArg HomotopyCategory.mk (hv y₁)) ≫
        (HomotopyCategory.homMk (uB.map ((pre i).app C))) ≫
          eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm) := by
    rw [← mapHomotopyCategory_map_homMk, huX]
    exact hξ
  have hcanc1 : eqToHom (congrArg HomotopyCategory.mk (hv y₁).symm) ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₁)) =
      𝟙 (HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₁))) := by
    rw [eqToHom_trans]
    change eqToHom (rfl : HomotopyCategory.mk
      (((pre i).app C).app _ (((pre f').app C).app _ y₁)) =
      HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₁))) = _
    rw [eqToHom_refl]
  have hcanc2 : eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm) ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₂)) =
      𝟙 (HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₂))) := by
    rw [eqToHom_trans]
    change eqToHom (rfl : HomotopyCategory.mk
      (((pre i).app C).app _ (((pre f').app C).app _ y₂)) =
      HomotopyCategory.mk
        (((pre i).app C).app _ (((pre f').app C).app _ y₂))) = _
    rw [eqToHom_refl]
  have hw : (HomotopyCategory.homMk ((uX.map ((pre f).app C)).ofEq (hv y₁) (hv y₂))) =
      (HomotopyCategory.homMk (uB.map ((pre i).app C))) := by
    rw [cobaseGen_toHoHom_ofEq, hstep]
    simp only [← Category.assoc]
    rw [hcanc1, Category.id_comp, Category.assoc, hcanc2, Category.comp_id]
  obtain ⟨uB', huB'1, huB'2⟩ :=
    exists_edge_correction_of_innerFibration ((pre i).app C)
      (innerFibration_pre_app_of_mono i C) uB
      ((uX.map ((pre f).app C)).ofEq (hv y₁) (hv y₂)) hw
  have hedge : (uB'.map ((pre i).app C)).edge =
      (uX.map ((pre f).app C)).edge := huB'2
  have hagree : yonedaEquiv.symm uB'.edge ≫ (pre i).app C =
      yonedaEquiv.symm uX.edge ≫ (pre f).app C := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp only [Equiv.apply_symm_apply]
    rw [← Edge.map_edge, ← Edge.map_edge]
    exact hedge
  obtain ⟨Wmap, hW1, hW2⟩ := exists_pre_lift_of_isPushout sq C _ _ hagree
  have hδ : ∀ (eBedge : ((ihom B).obj C) _⦋1⦌) (eXedge : ((ihom X).obj C) _⦋1⦌)
      (hB : Wmap ≫ (pre f').app C = yonedaEquiv.symm eBedge)
      (hX : Wmap ≫ (pre j).app C = yonedaEquiv.symm eXedge)
      (y : ((ihom Y).obj C) _⦋0⦌) (idx : Fin 2)
      (hBy : ((ihom B).obj C).δ idx eBedge = ((pre f').app C).app _ y)
      (hXy : ((ihom X).obj C).δ idx eXedge = ((pre j).app C).app _ y),
      ((ihom Y).obj C).δ idx (yonedaEquiv Wmap) = y := by
    intro eBedge eXedge hB hX y idx hBy hXy
    have hks : yonedaEquiv.symm (((ihom Y).obj C).δ idx (yonedaEquiv Wmap)) =
        yonedaEquiv.symm y := by
      apply (isPullback_pre_app_of_isPushout sq C).hom_ext
      · apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp]
        simp only [Equiv.apply_symm_apply]
        calc ((pre f').app C).app _ (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
            = ((ihom B).obj C).δ idx (((pre f').app C).app _ (yonedaEquiv Wmap)) :=
              δ_naturality_apply _ _ _
          _ = ((ihom B).obj C).δ idx eBedge := by
              rw [← yonedaEquiv_comp, hB, Equiv.apply_symm_apply]
          _ = ((pre f').app C).app _ y := hBy
      · apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp]
        simp only [Equiv.apply_symm_apply]
        calc ((pre j).app C).app _ (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
            = ((ihom X).obj C).δ idx (((pre j).app C).app _ (yonedaEquiv Wmap)) :=
              δ_naturality_apply _ _ _
          _ = ((ihom X).obj C).δ idx eXedge := by
              rw [← yonedaEquiv_comp, hX, Equiv.apply_symm_apply]
          _ = ((pre j).app C).app _ y := hXy
    have h2 := congrArg yonedaEquiv hks
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  have hsrc : ((ihom Y).obj C).δ 1 (yonedaEquiv Wmap) = y₁ :=
    hδ uB'.edge uX.edge hW1 hW2 y₁ 1 uB'.src_eq uX.src_eq
  have htgt : ((ihom Y).obj C).δ 0 (yonedaEquiv Wmap) = y₂ :=
    hδ uB'.edge uX.edge hW1 hW2 y₂ 0 uB'.tgt_eq uX.tgt_eq
  let eY : Edge y₁ y₂ := Edge.mk (yonedaEquiv Wmap) hsrc htgt
  refine ⟨(HomotopyCategory.homMk eY), ?_⟩
  have hedgeY : (eY.map ((pre f').app C)).edge = uB'.edge := by
    change ((pre f').app C).app _ (yonedaEquiv Wmap) = uB'.edge
    rw [← yonedaEquiv_comp, hW1, Equiv.apply_symm_apply]
  rw [mapHomotopyCategory_map_homMk, show eY.map ((pre f').app C) = uB' from
    Edge.ext hedgeY, huB'1]
  exact huB

/-! ## Conditional assemblies (§4 of the header) -/

/-- Precomposition with a monomorphism into a quasicategory satisfies
`innerIsoFibrations` as soon as the prism strict extension property
TODO(T34-A) holds for that pair: the inner fibration half
is `SSet.innerFibration_pre_app_of_mono` and the isofibration half
is `SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`
(packet T30). -/
theorem innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension
    [Mono i] (C : SSet.{u}) [Quasicategory C]
    (h : HoPrePrismStrictExtension i C) :
    innerIsoFibrations ((pre i).app C) := by
  rw [innerIsoFibrations.mem_iff]
  exact ⟨(innerFibration_iff _).1 (innerFibration_pre_app_of_mono i C),
    hoFunctor_pre_isIsofibration_of_prismStrictExtension C h⟩

/-- Essential surjectivity plus fullness of precomposition with a
cobase change, granted the isofibration property (A) of the left
leg at the given target: essential surjectivity is packet T30
(`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`) and
fullness is `SSet.hoFunctor_pre_full_of_isPushout` here, which
needs no isofibration input. -/
theorem hoFunctor_pre_essSurj_full_of_isPushout_of_isIsofibration
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C]
    (hIso : (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration) :
    (hoFunctor.map ((pre f').app C)).toFunctor.EssSurj ∧
      (hoFunctor.map ((pre f').app C)).toFunctor.Full :=
  ⟨hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C hIso,
    hoFunctor_pre_full_of_isPushout sq hf C⟩

/-- **Cobase change of a categorical equivalence along a
monomorphism, granted (A) and faithfulness.** This is the T30
assembly
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`
with the fullness input supplied unconditionally by
`SSet.hoFunctor_pre_full_of_isPushout` here. The remaining
hypotheses are exactly TODO(T34-A) (the isofibration property of
the left leg for every quasicategory target, i.e. by §0 the prism
strict extension property of §2) and TODO(T34-B2) (faithfulness,
i.e. correction of `2`-simplices rel boundary, §3). -/
theorem categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (hIso : ∀ (C : SSet.{u}) [Quasicategory C],
      (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration)
    (hFaith : ∀ (C : SSet.{u}) [Quasicategory C],
      (hoFunctor.map ((pre f').app C)).toFunctor.Faithful) :
    categoricalEquivalences f' :=
  categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful
    sq hf hIso
    (fun C _ => ⟨hoFunctor_pre_full_of_isPushout sq hf C, hFaith C⟩)

/-! ## The `0`-dimensional cell of (A) (§2 of the header) -/

/-- No simplex of `∂Δ[0]` exists in any degree: `∂Δ[0]` is the
bottom subcomplex (`SSet.boundary_zero`). -/
private lemma cobaseGen_boundaryZero_obj_elim {Δ : SimplexCategoryᵒᵖ}
    (x : (∂Δ[0] : SSet.{u}).obj Δ) : False := by
  have h := x.2
  simp only [boundary_zero, Subfunctor.bot_obj, Set.mem_empty_iff_false] at h

/-- Maps out of `∂Δ[0] ⊗ W` are unique, since `∂Δ[0]` has no
simplices. -/
private lemma cobaseGen_eq_of_boundaryZero_tensor {W C : SSet.{u}}
    (F G : (∂Δ[0] : SSet.{u}) ⊗ W ⟶ C) : F = G := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro x
  exact (cobaseGen_boundaryZero_obj_elim x.1).elim

/-- Vertices of `Fun(∂Δ[0], C)` are unique, through the prism
dictionary `SSet.ihomSimplexEquiv` at `n = 0`. -/
private lemma cobaseGen_subsingleton_ihom_vertex_boundaryZero (C : SSet.{u})
    (s t : ((ihom (∂Δ[0] : SSet.{u})).obj C) _⦋0⦌) : s = t := by
  apply (ihomSimplexEquiv (∂Δ[0] : SSet.{u}) C 0).symm.injective
  exact cobaseGen_eq_of_boundaryZero_tensor _ _

/-- **The `0`-dimensional cell of TODO(T34-A).** The prism strict
extension property holds along `∂Δ[0].ι` for every target `C`
(no quasicategory hypothesis is needed in dimension `0`): the
prism over `∂Δ[0]` is unique
(`cobaseGen_eq_of_boundaryZero_tensor`), vertices of
`Fun(∂Δ[0], C)` are unique, and the degenerate prism of the
identity edge at the prescribed vertex is the required extension.
This is the `n = 0` case of the cell step of §2 of the header; the
cases `n ≥ 1` need the prism triangulation recorded there as
TODO(T34-A)(1). -/
theorem hoPrePrismStrictExtension_boundary_zero (C : SSet.{u}) :
    HoPrePrismStrictExtension ∂Δ[0].ι C := by
  intro b a' e _he
  have h0 : ((ihom (Δ[0] : SSet.{u})).obj C).δ 1
      (ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge)) = b := by
    rw [ihomSimplexOfPrism_ihomPrismOfSimplex]
    exact (Edge.id b).src_eq
  have h1 : ((ihom (Δ[0] : SSet.{u})).obj C).δ 0
      (ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge)) = b := by
    rw [ihomSimplexOfPrism_ihomPrismOfSimplex]
    exact (Edge.id b).tgt_eq
  have hEq : edgeOfPrism (ihomPrismOfSimplex (Edge.id b).edge) h0 h1 =
      Edge.id b :=
    Edge.ext (by rw [edgeOfPrism_edge, ihomSimplexOfPrism_ihomPrismOfSimplex])
  exact ⟨ihomPrismOfSimplex (Edge.id b).edge, b,
    cobaseGen_subsingleton_ihom_vertex_boundaryZero C _ _, h0, h1,
    hEq.symm ▸ Edge.isEquivalence_id b,
    cobaseGen_eq_of_boundaryZero_tensor _ _⟩

/-- **TODO(T31-A) for the boundary inclusion `∂Δ[0].ι`.** For every
quasicategory `C`, precomposition with `∂Δ[0].ι` induces an
isofibration on homotopy categories of functor objects into `C`,
by `SSet.hoPrePrismStrictExtension_boundary_zero` and the prism
reduction of packet T30. For `∂Δ[n].ι` with `n ≥ 1` and a general
quasicategory target this remains TODO(T34-A); for Kan complex
targets and every `n` it is packet T31
(`SSet.hoFunctor_pre_isIsofibration_boundary_kanComplex`). -/
theorem hoFunctor_pre_isIsofibration_boundary_zero (C : SSet.{u})
    [Quasicategory C] :
    (hoFunctor.map ((pre ∂Δ[0].ι).app C)).toFunctor.IsIsofibration :=
  hoFunctor_pre_isIsofibration_of_prismStrictExtension C
    (hoPrePrismStrictExtension_boundary_zero C)

/-- Precomposition with `∂Δ[0].ι` into a quasicategory satisfies
`innerIsoFibrations`, as follows from
`SSet.hoPrePrismStrictExtension_boundary_zero` read through
`SSet.innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension`. -/
theorem innerIsoFibrations_pre_app_boundary_zero (C : SSet.{u})
    [Quasicategory C] :
    innerIsoFibrations ((pre ∂Δ[0].ι).app C) :=
  innerIsoFibrations_pre_app_of_hoPrePrismStrictExtension C
    (hoPrePrismStrictExtension_boundary_zero C)

end SSet

end
