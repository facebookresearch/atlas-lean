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
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismCobase

/-! # Unconditional cobase change along monomorphisms (packet T47)

This module attacks the four remaining items (i)–(iv) recorded in
the header of `PrismCobase.lean` (lines 29–39 there) together with
TODO(T34-B2) (faithfulness), towards the unconditional statement

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}).
```

Following the method of the earlier packets, this header first
gives the complete informal proof. The formal content then proves
the largest subset that the landed API supports, in dependency
order, and isolates the rest as precise TODOs at the end. **No
statement in this module claims the unconditional stability
instance above** unless it is explicitly proved; the conditional
assemblies name their remaining hypotheses.

## 0. What has to be proved (recap)

Fix `i : A ⟶ B`, `[Mono i]`, `C` a quasicategory, a vertex `b` of
`Fun(B, C) := (ihom B).obj C` and an equivalence edge
`e : Edge ((pre i)^* b) a'` of `Fun(A, C)`. By packets T30/T34
(`SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`,
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful`
with fullness `SSet.hoFunctor_pre_full_of_isPushout`
unconditional), cobase-change stability against monomorphisms
follows from two inputs for every monomorphism `i` and
quasicategory `C`:

* (A) `SSet.HoPrePrismStrictExtension i C`: the prism
  `H : A ⊗ Δ[1] ⟶ C` of `e` extends along `i ▷ Δ[1]` to a prism
  `F : B ⊗ Δ[1] ⟶ C` with source `b`, strict target restriction,
  and `(edgeOfPrism F _ _).IsEquivalence`;
* (B2) faithfulness of `hFun(f', C)` in every pushout square along
  `i`, via correction of `2`-simplices of `Fun(B, C)` rel boundary
  through the inner fibration `(pre i).app C`.

The proof of (A) has three layers, as in §1–§4 of the
`PrismCobase.lean` header: prism extension along boundary
inclusions by triangulation, the pointwise criterion that the
lifted edge is an equivalence, and closure of the prism extension
properties under the relative skeletal filtration. We recall the
argument in full because the formalization below follows it step
by step.

## 1. The `Δ[1]`-prism over a cell: source- and target-prescribed

Let `i = ∂Δ[n].ι`, `n ≥ 1`. The data `(H, b♯)` is a map out of
`S₀ := ∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` (formally
`SSet.prismSrcInitial n = Subcomplex.unionProd ∂Δ[n]
(stdSimplex.face {0})`). The prism `Δ[n] ⊗ Δ[1]` is triangulated
by `τₖ = ((0,0), …, (k,0), (k,1), …, (n,1))`, `k : Fin (n+1)`
(`SSet.prismTau`). Packet T43 (`PrismCobase.lean`) formalized: the
decreasing filtration `Gₘ = S₀ ⊔ ⨆_{k ≥ m} ofSimplex τₖ`
(`SSet.prismSrcFilt`), its steps `Gₘ = Gₘ₊₁ ⊔ ofSimplex τₘ`, top
`G_{n+1} = S₀` and bottom `G₀ = ⊤`; the attaching-horn computation
`(G_{k+1}).preimage τₖ = Λ[n+1, k]`
(`SSet.prismSrcFilt_preimage_prismTauMap`); injectivity of `τₖ`
on simplices (the `Mono` instance for `SSet.prodStdSimplex₁.ι`,
i.e. for `SSet.prismTauMap`, read pointwise by
`CategoryTheory.injective_of_mono`); the general
one-simplex attachment pushout and extension step
(`SSet.Subcomplex.isPushout_hornAttach`,
`SSet.Subcomplex.exists_extension_sup_of_horn_filler`); and the vertical edge
`SSet.prismVertZero` at vertex `0` with its membership in `S₀`.

What remains for the source-prescribed cell step is the
identification of the special edge and the finite induction.
The `(0,1)`-edge of `Δ[n+1]` maps under `τ₀` to the vertical edge
`(0,0) ⟶ (0,1)`: both are read through
`SSet.prodStdSimplex.objEquiv`, where `τ₀` has first coordinates
`t ↦ t` for `t ≤ 0` and `t ↦ t - 1` afterwards and second
coordinates `0, 1, 1, …`
(`SSet.prismTau_objEquiv_fst_val`, `SSet.prismTau_objEquiv_snd`),
so at positions `0, 1` it takes values `(0,0), (0,1)`, which is
`SSet.prismVertZero` by definition. Consequently the
`(0,1)`-edge of the horn map `Λ[n+1, 0] ⟶ C` induced by a partial
extension `φ : G₁ ⟶ C` — that is `SSet.leftHornEdge` of
`Subcomplex.hornLift ≫ φ` — is the image of `prismVertZero` under `φ`,
hence, by restriction to `S₀`, under the initial datum. When the
initial datum comes from `(H, b♯)` this edge is the evaluation of
`e` at vertex `0`, an equivalence by
`SSet.Edge.IsEquivalence.eval_vertex` (packet T34). The induction
now runs downwards from `G_{n+1} = S₀` to `G₀ = ⊤`: at step `k`
the horn `Λ[n+1, k]` is inner for `k ≥ 1` (filled by
`Quasicategory.hornFilling`, since `0 < k.castSucc < last (n+1)`),
and for `k = 0` it is the left outer horn `Λ[n+1, 0]`, special by
the identification above and filled by
`SSet.exists_fill_horn_left_of_isEquivalence` (packet T21, in the
form `Λ[m+2, 0]` with `n = m + 1`). Each filler extends the partial
map over `τₖ` by `SSet.Subcomplex.exists_extension_sup_of_horn_filler`, and
the filtration equality `Gₖ = Gₖ₊₁ ⊔ ofSimplex τₖ` transports it
to `Gₖ`, preserving the restriction to `S₀` at every stage. For
`n = 0` there is a single step along `Λ[1, 0]`; the filler is the
degenerate edge `C.σ 0 x₀` at the image `x₀` of the vertex
`(0,0)`, which lies in `S₀ = Δ[0] ⊗ {0}`, so no equivalence
hypothesis is needed: the prism is filled by a degeneracy. The
result is the source-prescribed extension property in subcomplex
form: a map out of `S₀` extends to `Δ[n] ⊗ Δ[1]` as soon as the
image of the single vertical edge at vertex `0` is an equivalence
(`SSet.exists_extension_of_unionProd_boundary_face_zero`).

The mirror (target-prescribed) filtration attaches the same
simplices in increasing order to
`S₁ := ∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {1}`. With
`G'ₘ := S₁ ⊔ ⨆_{k < m} ofSimplex τₖ`, the simplex `τₖ` is attached
to `G'ₖ` along `Λ[n+1, k+1]`: the faces omitting a vertex before
or after the turn delete a first coordinate and lie in
`∂Δ[n] ⊗ Δ[1]` by the same two face lemmas as for the source
filtration; the face omitting `(k,0)` is the diagonal shared with
`τₖ₋₁`, and for `k = 0` it lies over the top face `Δ[n] ⊗ {1}` in
`S₁`; the missing face omitting `(k,1)` is the diagonal
`codimOneSimplex (k+1)`, which lies neither in `S₁` (at vertex `k`
its second coordinate is `0`, and its first component is the
fundamental simplex) nor in any earlier `τ_{k'}` (the vertex
`(k,0)` is in its range, but `(k,0)` is in the range of `τ_{k'}`
only for `k ≤ k'`). The horns are inner for `k < n`, and the last
step `k = n` is the right outer horn `Λ[n+1, n+1]`, whose last
edge is the vertical edge `(n,0) ⟶ (n,1)` (`τₙ` at positions
`n, n+1`), filled by `SSet.exists_fill_horn_right_of_isEquivalence`
when that vertical is an equivalence. For `n = 0` the filler is
again degenerate, at the vertex `(0,1)`. This gives
`SSet.exists_extension_of_unionProd_boundary_face_one`. (The
opposite-simplicial-set trick would derive the mirror from the
source case, but the identification `Δ[n].op ≅ Δ[n]` reversing
horns is an upstream TODO in `Mathlib.AlgebraicTopology.
SimplicialSet.Op`, so the argument is duplicated here; the face
lemmas and the attachment pushout are shared.)

## 2. The `Δ[2]`-prism and the pointwise criterion

An edge `ε` of `Fun(B, C)` restricting strictly to an equivalence
`e` of `Fun(A, C)`, all of whose vertex evaluations are
equivalences, is an equivalence. Indeed, take inverse data
`e⁻¹`, `α : e ≫ e⁻¹ = id`, `β : e⁻¹ ≫ e = id` for `e`
(`SSet.Edge.IsEquivalence.nonempty_invStruct`); `α` and `β` are
prisms `A ⊗ Δ[2] ⟶ C`. Lift `e⁻¹` by the target-prescribed prism
extension to `φ` in `Fun(B, C)`. A `CompStruct` witness for
`ε ≫ φ = id` is a prism `B ⊗ Δ[2] ⟶ C` prescribed on `A ⊗ Δ[2]`
by `α` and on `B ⊗ Λ[2,0]` by `ε` and the degenerate prism; cell
by cell this is extension from `∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]` to
`Δ[n] ⊗ Δ[2]`. The top simplices are the shuffles
`τ_{a,b} = ((0,0), …, (a,0), (a,1), …, (b,1), (b,2), …, (n,2))`,
`0 ≤ a ≤ b ≤ n`, attached in lexicographically decreasing
`(b, a)` order; each has all faces prescribed or shared with an
earlier shuffle except one diagonal face, and the extremal
attachments are special outer horns whose special edge is a
vertical edge of a prescribed face prism — a pointwise
equivalence. Filling inner horns in `C` and special horns by T21
gives the two `CompStruct` prisms for `α` and `β`, hence
`(HomotopyCategory.homMk ε)` has inverse `(HomotopyCategory.homMk φ)`
(`HomotopyCategory.homMk_comp_homMk`, `HomotopyCategory.homMk_id`), i.e. `ε` is
an equivalence by `SSet.Edge.InvStruct.isEquivalence`. The only
formal content of this paragraph that does not need the shuffle
filtration is the last step — two `Δ[2]`-prisms with the correct
faces make the prism edge an equivalence — and that step is
formalized below (`SSet.edgeOfPrism_isEquivalence_of_compPrisms`),
so the pointwise criterion is reduced exactly to the
`Δ[2]`-prism horn extension properties for boundary inclusions
plus their skeletal closure.

## 3. Skeletal closure

The `Δ[1]`- and `Δ[2]`-prism extension properties are properties
`Q(i)` asserting existence of prism extensions with prescribed
vertical equivalences and no equivalence conclusion about functor
edges, so they are stable under pushout (tensoring with `Δ[m]`
preserves pushouts), coproducts (componentwise), composition, and
sequential composition along a tower (dependent choice; `⊗ Δ[m]`
is a left adjoint and preserves the colimit). A monomorphism `i`
has the relative skeletal filtration `skeletonOfMono i`
(upstream `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`)
with bottom `range i`, supremum `⊤`, and each step a pushout of a
coproduct of boundary inclusions
(`relativeCellComplexOfMono.isPushout`). Hence the cell cases
imply `Q(i)` for every monomorphism. The source `Δ[1]`-prism
property in general form (TODO(T47-B) below) asserts: given
`H : A ⊗ Δ[1] ⟶ C` and `g : B ⟶ C` agreeing at the source end,
with every vertical edge of `H` an equivalence, there is
`F : B ⊗ Δ[1] ⟶ C` extending `H` with source `g` and every
vertical an equivalence; the vertical conclusion is what makes
the two extension steps compose under pushout and transfinite
composition. Its cell case is the subcomplex extension of §1 read
through the prism dictionary: the initial datum `(H, b♯)` glues
along `Subcomplex.unionProd.isPushout` to a map out of `S₀` whose
vertical edge at vertex `0` is the vertical of `H` at vertex `0`
of `∂Δ[n]`, and the filled prism has the prescribed verticals
because every vertex of `Δ[n]` lies in `∂Δ[n]` for `n ≥ 1` and
the `n = 0` prism is degenerate.

## 4. Assembly of (A) and faithfulness (B2)

Given `e, b` as in §0: §1+§3 produce `F` extending `H` with source
`b` and pointwise-equivalence verticals (on `A` by `eval_vertex`,
at new vertices by construction); §2+§3 show its edge is an
equivalence. This is `SSet.HoPrePrismStrictExtension i C`, and T30
gives `(hoFunctor.map ((pre i).app C)).IsIsofibration`, i.e. (A).
For (B2), let `e₁ e₂` be edges of `Fun(Y, C)` with equal images
in `h Fun(B, C)`. Represent the downstairs equality by a
`CompStruct` `2`-simplex `sB` of `Fun(B, C)` against an identity
edge (`SSet.Edge.nonempty_compStruct_of_homMk_comp_eq`), and
the equality of the `X`-images (faithfulness of the equivalence
`hFun(f, C)`) by a `2`-simplex `sX` of `Fun(X, C)`. Their images
in `Fun(A, C)` have strictly equal boundaries. Correct `sB`
through the inner fibration `(pre i).app C` — in prism terms,
extend a homotopy of `Δ[2]`-prisms from
`A ⊗ Δ[2] ∪ B ⊗ ∂Δ[2]` data, cell by cell a shuffle filtration
of `Δ[n] ⊗ Δ[2] ⊗ Δ[1]` whose special edges are degenerate at the
vertices where the two prisms already agree — to `sB'` with the
same boundary and strict image the image of `sX`; glue at
`W = Δ[2]` by `SSet.exists_pre_lift_of_isPushout` to a
`2`-simplex of `Fun(Y, C)` witnessing `(HomotopyCategory.homMk e₁) = (HomotopyCategory.homMk e₂)`.
The gluing half of this argument is formalized below
(`SSet.hoFunctor_pre_faithful_of_isPushout_of_compCorrection`):
faithfulness follows from the `2`-simplex correction property of
`(pre i).app C`, stated as `SSet.CompCorrection` — the exact
`Δ[2]`-prism analogue of packet T31's
`SSet.exists_edge_correction_of_innerFibration` (which is the
`Δ[1]` case, a single inner horn `Λ[2,1]`). With (A) and (B2),
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful`
(packet T34) gives stability with no further formal steps; this
final assembly is recorded below with its two remaining
hypotheses named. Correction (2026-10 review): `CompCorrection ((pre i).app C)`
as stated is **false** in general. Two `2`-simplices of a
quasicategory with identical boundary need not be homotopic
relative to that boundary (in a Kan complex with nonzero
`π₂`, a nontrivial based `2`-simplex and the degenerate
`2`-simplex have the same boundary, and a relative homotopy
between them would null-homotope the `π₂` class); concretely,
for `i : ∂Δ[1] ⟶ Δ[1]`, endpoint restriction
`C^{Δ[1]} ⟶ C × C` cannot realize arbitrary prescribed
corrections. No shuffle argument can supply (B2) as stated.
A viable reformulation must add relative homotopy-class
compatibility between the two simplices, or replace this
faithfulness argument (for example by the mapping-space
route). Results below conditional on `CompCorrection` are
therefore retained only as formal reductions recording the
shape of the input, not as a viable discharge route.

## 5. Formal status of this module and remaining TODOs

Formalized here, sorry-free: the vertical-edge identifications
`SSet.prismTauMap_zero_app_edge` and
`SSet.prismTauMap_last_app_edge`; specialness of the two
extremal horns (`SSet.isEquivalence_leftHornEdge_prismSrcStep`,
`SSet.isEquivalence_rightHornEdge_prismTgtStep`), including the
two degenerate `n = 0` fillers with no equivalence hypothesis;
items (i) and (ii) over a cell in subcomplex form,
`SSet.exists_extension_of_unionProd_boundary_face_zero` and
`SSet.exists_extension_of_unionProd_boundary_face_one`, with the
mirror filtration `SSet.prismTgtFilt` and its attaching horns
`SSet.prismTgtFilt_preimage_prismTauMap` from scratch; the last
formal step of §2,
`SSet.edgeOfPrism_isEquivalence_of_compPrisms` (inverse
`Δ[2]`-prisms give an `Edge.InvStruct`); the gluing half of (B2),
`SSet.hoFunctor_pre_faithful_of_isPushout_of_compCorrection`;
and the final assemblies
`SSet.categoricalEquivalences.of_isPushout_of_prismStrictExtension_of_compCorrection`
and
`SSet.categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction`,
which reduce the unconditional stability instance to exactly
(A) `SSet.HoPrePrismStrictExtension i C` and (B2)
`SSet.CompCorrection ((pre i).app C)` for every monomorphism
`i`. In particular `SSet.HoPrePrismStrictExtension ∂Δ[n].ι C`
(boundary case, unconditional) is **not** proved here: it needs
the pointwise criterion of §2, whose only missing input is the
`Δ[2]`-prism extension over a cell.

* TODO(T47-Δ2) — the `Δ[2]`-shuffle filtration of §2: top
  simplices `τ_{a,b}` of `Δ[n] ⊗ Δ[2]` (to be defined through
  `SSet.prodStdSimplex.objEquiv`; there is no upstream
  `prodStdSimplex₂` enumeration), classification of the
  nondegenerate `τ_{a,b}`, face analysis, and the horn extension
  properties from
  `Subcomplex.unionProd ∂Δ[n] Λ[2,0]`/`Λ[2,2]` with special
  edges the pointwise verticals. Combined with (i)/(ii) above
  (target-prescribed lift of the inverse edge) and
  `SSet.edgeOfPrism_isEquivalence_of_compPrisms`, this proves
  `SSet.Edge.IsEquivalence.of_strict_restriction_pointwise` for
  `∂Δ[n].ι`, hence the boundary case of (A). Note: statements
  mixing `(mapHomotopyCategory (pre _)).map (HomotopyCategory.homMk _)` with
  `eqToHom (congrArg HomotopyCategory.mk _)` time out in
  `isDefEq` in this context; keep conjugation statements at the
  level of `(HomotopyCategory.homMk (_e.map _))` (cf.
  `SSet.cobaseUncond_pre_toHoHom_conj` in the proof of
  faithfulness below) and convert by `SSet.mapHomotopyCategory_map_homMk`
  rewrites with explicit arguments only.
* TODO(T47-B) — prism extension along a general monomorphism in
  functor form and its skeletal closure (§3): gluing
  `(H, b♯)` along `Subcomplex.unionProd.isPushout`, the bridge
  identifying the image of `SSet.prismVertZero`/`prismVertLast`
  with the vertex evaluation of `e` (through
  `SSet.evalDeltaZeroIso` at `⦋1⦌`, the `1`-simplex analogue of
  `SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv`), endpoint and
  strict-restriction computations for the filled prism via
  `SSet.δ_one_ihomSimplexOfPrism`/`δ_zero`, then closure of the
  source/target/`Δ[2]` extension properties under pushouts,
  coproducts, composition and the `skeletonOfMono` tower, and
  assembly into `SSet.HoPrePrismStrictExtension i C` for all
  monomorphisms `i`, hence
  `SSet.hoFunctor_pre_isIsofibration_of_mono` by T30.
* TODO(T47-B2) — reformulate or replace
  `SSet.CompCorrection ((pre i).app C)`: as stated it is false
  in general (see the correction in §4 above: relative
  homotopy classes in `π₂` obstruct arbitrary correction), so
  neither the triple-product shuffle nor any other argument
  can prove it. The open task is a corrected faithfulness
  input — a relative correction property carrying
  homotopy-class compatibility data, with its shuffle
  homotopy-extension proof, or the mapping-space route
  (TODO(T32-kan) in earlier packets) replacing this argument
  entirely. This supersedes both the naive `Λ[3,1]` correction
  of `CobaseChangeGeneral.lean` §3 and the `CompCorrection`
  formulation here.

With TODO(T47-Δ2) and TODO(T47-B) supplying (A), the theorem
`SSet.categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction`
below would yield the unconditional instance *if* its
`CompCorrection` hypothesis could be supplied; it cannot, as
stated (see the §4 correction), so that assembly is a formal
reduction only, pending the reformulated TODO(T47-B2).

## References

* J. Lurie, *Higher Topos Theory*, §2.3 (Proposition 2.3.4.5).
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233, §2.
* *Kerodon*, §4.5, Corollary 4.5.4.14.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-! ## The vertical edge of `τ₀` (§1 of the header)

The `(0,1)`-edge of `Δ[n+1]` maps under `τ₀` to `prismVertZero`,
and the `(n,n+1)`-edge maps under `τₙ` to the vertical edge at
vertex `n`. Through `Subcomplex.hornLift_ι` these identify the special
edges of the two extremal attaching horns. -/

section PrismVerticalIdentification

variable {n : ℕ}

/-- Values of the vertical edge at vertex `0` through
`prodStdSimplex.objEquiv`: at position `t` it is `(0, t)`. -/
lemma prismVertZero_objEquiv_apply (t : Fin 2) :
    prodStdSimplex.objEquiv.{u} (prismVertZero n) t = (0, t) :=
  rfl

/-- The vertical edge of the prism at the last vertex `n`: the
`1`-simplex `(n,0) ⟶ (n,1)`. This is the special edge of the
last attaching horn `Λ[n+1, n+1]` of the mirror filtration. -/
noncomputable def prismVertLast (n : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋1⦌ :=
  prodStdSimplex.objEquiv.symm
    ⟨fun t ↦ (⟨n, by omega⟩, t), fun _ _ hab ↦ ⟨le_rfl, hab⟩⟩

/-- Values of the vertical edge at vertex `n` through
`prodStdSimplex.objEquiv`. -/
lemma prismVertLast_objEquiv_apply (t : Fin 2) :
    prodStdSimplex.objEquiv.{u} (prismVertLast n) t =
      (⟨n, by omega⟩, t) :=
  rfl

lemma prismVertLast_fst_apply (t : Fin 2) :
    (prismVertLast n).1 t = ⟨n, by omega⟩ :=
  rfl

/-- The image of the `(0,1)`-edge of `Δ[n+1]` under `τ₀` is the
vertical edge at vertex `0`: at positions `0` and `1`, the chain
`τ₀` takes the values `(0,0)` and `(0,1)` by
`prismTau_objEquiv_fst_val`/`prismTau_objEquiv_snd` at `k = 0`. -/
lemma prismTauMap_zero_app_edge :
    (prismTauMap.{u} n 0).app _
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _)) =
      prismVertZero n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t).val = t.val := fun t ↦ by
    fin_cases t <;> rfl
  have h1 : stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _) =
      stdSimplex.objEquiv.symm
        (stdSimplex.objEquiv
          (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩ (Fin.zero_le _))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, prismTauMap, prodStdSimplex₁.ι_def,
    yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply, prismVertZero_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have ht2 := t.isLt
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := n)
      (k := (0 : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change (if t.val ≤ 0 then t.val else t.val - 1) = 0
    split_ifs <;> omega
  · have h := prismTau_objEquiv_snd.{u} (n := n)
      (k := (0 : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) 0 ⟨1, by omega⟩
          (Fin.zero_le _))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    rcases ht with h0 | h0 <;> simp [h0, Fin.ext_iff]

/-- The image of the `(n,n+1)`-edge of `Δ[n+1]` under `τₙ` is the
vertical edge at vertex `n`: at positions `n` and `n+1`, the chain
`τₙ` takes the values `(n,0)` and `(n,1)`. -/
lemma prismTauMap_last_app_edge :
    (prismTauMap.{u} n ⟨n, by omega⟩).app _
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def])) =
      prismVertLast n := by
  have hpos : ∀ t : Fin 2, ((stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]))).toOrderHom t).val = n + t.val :=
    fun t ↦ by fin_cases t <;> rfl
  have h1 :
      stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]) =
        stdSimplex.objEquiv.symm
          (stdSimplex.objEquiv
            (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
              (by simp [Fin.le_def]))) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [h1, prismTauMap, prodStdSimplex₁.ι_def,
    yonedaEquiv_symm_app_objEquiv_symm]
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prodStdSimplex.objEquiv_map_apply, prismVertLast_objEquiv_apply]
  have ht : t.val = 0 ∨ t.val = 1 := by have h2 := t.isLt; omega
  have ht2 := t.isLt
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := n)
      (k := (⟨n, by omega⟩ : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    change (if n + t.val ≤ n then n + t.val else n + t.val - 1) = n
    split_ifs <;> omega
  · have h := prismTau_objEquiv_snd.{u} (n := n)
      (k := (⟨n, by omega⟩ : Fin (n + 1))) (t := (stdSimplex.objEquiv
        (stdSimplex.edge (n + 1) ⟨n, by omega⟩ ⟨n + 1, by omega⟩
          (by simp [Fin.le_def]))).toOrderHom t)
    rw [hpos t] at h
    rw [h]
    rcases ht with h0 | h0 <;> simp [h0, Fin.ext_iff]

/-- The vertical edge at vertex `n` lies in `∂Δ[n] ⊗ Δ[1]` for
`n ≥ 1`: its first components miss the value `0`. -/
lemma prismVertLast_mem_boundary_prod (hn : 1 ≤ n) :
    prismVertLast.{u} n ∈ ((∂Δ[n]).prod ⊤).obj _ :=
  ofSimplex_le_prod_top_of_fst_mem
    (mem_boundary_of_forall_ne _ ⟨0, by omega⟩ (fun t ht ↦ by
      rw [prismVertLast_fst_apply] at ht
      have hval := congrArg Fin.val ht
      change n = 0 at hval
      omega)) _
    (Subcomplex.mem_ofSimplex_obj _)

end PrismVerticalIdentification

/-! ## The special edges of the extremal attaching horns

Through `Subcomplex.hornLift_ι`, the `(0,1)`-edge of the last
source-filtration horn map is the image of `prismVertZero`, and
the last edge of the last mirror-filtration horn map is the image
of `prismVertLast`. -/

section PrismSpecialEdges

variable {n : ℕ} {C : SSet.{u}}

/-- The constant vertex of the prism at `p : Fin (n+1) × Fin 2`. -/
noncomputable def prismVertConst (n : ℕ) (p : Fin (n + 1) × Fin 2) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ :=
  prodStdSimplex.objEquiv.symm (OrderHom.const (Fin 1) p)

/-- Values of the constant vertex through `prodStdSimplex.objEquiv`. -/
lemma prismVertConst_objEquiv_apply (p : Fin (n + 1) × Fin 2)
    (t : Fin 1) :
    prodStdSimplex.objEquiv.{u} (prismVertConst n p) t = p :=
  rfl

/-- The vertical edge at vertex `0` lies in every stage of the
source filtration. -/
lemma prismVertZero_mem_prismSrcFilt (hn : 1 ≤ n) (m : ℕ) :
    prismVertZero.{u} n ∈ (prismSrcFilt n m).obj _ :=
  (prismSrcInitial_le_prismSrcFilt m) _
    (prismVertZero_mem_prismSrcInitial hn)

/-- The horn lift for `τ₀` sends the `(0,1)`-edge simplex of
`Λ[m+2, 0]` to the vertical edge at vertex `0`. -/
lemma hornLift_app_leftHornEdgeSimplex (m : ℕ) :
    (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
        (0 : Fin (m + 2)).castSucc
        (prismSrcFilt_preimage_prismTauMap (0 : Fin (m + 2)))).app _
        (leftHornEdgeSimplex.{u} m) =
      ⟨prismVertZero (m + 1),
        prismVertZero_mem_prismSrcFilt (by omega) 1⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
          (0 : Fin (m + 2)).castSucc
          (prismSrcFilt_preimage_prismTauMap
            (0 : Fin (m + 2)))).app _
          (leftHornEdgeSimplex.{u} m)).val
      = (prismTauMap.{u} (m + 1) 0).app _
          (stdSimplex.edge (m + 2) 0 ⟨1, by omega⟩ (Fin.zero_le _)) :=
        congr($(Subcomplex.hornLift_ι
          (prismSrcFilt_preimage_prismTauMap (0 : Fin (m + 2)))).app _
            (leftHornEdgeSimplex.{u} m))
    _ = prismVertZero (m + 1) := prismTauMap_zero_app_edge

/-- The `(0,1)`-edge of the last source-filtration horn map is
the image of the vertical edge at vertex `0`. -/
lemma leftHornEdge_hornLift_comp (m : ℕ)
    (φ : ((prismSrcFilt (m + 1) 1 :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (leftHornEdge
        (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
            (0 : Fin (m + 2)).castSucc
            (prismSrcFilt_preimage_prismTauMap
              (0 : Fin (m + 2))) ≫ φ)).edge =
      φ.app _ ⟨prismVertZero (m + 1),
        prismVertZero_mem_prismSrcFilt (by omega) 1⟩ :=
  congrArg (φ.app _) (hornLift_app_leftHornEdgeSimplex m)

/-- The last source-filtration horn is special as soon as the
vertical edge at vertex `0` of the initial datum is an
equivalence. -/
lemma isEquivalence_leftHornEdge_prismSrcStep (m : ℕ)
    {φ : ((prismSrcFilt (m + 1) 1 :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((prismSrcInitial (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt 1) ≫
        φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertZero (m + 1),
        prismVertZero_mem_prismSrcInitial (by omega)⟩)).IsEquivalence) :
    (leftHornEdge
        (Subcomplex.hornLift (prismSrcFilt (m + 1) 1) (prismTau (m + 1) 0)
            (0 : Fin (m + 2)).castSucc
            (prismSrcFilt_preimage_prismTauMap
              (0 : Fin (m + 2))) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      leftHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨prismVertZero (m + 1),
          prismVertZero_mem_prismSrcInitial (by omega)⟩)) ?_).2 hVert
  rw [leftHornEdge_hornLift_comp]
  exact congr($(hrestr).app _ ⟨prismVertZero (m + 1),
    prismVertZero_mem_prismSrcInitial (by omega)⟩)

/-- The `δ 1` face of `τ₀` over `Δ[0]` is the vertex `(0,0)`. -/
lemma prismTau_zero_δ_one :
    (Δ[0] ⊗ Δ[1] : SSet.{u}).δ 1 (prismTau 0 0) =
      prismVertConst 0 (0, 0) := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prism_objEquiv_δ_apply, prismVertConst_objEquiv_apply]
  fin_cases t
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (1 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((1 : Fin 2).succAbove ⟨0, by omega⟩).val = 0 := rfl
    rw [hpos] at h
    change ((prodStdSimplex.objEquiv.{u} (prismTau 0 0)
      ((1 : Fin 2).succAbove ⟨0, by omega⟩)).1).val = 0
    rw [h]
    simp
  · have h := prismTau_objEquiv_snd.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (1 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((1 : Fin 2).succAbove ⟨0, by omega⟩).val = 0 := rfl
    rw [hpos] at h
    rw [h]
    simp

/-- The constant vertex `(0,0)` lies in the source initial
subcomplex over `Δ[0]`: its second coordinate is `0`. -/
lemma prismVertConst_zero_zero_mem_prismSrcInitial :
    prismVertConst.{u} 0 (0, 0) ∈ (prismSrcInitial 0).obj _ := by
  refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
  rw [stdSimplex.mem_face_iff]
  intro i
  exact Finset.mem_singleton.2 rfl

/-- **The degenerate filler for the `n = 0` source step**: over
`Δ[0]`, the horn `Λ[1, 0]` induced by any map out of
`prismSrcFilt 0 1` is filled by the degenerate edge at the image
of the vertex `(0,0)`. No quasicategory or equivalence hypothesis
is used. -/
lemma exists_degen_filler_prismSrc_zero
    (φ : ((prismSrcFilt 0 1 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ σC : Δ[1] ⟶ C,
      Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
          (0 : Fin 1).castSucc
          (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ =
        Λ[1, (0 : Fin 1).castSucc].ι ≫ σC := by
  set memF : prismVertConst.{u} 0 (0, 0) ∈ (prismSrcFilt 0 1).obj _ :=
    (prismSrcInitial_le_prismSrcFilt 1) _
      prismVertConst_zero_zero_mem_prismSrcInitial with hmemF
  set pt : ((prismSrcFilt 0 1 :
      (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) _⦋0⦌ :=
    ⟨prismVertConst 0 (0, 0), memF⟩ with hpt
  set x₀ : C _⦋0⦌ := φ.app _ pt with hx₀
  refine ⟨yonedaEquiv.symm (C.σ 0 x₀), ?_⟩
  have hι : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
        Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
          (0 : Fin 1).castSucc
          (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) =
      yonedaEquiv.symm pt := by
    rw [← cancel_mono (prismSrcFilt 0 1).ι]
    have e1 : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
          Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
            (0 : Fin 1).castSucc
            (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismSrcFilt 0 1).ι =
        yonedaEquiv.symm ((Δ[0] ⊗ Δ[1] : SSet.{u}).δ 1 (prismTau 0 0)) := by
      -- `hhl` is `Subcomplex.hornLift_ι` at the preimage
      -- computation, with its type ascribed in the goal's form:
      -- `prismTauMap` is now the (semireducible) def
      -- `prodStdSimplex₁.ι`, so the bare `hornLift_ι` rewrite no
      -- longer matches the goal at reducible transparency.
      have hhl : Subcomplex.hornLift (prismSrcFilt 0 1)
            (prismTau 0 0) (0 : Fin 1).castSucc
            (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismSrcFilt 0 1).ι =
        Λ[1, (0 : Fin 1).castSucc].ι ≫
          yonedaEquiv.symm (prismTau 0 0) :=
        Subcomplex.hornLift_ι
          (prismSrcFilt_preimage_prismTauMap (0 : Fin 1))
      rw [hhl, ← Category.assoc, horn.ι_ι,
        stdSimplex.δ_comp_yonedaEquiv_symm]
    have e2 : yonedaEquiv.symm pt ≫
          (prismSrcFilt 0 1).ι =
        yonedaEquiv.symm (prismVertConst 0 (0, 0)) := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    rw [Category.assoc, e1, e2, prismTau_zero_δ_one]
  have hmaps : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
        (Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
            (0 : Fin 1).castSucc
            (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
      horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
        (Λ[1, (0 : Fin 1).castSucc].ι ≫
          yonedaEquiv.symm (C.σ 0 x₀)) := by
    have eL : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
          (Subcomplex.hornLift (prismSrcFilt 0 1) (prismTau 0 0)
              (0 : Fin 1).castSucc
              (prismSrcFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
        yonedaEquiv.symm x₀ := by
      rw [← Category.assoc, hι]
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hx₀.symm
    have eR : horn.ι (0 : Fin 1).castSucc (1 : Fin 2) (by decide) ≫
          (Λ[1, (0 : Fin 1).castSucc].ι ≫
            yonedaEquiv.symm (C.σ 0 x₀)) =
        yonedaEquiv.symm x₀ := by
      have hδσ : C.δ 1 (C.σ 0 x₀) = x₀ :=
        δ_comp_σ_succ_apply (0 : Fin 1) x₀
      rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm,
        hδσ]
    rw [eL, eR]
  apply horn.hom_ext
  intro j hj
  rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
  congr 1
  fin_cases j
  · exact absurd rfl hj
  · exact hmaps

end PrismSpecialEdges

/-! ## Source-prescribed prism extension over a cell (§1)

Finite downward induction along `prismSrcFilt`: inner horns are
filled in the quasicategory, the last horn is special by the
vertical-edge identification, and the `n = 0` step is degenerate. -/

section PrismSrcExtensionCell

variable {n : ℕ} {C : SSet.{u}}

private lemma exists_extension_prismSrcFilt [Quasicategory C]
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
          prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
    ∀ (d m : ℕ), m + d = n + 1 →
      ∃ φm : ((prismSrcFilt n m :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt m) ≫ φm =
          φ₀ := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmn1 : m = n + 1 := by omega
    subst hmn1
    refine ⟨(Subcomplex.eqToIso prismSrcFilt_top).hom ≫ φ₀, ?_⟩
    have hid : Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt (n + 1)) ≫
          (Subcomplex.eqToIso prismSrcFilt_top).hom = 𝟙 _ := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (prismSrcInitial n).ι]
      simp
    rw [← Category.assoc, hid, Category.id_comp]
  | succ d ih =>
    intro m hm
    have hm1 : (m + 1) + d = n + 1 := by omega
    obtain ⟨φ₁, hφ₁⟩ := ih (m + 1) hm1
    have hmn : m ≤ n := by omega
    have hpre := prismSrcFilt_preimage_prismTauMap.{u} (⟨m, by omega⟩ :
      Fin (n + 1))
    obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 1] ⟶ C,
        Subcomplex.hornLift (prismSrcFilt n (m + 1))
            (prismTau n ⟨m, by omega⟩)
            (⟨m, by omega⟩ : Fin (n + 1)).castSucc hpre ≫ φ₁ =
          Λ[n + 1, (⟨m, by omega⟩ : Fin (n + 1)).castSucc].ι ≫ σC := by
      by_cases hm0 : m = 0
      · subst hm0
        by_cases hn0 : n = 0
        · subst hn0
          exact exists_degen_filler_prismSrc_zero φ₁
        · have hn1 : 1 ≤ n := by omega
          obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
          refine exists_fill_horn_left_of_isEquivalence _ ?_
          exact isEquivalence_leftHornEdge_prismSrcStep m' hφ₁
            (hVert hn1)
      · have hk0 : (0 : Fin (n + 2)) <
            (⟨m, by omega⟩ : Fin (n + 1)).castSucc := by
          rw [Fin.lt_def, Fin.val_castSucc]
          change 0 < m
          omega
        have hkn : (⟨m, by omega⟩ : Fin (n + 1)).castSucc <
            Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last]
          change m < n + 1
          omega
        exact Quasicategory.hornFilling hk0 hkn _
    obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
      (fun h ↦ injective_of_mono _ h) φ₁ σC hσC
    refine ⟨(Subcomplex.eqToIso (prismSrcFilt_eq_succ_sup hmn)).hom ≫
        φ', ?_⟩
    have hcomp : Subcomplex.homOfLE
          (prismSrcInitial_le_prismSrcFilt m) ≫
          (Subcomplex.eqToIso (prismSrcFilt_eq_succ_sup hmn)).hom =
        Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt (m + 1)) ≫
          Subcomplex.homOfLE (show prismSrcFilt n (m + 1) ≤
            prismSrcFilt n (m + 1) ⊔
              Subcomplex.ofSimplex
                (prismTau n ⟨m, Nat.lt_succ_of_le hmn⟩) from
            le_sup_left) := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
      simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
    exact hφ₁

/-- **Source-prescribed `Δ[1]`-prism extension over a cell**
(packet T47(i), closing the source half of `PrismCobase.lean`
item (i)). A map out of `∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` into a
quasicategory extends to the prism `Δ[n] ⊗ Δ[1]` as soon as the
image of the vertical edge at vertex `0` is an equivalence (no
hypothesis is needed for `n = 0`, where the filler is
degenerate). The proof is the downward induction along
`SSet.prismSrcFilt` of §1 of the header. -/
theorem exists_extension_of_unionProd_boundary_face_zero
    [Quasicategory C]
    (φ₀ : ((prismSrcInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
          prismVertZero_mem_prismSrcInitial hn⟩)).IsEquivalence) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (prismSrcInitial n).ι ≫ F = φ₀ := by
  obtain ⟨φm, hφm⟩ := exists_extension_prismSrcFilt φ₀ hVert (n + 1) 0
    (by omega)
  set iso : ((prismSrcFilt n 0 :
      (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) :=
    Subcomplex.eqToIso prismSrcFilt_zero ≪≫ Subcomplex.topIso _ with hiso
  refine ⟨iso.inv ≫ φm, ?_⟩
  have hhom : iso.hom = (prismSrcFilt n 0).ι := by
    rw [hiso, Iso.trans_hom, Subcomplex.eqToIso_hom,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (prismSrcInitial n).ι =
      Subcomplex.homOfLE (prismSrcInitial_le_prismSrcFilt 0) ≫
        iso.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  rw [hι, Category.assoc, ← Category.assoc iso.hom iso.inv φm,
    Iso.hom_inv_id, Category.id_comp]
  exact hφm

end PrismSrcExtensionCell

/-! ## The target-prescribed (mirror) prism filtration (§1)

The increasing filtration `G'ₘ = S₁ ⊔ ⨆_{k < m} ofSimplex τₖ`
attaches `τₖ` along `Λ[n+1, k+1]`. The face lemmas are shared
with the source filtration; the attaching-horn computation is the
mirror of `SSet.prismSrcFilt_preimage_prismTauMap`. -/

section PrismTgtFiltration

variable {n : ℕ}

/-- The initial subcomplex for the target-prescribed prism:
`∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {1}`. -/
noncomputable abbrev prismTgtInitial (n : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd ∂Δ[n] (stdSimplex.face {1})

/-- The increasing prism filtration: `S₁` together with the top
simplices `τₖ` for `k < m`. -/
noncomputable def prismTgtFilt (n : ℕ) (m : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  prismTgtInitial n ⊔ ⨆ (k : Fin (n + 1)) (_ : k.val < m),
    Subcomplex.ofSimplex (prismTau n k)

lemma prismTgtInitial_le_prismTgtFilt (m : ℕ) :
    prismTgtInitial n ≤ prismTgtFilt n m :=
  le_sup_left

lemma ofSimplex_prismTau_le_prismTgtFilt {m : ℕ} {k : Fin (n + 1)}
    (h : k.val < m) :
    Subcomplex.ofSimplex (prismTau n k) ≤ prismTgtFilt n m := by
  unfold prismTgtFilt
  refine (le_iSup_of_le k ?_).trans le_sup_right
  exact le_iSup_of_le h le_rfl

lemma prismTgtFilt_le_succ (m : ℕ) :
    prismTgtFilt n m ≤ prismTgtFilt n (m + 1) := by
  unfold prismTgtFilt
  apply sup_le le_sup_left
  apply iSup_le
  intro k
  apply iSup_le
  intro h
  refine (le_iSup_of_le k ?_).trans le_sup_right
  exact le_iSup_of_le (Nat.lt_trans h (Nat.lt_succ_self m)) le_rfl

/-- One mirror filtration step: `G'ₘ₊₁ = G'ₘ ⊔ ofSimplex τₘ`. -/
lemma prismTgtFilt_succ_eq_sup {m : ℕ} (hm : m ≤ n) :
    prismTgtFilt n (m + 1) = prismTgtFilt n m ⊔
      Subcomplex.ofSimplex (prismTau n ⟨m, by omega⟩) := by
  apply le_antisymm
  · unfold prismTgtFilt
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro k
    apply iSup_le
    intro h
    by_cases hk : k.val = m
    · have hke : k = ⟨m, by omega⟩ := Fin.ext hk
      rw [hke]
      exact le_sup_right
    · refine (le_iSup_of_le k ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le (show k.val < m by omega) le_rfl
  · exact sup_le (prismTgtFilt_le_succ m)
      (ofSimplex_prismTau_le_prismTgtFilt (Nat.lt_succ_self m))

/-- The bottom of the increasing filtration is the target initial
subcomplex. -/
lemma prismTgtFilt_zero :
    prismTgtFilt n 0 = prismTgtInitial n := by
  refine le_antisymm ?_ le_sup_left
  unfold prismTgtFilt
  refine sup_le le_rfl ?_
  apply iSup_le
  intro k
  apply iSup_le
  intro h
  exfalso
  exact Nat.not_lt_zero _ h

/-- The top of the increasing filtration is the whole prism. -/
lemma prismTgtFilt_top : prismTgtFilt n (n + 1) = ⊤ := by
  refine (prodStdSimplex.subcomplex_eq_top_iff
    (prismTgtFilt n (n + 1)) rfl).2 ?_
  intro x hx
  obtain ⟨k, hk⟩ :=
    prodStdSimplex₁.nonDegenerateEquiv.surjective ⟨x, hx⟩
  have hval : prismTau n k = x := congrArg Subtype.val hk
  rw [← hval]
  exact ofSimplex_prismTau_le_prismTgtFilt k.isLt _
    (Subcomplex.mem_ofSimplex_obj _)

/-- The diagonal simplex `codimOneSimplex j` does not lie in the
target initial subcomplex when its second coordinates take the
value `0`: its first component is the fundamental simplex of
`Δ[n]`. -/
lemma codimOne_notMem_prismTgtInitial {j : Fin (n + 2)}
    {t₀ : Fin (n + 1)}
    (ht₀ : stdSimplex.objMk₁.{u} j t₀ = 0) :
    ((prodStdSimplex₁.codimOneSimplex j).1 :
      (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) ∉
      (prismTgtInitial n).obj _ := by
  intro hmem
  have hmem2 := (Subcomplex.mem_unionProd_iff _ _ _).1 hmem
  rcases hmem2 with hsnd | hfst
  · have h1 := (stdSimplex.mem_face_iff _ _).1 hsnd t₀
    rw [codimOne_snd, ht₀] at h1
    simp at h1
  · rw [codimOne_fst] at hfst
    exact stdSimplex.notMem_boundary n hfst

/-- **The attaching horn for the increasing filtration**: the
preimage of `G'ₖ` under `τₖ` is `Λ[n+1, k+1]`. The face omitting
`(k,0)` is shared with `τₖ₋₁` (over the top face for `k = 0`);
the missing diagonal face omitting `(k,1)` is in neither `S₁`
nor any earlier `τ_{k'}`, by the vertex `(k, 0)` of its range. -/
lemma prismTgtFilt_preimage_prismTauMap (k : Fin (n + 1)) :
    (prismTgtFilt n k.val).preimage (prismTauMap.{u} n k) =
      Λ[n + 1, k.succ] := by
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      image_face_singleton_compl_prismTauMap,
      prodStdSimplex₁.δ_succ_nonDegenerateEquiv,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold prismTgtFilt at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact codimOne_notMem_prismTgtInitial (j := k.succ)
        (t₀ := ⟨k.val, k.isLt⟩) (by
          rw [stdSimplex.objMk₁_apply]
          have hlt : (⟨k.val, k.isLt⟩ : Fin (n + 1)).castSucc <
              k.succ := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
            exact Nat.lt_succ_self _
          simp only [hlt, ↓reduceIte]) h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨k', hlt, hmem'⟩ := hI
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
          (prodStdSimplex₁.codimOneSimplex k.succ).1) ⊆
          Set.range (prodStdSimplex.objEquiv.{u} (prismTau n k')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      have hmemK : (⟨k.val, k.isLt⟩, (0 : Fin 2)) ∈ Set.range
          (prodStdSimplex.objEquiv.{u}
            (prodStdSimplex₁.codimOneSimplex k.succ).1) :=
        mem_range_codimOne_objEquiv.2
          (Or.inl ⟨rfl, by
            rw [Fin.val_succ]
            exact Nat.lt_succ_self _⟩)
      have hthis := hle2 hmemK
      have hle' : (⟨k.val, k.isLt⟩ : Fin (n + 1)) ≤ k' :=
        (prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff.{u}
          k' ⟨k.val, k.isLt⟩).1 hthis
      change k.val ≤ k'.val at hle'
      omega
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hj' : j ≠ k.succ := by
      simpa using hj
    rw [← Subcomplex.image_le_iff,
      image_face_singleton_compl_prismTauMap]
    by_cases hjk : j.val < k.val
    · exact (prismTau_δ_ofSimplex_le_boundary_prod_top_of_lt
        hjk).trans ((Subcomplex.prod_top_le_unionProd _ _).trans
          (prismTgtInitial_le_prismTgtFilt _))
    · by_cases hjk2 : k.val + 1 < j.val
      · exact (prismTau_δ_ofSimplex_le_boundary_prod_top_of_gt
          hjk2).trans ((Subcomplex.prod_top_le_unionProd _ _).trans
            (prismTgtInitial_le_prismTgtFilt _))
      · have hne : j.val ≠ k.val + 1 := fun hv ↦ hj' (Fin.ext (by
            rw [Fin.val_succ]; exact hv))
        have hj_eq : j = k.castSucc := Fin.ext (by
          show j.val = (k.castSucc).val
          rw [Fin.val_castSucc]
          omega)
        subst hj_eq
        rw [prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv]
        by_cases hk0 : k.val = 0
        · refine (ofSimplex_le_top_prod_of_snd_mem ?_).trans
            ((Subcomplex.top_prod_le_unionProd _ _).trans
              (prismTgtInitial_le_prismTgtFilt _))
          rw [codimOne_snd, stdSimplex.mem_face_iff]
          intro t
          rw [stdSimplex.objMk₁_apply]
          have ht : ¬ t.castSucc < k.castSucc := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_castSucc, hk0]
            exact Nat.not_lt_zero _
          simp only [ht, ↓reduceIte, Finset.mem_singleton]
        · have hkk : (⟨k.val - 1, by omega⟩ : Fin (n + 1)).succ =
              k.castSucc :=
            Fin.ext (by
              change ((⟨k.val - 1, by omega⟩ : Fin (n + 1)).succ).val =
                k.val
              rw [Fin.val_succ]
              change k.val - 1 + 1 = k.val
              omega)
          have hδ :=
            prodStdSimplex₁.δ_succ_nonDegenerateEquiv
              (⟨k.val - 1, by omega⟩ : Fin (n + 1))
          rw [hkk] at hδ
          rw [← hδ]
          have hmem'' : (Δ[n] ⊗ Δ[1] : SSet.{u}).δ k.castSucc
                (prismTau n ⟨k.val - 1, by omega⟩) ∈
              (Subcomplex.ofSimplex
                (prismTau n ⟨k.val - 1, by omega⟩)).obj _ :=
            (Subcomplex.ofSimplex
              (prismTau n ⟨k.val - 1, by omega⟩)).map _
              (Subcomplex.mem_ofSimplex_obj _)
          exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem'').trans
            (ofSimplex_prismTau_le_prismTgtFilt
              (show (⟨k.val - 1, by omega⟩ : Fin (n + 1)).val <
                k.val from by
                change k.val - 1 < k.val
                omega))

/-- For `n ≥ 1` the vertical edge at vertex `n` lies in the
target initial subcomplex, through its boundary factor. -/
lemma prismVertLast_mem_prismTgtInitial (hn : 1 ≤ n) :
    prismVertLast.{u} n ∈ (prismTgtInitial n).obj _ :=
  (Subcomplex.prod_top_le_unionProd ∂Δ[n] (stdSimplex.face {1})) _
    (prismVertLast_mem_boundary_prod hn)

/-- The vertical edge at vertex `n` lies in every stage of the
target filtration. -/
lemma prismVertLast_mem_prismTgtFilt (hn : 1 ≤ n) (m : ℕ) :
    prismVertLast.{u} n ∈ (prismTgtFilt n m).obj _ :=
  (prismTgtInitial_le_prismTgtFilt m) _
    (prismVertLast_mem_prismTgtInitial hn)

end PrismTgtFiltration

/-! ## The special edge of the last mirror horn and target extension

Mirror of `PrismSpecialEdges`/`PrismSrcExtensionCell`: the last
edge of `Λ[n+1, n+1]` is the vertical at vertex `n`, the `n = 0`
step is degenerate at `(0,1)`, and the induction runs upwards. -/

section PrismTgtExtensionCell

variable {n : ℕ} {C : SSet.{u}}

/-- The horn lift for `τₙ` sends the last-edge simplex of
`Λ[m+2, m+2]` to the vertical edge at vertex `m+1`. -/
lemma hornLift_app_rightHornEdgeSimplex (m : ℕ) :
    (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
        (prismTau (m + 1) ⟨m + 1, by omega⟩)
        (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
        (prismTgtFilt_preimage_prismTauMap
          (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
        (rightHornEdgeSimplex.{u} m) =
      ⟨prismVertLast (m + 1),
        prismVertLast_mem_prismTgtFilt (by omega) (m + 1)⟩ := by
  apply Subtype.ext
  calc ((Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
          (prismTau (m + 1) ⟨m + 1, by omega⟩)
          (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
          (prismTgtFilt_preimage_prismTauMap
            (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
          (rightHornEdgeSimplex.{u} m)).val
      = (prismTauMap.{u} (m + 1) ⟨m + 1, by omega⟩).app _
          (stdSimplex.edge (m + 2) ⟨m + 1, by omega⟩
            ⟨m + 2, by omega⟩ (by simp [Fin.le_def])) :=
        congr($(Subcomplex.hornLift_ι
          (prismTgtFilt_preimage_prismTauMap
            (⟨m + 1, by omega⟩ : Fin (m + 2)))).app _
            (rightHornEdgeSimplex.{u} m))
    _ = prismVertLast (m + 1) := prismTauMap_last_app_edge

/-- The last edge of the last mirror-filtration horn map is the
image of the vertical edge at the last vertex. -/
lemma rightHornEdge_hornLift_comp (m : ℕ)
    (φ : ((prismTgtFilt (m + 1) (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    (rightHornEdge
        (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
            (prismTau (m + 1) ⟨m + 1, by omega⟩)
            (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
            (prismTgtFilt_preimage_prismTauMap
              (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).edge =
      φ.app _ ⟨prismVertLast (m + 1),
        prismVertLast_mem_prismTgtFilt (by omega) (m + 1)⟩ :=
  congrArg (φ.app _) (hornLift_app_rightHornEdgeSimplex m)

/-- The last mirror-filtration horn is special as soon as the
vertical edge at the last vertex of the initial datum is an
equivalence. -/
lemma isEquivalence_rightHornEdge_prismTgtStep (m : ℕ)
    {φ : ((prismTgtFilt (m + 1) (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    {φ₀ : ((prismTgtInitial (m + 1) :
        (Δ[m + 1] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C}
    (hrestr : Subcomplex.homOfLE
        (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫ φ = φ₀)
    (hVert : (Edge.mk' (φ₀.app _ ⟨prismVertLast (m + 1),
        prismVertLast_mem_prismTgtInitial (by omega)⟩)).IsEquivalence) :
    (rightHornEdge
        (Subcomplex.hornLift (prismTgtFilt (m + 1) (m + 1))
            (prismTau (m + 1) ⟨m + 1, by omega⟩)
            (⟨m + 1, by omega⟩ : Fin (m + 2)).succ
            (prismTgtFilt_preimage_prismTauMap
              (⟨m + 1, by omega⟩ : Fin (m + 2))) ≫ φ)).IsEquivalence := by
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      rightHornEdge _) (e' := Edge.mk' (φ₀.app _
        ⟨prismVertLast (m + 1),
          prismVertLast_mem_prismTgtInitial (by omega)⟩)) ?_).2 hVert
  rw [rightHornEdge_hornLift_comp]
  exact congr($(hrestr).app _ ⟨prismVertLast (m + 1),
    prismVertLast_mem_prismTgtInitial (by omega)⟩)

/-- The `δ 0` face of `τ₀` over `Δ[0]` is the vertex `(0,1)`. -/
lemma prismTau_zero_δ_zero :
    (Δ[0] ⊗ Δ[1] : SSet.{u}).δ 0 (prismTau 0 0) =
      prismVertConst 0 (0, 1) := by
  apply prodStdSimplex.objEquiv.injective
  apply DFunLike.ext
  intro t
  rw [prism_objEquiv_δ_apply, prismVertConst_objEquiv_apply]
  fin_cases t
  apply Prod.ext
  · apply Fin.ext
    have h := prismTau_objEquiv_fst_val.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (0 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((0 : Fin 2).succAbove ⟨0, by omega⟩).val = 1 := rfl
    rw [hpos] at h
    change ((prodStdSimplex.objEquiv.{u} (prismTau 0 0)
      ((0 : Fin 2).succAbove ⟨0, by omega⟩)).1).val = 0
    rw [h]
    simp
  · have h := prismTau_objEquiv_snd.{u} (n := 0)
      (k := (0 : Fin 1)) (t := (0 : Fin 2).succAbove ⟨0, by omega⟩)
    have hpos : ((0 : Fin 2).succAbove ⟨0, by omega⟩).val = 1 := rfl
    rw [hpos] at h
    rw [h]
    simp

/-- The constant vertex `(0,1)` lies in the target initial
subcomplex over `Δ[0]`: its second coordinate is `1`. -/
lemma prismVertConst_zero_one_mem_prismTgtInitial :
    prismVertConst.{u} 0 (0, 1) ∈ (prismTgtInitial 0).obj _ := by
  refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl ?_)
  rw [stdSimplex.mem_face_iff]
  intro i
  exact Finset.mem_singleton.2 rfl

/-- **The degenerate filler for the `n = 0` target step**: over
`Δ[0]`, the horn `Λ[1, 1]` induced by any map out of
`prismTgtFilt 0 0` is filled by the degenerate edge at the image
of the vertex `(0,1)`. -/
lemma exists_degen_filler_prismTgt_zero
    (φ : ((prismTgtFilt 0 0 :
        (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C) :
    ∃ σC : Δ[1] ⟶ C,
      Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
          (0 : Fin 1).succ
          (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ =
        Λ[1, (0 : Fin 1).succ].ι ≫ σC := by
  set memF : prismVertConst.{u} 0 (0, 1) ∈ (prismTgtFilt 0 0).obj _ :=
    (prismTgtInitial_le_prismTgtFilt 0) _
      prismVertConst_zero_one_mem_prismTgtInitial with hmemF
  set pt : ((prismTgtFilt 0 0 :
      (Δ[0] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) _⦋0⦌ :=
    ⟨prismVertConst 0 (0, 1), memF⟩ with hpt
  set x₁ : C _⦋0⦌ := φ.app _ pt with hx₁
  refine ⟨yonedaEquiv.symm (C.σ 0 x₁), ?_⟩
  have hι : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
        Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
          (0 : Fin 1).succ
          (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) =
      yonedaEquiv.symm pt := by
    rw [← cancel_mono (prismTgtFilt 0 0).ι]
    have e1 : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
          Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
            (0 : Fin 1).succ
            (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismTgtFilt 0 0).ι =
        yonedaEquiv.symm ((Δ[0] ⊗ Δ[1] : SSet.{u}).δ 0 (prismTau 0 0)) := by
      -- As in the source case, `Subcomplex.hornLift_ι` with its
      -- type ascribed in the goal's form (`prismTauMap` is now
      -- the semireducible def `prodStdSimplex₁.ι`).
      have hhl : Subcomplex.hornLift (prismTgtFilt 0 0)
            (prismTau 0 0) (0 : Fin 1).succ
            (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫
          (prismTgtFilt 0 0).ι =
        Λ[1, (0 : Fin 1).succ].ι ≫
          yonedaEquiv.symm (prismTau 0 0) :=
        Subcomplex.hornLift_ι
          (prismTgtFilt_preimage_prismTauMap (0 : Fin 1))
      rw [hhl, ← Category.assoc, horn.ι_ι,
        stdSimplex.δ_comp_yonedaEquiv_symm]
    have e2 : yonedaEquiv.symm pt ≫
          (prismTgtFilt 0 0).ι =
        yonedaEquiv.symm (prismVertConst 0 (0, 1)) := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    rw [Category.assoc, e1, e2, prismTau_zero_δ_zero]
  have hmaps : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
        (Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
            (0 : Fin 1).succ
            (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
      horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
        (Λ[1, (0 : Fin 1).succ].ι ≫
          yonedaEquiv.symm (C.σ 0 x₁)) := by
    have eL : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
          (Subcomplex.hornLift (prismTgtFilt 0 0) (prismTau 0 0)
              (0 : Fin 1).succ
              (prismTgtFilt_preimage_prismTauMap (0 : Fin 1)) ≫ φ) =
        yonedaEquiv.symm x₁ := by
      rw [← Category.assoc, hι]
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact hx₁.symm
    have eR : horn.ι (0 : Fin 1).succ (0 : Fin 2) (by decide) ≫
          (Λ[1, (0 : Fin 1).succ].ι ≫
            yonedaEquiv.symm (C.σ 0 x₁)) =
        yonedaEquiv.symm x₁ := by
      have hδσ : C.δ 0 (C.σ 0 x₁) = x₁ :=
        δ_comp_σ_self_apply (0 : Fin 1) x₁
      rw [← Category.assoc, horn.ι_ι, stdSimplex.δ_comp_yonedaEquiv_symm,
        hδσ]
    rw [eL, eR]
  apply horn.hom_ext
  intro j hj
  rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
  congr 1
  fin_cases j
  · exact hmaps
  · exact absurd rfl hj

private lemma exists_extension_prismTgtFilt [Quasicategory C]
    (φ₀ : ((prismTgtInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertLast n,
          prismVertLast_mem_prismTgtInitial hn⟩)).IsEquivalence) :
    ∀ (m : ℕ), m ≤ n + 1 →
      ∃ φm : ((prismTgtFilt n m :
          (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C,
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫ φm =
          φ₀ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨(Subcomplex.eqToIso prismTgtFilt_zero).hom ≫ φ₀, ?_⟩
    have hid : Subcomplex.homOfLE
          (prismTgtInitial_le_prismTgtFilt (n := n) 0) ≫
          (Subcomplex.eqToIso (prismTgtFilt_zero (n := n))).hom =
          𝟙 _ := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (prismTgtInitial n).ι]
      simp
    rw [← Category.assoc, hid, Category.id_comp]
  | succ m ih =>
    intro hm
    obtain ⟨φ₁, hφ₁⟩ := ih (by omega)
    have hmn : m ≤ n := by omega
    have hpre := prismTgtFilt_preimage_prismTauMap.{u}
      (⟨m, by omega⟩ : Fin (n + 1))
    obtain ⟨σC, hσC⟩ : ∃ σC : Δ[n + 1] ⟶ C,
        Subcomplex.hornLift (prismTgtFilt n m)
            (prismTau n ⟨m, by omega⟩)
            (⟨m, by omega⟩ : Fin (n + 1)).succ hpre ≫ φ₁ =
          Λ[n + 1, (⟨m, by omega⟩ : Fin (n + 1)).succ].ι ≫ σC := by
      by_cases hmn' : m = n
      · obtain rfl : n = m := hmn'.symm
        by_cases hn0 : n = 0
        · subst hn0
          exact exists_degen_filler_prismTgt_zero φ₁
        · have hn1 : 1 ≤ n := by omega
          obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
          refine exists_fill_horn_right_of_isEquivalence _ ?_
          exact isEquivalence_rightHornEdge_prismTgtStep m' hφ₁
            (hVert hn1)
      · have hk0 : (0 : Fin (n + 2)) <
            (⟨m, by omega⟩ : Fin (n + 1)).succ := by
          rw [Fin.lt_def, Fin.val_succ]
          change 0 < m + 1
          omega
        have hkn : (⟨m, by omega⟩ : Fin (n + 1)).succ <
            Fin.last (n + 1) := by
          rw [Fin.lt_def, Fin.val_succ, Fin.val_last]
          change m + 1 < n + 1
          omega
        exact Quasicategory.hornFilling hk0 hkn _
    obtain ⟨φ', hφ'1, -⟩ := Subcomplex.exists_extension_sup_of_horn_filler hpre
      (fun h ↦ injective_of_mono _ h) φ₁ σC hσC
    refine ⟨(Subcomplex.eqToIso (prismTgtFilt_succ_eq_sup hmn)).hom ≫
        φ', ?_⟩
    have hcomp : Subcomplex.homOfLE
          (prismTgtInitial_le_prismTgtFilt (m + 1)) ≫
          (Subcomplex.eqToIso (prismTgtFilt_succ_eq_sup hmn)).hom =
        Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt m) ≫
          Subcomplex.homOfLE (show prismTgtFilt n m ≤
            prismTgtFilt n m ⊔
              Subcomplex.ofSimplex
                (prismTau n ⟨m, Nat.lt_succ_of_le hmn⟩) from
            le_sup_left) := by
      rw [Subcomplex.eqToIso_hom, ← cancel_mono (Subcomplex.ι _)]
      simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, hcomp, Category.assoc, hφ'1]
    exact hφ₁

/-- **Target-prescribed `Δ[1]`-prism extension over a cell**
(packet T47(ii), closing the mirror half of `PrismCobase.lean`
item (ii)). A map out of `∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {1}` into a
quasicategory extends to the prism `Δ[n] ⊗ Δ[1]` as soon as the
image of the vertical edge at the last vertex is an equivalence
(no hypothesis for `n = 0`). -/
theorem exists_extension_of_unionProd_boundary_face_one
    [Quasicategory C]
    (φ₀ : ((prismTgtInitial n :
        (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C)
    (hVert : ∀ hn : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertLast n,
          prismVertLast_mem_prismTgtInitial hn⟩)).IsEquivalence) :
    ∃ F : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ C,
      (prismTgtInitial n).ι ≫ F = φ₀ := by
  obtain ⟨φm, hφm⟩ := exists_extension_prismTgtFilt φ₀ hVert (n + 1)
    (by omega)
  set iso : ((prismTgtFilt n (n + 1) :
      (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≅
      (Δ[n] ⊗ Δ[1] : SSet.{u}) :=
    Subcomplex.eqToIso prismTgtFilt_top ≪≫ Subcomplex.topIso _ with hiso
  refine ⟨iso.inv ≫ φm, ?_⟩
  have hhom : iso.hom = (prismTgtFilt n (n + 1)).ι := by
    rw [hiso, Iso.trans_hom, Subcomplex.eqToIso_hom,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]
  have hι : (prismTgtInitial n).ι =
      Subcomplex.homOfLE (prismTgtInitial_le_prismTgtFilt (n + 1)) ≫
        iso.hom := by
    rw [hhom]
    exact (Subcomplex.homOfLE_ι _).symm
  rw [hι, Category.assoc, ← Category.assoc iso.hom iso.inv φm,
    Iso.hom_inv_id, Category.id_comp]
  exact hφm

end PrismTgtExtensionCell

/-! ## From `Δ[2]`-prisms to equivalence of the prism edge (§2)

The formal last step of the pointwise criterion: a `Δ[1]`-prism
edge equipped with an inverse prism and two `Δ[2]`-prisms
witnessing the two compositions with the degenerate prisms is an
equivalence, through `Edge.InvStruct`. The `Δ[2]`-prisms
themselves are exactly the output of the shuffle filtration of
§2 of the header, which remains to be formalized. -/

section CompPrismsEquivalence

variable {B C : SSet.{u}} {x₀ x₁ : ((ihom B).obj C) _⦋0⦌}

/-- **A prism edge with inverse `Δ[2]`-prisms is an
equivalence.** Given prisms `F G : B ⊗ Δ[1] ⟶ C` between
prescribed vertices and prisms `P Q : B ⊗ Δ[2] ⟶ C` whose
`δ₂`- and `δ₀`-faces are `F, G` (resp. `G, F`) and whose
`δ₁`-face is the degenerate prism at the source vertex, the edge
of `F` in `Fun(B, C)` is an equivalence: the two `Δ[2]`-prisms
are `CompStruct` witnesses through
`SSet.δ_ihomSimplexOfPrism`/`SSet.σ_ihomSimplexOfPrism`, i.e. an
`Edge.InvStruct` for `edgeOfPrism F`. -/
theorem edgeOfPrism_isEquivalence_of_compPrisms
    (F G : B ⊗ Δ[1] ⟶ C)
    (hF₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism F) = x₀)
    (hF₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) = x₁)
    (hG₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism G) = x₁)
    (hG₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism G) = x₀)
    (P Q : B ⊗ Δ[2] ⟶ C)
    (hP₂ : (B ◁ stdSimplex.δ 2) ≫ P = F)
    (hP₀ : (B ◁ stdSimplex.δ 0) ≫ P = G)
    (hP₁ : (B ◁ stdSimplex.δ 1) ≫ P =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F)
    (hQ₂ : (B ◁ stdSimplex.δ 2) ≫ Q = G)
    (hQ₀ : (B ◁ stdSimplex.δ 0) ≫ Q = F)
    (hQ₁ : (B ◁ stdSimplex.δ 1) ≫ Q =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ G) :
    (edgeOfPrism F hF₀ hF₁).IsEquivalence := by
  have hcompP : Edge.CompStruct (edgeOfPrism F hF₀ hF₁)
      (edgeOfPrism G hG₀ hG₁) (Edge.id x₀) :=
    Edge.CompStruct.mk (ihomSimplexOfPrism P)
      (by rw [δ_ihomSimplexOfPrism, hP₂, edgeOfPrism_edge])
      (by rw [δ_ihomSimplexOfPrism, hP₀, edgeOfPrism_edge])
      (by
        rw [δ_ihomSimplexOfPrism, hP₁, ← σ_ihomSimplexOfPrism,
          ← δ_ihomSimplexOfPrism, hF₀, Edge.id_edge])
  have hcompQ : Edge.CompStruct (edgeOfPrism G hG₀ hG₁)
      (edgeOfPrism F hF₀ hF₁) (Edge.id x₁) :=
    Edge.CompStruct.mk (ihomSimplexOfPrism Q)
      (by rw [δ_ihomSimplexOfPrism, hQ₂, edgeOfPrism_edge])
      (by rw [δ_ihomSimplexOfPrism, hQ₀, edgeOfPrism_edge])
      (by
        rw [δ_ihomSimplexOfPrism, hQ₁, ← σ_ihomSimplexOfPrism,
          ← δ_ihomSimplexOfPrism, hG₀, Edge.id_edge])
  have hI : Edge.InvStruct (edgeOfPrism F hF₀ hF₁) :=
    { inv := edgeOfPrism G hG₀ hG₁, homInvId := hcompP,
      invHomId := hcompQ }
  exact hI.isEquivalence

end CompPrismsEquivalence

/-! ## Faithfulness from `2`-simplex correction (§4, TODO(T34-B2))

The `Δ[2]`-analogue of packet T31's edge correction: a
`CompStruct` `2`-simplex can be corrected rel boundary through
`p` so that its strict image is a prescribed `2`-simplex with the
same boundary edges downstairs. Faithfulness of precomposition
with a cobase change follows by gluing at `Δ[2]` along the
pullback `SSet.isPullback_pre_app_of_isPushout`, exactly as
fullness (packet T34) follows from edge correction by gluing at
`Δ[1]`. -/

section FaithfulnessAssembly

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y}
  {j : X ⟶ Y}

private lemma cobaseUncond_edge_map_map {E F G : SSet.{u}}
    {x₀ x₁ : E _⦋0⦌} (e : Edge x₀ x₁) (g : E ⟶ F) (h : F ⟶ G) :
    (e.map g).map h = e.map (g ≫ h) :=
  Edge.ext (by simp [Edge.map_edge])

private lemma cobaseUncond_toHoHom_ofEq {W : SSet.{u}}
    {a b a' b' : W _⦋0⦌} (e : Edge a b) (h₀ : a = a') (h₁ : b = b') :
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

/-- **Correction of `2`-simplices rel boundary** through
`p : E ⟶ B`: every `CompStruct` `2`-simplex `s` of `E` can be
replaced by a `2`-simplex `s'` with the same three boundary edges
whose strict image under `p` is a prescribed `CompStruct`
`2`-simplex `t` downstairs with boundary the images of the same
edges. For `p = (pre i).app C` this is the prism extension problem
for homotopies of `Δ[2]`-prisms of §4 of the header; it is the
`Δ[2]`-analogue of
`SSet.exists_edge_correction_of_innerFibration` (packet T31).
Unlike that `Δ[1]` case, this `Δ[2]` property is false in
general: relative `π₂` classes obstruct correcting to an
arbitrary prescribed `t` (see the correction in the module
header). It is kept, with the theorems conditional on it, as
a formal reduction recording the input shape a corrected
relative-compatibility version would need. -/
def CompCorrection {E B : SSet.{u}} (p : E ⟶ B) : Prop :=
  ∀ {x₀ x₁ x₂ : E _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂}
    (_s : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (t : Edge.CompStruct (e₀₁.map p) (e₁₂.map p) (e₀₂.map p)),
    ∃ s' : Edge.CompStruct e₀₁ e₁₂ e₀₂, p.app _ s'.simplex = t.simplex

/-- Conjugation of the two restrictions of an edge of `Fun(Y, C)`
to `Fun(A, C)` by the vertex equalities of the pullback square:
the `B`-restriction followed by `pre i` is the `eqToHom`
conjugate of the `X`-restriction followed by `pre f`. -/
private lemma cobaseUncond_pre_toHoHom_conj (C : SSet.{u})
    {y₁ y₂ : ((ihom Y).obj C) _⦋0⦌}
    (hv : ∀ y : ((ihom Y).obj C) _⦋0⦌,
      ((pre f).app C).app _ (((pre j).app C).app _ y) =
        ((pre i).app C).app _ (((pre f').app C).app _ y))
    (eY : Edge y₁ y₂)
    (hedge : ((eY.map ((pre j).app C)).map ((pre f).app C)).edge =
      ((eY.map ((pre f').app C)).map ((pre i).app C)).edge) :
    (HomotopyCategory.homMk ((eY.map ((pre f').app C)).map ((pre i).app C))) =
      eqToHom (congrArg HomotopyCategory.mk (hv y₁).symm) ≫
        (HomotopyCategory.homMk ((eY.map ((pre j).app C)).map ((pre f).app C))) ≫
        eqToHom (congrArg HomotopyCategory.mk (hv y₂)) := by
  have hw : ((eY.map ((pre j).app C)).map ((pre f).app C)).ofEq
        (hv y₁) (hv y₂) =
      (eY.map ((pre f').app C)).map ((pre i).app C) :=
    Edge.ext hedge
  rw [← cobaseUncond_toHoHom_ofEq
    ((eY.map ((pre j).app C)).map ((pre f).app C)) (hv y₁) (hv y₂)]
  exact congrArg HomotopyCategory.homMk hw.symm

/-- Faces of a glued `2`-simplex of `Fun(Y, C)` are read off from
either projection, by joint monicity of the pullback square
`SSet.isPullback_pre_app_of_isPushout`. -/
private lemma cobaseUncond_δ_yonedaEquiv_of_lift
    (sq : IsPushout i f f' j) (C : SSet.{u})
    {Wmap : Δ[2] ⟶ (ihom Y).obj C}
    {sBe : ((ihom B).obj C) _⦋2⦌} {sXe : ((ihom X).obj C) _⦋2⦌}
    {sY : ((ihom Y).obj C) _⦋1⦌} {idx : Fin 3}
    (hB : Wmap ≫ (pre f').app C = yonedaEquiv.symm sBe)
    (hX : Wmap ≫ (pre j).app C = yonedaEquiv.symm sXe)
    (hBy : ((ihom B).obj C).δ idx sBe = ((pre f').app C).app _ sY)
    (hXy : ((ihom X).obj C).δ idx sXe = ((pre j).app C).app _ sY) :
    ((ihom Y).obj C).δ idx (yonedaEquiv Wmap) = sY := by
  have hks : yonedaEquiv.symm (((ihom Y).obj C).δ idx
        (yonedaEquiv Wmap)) =
      yonedaEquiv.symm sY := by
    apply (isPullback_pre_app_of_isPushout sq C).hom_ext
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simp only [Equiv.apply_symm_apply]
      calc ((pre f').app C).app _
            (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
          = ((ihom B).obj C).δ idx
              (((pre f').app C).app _ (yonedaEquiv Wmap)) :=
            δ_naturality_apply ((pre f').app C) idx (yonedaEquiv Wmap)
        _ = ((ihom B).obj C).δ idx sBe := by
            rw [← yonedaEquiv_comp, hB, Equiv.apply_symm_apply]
        _ = ((pre f').app C).app _ sY := hBy
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp]
      simp only [Equiv.apply_symm_apply]
      calc ((pre j).app C).app _
            (((ihom Y).obj C).δ idx (yonedaEquiv Wmap))
          = ((ihom X).obj C).δ idx
              (((pre j).app C).app _ (yonedaEquiv Wmap)) :=
            δ_naturality_apply ((pre j).app C) idx (yonedaEquiv Wmap)
        _ = ((ihom X).obj C).δ idx sXe := by
            rw [← yonedaEquiv_comp, hX, Equiv.apply_symm_apply]
        _ = ((pre j).app C).app _ sY := hXy
  have h2 := congrArg yonedaEquiv hks
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2

/-- **Faithfulness of precomposition with a cobase change,
granted `2`-simplex correction.** In a pushout square with
`f` a categorical equivalence (no hypothesis on `i` is used), if
`2`-simplices correct through `(pre i).app C` rel boundary
(`SSet.CompCorrection`), then precomposition with `f'` is
faithful on homotopy categories into `C`: represent the two
morphisms by edges, witness their downstairs equality in
`Fun(B, C)` and (through the equivalence `hFun(f, C)`) in
`Fun(X, C)` by `CompStruct` `2`-simplices, correct the first so
the two agree strictly in `Fun(A, C)`, and glue at `Δ[2]`. -/
theorem hoFunctor_pre_faithful_of_isPushout_of_compCorrection
    (sq : IsPushout i f f' j) (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C]
    (hCorr : CompCorrection ((pre i).app C)) :
    (hoFunctor.map ((pre f').app C)).toFunctor.Faithful := by
  have hFf : (hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
    (categoricalEquivalences.mem_iff f).1 hf C inferInstance
  have hFf' : (mapHomotopyCategory ((pre f).app C)).IsEquivalence := hFf
  have := hFf'
  change (mapHomotopyCategory ((pre f').app C)).Faithful
  constructor
  intro P Q φ ψ hφψ
  obtain ⟨y₁, rfl⟩ : ∃ y, HomotopyCategory.mk y = P :=
    ⟨_, HomotopyCategory.objEquiv.left_inv P⟩
  obtain ⟨y₂, rfl⟩ : ∃ y, HomotopyCategory.mk y = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  obtain ⟨eYφ, hφ⟩ := Edge.exists_homMk_eq φ
  obtain ⟨eYψ, hψ⟩ := Edge.exists_homMk_eq ψ
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
  have huB : (HomotopyCategory.homMk (eYφ.map ((pre f').app C))) =
      (HomotopyCategory.homMk (eYψ.map ((pre f').app C))) := by
    rw [← mapHomotopyCategory_map_homMk, ← mapHomotopyCategory_map_homMk, hφ, hψ]
    exact hφψ
  have hedgeA : ∀ eY : Edge y₁ y₂,
      ((eY.map ((pre j).app C)).map ((pre f).app C)).edge =
        ((eY.map ((pre f').app C)).map ((pre i).app C)).edge := by
    intro eY
    rw [cobaseUncond_edge_map_map, cobaseUncond_edge_map_map,
      Edge.map_edge, Edge.map_edge]
    have key1 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
      rw [pre_map]; rfl
    have key2 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
      rw [pre_map]; rfl
    rw [key1, key2, sq.w]
  have huB' : (HomotopyCategory.homMk ((eYφ.map ((pre f').app C)).map
        ((pre i).app C))) =
      (HomotopyCategory.homMk ((eYψ.map ((pre f').app C)).map ((pre i).app C))) := by
    rw [← mapHomotopyCategory_map_homMk ((pre i).app C) (eYφ.map ((pre f').app C)),
      ← mapHomotopyCategory_map_homMk ((pre i).app C) (eYψ.map ((pre f').app C)), huB]
  have huX : (HomotopyCategory.homMk (eYφ.map ((pre j).app C))) =
      (HomotopyCategory.homMk (eYψ.map ((pre j).app C))) := by
    apply (mapHomotopyCategory ((pre f).app C)).map_injective
    rw [mapHomotopyCategory_map_homMk ((pre f).app C) (eYφ.map ((pre j).app C)),
      mapHomotopyCategory_map_homMk ((pre f).app C) (eYψ.map ((pre j).app C))]
    have step : ∀ eY : Edge y₁ y₂,
        (HomotopyCategory.homMk ((eY.map ((pre j).app C)).map ((pre f).app C))) =
          eqToHom (congrArg HomotopyCategory.mk (hv y₁)) ≫
            (HomotopyCategory.homMk ((eY.map ((pre f').app C)).map ((pre i).app C))) ≫
            eqToHom (congrArg HomotopyCategory.mk (hv y₂).symm) := by
      intro eY
      have h1 := cobaseUncond_pre_toHoHom_conj C hv eY (hedgeA eY)
      rw [h1]
      simp
    rw [step, step, huB']
  obtain ⟨sB⟩ := Edge.nonempty_compStruct_of_homMk_comp_eq
    (show (HomotopyCategory.homMk (eYφ.map ((pre f').app C))) ≫
        (HomotopyCategory.homMk (Edge.id _)) =
      (HomotopyCategory.homMk (eYψ.map ((pre f').app C))) by
      rw [HomotopyCategory.homMk_id, Category.comp_id]; exact huB)
  obtain ⟨sX⟩ := Edge.nonempty_compStruct_of_homMk_comp_eq
    (show (HomotopyCategory.homMk (eYφ.map ((pre j).app C))) ≫
        (HomotopyCategory.homMk (Edge.id _)) =
      (HomotopyCategory.homMk (eYψ.map ((pre j).app C))) by
      rw [HomotopyCategory.homMk_id, Category.comp_id]; exact huX)
  have hid : ((Edge.id (((pre j).app C).app _ y₂)).map
        ((pre f).app C)).edge =
      ((Edge.id (((pre f').app C).app _ y₂)).map ((pre i).app C)).edge := by
    calc ((Edge.id (((pre j).app C).app _ y₂)).map
          ((pre f).app C)).edge
        = (Edge.id (((pre f).app C).app _
            (((pre j).app C).app _ y₂))).edge :=
          congrArg Edge.edge (Edge.map_id _ _)
      _ = ((ihom A).obj C).σ 0 (((pre f).app C).app _
            (((pre j).app C).app _ y₂)) := Edge.id_edge _
      _ = ((ihom A).obj C).σ 0 (((pre i).app C).app _
            (((pre f').app C).app _ y₂)) :=
          congrArg _ (hv y₂)
      _ = (Edge.id (((pre i).app C).app _
            (((pre f').app C).app _ y₂))).edge := (Edge.id_edge _).symm
      _ = ((Edge.id (((pre f').app C).app _ y₂)).map
            ((pre i).app C)).edge :=
          congrArg Edge.edge (Edge.map_id _ _).symm
  set t : Edge.CompStruct
      ((eYφ.map ((pre f').app C)).map ((pre i).app C))
      ((Edge.id (((pre f').app C).app _ y₂)).map ((pre i).app C))
      ((eYψ.map ((pre f').app C)).map ((pre i).app C)) :=
    (sX.map ((pre f).app C)).ofEq (hedgeA eYφ) hid (hedgeA eYψ) with htdef
  have ht : t.simplex = ((pre f).app C).app _ sX.simplex := rfl
  obtain ⟨sB', hsB'⟩ := hCorr sB t
  have hagree : yonedaEquiv.symm sB'.simplex ≫ (pre i).app C =
      yonedaEquiv.symm sX.simplex ≫ (pre f).app C := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    rw [hsB', ht]
  obtain ⟨Wmap, hW1, hW2⟩ := exists_pre_lift_of_isPushout sq C _ _ hagree
  have hface2 : ((ihom Y).obj C).δ 2 (yonedaEquiv Wmap) = eYφ.edge :=
    cobaseUncond_δ_yonedaEquiv_of_lift sq C hW1 hW2
      (by rw [sB'.d₂, Edge.map_edge]) (by rw [sX.d₂, Edge.map_edge])
  have hface0 : ((ihom Y).obj C).δ 0 (yonedaEquiv Wmap) =
      (Edge.id y₂).edge :=
    cobaseUncond_δ_yonedaEquiv_of_lift sq C hW1 hW2
      (by rw [sB'.d₀, ← Edge.map_edge, Edge.map_id])
      (by rw [sX.d₀, ← Edge.map_edge, Edge.map_id])
  have hface1 : ((ihom Y).obj C).δ 1 (yonedaEquiv Wmap) = eYψ.edge :=
    cobaseUncond_δ_yonedaEquiv_of_lift sq C hW1 hW2
      (by rw [sB'.d₁, Edge.map_edge]) (by rw [sX.d₁, Edge.map_edge])
  have hCS : Edge.CompStruct eYφ (Edge.id y₂) eYψ :=
    Edge.CompStruct.mk (yonedaEquiv Wmap) hface2 hface0 hface1
  rw [← hφ, ← hψ]
  have hc := HomotopyCategory.homMk_comp_homMk hCS
  rwa [HomotopyCategory.homMk_id, Category.comp_id] at hc

/-- **Cobase change of a categorical equivalence along a
monomorphism, granted (A) and `2`-simplex correction.** Packet
T34's assembly
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful`
with the isofibration input supplied by prism strict extension
(T30) and faithfulness by
`SSet.hoFunctor_pre_faithful_of_isPushout_of_compCorrection`. -/
theorem categoricalEquivalences.of_isPushout_of_prismStrictExtension_of_compCorrection
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (hA : ∀ (C : SSet.{u}) [Quasicategory C],
      HoPrePrismStrictExtension i C)
    (hCorr : ∀ (C : SSet.{u}) [Quasicategory C],
      CompCorrection ((pre i).app C)) :
    categoricalEquivalences f' :=
  categoricalEquivalences.of_isPushout_of_isIsofibration_of_faithful
    sq hf
    (fun C _ ↦ hoFunctor_pre_isIsofibration_of_prismStrictExtension C
      (hA C))
    (fun C _ ↦ hoFunctor_pre_faithful_of_isPushout_of_compCorrection
      sq hf C (hCorr C))

/-- **Stability of categorical equivalences under cobase change
against monomorphisms, granted prism strict extension (A) and
`2`-simplex correction (B2) for every monomorphism.** This is the
target instance
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet)` with exactly the two
remaining prism inputs as hypotheses; see the TODO list at the
end of this module. -/
theorem
    categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction
    (hA : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (C : SSet.{u})
      [Quasicategory C], HoPrePrismStrictExtension i C)
    (hCorr : ∀ {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (C : SSet.{u})
      [Quasicategory C], CompCorrection ((pre i).app C)) :
    categoricalEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u}) := by
  constructor
  intro A B i hi
  have : Mono i := hi
  constructor
  intro Z W f' g' g sq hf
  exact
    categoricalEquivalences.of_isPushout_of_prismStrictExtension_of_compCorrection
      sq hf (hA i) (hCorr i)

end FaithfulnessAssembly

end SSet

end
