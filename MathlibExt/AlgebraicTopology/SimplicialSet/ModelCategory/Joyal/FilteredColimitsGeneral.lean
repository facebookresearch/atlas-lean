/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FilteredColimits
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeMono
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint
public import MathlibExt.CategoryTheory.MorphismProperty.Limits
public import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredFactorization
public import MathlibExt.AlgebraicTopology.SimplicialSet.QuasicategoryFilteredColimits

/-!
# General filtered-colimit closure for Joyal categorical equivalences
(packet T40)

This module is packet T40 of the Joyal model structure programme: the
generalization of `FilteredColimits.lean` (packet T27) from
inner-anodyne steps to *arbitrary* categorical-equivalence steps along
monomorphisms. The target statements are, for
`W := SSet.categoricalEquivalences` and
`K := MorphismProperty.monomorphisms SSet.{u} ⊓ W`,

* (G-trans) transfinite composites of `K`-steps lie in `W` (in fact in
  `K`), i.e. `K.IsStableUnderTransfiniteCompositionOfShape J`, in
  particular sequential `ℕ`-indexed composites; and
* (G-filt) filtered colimits in the arrow category of `W`-maps between
  diagrams with monomorphic transition maps lie in `W`.

Together with cobase-change stability these are the closure properties
needed to keep relative `J`-cell maps inside `K` (weak saturation in
the recognition input for the Joyal model structure). Packet T27
proved (G-trans) when every step is inner anodyne, by the formal
stability of the `llp` class `innerAnodyneExtensions`, and recorded
the arbitrary-step form as open. This packet was asked to choose
between two routes: (a) deduce the closure from cobase-change
stability by a weakly-saturated-class argument, and (b) a direct
finite-presentability probe argument at the level of the defining
`hFun` test. The informal analysis below shows that route (a) as
pure formality is *circular*, identifies the exact non-formal inputs
that route (b) consumes, and this module formalizes route (b) as far
as the landed API (packets T27, T28, T30, T31, T32) supports.

## 1. Informal proof and hypothesis analysis

Recall `SSet.categoricalEquivalences.mem_iff`: `f : X ⟶ Y` is in `W`
iff for every quasicategory `C` the functor
`hFun(f, C) := (SSet.hoFunctor.map ((MonoidalClosed.pre f).app C)).toFunctor :
h Fun(Y, C) ⥤ h Fun(X, C)` is an equivalence of ordinary categories,
where `Fun(W, C) := (ihom W).obj C`. Objects of `h Fun(W, C)` are the
vertices of `Fun(W, C)`, i.e. the maps `W ⟶ C`
(`SSet.ihomVertexEquiv`), and morphisms are represented by edges
(`SSet.Edge.exists_toHoHom_eq`), with equality of morphisms witnessed
by `Edge.CompStruct` `2`-simplices
(`SSet.Edge.nonempty_compStruct_of_toHoHom_comp_eq`).

Let now `F : ℕ ⥤ SSet` be a sequential diagram whose successor steps
`tₙ : F.obj n ⟶ F.obj (n + 1)` lie in `K`, let `c` be a colimit
cocone, and let `φ := c.ι.app 0 : F.obj 0 ⟶ c.pt` be the sequential
composite. Write `sₙ : F.obj 0 ⟶ F.obj n` for the initial segments;
each `sₙ ∈ W` by finite composition (`W` is multiplicative). By T27
(`SSet.isLimit_ihomCone`, here reproved in the `ℕ`-gluing form
`SSet.exists_ihomDesc_nat` because T27 is stated in the same
universe), `Fun(c.pt, C)` is the strict inverse limit of the
`Fun(F.obj n, C)` along the `(pre tₙ).app C`: vertices, edges and
`2`-simplices of `Fun(c.pt, C)` are strictly compatible families.
To show `hFun(φ, C)` is an equivalence one must rectify data that
stagewise equivalences supply only up to isomorphism in the
`h Fun(F.obj n, C)` into strictly compatible families. There are
three rectifications, of increasing depth:

*Essential surjectivity.* Given a vertex `a₀` of `Fun(F.obj 0, C)`,
build vertices `bₙ` of `Fun(F.obj n, C)` with
`(pre tₙ)^* bₙ₊₁ = bₙ` *on the nose* and `b₀ = a₀`; the glued vertex
then maps to `a₀` strictly. Start from any preimage `b'ₙ₊₁` of `a₀`
under the equivalence `hFun(sₙ₊₁, C)`. Its restriction
`(pre tₙ)^* b'ₙ₊₁` is isomorphic to `bₙ` in `h Fun(F.obj n, C)`
(reflect the given isomorphism along the equivalence
`hFun(sₙ, C)`), and the *isofibration property*

  (H-A) for every monomorphism `i` and quasicategory `C`,
  `hFun(i, C)` is an isofibration

lifts that isomorphism to a vertex `bₙ₊₁` with strict restriction
(`Functor.exists_iso_lift`). This is exactly TODO(T26-A) of packet
T26 = TODO(T34-A) of packet T34: by T26/T30 it is prism strict
extension `SSet.HoPrePrismStrictExtension i C`, i.e. Joyal's
extension theorem along a monomorphism by special outer horns. It
is now landed unconditionally, for every monomorphism into a
quasicategory, as `SSet.hoFunctor_pre_isIsofibration_of_mono`
(`DwyerKanFinal.lean`, packet T66) — which covers this application,
since `C` ranges over all quasicategories and the steps `tₙ ∈ K`
are monomorphisms. In a complete formalization (H-A) is therefore
supplied by that theorem, consumed only at the steps `tₙ`.

*Fullness.* Given vertices `b, b'` of `Fun(c.pt, C)` (strict families
`bₙ, b'ₙ`) and an edge `e₀` of `Fun(F.obj 0, C)` between their
restrictions, build edges `eₙ : Edge bₙ b'ₙ` with
`(eₙ₊₁.map ((pre tₙ).app C)).edge = eₙ.edge` on the nose. Choose any
representative `e'ₙ₊₁` of the unique preimage class under the
equivalence `hFun(sₙ₊₁, C)`; its restriction represents the same
morphism as `eₙ` (faithfulness of `hFun(sₙ, C)`), and packet T31's
edge correction through the inner fibration `(pre tₙ).app C`
(`SSet.exists_edge_correction_of_innerFibration`, a lift against
`Λ[2, 1]`) corrects `e'ₙ₊₁` inside its class to strict restriction
`eₙ`. No special horns are needed: of the three parts, fullness
over `ℕ` needs no unlanded input beyond packet T31 and dependent
choice along `ℕ`.

*Faithfulness.* Given edges `E, E'` of `Fun(c.pt, C)` whose
restrictions to stage `0` have the same class, stagewise
faithfulness of the `hFun(sₙ, C)` gives `CompStruct` `2`-simplices
`σₙ` in `Fun(F.obj n, C)` witnessing equality at each stage, but
gluing them needs correction of `σₙ₊₁` through `(pre tₙ).app C`,
relative to its three faces, so that its strict image is `σₙ`. As
analysed in packet T34 (§3 there), the naive `Λ[3, 1]` lift does
not prescribe two faces at once; the correct input is
mapping-space/slice API that is not landed (TODO(T32-kan),
TODO(T34-B2)). In a complete formalization faithfulness over `ℕ`
would therefore be conditional on the corresponding correction
property for `2`-simplices through `(pre i).app C`, as an explicit
hypothesis.

Assembling the three parts would give (G-trans) for `ℕ` conditional
on (H-A) and that correction property, the sequences being chosen
by dependent choice along `ℕ`; the same proof over a general
well-ordered shape `J` needs dependent choice along `J` with the
limit stages glued by the limit cone. The `ℕ` case is the one
consumed by the small object argument at `ℵ₀`
(cf. `SmallObject.lean`). *This sequential `hFun` rectification is
analysed here but not formalized in this module*; §2 records
precisely what is formalized (the formal cobase-change consequence
and the unconditional `π₀` shadows below).

*Why cobase-change stability alone does not formally suffice.*
Route (a) would define, e.g.,
`W' := { f | every pushout of f lies in W }` and argue that `W'` is
weakly saturated. But stability of `W'` under transfinite
composition unfolds to: a pushout of a composite is a composite of
pushouts, each in `W` — and concluding that the composite is in `W`
is (G-trans) itself. Cobase-change stability controls single
pushouts; the limit step of a transfinite composite is a filtered
colimit, not a pushout, and no manipulation with the saturation
operations `.pushouts`, `.coproducts`,
`.transfiniteCompositionsOfShape`, `.retracts` produces it from
cobase-change stability alone. (In practice the implication runs
the other way: (H-A) plus fullness/faithfulness *imply*
cobase-change stability, by packet T30's assembly
`SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`.)
What cobase-change stability *does* give formally — stability of
`K` under cobase change against monomorphisms, i.e. the single
cell-attachment step — is recorded in §2 below (the
`..._of_isStableUnderCobaseChange` theorems).
The finitary content that closes the limit step in `SSet` is that
vertices, edges and `2`-simplices are finite probes, which is
route (b).

*The `π₀` (homotopy-category) shadows, unconditionally.* For a
filtered colimit map `φ` (same universe, no monomorphism hypothesis
needed), essential surjectivity of `mapHomotopyCategory φ` is a
`Δ[0]`-probe argument from T27 factorization and T28 stagewise
essential surjectivity. If moreover every stage is a quasicategory
(hence so is the colimit, by the neutral
`SSet.Quasicategory.ofIsFilteredColimit`, imported from
[QuasicategoryFilteredColimits.lean](../../QuasicategoryFilteredColimits.lean)),
fullness and faithfulness on morphism sets of homotopy
categories are `Δ[1]`- resp. `Δ[2]`-probe arguments: a *single*
edge or `2`-simplex of the colimit factors through one stage, and
finitely many endpoint/face equalities in the colimit are already
equalities at a later stage (`SSet.exists_eq_of_isFilteredColimit`).
No rectification of infinite families occurs, because the probes
themselves are finite. This module formalizes essential
surjectivity (`SSet.categoricalEquivalences.of_isColimit_dwyerKanEssentiallySurjective`)
and the fullness half between quasicategories
(`SSet.surjective_mapHomotopyCategory_map_of_isColimit`); the
faithfulness half is the same `Δ[2]`-probe argument and is left as
TODO(T40-faith) below. Together they would give
`SSet.dwyerKanFullyFaithfulPiZero` of the colimit map, i.e. the
Dwyer–Kan conclusion at the `π₀` level of packet T32. Upgrading
these shadows to `φ ∈ W` for general filtered
shapes would require either the mapping-space Dwyer–Kan
characterization and its converse (TODO(T28-mapping-spaces),
TODO(T28-dwyerKan-converse), open) or rectification of
pseudo-cones over non-well-ordered filtered shapes along the
isofibrations (H-A), which is likewise not formalized.

## 2. What is proved in this module

*Unconditional.*

* The quasicategory-colimit closure is the neutral
  `SSet.Quasicategory.ofIsFilteredColimit` (same-universe filtered
  colimits of quasicategories are quasicategories; horn probes
  factor through stages), imported from
  [QuasicategoryFilteredColimits.lean](../../QuasicategoryFilteredColimits.lean).
* The equalization engine for finite probes is the neutral
  `SSet.exists_simplex_eq_at_stage` (simplices with equal colimit
  images agree at a common later stage), imported from
  [FilteredFactorization.lean](../../FilteredFactorization.lean).
* Filtered-colimit shadows: essential surjectivity in general
  (`...of_isColimit_dwyerKanEssentiallySurjective`), and fullness on
  homotopy-category morphism sets between quasicategories
  (`SSet.surjective_mapHomotopyCategory_map_of_isColimit`), by the
  `Δ[0]`- resp. `Δ[1]`-probe arguments above.
* Collapses and finite cases: a monomorphism that is a trivial Kan
  fibration is an isomorphism
  (`SSet.isIso_of_mono_of_rlp_I`, from the strict section of packet
  T23), the endpoint inclusion `Δ[0] ⟶ SSet.coherentIso` is a
  monomorphism hence lies in `K`
  (`SSet.mono_coherentIso_endpointInclusion`), and finite composites
  of `W`-maps are in `W` (multiplicativity). In particular the
  "trivial-fibration steps" case of (G-trans) along monomorphisms
  collapses to isomorphisms, whose filtered colimits and transfinite
  composites are isomorphisms upstream, and the inner-anodyne case
  is packet T27.

*Conditional, with the hypothesis surface kept explicit (a plain
hypothesis, not a typeclass).*

* The formal cobase-change consequence (the
  `monomorphisms_inf_..._of_isStableUnderCobaseChange` theorem) and
  its membership form
  `SSet.mem_of_isPushout_of_isStableUnderCobaseChange`, from the bare
  hypothesis
  `W.IsStableUnderCobaseChangeAgainst (monomorphisms SSet)` —
  exactly the cobase-change form proved conditionally in packets
  T30/T31 (per-square isofibration + full/faithful hypotheses) and
  unconditionally in the special cases recorded there. §1 explains
  why this hypothesis alone does not formally yield the
  transfinite/filtered limit step: that step is the rectification
  analysed in §1, conditional on (H-A) and the `2`-simplex
  correction property, and is not formalized here.

## 3. What is not proved (precise remaining TODOs)

* TODO(T40-faith): faithfulness half of the `π₀` shadow (the
  `Δ[2]`-probe argument mirroring
  `SSet.surjective_mapHomotopyCategory_map_of_isColimit`), which
  with that lemma and essential surjectivity would give
  `SSet.dwyerKanFullyFaithfulPiZero` and an equivalence on
  homotopy categories for filtered colimits between quasicategories.
* TODO(T40-A) = TODO(T34-A): (H-A) for a general monomorphism and
  quasicategory target (prism triangulation / Joyal extension).
* TODO(T40-B2) = TODO(T34-B2): correction of `2`-simplices rel
  boundary through `(pre i).app C`, blocked on slice/mapping-space
  API.
* TODO(T40-J): the sequential/well-ordered `hFun` rectification of
  §1 (essential surjectivity from (H-A), fullness from packet T31
  by dependent choice, faithfulness from TODO(T40-B2)), giving
  (G-trans) for `ℕ` and then for general well-ordered `J` (dependent
  choice along `J`, limit stages glued by
  `SSet.isLimit_ihomCone`). Once (G-filt) is available for
  well-ordered shapes, general (G-trans) also follows formally
  upstream (`IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape`).
* TODO(T40-filt): (G-filt) at the `hFun` level for general filtered
  shapes (rectification of pseudo-cones over filtered inverse
  systems of functor quasicategories), and the two-diagram
  sequential form with component maps in `K` (the same
  rectification with the pullback correction of
  `SSet.isPullback_pre_app_of_isPushout` in place of single-map
  correction). Only the `π₀` shadows of §2 are proved here.
* Coproducts of `W`-maps (TODO(T20-products)) remain open, so even
  granting (H-A) and (H-B2) the full relative `J`-cell saturation
  additionally needs the coproduct step.

Consequently no unconditional instance
`IsStableUnderFilteredColimits W` or
`IsStableUnderTransfiniteCompositionOfShape K J` for arbitrary
steps is claimed in this module.

## References

* J. Lurie, *Higher Topos Theory*, §2.2.5 (the `hFun`
  characterization), §2.3 (categorical fibrations; the isofibration
  input (H-A) is Proposition 2.3.4.5 in prism form).
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233, §2 (stability of categorical equivalences under
  pushouts along monomorphisms and under filtered colimits).
* *Kerodon*, Corollary 4.5.4.14 (stability under pushout along
  monomorphisms), §4.5 (categorical fibrations and cores).
* P. Goerss and J. Jardine, *Simplicial Homotopy Theory*, VII
  Lemma 3.5 (finite simplicial sets factor through filtered
  colimits, the probe input from packet T27).
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-!
## The homotopy-category shadows of filtered closure
-/

section FilteredShadows

variable {J : Type u} [Category.{u} J] [IsFiltered J]
  {F₁ F₂ : J ⥤ SSet.{u}} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

/-- **Essential surjectivity of a filtered colimit of categorical
equivalences** (same universe, no monomorphism or quasicategory
hypothesis): the colimit map is `SSet.dwyerKanEssentiallySurjective`.
A vertex of the colimit factors through a stage (`Δ[0]`-probe,
packet T27), stagewise essential surjectivity (packet T28) supplies
a preimage vertex and an isomorphism there, and
`mapHomotopyCategory` of the cocone leg transports it to the
colimit. -/
theorem categoricalEquivalences.of_isColimit_dwyerKanEssentiallySurjective
    (hc₂ : IsColimit c₂) (α : F₁ ⟶ F₂)
    (hα : ∀ j, categoricalEquivalences (α.app j)) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = α.app j ≫ c₂.ι.app j) :
    _root_.SSet.dwyerKanEssentiallySurjective φ := by
  change (mapHomotopyCategory φ).EssSurj
  refine ⟨fun Y => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : c₂.pt _⦋0⦌, HomotopyCategory.mk y = Y :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Y⟩
  obtain ⟨j, y', hy'⟩ :=
    exists_simplex_factorization_of_isFilteredColimit hc₂ y
  obtain ⟨x', ⟨β⟩⟩ := (hα j).exists_nonempty_iso_mk_app y'
  refine ⟨HomotopyCategory.mk ((c₁.ι.app j).app _ x'), ⟨?_⟩⟩
  have hβ := (mapHomotopyCategory (c₂.ι.app j)).mapIso β
  rw [mapHomotopyCategory_obj_mk, mapHomotopyCategory_obj_mk] at hβ
  have happ : (c₂.ι.app j).app _ ((α.app j).app _ x') =
      φ.app _ ((c₁.ι.app j).app _ x') := by
    have h1 : ((α.app j ≫ c₂.ι.app j).app (op ⦋0⦌)) x' =
        ((c₁.ι.app j ≫ φ).app (op ⦋0⦌)) x' := by rw [hφ j]
    exact h1
  rw [happ, hy'] at hβ
  exact (eqToIso (mapHomotopyCategory_obj_mk φ _)) ≪≫ hβ ≪≫
    (eqToIso hy)

end FilteredShadows

/-!
## Collapses: trivial fibrations, isomorphisms, the endpoint
inclusion
-/

section Collapses

variable {X Y : SSet.{u}} {p : X ⟶ Y}

/-- A monomorphism that is a trivial Kan fibration is an
isomorphism: the strict section of
`SSet.exists_section_of_rlp_I` (packet T23) is a two-sided inverse
by monomorphism cancellation. Hence trivial-fibration steps along
monomorphisms contribute nothing new to (G-trans): they are
isomorphisms. -/
theorem isIso_of_mono_of_rlp_I [Mono p]
    (hp : modelCategoryQuillen.I.rlp p) : IsIso p := by
  obtain ⟨s, hs⟩ := exists_section_of_rlp_I hp
  have h1 : p ≫ s = 𝟙 X :=
    (cancel_mono p).mp (by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  exact ⟨⟨s, h1, hs⟩⟩

/-- Transfinite compositions of isomorphisms are categorical
equivalences (indeed isomorphisms, upstream), any shape. -/
theorem categoricalEquivalences.of_transfiniteCompositionOfShape_isomorphisms
    (J : Type v) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {f : X ⟶ Y}
    (hf : (MorphismProperty.isomorphisms SSet.{u}).TransfiniteCompositionOfShape
      J f) :
    categoricalEquivalences f := by
  have hf' := MorphismProperty.transfiniteCompositionsOfShape_le
    (W := MorphismProperty.isomorphisms SSet.{u}) J f hf.mem
  have : IsIso f := hf'
  exact categoricalEquivalences.of_isIso f

/-- The endpoint inclusion `Δ[0] ⟶ SSet.coherentIso` is a
monomorphism: it is a strict section of the terminal map
(`SSet.coherentIso.endpointInclusion_comp_toDeltaZero`), hence a
split monomorphism. -/
theorem mono_coherentIso_endpointInclusion :
    Mono coherentIso.endpointInclusion := by
  have hsec : coherentIso.endpointInclusion ≫ coherentIso.toDeltaZero =
      𝟙 _ :=
    coherentIso.endpointInclusion_comp_toDeltaZero
  refine ⟨fun {Z} g h w => ?_⟩
  calc g = g ≫ (coherentIso.endpointInclusion ≫
        coherentIso.toDeltaZero) := by rw [hsec, Category.comp_id]
    _ = h ≫ (coherentIso.endpointInclusion ≫
        coherentIso.toDeltaZero) := by
      rw [← Category.assoc, ← Category.assoc, w]
    _ = h := by rw [hsec, Category.comp_id]

/-- The endpoint inclusion lies in
`monomorphisms ⊓ categoricalEquivalences`: it is a monomorphism
(`SSet.mono_coherentIso_endpointInclusion`) and categorical
(packet T22, `SSet.categoricalEquivalences.coherentIso_endpointInclusion`). -/
theorem coherentIso_endpointInclusion_mem :
    (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u})
      coherentIso.endpointInclusion :=
  (MorphismProperty.inf_iff _ _ _).2
    ⟨mono_coherentIso_endpointInclusion,
      categoricalEquivalences.coherentIso_endpointInclusion⟩

end Collapses

/-!
## The formal cobase-change consequence
-/

section CobaseStep

/-- **The cell-attachment step from cobase-change stability.** If
`W` is stable under cobase change against monomorphisms, then so is
`monomorphisms ⊓ W`: in a pushout square with monomorphic left leg,
the cobase change of a map in `monomorphisms ⊓ W` is a monomorphism
(monomorphisms of simplicial sets are stable under cobase change
upstream) and is in `W` by hypothesis. This is the part of weak
saturation that *does* follow formally from cobase-change
stability; the limit (transfinite/filter) step does not, see §1 of
the module header. -/
theorem monomorphisms_inf_categoricalEquivalences_isStableUnderCobaseChangeAgainst_of_isStableUnderCobaseChange
    (h : categoricalEquivalences.{u}.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u})) :
    MorphismProperty.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences.{u})
      (MorphismProperty.monomorphisms SSet.{u}) := by
  constructor
  intro A B i hi
  constructor
  intro Z W f' g' g sq hf
  obtain ⟨hgMono, hgW⟩ := (MorphismProperty.inf_iff _ _ _).1 hf
  rw [MorphismProperty.inf_iff]
  exact ⟨MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hgMono,
    h.of_isPushout sq hi hgW⟩

/-- Membership form of the cell-attachment step: the cobase change of
a map in `monomorphisms ⊓ W` along a monomorphism is in
`monomorphisms ⊓ W`, granted cobase-change stability of `W`. -/
theorem mem_of_isPushout_of_isStableUnderCobaseChange
    (h : categoricalEquivalences.{u}.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u}))
    {A B X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) (hi : Mono i)
    (hf : (MorphismProperty.monomorphisms SSet.{u} ⊓
      categoricalEquivalences.{u}) f) :
    (MorphismProperty.monomorphisms SSet.{u} ⊓
      categoricalEquivalences.{u}) f' :=
  (monomorphisms_inf_categoricalEquivalences_isStableUnderCobaseChangeAgainst_of_isStableUnderCobaseChange
    h).of_isPushout sq hi hf

end CobaseStep

/-!
## `π₀`-fullness for filtered colimits between quasicategories
-/

section FilteredPiZero

variable {J : Type u} [Category.{u} J] [IsFiltered J]
  {F₁ F₂ : J ⥤ SSet.{u}} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

omit [IsFiltered J] in
/-- Cocone compatibility at simplices: pushing a simplex along an
arrow and then mapping to the colimit agrees with mapping it
directly. -/
private lemma fgc_ι_app_map_app {F : J ⥤ SSet.{u}} {c : Cocone F}
    {i k : J} (w : i ⟶ k) {n : ℕ} (σ : F.obj i _⦋n⦌) :
    (c.ι.app k).app (op ⦋n⦌) ((F.map w).app (op ⦋n⦌) σ) =
      (c.ι.app i).app (op ⦋n⦌) σ := by
  have hh := ConcreteCategory.congr_hom (congr_app (c.w w) (op ⦋n⦌)) σ
  exact hh

omit [IsFiltered J] in
/-- Naturality of `α` at simplices, in push-forward form. -/
private lemma fgc_α_app_map_app (α : F₁ ⟶ F₂) {i k : J} (w : i ⟶ k)
    {n : ℕ} (σ : F₁.obj i _⦋n⦌) :
    (F₂.map w).app (op ⦋n⦌) ((α.app i).app (op ⦋n⦌) σ) =
      (α.app k).app (op ⦋n⦌) ((F₁.map w).app (op ⦋n⦌) σ) := by
  have hh := ConcreteCategory.congr_hom
    (congr_app (α.naturality w) (op ⦋n⦌)) σ
  exact hh.symm

omit [IsFiltered J] in
/-- The colimit-compatibility of `φ` at simplices. -/
private lemma fgc_ι₂_app_α_app (α : F₁ ⟶ F₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = α.app j ≫ c₂.ι.app j) (j : J)
    {n : ℕ} (σ : F₁.obj j _⦋n⦌) :
    (c₂.ι.app j).app (op ⦋n⦌) ((α.app j).app (op ⦋n⦌) σ) =
      φ.app (op ⦋n⦌) ((c₁.ι.app j).app (op ⦋n⦌) σ) := by
  have hh := ConcreteCategory.congr_hom (congr_app (hφ j) (op ⦋n⦌)) σ
  exact hh.symm

/-- Equalizing a pair of simplices at one stage along a *single*
arrow: first equalize along two arrows
(`SSet.exists_simplex_eq_at_stage`), then coequalize the arrows in
the filtered indexing category. Pushing all data along the resulting
common arrow preserves previously achieved strict equalities. -/
private lemma fgc_exists_common_arrow_simplex_eq {F : J ⥤ SSet.{u}}
    {c : Cocone F} (hc : IsColimit c) {n : ℕ} {k : J}
    {a b : F.obj k _⦋n⦌}
    (h : (c.ι.app k).app (op ⦋n⦌) a = (c.ι.app k).app (op ⦋n⦌) b) :
    ∃ (m : J) (w : k ⟶ m),
      (F.map w).app (op ⦋n⦌) a = (F.map w).app (op ⦋n⦌) b := by
  obtain ⟨l, u, v, huv⟩ := exists_simplex_eq_at_stage hc h
  refine ⟨IsFiltered.coeq u v, u ≫ IsFiltered.coeqHom u v, ?_⟩
  have hcond : u ≫ IsFiltered.coeqHom u v =
      v ≫ IsFiltered.coeqHom u v :=
    IsFiltered.coeq_condition u v
  have e1 : (F.map (u ≫ IsFiltered.coeqHom u v)).app (op ⦋n⦌) a =
      (F.map (IsFiltered.coeqHom u v)).app (op ⦋n⦌)
        ((F.map u).app (op ⦋n⦌) a) := by
    rw [F.map_comp]; rfl
  have e2 : (F.map (u ≫ IsFiltered.coeqHom u v)).app (op ⦋n⦌) b =
      (F.map (IsFiltered.coeqHom u v)).app (op ⦋n⦌)
        ((F.map v).app (op ⦋n⦌) b) := by
    rw [hcond, F.map_comp]; rfl
  rw [e1, e2, huv]



/-- **Edge factorization at a stage.** Every edge of the target
colimit between `φ`-image vertices is, at some stage `m`, the image
under the cocone leg of an edge of `F₂.obj m` between `α`-image
vertices lying strictly over the given vertices. The proof factors
the `Δ[1]`- and `Δ[0]`-probes, passes to a common stage, and
equalizes the two endpoint equalities successively along common
arrows (`fgc_exists_common_arrow_simplex_eq`). -/
private lemma fgc_exists_edge_stage (hc₁ : IsColimit c₁)
    (hc₂ : IsColimit c₂) (α : F₁ ⟶ F₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = α.app j ≫ c₂.ι.app j)
    {x y : c₁.pt _⦋0⦌} (e' : Edge (φ.app _ x) (φ.app _ y)) :
    ∃ (m : J) (xm ym : F₁.obj m _⦋0⦌)
      (em : Edge ((α.app m).app _ xm) ((α.app m).app _ ym)),
      (c₁.ι.app m).app _ xm = x ∧ (c₁.ι.app m).app _ ym = y ∧
        (c₂.ι.app m).app _ em.edge = e'.edge := by
  obtain ⟨j1, σ1, hσ1⟩ :=
    exists_simplex_factorization_of_isFilteredColimit hc₂ e'.edge
  obtain ⟨j2, x2, hx2⟩ :=
    exists_simplex_factorization_of_isFilteredColimit hc₁ x
  obtain ⟨j3, y3, hy3⟩ :=
    exists_simplex_factorization_of_isFilteredColimit hc₁ y
  -- A common stage for the three probes.
  set k12 := IsFiltered.max j1 j2 with hk12
  set k0 := IsFiltered.max k12 j3 with hk0
  set a1 : j1 ⟶ k0 :=
    IsFiltered.leftToMax j1 j2 ≫ IsFiltered.leftToMax k12 j3 with ha1
  set a2 : j2 ⟶ k0 :=
    IsFiltered.rightToMax j1 j2 ≫ IsFiltered.leftToMax k12 j3 with ha2
  set a3 : j3 ⟶ k0 := IsFiltered.rightToMax k12 j3 with ha3
  set σ : F₂.obj k0 _⦋1⦌ := (F₂.map a1).app _ σ1 with hσdef
  set xk : F₁.obj k0 _⦋0⦌ := (F₁.map a2).app _ x2 with hxkdef
  set yk : F₁.obj k0 _⦋0⦌ := (F₁.map a3).app _ y3 with hykdef
  have hσ : (c₂.ι.app k0).app _ σ = e'.edge := by
    rw [hσdef, fgc_ι_app_map_app]; exact hσ1
  have hxk : (c₁.ι.app k0).app _ xk = x := by
    rw [hxkdef, fgc_ι_app_map_app]; exact hx2
  have hyk : (c₁.ι.app k0).app _ yk = y := by
    rw [hykdef, fgc_ι_app_map_app]; exact hy3
  -- Equalize the source endpoint.
  have hsrcImg : (c₂.ι.app k0).app _ ((F₂.obj k0).δ 1 σ) =
      (c₂.ι.app k0).app _ ((α.app k0).app _ xk) := by
    rw [δ_naturality_apply, hσ]
    change (c₂.pt).δ 1 e'.edge = _
    rw [e'.src_eq, fgc_ι₂_app_α_app α φ hφ k0 xk, hxk]
  obtain ⟨l, w1, hw1⟩ :=
    fgc_exists_common_arrow_simplex_eq hc₂ hsrcImg
  set σ₁ : F₂.obj l _⦋1⦌ := (F₂.map w1).app _ σ with hσ₁def
  set x₁ : F₁.obj l _⦋0⦌ := (F₁.map w1).app _ xk with hx₁def
  set y₁ : F₁.obj l _⦋0⦌ := (F₁.map w1).app _ yk with hy₁def
  have hσ₁ : (c₂.ι.app l).app _ σ₁ = e'.edge := by
    rw [hσ₁def, fgc_ι_app_map_app]; exact hσ
  have hx₁ : (c₁.ι.app l).app _ x₁ = x := by
    rw [hx₁def, fgc_ι_app_map_app]; exact hxk
  have hy₁ : (c₁.ι.app l).app _ y₁ = y := by
    rw [hy₁def, fgc_ι_app_map_app]; exact hyk
  have hsrc : (F₂.obj l).δ 1 σ₁ = (α.app l).app _ x₁ := by
    rw [hσ₁def, ← δ_naturality_apply, hw1, hx₁def,
      fgc_α_app_map_app]
  -- Equalize the target endpoint; the source equality is preserved
  -- because everything is pushed along the single arrow `w2`.
  have htgtImg : (c₂.ι.app l).app _ ((F₂.obj l).δ 0 σ₁) =
      (c₂.ι.app l).app _ ((α.app l).app _ y₁) := by
    rw [δ_naturality_apply, hσ₁]
    change (c₂.pt).δ 0 e'.edge = _
    rw [e'.tgt_eq, fgc_ι₂_app_α_app α φ hφ l y₁, hy₁]
  obtain ⟨m, w2, hw2⟩ :=
    fgc_exists_common_arrow_simplex_eq hc₂ htgtImg
  set σ₂ : F₂.obj m _⦋1⦌ := (F₂.map w2).app _ σ₁ with hσ₂def
  set xm : F₁.obj m _⦋0⦌ := (F₁.map w2).app _ x₁ with hxmdef
  set ym : F₁.obj m _⦋0⦌ := (F₁.map w2).app _ y₁ with hymdef
  have hσ₂ : (c₂.ι.app m).app _ σ₂ = e'.edge := by
    rw [hσ₂def, fgc_ι_app_map_app]; exact hσ₁
  have hxm : (c₁.ι.app m).app _ xm = x := by
    rw [hxmdef, fgc_ι_app_map_app]; exact hx₁
  have hym : (c₁.ι.app m).app _ ym = y := by
    rw [hymdef, fgc_ι_app_map_app]; exact hy₁
  have hsrc₂ : (F₂.obj m).δ 1 σ₂ = (α.app m).app _ xm := by
    rw [hσ₂def, ← δ_naturality_apply, hsrc, hxmdef,
      fgc_α_app_map_app]
  have htgt₂ : (F₂.obj m).δ 0 σ₂ = (α.app m).app _ ym := by
    rw [hσ₂def, ← δ_naturality_apply, hw2, hymdef,
      fgc_α_app_map_app]
  exact ⟨m, xm, ym, Edge.mk σ₂ hsrc₂ htgt₂, hxm, hym, hσ₂⟩

/-- Surjectivity half of `π₀`-full-faithfulness for a filtered
colimit: factor the representing edge at a stage
(`fgc_exists_edge_stage`), lift it there by stagewise
`π₀`-fullness (packet T32), push the lift to the colimit, and
compare homotopy classes by transporting edges along the endpoint
equalities (`Edge.ofEq`, `Edge.CompStruct.ofEq`). -/
theorem surjective_mapHomotopyCategory_map_of_isColimit
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (hF₁ : ∀ j, Quasicategory (F₁.obj j))
    (hF₂ : ∀ j, Quasicategory (F₂.obj j))
    (α : F₁ ⟶ F₂) (hα : ∀ j, categoricalEquivalences (α.app j))
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = α.app j ≫ c₂.ι.app j)
    {x y : c₁.pt _⦋0⦌} :
    Function.Surjective ((mapHomotopyCategory φ).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) →
        (HomotopyCategory.mk (φ.app _ x) ⟶
          HomotopyCategory.mk (φ.app _ y))) := by
  intro ψ
  have : Quasicategory c₂.pt :=
    Quasicategory.ofIsFilteredColimit hc₂ hF₂
  set ψ' : (HomotopyCategory.mk (φ.app _ x) : hoFunctor.obj c₂.pt) ⟶
      (HomotopyCategory.mk (φ.app _ y) : hoFunctor.obj c₂.pt) := ψ with hψ'
  obtain ⟨e', he'⟩ := Edge.exists_toHoHom_eq ψ'
  obtain ⟨m, xm, ym, em, hxm, hym, hem⟩ :=
    fgc_exists_edge_stage hc₁ hc₂ α φ hφ e'
  have : Quasicategory (F₁.obj m) := hF₁ m
  obtain ⟨e₁, he₁⟩ :=
    ((hα m).dwyerKanFullyFaithfulPiZero).exists_edge_map_toHoHom_eq em
  set e := (e₁.map (c₁.ι.app m)).ofEq hxm hym with hedef
  have hmapφ : (mapHomotopyCategory φ).map e.toHoHom =
      (e.map φ).toHoHom := (Edge.toHoHom_map e φ).symm
  set E3 := (e₁.map (α.app m)).map (c₂.ι.app m) with hE3
  set E2 := em.map (c₂.ι.app m) with hE2
  have he₁' : HomotopyCategory.homMk (e₁.map (α.app m)) =
      HomotopyCategory.homMk em := he₁
  have hE3E2 : HomotopyCategory.homMk E3 =
      HomotopyCategory.homMk E2 := by
    have h1 : HomotopyCategory.homMk E3 =
        (mapHomotopyCategory (c₂.ι.app m)).map
          (HomotopyCategory.homMk (e₁.map (α.app m))) :=
      (mapHomotopyCategory_map_homMk _ _).symm
    have h2 : HomotopyCategory.homMk E2 =
        (mapHomotopyCategory (c₂.ι.app m)).map
          (HomotopyCategory.homMk em) :=
      (mapHomotopyCategory_map_homMk _ _).symm
    rw [h1, h2, he₁']
  have happX : φ.app _ x =
      (c₂.ι.app m).app _ ((α.app m).app _ xm) := by
    have e1 := fgc_ι₂_app_α_app α φ hφ m xm
    rw [hxm] at e1
    exact e1.symm
  have happY : φ.app _ y =
      (c₂.ι.app m).app _ ((α.app m).app _ ym) := by
    have e1 := fgc_ι₂_app_α_app α φ hφ m ym
    rw [hym] at e1
    exact e1.symm
  have hedge1 : (e.map φ).edge = E3.edge := by
    have heEdge : e.edge = (c₁.ι.app m).app _ e₁.edge := rfl
    rw [hE3]
    simp only [Edge.map_edge, heEdge]
    exact (fgc_ι₂_app_α_app α φ hφ m e₁.edge).symm
  have hedge2 : E2.edge = e'.edge := by
    rw [hE2, Edge.map_edge]; exact hem
  set E3' := E3.ofEq happX.symm happY.symm with hE3'
  set E2' := E2.ofEq happX.symm happY.symm with hE2'
  have hE1 : e.map φ = E3' := Edge.ext hedge1
  have hE2eq : E2' = e' := Edge.ext hedge2
  have hmid : HomotopyCategory.homMk E3' =
      HomotopyCategory.homMk E2' := by
    have hE3E2' : E3.toHoHom = E2.toHoHom := hE3E2
    have hcomp : E3.toHoHom ≫
        (Edge.id ((c₂.ι.app m).app _ ((α.app m).app _ ym))).toHoHom =
        E2.toHoHom := by
      rw [Edge.toHoHom_id, Category.comp_id]
      exact hE3E2'
    obtain ⟨S⟩ := Edge.nonempty_compStruct_of_toHoHom_comp_eq
      (X := c₂.pt) hcomp
    have S' := S.ofEq (f₀₁ := E3') (f₁₂ := Edge.id (φ.app _ y))
      (f₀₂ := E2') rfl ((congrArg (c₂.pt.σ 0) happY).symm) rfl
    have hS : HomotopyCategory.homMk E3' ≫
        HomotopyCategory.homMk (Edge.id (φ.app _ y)) =
        HomotopyCategory.homMk E2' :=
      Edge.toHoHom_comp S'
    have hid : HomotopyCategory.homMk (Edge.id (φ.app _ y)) = 𝟙 _ :=
      Edge.toHoHom_id _
    rw [hid, Category.comp_id] at hS
    exact hS
  have hgoal : (e.map φ).toHoHom = e'.toHoHom := by
    change HomotopyCategory.homMk (e.map φ) =
      HomotopyCategory.homMk e'
    rw [hE1, hmid, hE2eq]
  exact ⟨e.toHoHom, hmapφ.trans (hgoal.trans he')⟩

end FilteredPiZero

end SSet

end
