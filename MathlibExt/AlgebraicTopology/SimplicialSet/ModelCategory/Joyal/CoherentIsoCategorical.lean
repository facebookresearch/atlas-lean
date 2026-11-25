/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-! # The endpoint inclusion `Δ[0] ⟶ SSet.coherentIso`

The goal of this packet (T14 of the Joyal model structure
programme) is the second JY3 gate example: the endpoint inclusion
`SSet.coherentIso.endpointInclusion : Δ[0] ⟶ SSet.coherentIso` selecting the
source vertex `SSet.coherentIso.x₀` is a Joyal categorical equivalence, i.e.

```text
SSet.categoricalEquivalences SSet.coherentIso.endpointInclusion.
```

Unpacked through `SSet.categoricalEquivalences.mem_iff`, this says that for
every quasicategory `C` the evaluation functor
`(SSet.hoFunctor.map ((MonoidalClosed.pre endpointInclusion).app C)).toFunctor`
from `h Fun(coherentIso, C)` to `h Fun(Δ[0], C)` is an equivalence of
ordinary categories. It does *not* follow from the inner-anodyne theorem of
`InnerAnodyneCategorical.lean`: the endpoint inclusion is not bijective on
vertices, hence not inner anodyne.

## What is proved here

* The endpoint inclusion itself, as `yonedaEquiv.symm coherentIso.x₀`
  (equivalently `SSet.const coherentIso.x₀`; this is the same simplicial map
  whose image under `SSet.simplicialSpaceDiscrete` is the Rezk completeness
  map), together with its strict retraction
  `SSet.coherentIso.toDeltaZero`, the unique map to the terminal `Δ[0]`.
* Essential surjectivity of the evaluation functor for *every* simplicial set
  `C`, with no quasicategory hypothesis
  (`SSet.coherentIso.hoPre_endpointInclusion_essSurj`): precomposition with
  `toDeltaZero` is a strict section after `SSet.hoFunctor`, which at the
  vertex level is the constant-map construction; on objects the evaluation
  functor sends the vertex classified by `g : coherentIso ⟶ C` to the vertex
  classified by the constant map at `g.app _ coherentIso.x₀`
  (`SSet.coherentIso.hoPre_endpointInclusion_obj_mk_ihomVertexEquiv`, using the
  vertex dictionary `SSet.ihomVertexEquiv`).
* The vertex-level edge reading: every `g : coherentIso ⟶ C` sends
  `coherentIso.hom` to an equivalence edge of `C`
  (`SSet.coherentIso.isEquivalence_hom_map`).
* The vertex-level calculations use the shared
  evaluation-at-a-vertex API of
  `MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices`: the
  vertex dictionary `SSet.ihomVertexEquiv`, currying against the
  canonical evaluations `(MonoidalClosed.unitIsoSelf C).hom` and
  `(SSet.evalDeltaZeroIso C).hom` (`SSet.curry'_unitIsoSelf_hom`,
  `SSet.curry'_evalDeltaZeroIso_hom`), the vertex formula for
  evaluation at `Δ[0]`
  (`SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv`), and the
  Yoneda/unit dictionary `SSet.yonedaEquiv_eq_unitHomEquiv`. That
  low-level module is the single canonical home of this API (audit
  F4), shared with `NotCategorical.lean` and
  `MathlibExt.AlgebraicTopology.SimplicialSet.NerveDescent`; the evaluation isomorphisms themselves
  are upstream `MonoidalClosed.unitIsoSelf` and
  `SSet.evalDeltaZeroIso`/`SSet.Δ0IsoUnit` in
  `MathlibExt.AlgebraicTopology.SimplicialSet.Slice`.
* The reduction of fullness and faithfulness of the evaluation functor to
  two explicitly stated extension properties in their weak
  homotopy-category-level forms:
  `SSet.coherentIso.edgeExtensionProperty` merely asserts that for
  each endpoint edge `ε'` there is an edge `ε` whose endpoint
  evaluation has the same `HomotopyCategory.homMk` as `ε'`, while
  `SSet.coherentIso.compExtensionProperty` merely transfers existence
  of a `CompStruct` from evaluated edges to the original edges; it does
  not lift a supplied `2`-simplex or prescribe strict prism face data.
  Concretely:
  `hoPre_endpointInclusion_full_of_edgeExtensionProperty`,
  `hoPre_endpointInclusion_faithful_of_compExtensionProperty`, and the
  conditional main theorem
  `SSet.categoricalEquivalences.coherentIso_endpointInclusion_of_extensions`.
  Since essential surjectivity is unconditional, membership is also
  characterised as fullness plus faithfulness for all quasicategories
  (`SSet.categoricalEquivalences_coherentIso_endpointInclusion_iff`).
  The full/faithful reduction uses only that morphisms in the homotopy
  categories of the two functor objects are represented by single edges and
  that composition relations are witnessed by `2`-simplices
  (`SSet.Edge.exists_homMk_eq` and
  `SSet.Edge.nonempty_compStruct_of_homMk_comp_eq`), which apply because
  an internal hom into a quasicategory is a quasicategory.

## What is not proved in this file

The unconditional statement
`SSet.categoricalEquivalences SSet.coherentIso.endpointInclusion` is
not proved in this file; it is proved in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint`
as `SSet.categoricalEquivalences.coherentIso_endpointInclusion`
(packet T22), which discharges the two prism-extension properties
above (`SSet.coherentIso.edgeExtensionProperty_of_quasicategory` and
`SSet.coherentIso.compExtensionProperty_of_quasicategory`) and feeds
them into the conditional theorem of this file. No statement in this
file alone should be read as claiming the gate example
unconditionally.

The coskeletal partial route is in
`MathlibExt/AlgebraicTopology/Quasicategory/CoherentIsoExtension.lean`:
an edge with inverse data always extends coherently into the
`2`-coskeleton of its ambient simplicial set
(`SSet.Edge.InvStruct.exists_coherentIso_extension_cosk`), extension to
`X` itself is equivalent to lifting that coskeletal extension along the
unit `X ⟶ (Truncated.cosk 2).obj ((truncation 2).obj X)`
(`SSet.Edge.coherentIso_extension_iff_exists_coskMap_lift`), and for
`2`-coskeletal (in particular strict Segal, hence nerve) quasicategory
targets the full extension characterization holds
(`SSet.Edge.isEquivalence_iff_coherentIso_extension_of_isCoskeletal`,
`SSet.Edge.isEquivalence_iff_coherentIso_extension_of_isStrictSegal`).

The analogous ordinary-category evaluation equivalence out of
`CategoryTheory.WalkingIso` is generic infrastructure and lives in
`MathlibExt.CategoryTheory.WalkingIsoEvaluation`
(`CategoryTheory.WalkingIso.equivalenceEvaluationZero`); it is not
proved or used in this file.

## References

* J. Lurie, *Higher Topos Theory*, §2.2.5 (weak categorical equivalences)
  and Proposition 1.2.4.3 (special outer horns).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

namespace coherentIso

/-- The endpoint inclusion `Δ[0] ⟶ SSet.coherentIso` selecting the source
vertex `coherentIso.x₀`. It is defined as the Yoneda map
`yonedaEquiv.symm coherentIso.x₀`, in the same form used for the underlying
simplicial map of the Rezk completeness map. -/
noncomputable def endpointInclusion : (Δ[0] : SSet.{u}) ⟶ coherentIso.{u} :=
  yonedaEquiv.symm x₀

/-- The endpoint inclusion is the constant map at the source vertex. -/
lemma endpointInclusion_eq_const :
    endpointInclusion.{u} = const x₀ :=
  yonedaEquiv_symm_zero x₀

/-- The unique map from `SSet.coherentIso` to the terminal simplicial set
`Δ[0]`. -/
noncomputable def toDeltaZero : coherentIso.{u} ⟶ (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.from _

/-- The endpoint inclusion is a strict section of the terminal map: the
composite `Δ[0] ⟶ coherentIso ⟶ Δ[0]` is the identity, by terminality of
`Δ[0]`. -/
lemma endpointInclusion_comp_toDeltaZero :
    endpointInclusion.{u} ≫ toDeltaZero = 𝟙 (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The forward edge of `SSet.coherentIso` maps to an equivalence edge under
every map `g : SSet.coherentIso ⟶ C`. Thus every vertex of the simplicial
functor object `Fun(coherentIso, C)` determines, through
`SSet.ihomVertexEquiv`, an equivalence edge of `C` whose source is the
evaluation of the vertex at `x₀`. -/
theorem isEquivalence_hom_map {C : SSet.{u}} (g : coherentIso.{u} ⟶ C) :
    (hom.map g).IsEquivalence :=
  Edge.isEquivalence_coherentIso_hom.map g

/-- The **edge extension property** for the endpoint evaluation into `C`,
in its deliberately weak, homotopy-category-level form: for every
edge `ε'` of the target functor object `Fun(Δ[0], C)` between
evaluated vertices, there merely *exists* an edge `ε` of
`Fun(coherentIso, C)` between the original vertices whose evaluated
edge has the same `HomotopyCategory.homMk` as `ε'`. This does **not** ask for
a strict prism extension restricting along `{x₀} ⊗ Δ[1]` to the
given edge: through the prism dictionary
(`MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism`) such a
prism would be additional strict data that the definition does not
require. The downstream endpoint proof exploits exactly this
weaker form. -/
def edgeExtensionProperty (C : SSet.{u}) : Prop :=
  ∀ {a a' : ((ihom coherentIso).obj C) _⦋0⦌}
    (ε' : Edge (((pre endpointInclusion).app C).app (op ⦋0⦌) a)
      (((pre endpointInclusion).app C).app (op ⦋0⦌) a')),
    ∃ ε : Edge a a',
      (HomotopyCategory.homMk (ε.map ((pre endpointInclusion).app C))) = (HomotopyCategory.homMk ε')

/-- The **composition extension property** for the endpoint evaluation
into `C`, again in existence-only form: if there exists a
`CompStruct` between the evaluated edges in `Fun(Δ[0], C)`, then
there exists a `CompStruct` between the original edges. This only
transfers the mere existence of a composition witness; it does not
lift a supplied `2`-simplex, choose a prism
`SSet.coherentIso ⊗ Δ[2] ⟶ C`, or preserve any face data beyond the
endpoints fixed by the types. -/
def compExtensionProperty (C : SSet.{u}) : Prop :=
  ∀ {a b c : ((ihom coherentIso).obj C) _⦋0⦌}
    {ε₁ : Edge a b} {ε₂ : Edge b c} {ε₁₂ : Edge a c},
    Nonempty (Edge.CompStruct (ε₁.map ((pre endpointInclusion).app C))
      (ε₂.map ((pre endpointInclusion).app C))
      (ε₁₂.map ((pre endpointInclusion).app C))) →
    Nonempty (Edge.CompStruct ε₁ ε₂ ε₁₂)

end coherentIso

namespace coherentIso

/-- Evaluation at the endpoint on objects: the homotopy-category functor of
precomposition with the endpoint inclusion sends the object classified by
`g : SSet.coherentIso ⟶ C` to the object classified by the constant map at
the vertex `g.app _ coherentIso.x₀` of `C`. -/
theorem hoPre_endpointInclusion_obj_mk_ihomVertexEquiv (C : SSet.{u})
    (g : coherentIso.{u} ⟶ C) :
    (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv coherentIso C g)) =
      HomotopyCategory.mk
        (ihomVertexEquiv (Δ[0]) C (const (g.app (op ⦋0⦌) x₀))) := by
  have hF : (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor =
      mapHomotopyCategory ((pre endpointInclusion).app C) :=
    rfl
  rw [hF, mapHomotopyCategory_obj_mk, ihomVertexEquiv_pre_app,
    endpointInclusion_eq_const, const_comp]

/-- **Essential surjectivity of endpoint evaluation, unconditionally.** For
every simplicial set `C` (no quasicategory hypothesis), the functor
`h Fun(coherentIso, C) ⟶ h Fun(Δ[0], C)` induced by precomposition with the
endpoint inclusion is essentially surjective. Indeed, precomposition with
the terminal map `coherentIso.toDeltaZero` is a strict section after
`SSet.hoFunctor`, by `endpointInclusion_comp_toDeltaZero`; at the vertex
level this is surjectivity via constant maps. -/
theorem hoPre_endpointInclusion_essSurj (C : SSet.{u}) :
    (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor.EssSurj := by
  refine ⟨fun b => ?_⟩
  refine ⟨(hoFunctor.map ((pre toDeltaZero).app C)).toFunctor.obj b, ⟨?_⟩⟩
  have hcomp :
      (hoFunctor.map ((pre toDeltaZero).app C)).toFunctor ⋙
          (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor =
        𝟭 (hoFunctor.obj ((ihom (Δ[0] : SSet.{u})).obj C)) := by
    rw [← hoFunctor_pre_comp, endpointInclusion_comp_toDeltaZero,
      hoFunctor_pre_id]
  exact eqToIso (congrFun (congrArg Functor.obj hcomp) b)

variable (C : SSet.{u}) [Quasicategory C]

/-- Fullness of endpoint evaluation follows from the edge extension
property. Every morphism in `h Fun(Δ[0], C)` between evaluated vertices is
represented by a single edge (`SSet.Edge.exists_homMk_eq`, applicable
because `Fun(Δ[0], C)` is a quasicategory), and the extension property
lifts that edge through evaluation. -/
theorem hoPre_endpointInclusion_full_of_edgeExtensionProperty
    (h : edgeExtensionProperty C) :
    (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor.Full := by
  have hF : (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor =
      mapHomotopyCategory ((pre endpointInclusion).app C) :=
    rfl
  rw [hF]
  refine ⟨?_⟩
  intro P Q f
  obtain ⟨a, rfl⟩ : ∃ a, HomotopyCategory.mk a = P :=
    ⟨_, HomotopyCategory.objEquiv.left_inv P⟩
  obtain ⟨a', rfl⟩ : ∃ a, HomotopyCategory.mk a = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  obtain ⟨ε', hε'⟩ := Edge.exists_homMk_eq
    (x₀ := ((pre endpointInclusion).app C).app (op ⦋0⦌) a)
    (x₁ := ((pre endpointInclusion).app C).app (op ⦋0⦌) a') f
  obtain ⟨ε, hε⟩ := h ε'
  exact ⟨(HomotopyCategory.homMk ε), by rw [← hε', ← hε, ← mapHomotopyCategory_map_homMk]⟩

/-- Faithfulness of endpoint evaluation follows from the composition
extension property. Morphisms in `h Fun(coherentIso, C)` are represented by
single edges; equality of their evaluations gives, after composing with an
identity edge, a `CompStruct` between the evaluated edges
(`SSet.Edge.nonempty_compStruct_of_homMk_comp_eq`), and the extension
property lifts it to a `CompStruct` witnessing equality before evaluation.
-/
theorem hoPre_endpointInclusion_faithful_of_compExtensionProperty
    (h : compExtensionProperty C) :
    (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor.Faithful := by
  have hF : (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor =
      mapHomotopyCategory ((pre endpointInclusion).app C) :=
    rfl
  rw [hF]
  refine ⟨?_⟩
  intro P Q f g hfg
  obtain ⟨a, rfl⟩ : ∃ a, HomotopyCategory.mk a = P :=
    ⟨_, HomotopyCategory.objEquiv.left_inv P⟩
  obtain ⟨a', rfl⟩ : ∃ a, HomotopyCategory.mk a = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  obtain ⟨ε₁, rfl⟩ := Edge.exists_homMk_eq (x₀ := a) (x₁ := a') f
  obtain ⟨ε₂, rfl⟩ := Edge.exists_homMk_eq (x₀ := a) (x₁ := a') g
  rw [mapHomotopyCategory_map_homMk, mapHomotopyCategory_map_homMk] at hfg
  have hcomp :
      (HomotopyCategory.homMk (ε₁.map ((pre endpointInclusion).app C))) ≫
          (HomotopyCategory.homMk ((Edge.id a').map ((pre endpointInclusion).app C))) =
        (HomotopyCategory.homMk (ε₂.map ((pre endpointInclusion).app C))) := by
    rw [Edge.map_id, HomotopyCategory.homMk_id, Category.comp_id]
    exact hfg
  obtain ⟨hc⟩ := h (Edge.nonempty_compStruct_of_homMk_comp_eq hcomp)
  have hcc := HomotopyCategory.homMk_comp_homMk hc
  rwa [HomotopyCategory.homMk_id, Category.comp_id] at hcc

/-- Endpoint evaluation into a quasicategory is an equivalence of ordinary
categories as soon as the two prism-extension properties hold: essential
surjectivity is unconditional
(`hoPre_endpointInclusion_essSurj`), fullness is the edge extension
property, and faithfulness is the composition extension property. -/
theorem hoPre_endpointInclusion_isEquivalence_of_extensions
    (hE : edgeExtensionProperty C) (hC : compExtensionProperty C) :
    (hoFunctor.map ((pre endpointInclusion).app C)).toFunctor.IsEquivalence :=
  { faithful :=
      hoPre_endpointInclusion_faithful_of_compExtensionProperty C hC
    full := hoPre_endpointInclusion_full_of_edgeExtensionProperty C hE
    essSurj := hoPre_endpointInclusion_essSurj C }

end coherentIso

/-- Since endpoint evaluation is unconditionally essentially surjective, the
endpoint inclusion is a categorical equivalence if and only if endpoint
evaluation into every quasicategory is full and faithful. -/
theorem categoricalEquivalences_coherentIso_endpointInclusion_iff :
    categoricalEquivalences.{u} coherentIso.endpointInclusion ↔
      ∀ (C : SSet.{u}), Quasicategory C →
        (hoFunctor.map
            ((pre coherentIso.endpointInclusion).app C)).toFunctor.Full ∧
          (hoFunctor.map
            ((pre coherentIso.endpointInclusion).app C)).toFunctor.Faithful := by
  constructor
  · intro h C hC
    have hI := (categoricalEquivalences.mem_iff
      coherentIso.endpointInclusion).1 h C hC
    exact ⟨hI.full, hI.faithful⟩
  · intro h
    rw [categoricalEquivalences.mem_iff]
    intro C hC
    obtain ⟨hFull, hFaith⟩ := h C hC
    exact { faithful := hFaith
            full := hFull
            essSurj := coherentIso.hoPre_endpointInclusion_essSurj C }

/-- **Conditional main theorem.** The endpoint inclusion
`Δ[0] ⟶ SSet.coherentIso` is a Joyal categorical equivalence as soon as the
edge and composition extension properties hold for every quasicategory.
These two hypotheses are the homotopy-level extension properties
isolated above; they are discharged downstream in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint`.
This conditional assembly does not by itself establish the gate
example. -/
theorem categoricalEquivalences.coherentIso_endpointInclusion_of_extensions
    (h : ∀ (C : SSet.{u}), Quasicategory C →
      coherentIso.edgeExtensionProperty C ∧
        coherentIso.compExtensionProperty C) :
    categoricalEquivalences.{u} coherentIso.endpointInclusion := by
  rw [categoricalEquivalences.mem_iff]
  intro C hC
  obtain ⟨hE, hComp⟩ := h C hC
  exact @coherentIso.hoPre_endpointInclusion_isEquivalence_of_extensions
    C hC hE hComp

end SSet
