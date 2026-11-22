/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Descent
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration

/-!
# Boundary lifting, slice comparisons, and pre-fibrant descent data

This file records boundary lifting for trivial Kan fibrations, including
surjectivity in dimension zero, and transport across genuine pullback squares.
It also defines the under-slice comparison map and the pointwise condition
`SSet.MappingSpaceLeftTrivialFibration`, with its identity and composition laws.
The geometric consequences of that condition are proved in
`BoundaryLiftingCore.lean`, `SliceLeftFibration.lean`, and `ContractibleFiber.lean`.

`SSet.HasPreFibrantDescentDatum` records descent of one inner fibration to a
pre-fibrant base. `SSet.PreFibrantDescentReplacementExists` records the uniform
replacement property from Stevenson Proposition 4.12. Both conclusions concern
pre-fibrant targets; their selected-horn construction is separate from a
quasicategory replacement.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y S T : SSet.{u}}

/-!
### Trivial Kan fibrations as boundary lifting properties
-/

/-- A map is a trivial Kan fibration (`modelCategoryQuillen.I.rlp`)
if and only if it has the right lifting property against every
boundary inclusion. The forward direction is
`SSet.hasLiftingProperty_boundary_of_rlp_I` (the supporting results); the
reverse direction destructures membership in
`SSet.modelCategoryQuillen.I = .ofHoms (fun n ↦ ∂Δ[n].ι)`. -/
theorem modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary
    (p : X ⟶ S) :
    modelCategoryQuillen.I.rlp p ↔
      ∀ n : ℕ, HasLiftingProperty (boundary n).ι p := by
  refine ⟨fun hp ↦ hasLiftingProperty_boundary_of_rlp_I hp, fun h ↦ ?_⟩
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact h n

/-!
### Step 2 of Stevenson's proof: the case `n = 0`
-/

/-- Stevenson's `n = 0` case, surjective form: a map surjective on
vertices has the right lifting property against `(boundary 0).ι`.
Since `∂Δ[0] = ⊥` (`SSet.boundary_zero`) is initial, a lift is
exactly a chosen preimage in degree `0` of the vertex classified
by the bottom map. -/
theorem hasLiftingProperty_boundary_zero_of_surjective_app_zero
    {p : X ⟶ S} (hf : Function.Surjective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (boundary 0).ι p where
  sq_hasLift {top bottom} sq := by
    obtain ⟨x, hx⟩ := hf (yonedaEquiv bottom)
    have hinit : IsInitial ((boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) :=
      (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
        (Subcomplex.eqToIso boundary_zero).symm
    refine CommSq.HasLift.mk' ⟨yonedaEquiv.symm x, hinit.hom_ext _ _, ?_⟩
    rw [yonedaEquiv_symm_comp, hx, Equiv.symm_apply_apply]

/-- Stevenson's `n = 0` case: a map bijective on vertices has the
right lifting property against `(boundary 0).ι`. -/
theorem hasLiftingProperty_boundary_zero_of_bijective_app_zero
    {p : X ⟶ S} (hf : Function.Bijective (p.app (op ⦋0⦌))) :
    HasLiftingProperty (boundary 0).ι p :=
  hasLiftingProperty_boundary_zero_of_surjective_app_zero hf.2

/-- For a vertex-bijective map, being a trivial Kan fibration is
exactly boundary lifting in positive degrees: the `n = 0` case is
Stevenson's Step 2, so only `n ≥ 1` (Step 3) remains. -/
theorem modelCategoryQuillen_I_rlp_iff_of_bijective_app_zero {p : X ⟶ S}
    (hf : Function.Bijective (p.app (op ⦋0⦌))) :
    modelCategoryQuillen.I.rlp p ↔
      ∀ n : ℕ, 1 ≤ n → HasLiftingProperty (boundary n).ι p := by
  rw [modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary]
  refine ⟨fun h n _ ↦ h n, fun h n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hasLiftingProperty_boundary_zero_of_bijective_app_zero hf
  · exact h n hn

/-!
### Step 0 transport: pullback (descent) squares

Throughout, `sq : IsPullback g p q f` is a descent square in
Stevenson's sense: `p : X ⟶ S` and `q : Y ⟶ T` are the vertical
maps, `g : X ⟶ Y` and `f : S ⟶ T` the horizontal maps, with
`g ≫ q = p ≫ f`.
-/

/-- Trivial Kan fibrations pull back along descent squares: if
`q` is a trivial Kan fibration and `p` is its pullback along `f`,
then `p` is a trivial Kan fibration. This is base-change stability
of the right lifting class `modelCategoryQuillen.I.rlp`, and is
the final arrow of Stevenson's descent reduction (Step 0). -/
theorem modelCategoryQuillen_I_rlp_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hq : modelCategoryQuillen.I.rlp q) :
    modelCategoryQuillen.I.rlp p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hq

/-- Categorical equivalences transport to the right side of a
descent square whose horizontal maps are categorical
equivalences: `g ≫ q = p ≫ f` is a categorical equivalence, and
cancelling `g` (two-out-of-three,
`SSet.categoricalEquivalences.hasTwoOutOfThreeProperty`) gives
`q`. This is Stevenson's "Clearly `p'` is a categorical
equivalence" in Step 0, with horizontal categorical equivalences
in practice supplied by inner anodyneness via
`SSet.categoricalEquivalences.of_innerAnodyneExtensions`. -/
theorem categoricalEquivalences_right_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hg : categoricalEquivalences g) (hf : categoricalEquivalences f)
    (hp : categoricalEquivalences p) : categoricalEquivalences q := by
  have hcomp : categoricalEquivalences (g ≫ q) := by
    rw [sq.w]
    exact categoricalEquivalences.comp_mem _ _ hp hf
  exact categoricalEquivalences.of_precomp g q hg hcomp

/-- Vertex-bijectivity of the base map of a descent square
implies vertex-bijectivity of the top map: evaluation in degree
`0` preserves the pullback, and in `Type` the pullback of an
isomorphism is an isomorphism
(`CategoryTheory.IsPullback.isIso_fst_of_isIso` read through
`CategoryTheory.isIso_iff_bijective`). -/
theorem bijective_app_zero_fst_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    Function.Bijective (g.app (op ⦋0⦌)) := by
  have sq0 := sq.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))
  have hfI : IsIso (((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)).map f) := by
    rw [isIso_iff_bijective]
    exact hf
  have hgI := sq0.isIso_fst_of_isIso (inst := hfI)
  exact (isIso_iff_bijective _).mp hgI

/-- Vertex-bijectivity transports to the right side of a descent
square: if `f` and `p` are bijective on vertices, so is `q`. The
top map is bijective on vertices by
`SSet.bijective_app_zero_fst_of_isPullback`, the composite
`g ≫ q = p ≫ f` is bijective in degree `0`, and bijectivity
cancels on the left. This is Stevenson's "also a bijection on
objects" in Step 0. -/
theorem bijective_app_zero_right_of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    (hf : Function.Bijective (f.app (op ⦋0⦌)))
    (hp : Function.Bijective (p.app (op ⦋0⦌))) :
    Function.Bijective (q.app (op ⦋0⦌)) := by
  have hg : Function.Bijective (g.app (op ⦋0⦌)) :=
    bijective_app_zero_fst_of_isPullback sq hf
  have hcomp : Function.Bijective ((g ≫ q).app (op ⦋0⦌)) := by
    rw [sq.w, NatTrans.comp_app]
    exact hf.comp hp
  have hqapp : (g ≫ q).app (op ⦋0⦌) = q.app (op ⦋0⦌) ∘ g.app (op ⦋0⦌) := rfl
  rw [hqapp] at hcomp
  refine ⟨fun a b hab ↦ ?_, Function.Surjective.of_comp hcomp.2⟩
  obtain ⟨a', rfl⟩ := hg.2 a
  obtain ⟨b', rfl⟩ := hg.2 b
  exact congrArg (g.app (op ⦋0⦌)) (hcomp.1 hab)

/-!
### Step 3 geometry: the slice comparison map
-/

/-- Stevenson's slice comparison map `X_{x/} → S_{x/} ×_S X`
(the right vertical map of the transposed square in Step 3; here
the base vertex of the target slice is `x ≫ p`): the map into the
pullback of `SSet.sliceUnder.proj S (x ≫ p)` along `p` induced by
postcomposition (`SSet.sliceUnder.map`) and by the forgetful map
(`SSet.sliceUnder.proj`), which agree after mapping to `S` by
`SSet.sliceUnder.map_proj`. Stevenson proves this map is a left
fibration when `p` is an inner fibration, with fiber over `y` the
mapping-space map `SSet.mappingSpaceLeft.map X x y p`; neither
statement is landed (no left-fibration API for join slices), and
the transposition of boundary lifting problems against `p` to
boundary lifting problems against this map — via the join
decomposition `∂Δⁿ = Δ^{{0}} ⋆ ∂Δ^{{1,…,n}} ∪ Δ^{{1,…,n}}` — is
the geometric heart of the missing core below. -/
noncomputable def sliceUnderComparison {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnder X x ⟶ pullback (sliceUnder.proj S (x ≫ p)) p :=
  pullback.lift (sliceUnder.map X x p) (sliceUnder.proj X x)
    (sliceUnder.map_proj X x p)

/-- The slice comparison map followed by the first pullback
projection is postcomposition on under-slices. -/
@[reassoc (attr := simp)]
theorem sliceUnderComparison_fst {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnderComparison (p := p) x ≫
        pullback.fst (sliceUnder.proj S (x ≫ p)) p =
      sliceUnder.map X x p :=
  pullback.lift_fst _ _ _

/-- The slice comparison map followed by the second pullback
projection is the forgetful map of the source under-slice. -/
@[reassoc (attr := simp)]
theorem sliceUnderComparison_snd {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnderComparison (p := p) x ≫
        pullback.snd (sliceUnder.proj S (x ≫ p)) p =
      sliceUnder.proj X x :=
  pullback.lift_snd _ _ _

/-!
### Step 1 conclusion as a predicate
-/

/-- The conclusion of Stevenson's Step 1 for a map `p`: every
induced map on naive (left, join-slice) mapping spaces
`Homᴸ_X(a, b) → Homᴸ_S(a ≫ p, b ≫ p)` is a trivial Kan
fibration. For an inner fibration `p` between pre-fibrant
simplicial sets which is a categorical equivalence, Stevenson
deduces this from Proposition 3.5 and Remark 3.7 (weak
equivalences between the Kan complexes of Remark 3.3) plus the
Kan-fibration property of fibers of the left fibration
`SSet.sliceUnderComparison`; none of those inputs is landed, so
in this file the predicate is only named and given its formal
sanity properties. Compare `SSet.dwyerKanFullyFaithfulLeft`
(Descent.lean), which asks for a realization weak equivalence
of the same maps: the present predicate is the fibration
strengthening that Step 3 actually consumes. -/
def MappingSpaceLeftTrivialFibration {X S : SSet.{u}} (p : X ⟶ S) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
    modelCategoryQuillen.I.rlp (mappingSpaceLeft.map X a b p)

/-- The identity map satisfies
`SSet.MappingSpaceLeftTrivialFibration`: the induced
mapping-space map is the identity
(`SSet.mappingSpaceLeft.map_id`), and right lifting classes
contain identities. No Kan-ness hypothesis is needed, as for
the unconditional `SSet.dwyerKanFullyFaithfulLeft_id`. -/
theorem mappingSpaceLeftTrivialFibration_id :
    MappingSpaceLeftTrivialFibration (𝟙 X) := by
  intro a b
  rw [mappingSpaceLeft.map_id]
  exact MorphismProperty.id_mem _ _

/-- `SSet.MappingSpaceLeftTrivialFibration` is stable under
composition, by `SSet.mappingSpaceLeft.map_comp` and stability of
right lifting classes under composition. -/
theorem MappingSpaceLeftTrivialFibration.comp {p : X ⟶ S} {q : S ⟶ T}
    (hp : MappingSpaceLeftTrivialFibration p)
    (hq : MappingSpaceLeftTrivialFibration q) :
    MappingSpaceLeftTrivialFibration (p ≫ q) := by
  intro a b
  rw [mappingSpaceLeft.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (hp a b) (hq (a ≫ p) (b ≫ p))

/-- Stevenson's `n = 1` sentence, modulo the edge dictionary: if
`p` satisfies `SSet.MappingSpaceLeftTrivialFibration`, every
induced left mapping-space map is surjective on vertices (a
trivial Kan fibration is surjective on vertices,
`SSet.exists_vertex_lift_of_rlp_I`). Under the identification of
`0`-simplices of `Homᴸ` with edges — blocked by the transported
vertex maps `SSet.leftVertex` of JoinSlice.lean — this says every
edge of `S` between image vertices lifts to an edge of `X`. -/
theorem MappingSpaceLeftTrivialFibration.surjective_app_zero {p : X ⟶ S}
    (hp : MappingSpaceLeftTrivialFibration p)
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Surjective ((mappingSpaceLeft.map X a b p).app (op ⦋0⦌)) :=
  fun y ↦ exists_vertex_lift_of_rlp_I (hp a b) y

/-!
### The landed `π₀` shadow of Step 1 (the supporting results)

Unconditionally, a categorical equivalence is fully faithful on
morphism sets of homotopy categories
(`SSet.categoricalEquivalences.dwyerKanFullyFaithfulPiZero`).
For a quasicategory these are `π₀` of the mapping spaces, so
this is the `π₀` shadow of Stevenson's Step 1 — and of his
`n = 1` step it gives edge lifting *up to homotopy*, not on the
nose. Strictifying a homotopic lift to a strict one is exactly
the missing Kan-fibration input for mapping-space maps.
-/

/-- **Fullness on edges up to homotopy** for a categorical
equivalence out of a quasicategory: every edge between image
vertices is homotopic (equal in the homotopy category) to the
image of an edge. This is the supporting results
`SSet.dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq`
in the homotopy category; compare
`SSet.MappingSpaceLeftTrivialFibration.surjective_app_zero`,
which would give strict lifts under the edge dictionary. -/
theorem categoricalEquivalences.exists_edge_map_toHoHom_eq
    [Quasicategory X] {f : X ⟶ S} (hf : categoricalEquivalences f)
    {x y : X _⦋0⦌} (e' : Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : Edge x y, (e.map f).toHoHom = e'.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq e'

/-- **Faithfulness on edges up to homotopy** for a categorical
equivalence: edges with homotopic images are homotopic. the supporting results `SSet.dwyerKanFullyFaithfulPiZero.edge_map_toHoHom_injective`
in the homotopy category. -/
theorem categoricalEquivalences.edge_map_toHoHom_injective
    {f : X ⟶ S} (hf : categoricalEquivalences f) {x y : X _⦋0⦌}
    {e₁ e₂ : Edge x y}
    (h : (e₁.map f).toHoHom = (e₂.map f).toHoHom) :
    e₁.toHoHom = e₂.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.edge_map_toHoHom_injective h

/-!
### Pre-fibrant descent data
-/

/-- A pre-fibrant descent datum for one inner fibration `p : X ⟶ S`:
an inner-anodyne, vertex-bijective map `f : S ⟶ T` with pre-fibrant target,
together with inner-anodyne descent of `p` along `f`. Vertex bijectivity is
recorded explicitly for degree-zero transport. The target is only required to
be pre-fibrant. -/
def HasPreFibrantDescentDatum {X S : SSet.{u}} (p : X ⟶ S) : Prop :=
  ∃ (T : SSet.{u}) (f : S ⟶ T),
    innerAnodyneExtensions f ∧ IsPreFibrant T ∧
      Function.Bijective (f.app (op ⦋0⦌)) ∧
      SatisfiesInnerAnodyneDescent p f

/-- Over a pre-fibrant base an inner fibration has a descent datum
along the identity. -/
theorem hasPreFibrantDescentDatum_of_isPreFibrant {p : X ⟶ S}
    [InnerFibration p] [IsPreFibrant S] :
    HasPreFibrantDescentDatum p :=
  ⟨S, 𝟙 S, innerAnodyneExtensions.id_mem S, inferInstance, by
      have h : ∀ x : S _⦋0⦌, (𝟙 S : S ⟶ S).app (op ⦋0⦌) x = x :=
        fun x ↦ by simp
      exact ⟨fun a b hab ↦ by rwa [h, h] at hab, fun b ↦ ⟨b, h b⟩⟩,
    satisfiesInnerAnodyneDescent_id p⟩

/-- The uniform pre-fibrant replacement property of Stevenson
Proposition 4.12: every simplicial set admits an inner-anodyne,
vertex-bijective map to a pre-fibrant target along which every inner fibration
admits inner-anodyne descent. This predicate is an explicit hypothesis; its
selected-horn assembly is developed in `DescentProp412.lean` and
`SelectiveTower.lean`. -/
def PreFibrantDescentReplacementExists : Prop :=
  ∀ S : SSet.{u}, ∃ (T : SSet.{u}) (f : S ⟶ T),
    innerAnodyneExtensions f ∧ IsPreFibrant T ∧
      Function.Bijective (f.app (op ⦋0⦌)) ∧
      ∀ {X : SSet.{u}} (p : X ⟶ S), InnerFibration p →
        SatisfiesInnerAnodyneDescent p f

/-- The uniform Proposition 4.12 hypothesis supplies a descent
datum for every inner fibration. -/
theorem HasPreFibrantDescentDatum.of_replacementExists
    (h : PreFibrantDescentReplacementExists.{u}) {p : X ⟶ S}
    [InnerFibration p] : HasPreFibrantDescentDatum p := by
  obtain ⟨T, f, hfAnod, hT, hfBij, hdesc⟩ := h S
  exact ⟨T, f, hfAnod, hT, hfBij, hdesc p inferInstance⟩

end SSet

end
