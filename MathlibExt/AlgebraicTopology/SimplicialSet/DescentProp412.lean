/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerFibrationCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceW
public import MathlibExt.AlgebraicTopology.SimplicialSet.FixedVertexModelStructure
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Pullback descent, sequential towers, and mapping-preserving replacement data

This file develops genuine pullback descent along pushouts and sequential
colimits, including the dependent tower construction and its inner-fibration
and inner-anodyness properties. Its selected-horn assembly produces
pre-fibrant-target descent data under the explicitly supplied horn-cell
hypothesis `SSet.HornDescent412`.

It also records the pointwise property `SSet.HasProp35Replacement`: a particular
simplicial set admits an inner-anodyne map to a quasicategory preserving all
naive left mapping spaces by isomorphisms. Given such data for the two objects,
the mapping-space comparison with quasicategories has the stated conditional
Dwyer–Kan consequences. This property is available, for example, by the identity
on a quasicategory. It is not available for every pre-fibrant simplicial set:
Campbell's collapsed two-simplex has discrete two-point naive left mapping
space while the corresponding hom set of its homotopy category is a singleton.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {S T X Y Z : SSet.{u}}

/-!
### §0. Inner anodyne maps are bijective on vertices

Stevenson §5.1 ("every inner anodyne map is bijective on
vertices, since the inner horn inclusions have this property")
is landed as `SSet.innerAnodyneExtensions_le_vertexBijective`
(weak saturation). We record the membership form in the
`Function.Bijective (f.app (op ⦋0⦌))` shape used by
`SSet.HasPreFibrantDescentDatum` and discharge that datum's
explicit vertex-bijectivity clause.
-/

/-- **Inner anodyne maps are bijective on vertices**
(Stevenson §5.1): if `f` is inner anodyne then `f` is bijective
on `0`-simplices. This is
`SSet.isVertexBijective_of_innerAnodyneExtensions` read through
`SSet.isVertexBijective_iff`. -/
theorem bijective_app_zero_of_innerAnodyneExtensions {f : X ⟶ Y}
    (hf : innerAnodyneExtensions f) :
    Function.Bijective (f.app (op ⦋0⦌)) :=
  (isVertexBijective_iff f).mp
    (isVertexBijective_of_innerAnodyneExtensions hf)

/-- A Proposition 4.12 descent datum for `p` follows from inner
anodyne descent along an inner anodyne map to a pre-fibrant
simplicial set, with **no separate vertex-bijectivity
hypothesis**: that clause of `SSet.HasPreFibrantDescentDatum` is
supplied by
`SSet.bijective_app_zero_of_innerAnodyneExtensions`. -/
theorem hasPreFibrantDescentDatum_of_innerAnodyne {p : X ⟶ S}
    {f : S ⟶ T} (hf : innerAnodyneExtensions f) [IsPreFibrant T]
    (h : SatisfiesInnerAnodyneDescent p f) :
    HasPreFibrantDescentDatum p :=
  ⟨T, f, hf, inferInstance,
    bijective_app_zero_of_innerAnodyneExtensions hf, h⟩

/-- The uniform Proposition 4.12 hypothesis
`SSet.PreFibrantDescentReplacementExists` follows from the same
statement with its vertex-bijectivity clause deleted: for every
`S` an inner anodyne map `S ⟶ T` with `T` pre-fibrant along
which every inner fibration over `S` satisfies inner anodyne
descent. The deleted clause is automatic by
`SSet.bijective_app_zero_of_innerAnodyneExtensions`. -/
theorem preFibrantDescentReplacementExists_of_innerAnodyne
    (h : ∀ S : SSet.{u}, ∃ (T : SSet.{u}) (f : S ⟶ T),
      innerAnodyneExtensions f ∧ IsPreFibrant T ∧
        ∀ {X : SSet.{u}} (p : X ⟶ S), InnerFibration p →
          SatisfiesInnerAnodyneDescent p f) :
    PreFibrantDescentReplacementExists.{u} := by
  intro S
  obtain ⟨T, f, hf, hT, hdesc⟩ := h S
  exact ⟨T, f, hf, hT,
    bijective_app_zero_of_innerAnodyneExtensions hf, hdesc⟩

/-!
### (i) Left mapping spaces: simplex lemma, Whitehead assembly,
two-out-of-six

Stevenson's §3 is stated with *left* mapping spaces `Homᴸ`, while
the landed full-faithfulness predicate
`SSet.dwyerKanFullyFaithful` uses right ones
(the additional comparison obligation). No comparison `Homᴸ ≃ Homᴿ` is landed.
What is formalized here is the left-handed infrastructure in the
same form as the supporting results on the right, so that both sides are
reduced to the *same* finite-probe input
(`SSet.dwyerKanFullyFaithfulProbes`, which is left/right
agnostic) plus π-bridge identifications: the simplex-level
description of the induced map, the Whitehead assembly, and
two-out-of-six. Kan-ness of left mapping spaces of pre-fibrant
simplicial sets (Remark 3.3) is the named predicate
`SSet.LeftMappingSpacesKan` (the additional comparison obligation).
-/

/-- All naive (left) mapping spaces of `X` are Kan complexes.
For pre-fibrant `X` this is Stevenson's Remark 3.3, which is not
yet proved (the additional comparison obligation); the predicate names exactly
that input where it is consumed. -/
def LeftMappingSpacesKan (X : SSet.{u}) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X, KanComplex (mappingSpaceLeft X a b)

namespace mappingSpaceLeft

variable (X : SSet.{u}) (a b : (Δ[0] : SSet.{u}) ⟶ X)

/-- Under the transport `SSet.mappingSpaceLeft.simplexEquivSucc`
(an `n`-simplex of the left mapping space read as an
`(n + 1)`-simplex of `X`), the induced map
`SSet.mappingSpaceLeft.map X a b F` is postcomposition with `F`.
Left analogue of
`SSet.mappingSpaceRight.simplexEquivSucc_map_app_val`
(the supporting results). -/
theorem simplexEquivSucc_map_app_val {Y : SSet.{u}} (F : X ⟶ Y)
    (n : ℕ) (σ : (mappingSpaceLeft X a b).obj (op ⦋n⦌)) :
    ((simplexEquivSucc Y (a ≫ F) (b ≫ F) n)
        ((map X a b F).app (op ⦋n⦌) σ)).1 =
      ((simplexEquivSucc X a b n) σ).1 ≫ F := by
  change (SSet.joinStdSimplexIso 0 n).inv ≫ (σ.1 ≫ F) =
    ((SSet.joinStdSimplexIso 0 n).inv ≫ σ.1) ≫ F
  rw [Category.assoc]

end mappingSpaceLeft

variable {f : X ⟶ Y}

/-- **Whitehead criterion for full faithfulness on left mapping
spaces, `π₀` form**: if all left mapping spaces of `X` and all
the target left mapping spaces are Kan complexes, and for every
pair of vertices the induced map
`SSet.mappingSpaceLeft.map X a b f` is bijective on connected
components `SSet.mapπ₀` and on all positive based homotopy
groups, then `f` is fully faithful on left mapping spaces. Left
analogue of
`SSet.dwyerKanFullyFaithful.of_kan_bijective_mapPiZero_piMap`
(the supporting results), by `SSet.KanComplex.W_iff` applied pointwise and
transported along `SSet.dwyerKanFullyFaithfulLeft.of_kanComplexW`.
The Kan hypotheses are Remark 3.3 (the additional comparison obligation) and the
bijectivity hypotheses are the left π-bridge output of the
finite-probe predicate (the additional comparison obligation). -/
theorem dwyerKanFullyFaithfulLeft.of_kan_bijective_mapPiZero_piMap
    (hKanX : LeftMappingSpacesKan X)
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceLeft Y (a ≫ f) (b ≫ f)))
    (h₀ : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      Function.Bijective (mapπ₀ (mappingSpaceLeft.map X a b f)))
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceLeft X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceLeft.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    dwyerKanFullyFaithfulLeft f :=
  dwyerKanFullyFaithfulLeft.of_kanComplexW fun a b ↦ by
    have : KanComplex (mappingSpaceLeft X a b) := hKanX a b
    have : KanComplex (mappingSpaceLeft Y (a ≫ f) (b ≫ f)) :=
      hKanY a b
    exact (KanComplex.W_iff _).2 ⟨h₀ a b, fun n σ ↦ hπ a b n σ⟩

/-- **Two-out-of-six for full faithfulness on left mapping
spaces**: if `f ≫ g` and `g ≫ f` are fully faithful in the sense
of `SSet.dwyerKanFullyFaithfulLeft`, then `f` is. Left analogue
of `SSet.dwyerKanFullyFaithful.of_comp_comp` (the supporting results), by
`SSet.realizationWeakEquivalences.left_of_comp_comp` applied to
the chain of left mapping-space maps. -/
theorem dwyerKanFullyFaithfulLeft.of_comp_comp {g : Y ⟶ X}
    (hfg : dwyerKanFullyFaithfulLeft (f ≫ g))
    (hgf : dwyerKanFullyFaithfulLeft (g ≫ f)) :
    dwyerKanFullyFaithfulLeft f := by
  intro a b
  have hab : realizationWeakEquivalences
      (mappingSpaceLeft.map X a b f ≫
        mappingSpaceLeft.map Y (a ≫ f) (b ≫ f) g) := by
    rw [← mappingSpaceLeft.map_comp]
    exact hfg a b
  have hbc : realizationWeakEquivalences
      (mappingSpaceLeft.map Y (a ≫ f) (b ≫ f) g ≫
        mappingSpaceLeft.map X ((a ≫ f) ≫ g) ((b ≫ f) ≫ g) f) := by
    rw [← mappingSpaceLeft.map_comp]
    exact hgf (a ≫ f) (b ≫ f)
  exact realizationWeakEquivalences.left_of_comp_comp hab hbc

/-- The left-handed Dwyer–Kan predicate (Stevenson
Definition 2.16 with `Homᴸ` as in the paper): essentially
surjective and fully faithful on *left* mapping spaces. Compare
`SSet.isDwyerKanEquivalence`, which uses right mapping spaces;
their agreement is the additional comparison obligation. -/
def isDwyerKanEquivalenceLeft (f : X ⟶ Y) : Prop :=
  dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithfulLeft f

/-- A left Dwyer–Kan equivalence is essentially surjective. -/
theorem isDwyerKanEquivalenceLeft.dwyerKanEssentiallySurjective
    (h : isDwyerKanEquivalenceLeft f) :
    dwyerKanEssentiallySurjective f :=
  h.1

/-- A left Dwyer–Kan equivalence is fully faithful on left
mapping spaces. -/
theorem isDwyerKanEquivalenceLeft.dwyerKanFullyFaithfulLeft
    (h : isDwyerKanEquivalenceLeft f) :
    dwyerKanFullyFaithfulLeft f :=
  h.2

/-- A categorical equivalence satisfying Kan-ness of the
relevant left mapping spaces and bijectivity of `SSet.mapπ₀` and
of all positive based homotopy-group maps of
`SSet.mappingSpaceLeft.map` is a left Dwyer–Kan equivalence.
Left analogue of the supporting results capstone
`SSet.categoricalEquivalences.isDwyerKanEquivalence_of_kan_bijective_mapPiZero_piMap`;
supplying the bijectivity hypotheses from
`SSet.categoricalEquivalences.dwyerKanFullyFaithfulProbes` is
the left π-identification (the additional comparison obligation). -/
theorem
    categoricalEquivalences.isDwyerKanEquivalenceLeft_of_kan_bijective_mapPiZero_piMap
    (hf : categoricalEquivalences f)
    (hKanX : LeftMappingSpacesKan X)
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceLeft Y (a ≫ f) (b ≫ f)))
    (h₀ : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      Function.Bijective (mapπ₀ (mappingSpaceLeft.map X a b f)))
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceLeft X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceLeft.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    isDwyerKanEquivalenceLeft f :=
  ⟨hf.dwyerKanEssentiallySurjective,
    dwyerKanFullyFaithfulLeft.of_kan_bijective_mapPiZero_piMap
      hKanX hKanY h₀ hπ⟩

/-!
### (ii) Pointwise mapping-preserving replacement data

The comparison results in this section require an explicit replacement datum
for each of the two simplicial sets, together with the indicated Kan and
quasicategory mapping-space hypotheses. Pre-fibrancy alone does not provide
these data.
-/

/-- A pointwise mapping-preserving quasicategory replacement:
an inner-anodyne map `u : S ⟶ T` with quasicategory target which induces
isomorphisms on every naive left mapping space. The identity gives such data
for a quasicategory. Campbell's pre-fibrant counterexample prevents a uniform
existence theorem for all pre-fibrant simplicial sets. -/
def HasProp35Replacement (S : SSet.{u}) : Prop :=
  ∃ (T : SSet.{u}) (u : S ⟶ T),
    innerAnodyneExtensions u ∧ Quasicategory T ∧
      ∀ a b : (Δ[0] : SSet.{u}) ⟶ S,
        IsIso (mappingSpaceLeft.map S a b u)

/-- A map inducing isomorphisms on all left mapping spaces is
fully faithful on left mapping spaces, provided those mapping
spaces are Kan complexes on both sides: an isomorphism between
Kan complexes is a `SSet.KanComplex.W` weak equivalence
(`SSet.KanComplex.W.ofIso`), transported to a realization weak
equivalence along `SSet.KanComplex.W_iff_realizationWeakEquivalence`.
In particular this applies to the map of a
`SSet.HasProp35Replacement` datum. -/
theorem dwyerKanFullyFaithfulLeft_of_isIso_mappingSpaceLeft_map
    {u : X ⟶ Y} (hKanX : LeftMappingSpacesKan X)
    (hKanY : LeftMappingSpacesKan Y)
    (hiso : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      IsIso (mappingSpaceLeft.map X a b u)) :
    dwyerKanFullyFaithfulLeft u := by
  intro a b
  have : KanComplex (mappingSpaceLeft X a b) := hKanX a b
  have : KanComplex (mappingSpaceLeft Y (a ≫ u) (b ≫ u)) :=
    hKanY (a ≫ u) (b ≫ u)
  have : IsIso (mappingSpaceLeft.map X a b u) := hiso a b
  exact (KanComplex.W_iff_realizationWeakEquivalence
    (mappingSpaceLeft.map X a b u)).mp
    (KanComplex.W.ofIso (asIso (mappingSpaceLeft.map X a b u)))

/-- Extension along an inner anodyne map into a quasicategory:
if `u : X ⟶ Y` is inner anodyne and `Z` is a quasicategory,
every map `φ : X ⟶ Z` extends to `Y`, by lifting against the
inner fibration `terminal.from Z`. This produces the comparison
map `f'` between Proposition 3.5 replacements in Stevenson's
proof of Remark 3.7. -/
theorem exists_comp_eq_of_innerAnodyneExtensions {u : X ⟶ Y}
    (hu : innerAnodyneExtensions u) (φ : X ⟶ Z) [Quasicategory Z] :
    ∃ ψ : Y ⟶ Z, u ≫ ψ = φ := by
  have hfib : InnerFibration (terminal.from Z) :=
    (quasicategory_iff_of_isTerminal _ terminalIsTerminal).mp
      inferInstance
  have hlift : HasLiftingProperty u (terminal.from Z) := by
    rw [innerAnodyneExtensions_eq_llp_rlp] at hu
    exact hu _ InnerFibration.mem
  let sq : CommSq φ u (terminal.from Z) (terminal.from Y) :=
    CommSq.mk (Subsingleton.elim _ _)
  exact ⟨sq.lift, sq.fac_left⟩

/-- A vertex map `a' : Δ[0] ⟶ Y` factors through a map `u`
bijective on vertices: `a' = a ≫ u` for the constant vertex map
at the unique preimage `0`-simplex. -/
theorem exists_comp_eq_of_bijective_app_zero {u : X ⟶ Y}
    (hu0 : Function.Bijective (u.app (op ⦋0⦌)))
    (a' : (Δ[0] : SSet.{u}) ⟶ Y) :
    ∃ a : (Δ[0] : SSet.{u}) ⟶ X, a ≫ u = a' := by
  obtain ⟨x, hx⟩ := hu0.2 (yonedaEquiv a')
  refine ⟨const x, yonedaEquiv.injective ?_⟩
  rw [yonedaEquiv_comp, yonedaEquiv_const, hx]

/-- Two-out-of-three for full faithfulness on left mapping
spaces, cancelling on the right: if `v` is fully faithful on
left mapping spaces then `f ≫ v` is fully faithful iff `f` is,
by `SSet.realizationWeakEquivalences.of_postcomp` and
`SSet.dwyerKanFullyFaithfulLeft.comp` pointwise. -/
theorem dwyerKanFullyFaithfulLeft.comp_iff_left {f : X ⟶ Y}
    {v : Y ⟶ Z} (hv : dwyerKanFullyFaithfulLeft v) :
    dwyerKanFullyFaithfulLeft (f ≫ v) ↔
      dwyerKanFullyFaithfulLeft f := by
  constructor
  · intro h a b
    have hcomp := h a b
    rw [mappingSpaceLeft.map_comp] at hcomp
    exact realizationWeakEquivalences.of_postcomp _ _
      (hv (a ≫ f) (b ≫ f)) hcomp
  · intro h
    exact h.comp hv

/-- Two-out-of-three for full faithfulness on left mapping
spaces, cancelling on the left: if `u` is fully faithful on
left mapping spaces and bijective on vertices, then `u ≫ ψ` is
fully faithful iff `ψ` is. Vertex bijectivity is used to write
every vertex of the middle object as a `u`-image
(`SSet.exists_comp_eq_of_bijective_app_zero`). -/
theorem dwyerKanFullyFaithfulLeft.comp_iff_right_of_bijective_app_zero
    {u : X ⟶ Y} {ψ : Y ⟶ Z} (hu : dwyerKanFullyFaithfulLeft u)
    (hu0 : Function.Bijective (u.app (op ⦋0⦌))) :
    dwyerKanFullyFaithfulLeft (u ≫ ψ) ↔
      dwyerKanFullyFaithfulLeft ψ := by
  constructor
  · intro h a' b'
    obtain ⟨a, rfl⟩ := exists_comp_eq_of_bijective_app_zero hu0 a'
    obtain ⟨b, rfl⟩ := exists_comp_eq_of_bijective_app_zero hu0 b'
    have hcomp := h a b
    rw [mappingSpaceLeft.map_comp] at hcomp
    exact realizationWeakEquivalences.of_precomp _ _ (hu a b) hcomp
  · intro h
    exact hu.comp h

/-- **Stevenson Remark 3.7, reduced to its named inputs.** Let
`f : S ⟶ T` be bijective on vertices, and suppose given
Proposition 3.5 replacement data `u : S ⟶ S'`, `v : T ⟶ T'`
(inner anodyne, quasicategory targets, isomorphisms on naive
mapping spaces), Remark 3.3 for `S, T, S', T'`
(`SSet.LeftMappingSpacesKan`), and Proposition 2.24 for left
mapping spaces between quasicategories (the hypothesis `hQC`).
Then `f` being a categorical equivalence implies it induces
realization weak equivalences on all naive (left) mapping
spaces (agreeing with `SSet.KanComplex.W` on Kan mapping
spaces); only this forward implication is stated, since only
it is consumed downstream. The proof is Stevenson's: extend
`f ≫ v` along `u` to `ψ : S' ⟶ T'`, and transport the
property across the square `u ≫ ψ = f ≫ v` by two-out-of-three,
using that `u, v` are categorical equivalences
(`SSet.categoricalEquivalences.of_innerAnodyneExtensions`),
bijective on vertices (Stevenson §5.1, §0 above), and fully
faithful on left mapping spaces (isomorphisms between Kan
complexes). The replacement maps and mapping-space properties are
explicit pointwise hypotheses. -/
theorem categoricalEquivalences_to_dwyerKanFullyFaithfulLeft_of_prop35Data
    {f : S ⟶ T} (hf : Function.Bijective (f.app (op ⦋0⦌)))
    {S' T' : SSet.{u}} (u : S ⟶ S') (v : T ⟶ T')
    (hu : innerAnodyneExtensions u) (hv : innerAnodyneExtensions v)
    [Quasicategory S'] [Quasicategory T']
    (huIso : ∀ a b : (Δ[0] : SSet.{u}) ⟶ S,
      IsIso (mappingSpaceLeft.map S a b u))
    (hvIso : ∀ a b : (Δ[0] : SSet.{u}) ⟶ T,
      IsIso (mappingSpaceLeft.map T a b v))
    (hKanS : LeftMappingSpacesKan S) (hKanT : LeftMappingSpacesKan T)
    (hKanS' : LeftMappingSpacesKan S') (hKanT' : LeftMappingSpacesKan T')
    (hQC : ∀ {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
      (g : A ⟶ B), Function.Bijective (g.app (op ⦋0⦌)) →
        (categoricalEquivalences g → dwyerKanFullyFaithfulLeft g)) :
    categoricalEquivalences f → dwyerKanFullyFaithfulLeft f := by
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_innerAnodyneExtensions hu (f ≫ v)
  have huCat : categoricalEquivalences u :=
    categoricalEquivalences.of_innerAnodyneExtensions hu
  have hvCat : categoricalEquivalences v :=
    categoricalEquivalences.of_innerAnodyneExtensions hv
  have hu0 : Function.Bijective (u.app (op ⦋0⦌)) :=
    bijective_app_zero_of_innerAnodyneExtensions hu
  have hv0 : Function.Bijective (v.app (op ⦋0⦌)) :=
    bijective_app_zero_of_innerAnodyneExtensions hv
  have huFF : dwyerKanFullyFaithfulLeft u :=
    dwyerKanFullyFaithfulLeft_of_isIso_mappingSpaceLeft_map
      hKanS hKanS' huIso
  have hvFF : dwyerKanFullyFaithfulLeft v :=
    dwyerKanFullyFaithfulLeft_of_isIso_mappingSpaceLeft_map
      hKanT hKanT' hvIso
  have hψ0 : Function.Bijective (ψ.app (op ⦋0⦌)) := by
    have hcomp : Function.Bijective ((u ≫ ψ).app (op ⦋0⦌)) := by
      rw [hψ]
      have happ : (f ≫ v).app (op ⦋0⦌) =
          v.app (op ⦋0⦌) ∘ f.app (op ⦋0⦌) := rfl
      rw [happ]
      exact hv0.comp hf
    have happ : (u ≫ ψ).app (op ⦋0⦌) =
        ψ.app (op ⦋0⦌) ∘ u.app (op ⦋0⦌) := rfl
    rw [happ] at hcomp
    refine ⟨fun a b hab ↦ ?_, Function.Surjective.of_comp hcomp.2⟩
    obtain ⟨a', rfl⟩ := hu0.2 a
    obtain ⟨b', rfl⟩ := hu0.2 b
    exact congrArg (u.app (op ⦋0⦌)) (hcomp.1 hab)
  have hcat1 : categoricalEquivalences f ↔
      categoricalEquivalences (f ≫ v) :=
    ⟨fun h ↦ categoricalEquivalences.comp_mem _ _ h hvCat,
      fun h ↦ categoricalEquivalences.of_postcomp f v hvCat h⟩
  have hcat2 : categoricalEquivalences (u ≫ ψ) ↔
      categoricalEquivalences ψ :=
    ⟨fun h ↦ categoricalEquivalences.of_precomp u ψ huCat h,
      fun h ↦ categoricalEquivalences.comp_mem _ _ huCat h⟩
  rw [hψ] at hcat2
  have hcat : categoricalEquivalences f ↔ categoricalEquivalences ψ :=
    hcat1.trans hcat2
  have hff2 : dwyerKanFullyFaithfulLeft (u ≫ ψ) ↔
      dwyerKanFullyFaithfulLeft ψ :=
    dwyerKanFullyFaithfulLeft.comp_iff_right_of_bijective_app_zero
      huFF hu0
  rw [hψ] at hff2
  have hff : dwyerKanFullyFaithfulLeft f ↔
      dwyerKanFullyFaithfulLeft ψ :=
    (dwyerKanFullyFaithfulLeft.comp_iff_left hvFF).symm.trans hff2
  intro h
  exact hff.mpr ((hQC ψ hψ0) (hcat.mp h))

/-- **Stevenson Remark 3.7, biconditional form** (compatibility:
preserves the pre-existing public API; new uses should prefer the
forward `_to_` variant above unless they genuinely need the
converse). Same statement and proof as before the one-way
refactor. -/
theorem categoricalEquivalences_iff_dwyerKanFullyFaithfulLeft_of_prop35Data
    {f : S ⟶ T} (hf : Function.Bijective (f.app (op ⦋0⦌)))
    {S' T' : SSet.{u}} (u : S ⟶ S') (v : T ⟶ T')
    (hu : innerAnodyneExtensions u) (hv : innerAnodyneExtensions v)
    [Quasicategory S'] [Quasicategory T']
    (huIso : ∀ a b : (Δ[0] : SSet.{u}) ⟶ S,
      IsIso (mappingSpaceLeft.map S a b u))
    (hvIso : ∀ a b : (Δ[0] : SSet.{u}) ⟶ T,
      IsIso (mappingSpaceLeft.map T a b v))
    (hKanS : LeftMappingSpacesKan S) (hKanT : LeftMappingSpacesKan T)
    (hKanS' : LeftMappingSpacesKan S') (hKanT' : LeftMappingSpacesKan T')
    (hQC : ∀ {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
      (g : A ⟶ B), Function.Bijective (g.app (op ⦋0⦌)) →
        (categoricalEquivalences g ↔ dwyerKanFullyFaithfulLeft g)) :
    categoricalEquivalences f ↔ dwyerKanFullyFaithfulLeft f := by
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_innerAnodyneExtensions hu (f ≫ v)
  have huCat : categoricalEquivalences u :=
    categoricalEquivalences.of_innerAnodyneExtensions hu
  have hvCat : categoricalEquivalences v :=
    categoricalEquivalences.of_innerAnodyneExtensions hv
  have hu0 : Function.Bijective (u.app (op ⦋0⦌)) :=
    bijective_app_zero_of_innerAnodyneExtensions hu
  have hv0 : Function.Bijective (v.app (op ⦋0⦌)) :=
    bijective_app_zero_of_innerAnodyneExtensions hv
  have huFF : dwyerKanFullyFaithfulLeft u :=
    dwyerKanFullyFaithfulLeft_of_isIso_mappingSpaceLeft_map
      hKanS hKanS' huIso
  have hvFF : dwyerKanFullyFaithfulLeft v :=
    dwyerKanFullyFaithfulLeft_of_isIso_mappingSpaceLeft_map
      hKanT hKanT' hvIso
  have hψ0 : Function.Bijective (ψ.app (op ⦋0⦌)) := by
    have hcomp : Function.Bijective ((u ≫ ψ).app (op ⦋0⦌)) := by
      rw [hψ]
      have happ : (f ≫ v).app (op ⦋0⦌) =
          v.app (op ⦋0⦌) ∘ f.app (op ⦋0⦌) := rfl
      rw [happ]
      exact hv0.comp hf
    have happ : (u ≫ ψ).app (op ⦋0⦌) =
        ψ.app (op ⦋0⦌) ∘ u.app (op ⦋0⦌) := rfl
    rw [happ] at hcomp
    refine ⟨fun a b hab ↦ ?_, Function.Surjective.of_comp hcomp.2⟩
    obtain ⟨a', rfl⟩ := hu0.2 a
    obtain ⟨b', rfl⟩ := hu0.2 b
    exact congrArg (u.app (op ⦋0⦌)) (hcomp.1 hab)
  have hcat1 : categoricalEquivalences f ↔
      categoricalEquivalences (f ≫ v) :=
    ⟨fun h ↦ categoricalEquivalences.comp_mem _ _ h hvCat,
      fun h ↦ categoricalEquivalences.of_postcomp f v hvCat h⟩
  have hcat2 : categoricalEquivalences (u ≫ ψ) ↔
      categoricalEquivalences ψ :=
    ⟨fun h ↦ categoricalEquivalences.of_precomp u ψ huCat h,
      fun h ↦ categoricalEquivalences.comp_mem _ _ huCat h⟩
  rw [hψ] at hcat2
  have hcat : categoricalEquivalences f ↔ categoricalEquivalences ψ :=
    hcat1.trans hcat2
  have hff2 : dwyerKanFullyFaithfulLeft (u ≫ ψ) ↔
      dwyerKanFullyFaithfulLeft ψ :=
    dwyerKanFullyFaithfulLeft.comp_iff_right_of_bijective_app_zero
      huFF hu0
  rw [hψ] at hff2
  have hff : dwyerKanFullyFaithfulLeft f ↔
      dwyerKanFullyFaithfulLeft ψ :=
    (dwyerKanFullyFaithfulLeft.comp_iff_left hvFF).symm.trans hff2
  exact hcat.trans ((hQC ψ hψ0).trans hff.symm)

/-- A categorical equivalence is left Dwyer–Kan when the two
pre-fibrant objects have the supplied pointwise mapping-preserving
quasicategory replacements, the indicated mapping spaces are Kan, and the
quasicategory full-faithfulness comparison holds. These replacement data are
additional hypotheses, not consequences of pre-fibrancy. -/
-- The unused pre-fibrancy instances keep this public signature (compatibility contract).
@[nolint unusedArguments]
theorem categoricalEquivalences_to_isDwyerKanEquivalenceLeft_of_prop35
    {f : S ⟶ T} [IsPreFibrant S] [IsPreFibrant T]
    (hf : Function.Bijective (f.app (op ⦋0⦌)))
    (hS : HasProp35Replacement S) (hT : HasProp35Replacement T)
    (hKanS : LeftMappingSpacesKan S) (hKanT : LeftMappingSpacesKan T)
    (hKanQC : ∀ A : SSet.{u}, Quasicategory A → LeftMappingSpacesKan A)
    (hQC : ∀ {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
      (g : A ⟶ B), Function.Bijective (g.app (op ⦋0⦌)) →
        (categoricalEquivalences g → dwyerKanFullyFaithfulLeft g)) :
    categoricalEquivalences f → isDwyerKanEquivalenceLeft f := by
  obtain ⟨S', u, hu, hS'qc, huIso⟩ := hS
  obtain ⟨T', v, hv, hT'qc, hvIso⟩ := hT
  have : Quasicategory S' := hS'qc
  have : Quasicategory T' := hT'qc
  have hff :=
    categoricalEquivalences_to_dwyerKanFullyFaithfulLeft_of_prop35Data
      hf u v hu hv huIso hvIso hKanS hKanT
      (hKanQC S' hS'qc) (hKanQC T' hT'qc) hQC
  intro h
  exact (dwyerKanFullyFaithfulLeft_iff_of_bijective_app_zero hf).symm.mp
    (hff h)

/-- **Stevenson Remark 3.7, biconditional form** (compatibility:
preserves the pre-existing public API; new uses should prefer the
forward `_to_` variant above unless they genuinely need the
converse). Same statement and proof as before the one-way
refactor. -/
-- The unused pre-fibrancy instances keep this public signature (compatibility contract).
@[nolint unusedArguments]
theorem categoricalEquivalences_iff_isDwyerKanEquivalenceLeft_of_prop35
    {f : S ⟶ T} [IsPreFibrant S] [IsPreFibrant T]
    (hf : Function.Bijective (f.app (op ⦋0⦌)))
    (hS : HasProp35Replacement S) (hT : HasProp35Replacement T)
    (hKanS : LeftMappingSpacesKan S) (hKanT : LeftMappingSpacesKan T)
    (hKanQC : ∀ A : SSet.{u}, Quasicategory A → LeftMappingSpacesKan A)
    (hQC : ∀ {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
      (g : A ⟶ B), Function.Bijective (g.app (op ⦋0⦌)) →
        (categoricalEquivalences g ↔ dwyerKanFullyFaithfulLeft g)) :
    categoricalEquivalences f ↔ isDwyerKanEquivalenceLeft f := by
  obtain ⟨S', u, hu, hS'qc, huIso⟩ := hS
  obtain ⟨T', v, hv, hT'qc, hvIso⟩ := hT
  have : Quasicategory S' := hS'qc
  have : Quasicategory T' := hT'qc
  have hiff :=
    categoricalEquivalences_iff_dwyerKanFullyFaithfulLeft_of_prop35Data
      hf u v hu hv huIso hvIso hKanS hKanT
      (hKanQC S' hS'qc) (hKanQC T' hT'qc) hQC
  exact hiff.trans
    (dwyerKanFullyFaithfulLeft_iff_of_bijective_app_zero hf).symm

/-!
### (iii) Lemma 4.5: descent along pushouts

Stevenson Lemma 4.5 (§4.1): given `X₁ ← X₀ → X₂` over
`S₁ ← S₀ → S₂` with both squares pullbacks, `S₀ → S₂` a
monomorphism and all vertical maps inner fibrations, each
`X_i → S_i` satisfies descent along `S_i → S₁ ∪_{S₀} S₂`. The
side pullback squares come from van Kampen in the adhesive
category `SSet`; the induced map on pushouts is an inner
fibration because a simplex of a pushout factors through a leg
(degreewise joint surjectivity in `Type`).
-/

section Lemma45

variable {S₀ S₁ S₂ X₀ X₁ X₂ : SSet.{u}}
  {a : S₀ ⟶ S₁} {b : S₀ ⟶ S₂} {aX : X₀ ⟶ X₁} {bX : X₀ ⟶ X₂}
  {p₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}

/-- The map on pushouts induced by two pullback squares over a
span, as in Stevenson's Lemma 4.5: `pushout.desc` of
`p₁ ≫ inl` and `p₂ ≫ inr`, which agree on `X₀` by the two
pullback squares and the pushout condition. -/
noncomputable def pushoutMapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b) :
    pushout aX bX ⟶ pushout a b :=
  pushout.desc (p₁ ≫ pushout.inl a b) (p₂ ≫ pushout.inr a b) (by
    calc aX ≫ p₁ ≫ pushout.inl a b
        = p₀ ≫ a ≫ pushout.inl a b := by
          rw [← Category.assoc, sq1.w, Category.assoc]
      _ = p₀ ≫ b ≫ pushout.inr a b := by
          rw [pushout.condition]
      _ = bX ≫ p₂ ≫ pushout.inr a b := by
          rw [← Category.assoc, ← sq2.w, Category.assoc])

/-- The left square for `SSet.pushoutMapOfPullbacks` commutes. -/
@[reassoc (attr := simp)]
theorem pushoutMapOfPullbacks_inl (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) :
    pushout.inl aX bX ≫ pushoutMapOfPullbacks sq1 sq2 =
      p₁ ≫ pushout.inl a b :=
  pushout.inl_desc _ _ _

/-- The right square for `SSet.pushoutMapOfPullbacks` commutes. -/
@[reassoc (attr := simp)]
theorem pushoutMapOfPullbacks_inr (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) :
    pushout.inr aX bX ≫ pushoutMapOfPullbacks sq1 sq2 =
      p₂ ≫ pushout.inr a b :=
  pushout.inr_desc _ _ _

/-- The side squares in Stevenson's Lemma 4.5 are pullbacks:
the bottom pushout is van Kampen (`SSet` is adhesive and
`b : S₀ ⟶ S₂` is a monomorphism), the front and back faces are
the given pullbacks, and the top face is a pushout by
construction. -/
theorem isPullback_pushoutMapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] :
    IsPullback (pushout.inl aX bX) p₁ (pushoutMapOfPullbacks sq1 sq2)
        (pushout.inl a b) ∧
      IsPullback (pushout.inr aX bX) p₂ (pushoutMapOfPullbacks sq1 sq2)
        (pushout.inr a b) := by
  have hbot : IsPushout a b (pushout.inl a b) (pushout.inr a b) :=
    IsPushout.of_hasPushout a b
  have htop : IsPushout aX bX (pushout.inl aX bX)
      (pushout.inr aX bX) :=
    IsPushout.of_hasPushout aX bX
  have hleft : CommSq (pushout.inl aX bX) p₁
      (pushoutMapOfPullbacks sq1 sq2) (pushout.inl a b) :=
    ⟨pushoutMapOfPullbacks_inl sq1 sq2⟩
  have hright : CommSq (pushout.inr aX bX) p₂
      (pushoutMapOfPullbacks sq1 sq2) (pushout.inr a b) :=
    ⟨pushoutMapOfPullbacks_inr sq1 sq2⟩
  exact ((Adhesive.van_kampen' hbot) aX bX (pushout.inl aX bX)
    (pushout.inr aX bX) p₀ p₁ p₂ (pushoutMapOfPullbacks sq1 sq2)
    sq1 sq2 hleft hright htop.toCommSq).1 htop

/-- The left side square of Lemma 4.5 is a pullback. -/
theorem isPullback_pushoutInl_mapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] :
    IsPullback (pushout.inl aX bX) p₁ (pushoutMapOfPullbacks sq1 sq2)
      (pushout.inl a b) :=
  (isPullback_pushoutMapOfPullbacks sq1 sq2).1

/-- The right side square of Lemma 4.5 is a pullback. -/
theorem isPullback_pushoutInr_mapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] :
    IsPullback (pushout.inr aX bX) p₂ (pushoutMapOfPullbacks sq1 sq2)
      (pushout.inr a b) :=
  (isPullback_pushoutMapOfPullbacks sq1 sq2).2

end Lemma45

/-- Every simplex of a pushout of simplicial sets factors
through one of the two legs: evaluation in degree `n` preserves
the pushout cocone, whose legs are jointly surjective in `Type`
(`Types.jointly_surjective_of_isColimit`); a simplex coming from
the span vertex `S₀` is pushed into the left leg. This is the
degreewise content of "the canonical map `S₁ ⊔ S₂ → S` is
surjective" in Stevenson's proof of Lemma 4.5. -/
theorem exists_pushout_inl_or_inr_app_eq {S₀ S₁ S₂ : SSet.{u}}
    {a : S₀ ⟶ S₁} {b : S₀ ⟶ S₂} (n : ℕ) (σ : (pushout a b) _⦋n⦌) :
    (∃ σ₁ : S₁ _⦋n⦌, (pushout.inl a b).app (op ⦋n⦌) σ₁ = σ) ∨
      (∃ σ₂ : S₂ _⦋n⦌, (pushout.inr a b).app (op ⦋n⦌) σ₂ = σ) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌)
  have hc : IsColimit (E.mapCocone (colimit.cocone (span a b))) :=
    isColimitOfPreserves E (colimit.isColimit (span a b))
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc σ
  have hj : ∀ j : WalkingSpan, j = WalkingSpan.left ∨
      j = WalkingSpan.right ∨ j = WalkingSpan.zero := by
    intro j
    cases j with
    | none => exact Or.inr (Or.inr rfl)
    | some p =>
      cases p with
      | left => exact Or.inl rfl
      | right => exact Or.inr (Or.inl rfl)
  rcases hj j with rfl | rfl | rfl
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩
  · refine Or.inl ⟨(a.app (op ⦋n⦌)) y, ?_⟩
    have hw : a ≫ (colimit.cocone (span a b)).ι.app WalkingSpan.left =
        (colimit.cocone (span a b)).ι.app WalkingSpan.zero := by
      have hw' := (colimit.cocone (span a b)).w WalkingSpan.Hom.fst
      rwa [span_map_fst] at hw'
    have hw2 := types_congr_hom (congrArg (fun t => E.map t) hw) y
    simp only [Functor.map_comp, types_comp_apply] at hw2
    rw [← hy]
    exact hw2

section Lemma45

variable {S₀ S₁ S₂ X₀ X₁ X₂ : SSet.{u}}
  {a : S₀ ⟶ S₁} {b : S₀ ⟶ S₂} {aX : X₀ ⟶ X₁} {bX : X₀ ⟶ X₂}
  {p₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}

/-- Horn lifts against the right map of a pullback square whose
bottom simplex factors through the base of the square reduce to
horn lifts against the left map. -/
private theorem hasLift_horn_of_isPullback_factor
    {q : X ⟶ S} {p : X₁ ⟶ S₁} {inX : X₁ ⟶ X} {inS : S₁ ⟶ S}
    (sqL : IsPullback inX p q inS) [InnerFibration p]
    {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    {top : (Λ[n + 2, i] : SSet.{u}) ⟶ X} {bottom : Δ[n + 2] ⟶ S}
    (hsq : CommSq top Λ[n + 2, i].ι q bottom)
    (bottom₁ : Δ[n + 2] ⟶ S₁) (hbot : bottom₁ ≫ inS = bottom) :
    hsq.HasLift := by
  have hw : top ≫ q = (Λ[n + 2, i].ι ≫ bottom₁) ≫ inS := by
    rw [Category.assoc, hbot]
    exact hsq.w
  let top₁ : (Λ[n + 2, i] : SSet.{u}) ⟶ X₁ :=
    sqL.lift top (Λ[n + 2, i].ι ≫ bottom₁) hw
  have h1 : top₁ ≫ inX = top := sqL.lift_fst _ _ _
  have h2 : top₁ ≫ p = Λ[n + 2, i].ι ≫ bottom₁ := sqL.lift_snd _ _ _
  have hlift : HasLiftingProperty Λ[n + 2, i].ι p :=
    InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
  let sq₁ : CommSq top₁ Λ[n + 2, i].ι p bottom₁ := CommSq.mk h2
  refine CommSq.HasLift.mk' ⟨sq₁.lift ≫ inX, ?_, ?_⟩
  · rw [← Category.assoc, sq₁.fac_left, h1]
  · rw [Category.assoc, sqL.w, ← Category.assoc, sq₁.fac_right, hbot]

/-- The induced map on pushouts in Lemma 4.5 is an inner
fibration (Stevenson Remark 4.6): a horn over a simplex of the
pushout base factors, through the leg containing that simplex
and the side pullback, to a horn over `p₁` or over `p₂`. -/
theorem hasLiftingProperty_horn_pushoutMapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] [InnerFibration p₁] [InnerFibration p₂]
    {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    HasLiftingProperty Λ[n + 2, i].ι (pushoutMapOfPullbacks sq1 sq2)
    where
  sq_hasLift {top bottom} hsq := by
    rcases exists_pushout_inl_or_inr_app_eq (n + 2)
        (yonedaEquiv bottom) with ⟨σ₁, hσ₁⟩ | ⟨σ₂, hσ₂⟩
    · let bottom₁ : Δ[n + 2] ⟶ S₁ := yonedaEquiv.symm σ₁
      have hbot : bottom₁ ≫ pushout.inl a b = bottom := by
        simp only [bottom₁, yonedaEquiv_symm_comp, hσ₁,
          Equiv.symm_apply_apply]
      exact hasLift_horn_of_isPullback_factor
        (isPullback_pushoutInl_mapOfPullbacks sq1 sq2) h0 hn hsq
        bottom₁ hbot
    · let bottom₂ : Δ[n + 2] ⟶ S₂ := yonedaEquiv.symm σ₂
      have hbot : bottom₂ ≫ pushout.inr a b = bottom := by
        simp only [bottom₂, yonedaEquiv_symm_comp, hσ₂,
          Equiv.symm_apply_apply]
      exact hasLift_horn_of_isPullback_factor
        (isPullback_pushoutInr_mapOfPullbacks sq1 sq2) h0 hn hsq
        bottom₂ hbot

/-- **Remark 4.6**: the canonical map
`X₁ ∪_{X₀} X₂ → S₁ ∪_{S₀} S₂` of Lemma 4.5 is an inner
fibration. -/
theorem innerFibration_pushoutMapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] [InnerFibration p₁] [InnerFibration p₂] :
    InnerFibration (pushoutMapOfPullbacks sq1 sq2) where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_pushoutMapOfPullbacks sq1 sq2 h0 hn

/-- **Stevenson Lemma 4.5, left leg**: `p₁` satisfies descent
along `pushout.inl a b : S₁ ⟶ pushout a b`. -/
theorem satisfiesDescent_pushout_inl (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) [Mono b] [InnerFibration p₁]
    [InnerFibration p₂] :
    SatisfiesDescent p₁ (pushout.inl a b) :=
  SatisfiesDescent.of_isPullback
    (innerFibration_pushoutMapOfPullbacks sq1 sq2)
    (isPullback_pushoutInl_mapOfPullbacks sq1 sq2)

/-- **Stevenson Lemma 4.5, right leg**: `p₂` satisfies descent
along `pushout.inr a b : S₂ ⟶ pushout a b`. -/
theorem satisfiesDescent_pushout_inr (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) [Mono b] [InnerFibration p₁]
    [InnerFibration p₂] :
    SatisfiesDescent p₂ (pushout.inr a b) :=
  SatisfiesDescent.of_isPullback
    (innerFibration_pushoutMapOfPullbacks sq1 sq2)
    (isPullback_pushoutInr_mapOfPullbacks sq1 sq2)

/-- **Lemma 4.5 + Remark 4.6, inner anodyne form (right leg)**:
if moreover `aX` is inner anodyne, then the top map
`pushout.inr aX bX` is inner anodyne (cobase change), so `p₂`
satisfies *inner anodyne* descent along `pushout.inr a b`. -/
theorem satisfiesInnerAnodyneDescent_pushout_inr
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] [InnerFibration p₁] [InnerFibration p₂]
    (haX : innerAnodyneExtensions aX) :
    SatisfiesInnerAnodyneDescent p₂ (pushout.inr a b) :=
  SatisfiesInnerAnodyneDescent.of_isPullback
    (innerFibration_pushoutMapOfPullbacks sq1 sq2)
    (isPullback_pushoutInr_mapOfPullbacks sq1 sq2)
    (MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_hasPushout aX bX).flip haX)

/-- **Lemma 4.5 + Remark 4.6, inner anodyne form (left leg)**:
if moreover `bX` is inner anodyne, then `p₁` satisfies inner
anodyne descent along `pushout.inl a b`. -/
theorem satisfiesInnerAnodyneDescent_pushout_inl
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] [InnerFibration p₁] [InnerFibration p₂]
    (hbX : innerAnodyneExtensions bX) :
    SatisfiesInnerAnodyneDescent p₁ (pushout.inl a b) :=
  SatisfiesInnerAnodyneDescent.of_isPullback
    (innerFibration_pushoutMapOfPullbacks sq1 sq2)
    (isPullback_pushoutInl_mapOfPullbacks sq1 sq2)
    (MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_hasPushout aX bX) hbX)

end Lemma45

/-!
### (iii) Lemma 4.3: descent along sequential colimits

Stevenson Lemma 4.3 (§4.1) for towers `F G : ℕ ⥤ SSet` with
`p : G ⟶ F`: if every naturality square is a pullback, every
`G.map φ` is a monomorphism and every `p.app m` is an inner
fibration, then the colimit squares are pullbacks (degreewise,
by the description of filtered colimits in `Type`), the induced
map on colimits is an inner fibration (Remark 4.4, by finite
presentability of horns and simplices), and each `p.app m`
satisfies descent along `colimit.ι F m`.
-/

/-- The map on sequential colimits induced by a natural
transformation `p : G ⟶ F` of `ℕ`-diagrams, i.e. Stevenson's
`colim X_m → colim S_m` in Lemma 4.3. -/
noncomputable def colimitDescOfNatTrans {F G : ℕ ⥤ SSet.{u}}
    (p : G ⟶ F) : colimit G ⟶ colimit F :=
  colimit.desc G (Cocone.mk (colimit F)
    { app := fun k => p.app k ≫ colimit.ι F k
      naturality := by
        intro i j φ
        simp only [Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id]
        have h1 : G.map φ ≫ p.app j = p.app i ≫ F.map φ :=
          p.naturality φ
        have h2 : F.map φ ≫ colimit.ι F j = colimit.ι F i := by
          have hnat := (colimit.cocone F).ι.naturality φ
          simp
        rw [← Category.assoc, h1, Category.assoc, h2] })

/-- The legs of the colimit cocone commute with
`SSet.colimitDescOfNatTrans`. -/
@[reassoc (attr := simp)]
theorem colimit_ι_colimitDescOfNatTrans {F G : ℕ ⥤ SSet.{u}}
    (p : G ⟶ F) (k : ℕ) :
    colimit.ι G k ≫ colimitDescOfNatTrans p =
      p.app k ≫ colimit.ι F k :=
  colimit.ι_desc _ _

/-- Cocone compatibility for sequential colimits:
`F.map φ ≫ colimit.ι F j = colimit.ι F i`. -/
theorem colimit_map_ι {F : ℕ ⥤ SSet.{u}} {i j : ℕ} (φ : i ⟶ j) :
    F.map φ ≫ colimit.ι F j = colimit.ι F i :=
  (colimit.cocone F).w φ

/-- Pullback squares of simplicial sets are detected in each
degree: if the evaluated square in `Type u` is a pullback for
every `n`, the original square is a pullback. This is Mathlib's
`IsPullback.of_forall_isPullback_app` plus the observation that
every object of `SimplexCategoryᵒᵖ` is `op ⦋n⦌` for some `n`. -/
theorem isPullback_of_isPullback_app {g : X ⟶ Y} {p : X ⟶ S}
    {q : Y ⟶ T} {f : S ⟶ T}
    (h : ∀ n : ℕ, IsPullback (g.app (op ⦋n⦌)) (p.app (op ⦋n⦌))
      (q.app (op ⦋n⦌)) (f.app (op ⦋n⦌))) :
    IsPullback g p q f :=
  IsPullback.of_forall_isPullback_app (fun k ↦ by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = op ⦋n⦌ := ⟨k.unop.len, by simp⟩
    exact h n)

section Lemma43

variable {F G : ℕ ⥤ SSet.{u}} {p : G ⟶ F}

/-- Element form of a morphism equality `α ≫ β = γ` in degree
`n`. -/
private theorem app_comp_eq {A B C : SSet.{u}} {α : A ⟶ B} {β : B ⟶ C}
    {γ : A ⟶ C} (H : α ≫ β = γ) (n : ℕ) (x : A _⦋n⦌) :
    (β.app (op ⦋n⦌)) ((α.app (op ⦋n⦌)) x) = (γ.app (op ⦋n⦌)) x := by
  have h := types_congr_hom (congrArg (fun t => t.app (op ⦋n⦌)) H) x
  rwa [NatTrans.comp_app, types_comp_apply] at h

/-- The evaluated square of Lemma 4.3 in degree `n` is a
pullback in `Type u`: an element of `colim G` over an element of
`F.obj m` is represented at some stage, enlarged so the
compatibility is witnessed at a finite stage
(`Types.FilteredColimit.isColimit_eq_iff`), and then pulled
back to stage `m` by the stage pullback square; uniqueness uses
injectivity of the transition maps of `G`. -/
theorem isPullback_app_colimit_ι
    (hsq : ∀ {m k : ℕ} (φ : m ⟶ k),
      IsPullback (G.map φ) (p.app m) (p.app k) (F.map φ))
    (hmono : ∀ {m k : ℕ} (φ : m ⟶ k), Mono (G.map φ))
    (m n : ℕ) :
    IsPullback ((colimit.ι G m).app (op ⦋n⦌)) ((p.app m).app (op ⦋n⦌))
      ((colimitDescOfNatTrans p).app (op ⦋n⦌))
      ((colimit.ι F m).app (op ⦋n⦌)) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌)
  have hcG : IsColimit (E.mapCocone (colimit.cocone G)) :=
    isColimitOfPreserves E (colimit.isColimit G)
  have hcF : IsColimit (E.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves E (colimit.isColimit F)
  rw [Types.isPullback_iff ((colimit.ι G m).app (op ⦋n⦌))
    ((colimitDescOfNatTrans p).app (op ⦋n⦌)) ((p.app m).app (op ⦋n⦌))
    ((colimit.ι F m).app (op ⦋n⦌))]
  refine ⟨?_, ?_, ?_⟩
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app,
      colimit_ι_colimitDescOfNatTrans]
  · intro x₁ y₁ h
    obtain ⟨j, φ, hφ⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcG x₁ y₁).mp h.1
    have hinj : Function.Injective ((G.map φ).app (op ⦋n⦌)) := by
      have : Mono (G.map φ) := hmono φ
      exact CategoryTheory.injective_of_mono _
    exact hinj hφ
  · intro x s hxs
    obtain ⟨k, xk, hk⟩ := Types.jointly_surjective_of_isColimit hcG x
    set l₀ := max k m with hl₀
    let φk : k ⟶ l₀ := homOfLE (Nat.le_max_left k m)
    let φm : m ⟶ l₀ := homOfLE (Nat.le_max_right k m)
    let xl₀ : (G.obj l₀) _⦋n⦌ := ((G.map φk).app (op ⦋n⦌)) xk
    have e1 : ((colimit.ι G l₀).app (op ⦋n⦌)) xl₀ = x := by
      have h1 := app_comp_eq (colimit_map_ι φk) n xk
      rw [h1]
      exact hk
    have hq : ((colimitDescOfNatTrans p).app (op ⦋n⦌)) x =
        ((colimit.ι F l₀).app (op ⦋n⦌))
          (((p.app l₀).app (op ⦋n⦌)) xl₀) := by
      rw [← e1]
      exact app_comp_eq (colimit_ι_colimitDescOfNatTrans p l₀) n xl₀
    have hιF : ((colimit.ι F m).app (op ⦋n⦌)) s =
        ((colimit.ι F l₀).app (op ⦋n⦌)) (((F.map φm).app (op ⦋n⦌)) s) :=
      (app_comp_eq (colimit_map_ι φm) n s).symm
    have heq : ((colimit.ι F l₀).app (op ⦋n⦌))
          (((p.app l₀).app (op ⦋n⦌)) xl₀) =
        ((colimit.ι F l₀).app (op ⦋n⦌)) (((F.map φm).app (op ⦋n⦌)) s) := by
      rw [← hq, hxs, hιF]
    obtain ⟨j, f₁, f₂, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff (F ⋙ E) hcF).mp heq
    have hff : f₁ = f₂ := Subsingleton.elim _ _
    subst hff
    let xj : (G.obj j) _⦋n⦌ := ((G.map f₁).app (op ⦋n⦌)) xl₀
    have hnat : ((p.app j).app (op ⦋n⦌)) xj =
        ((F.map f₁).app (op ⦋n⦌)) (((p.app l₀).app (op ⦋n⦌)) xl₀) :=
      app_comp_eq (p.naturality f₁) n xl₀
    have hcompF : ((F.map f₁).app (op ⦋n⦌))
          (((F.map φm).app (op ⦋n⦌)) s) =
        ((F.map (φm ≫ f₁)).app (op ⦋n⦌)) s :=
      app_comp_eq (F.map_comp φm f₁).symm n s
    have hf' : ((F.map f₁).app (op ⦋n⦌))
          (((p.app l₀).app (op ⦋n⦌)) xl₀) =
        ((F.map f₁).app (op ⦋n⦌)) (((F.map φm).app (op ⦋n⦌)) s) := hf
    have hstage : ((p.app j).app (op ⦋n⦌)) xj =
        ((F.map (φm ≫ f₁)).app (op ⦋n⦌)) s := by
      rw [hnat, hf', hcompF]
    obtain ⟨xm, hxm1, hxm2⟩ :=
      Types.exists_of_isPullback ((hsq (φm ≫ f₁)).map E) xj s hstage
    have hxm1' : ((G.map (φm ≫ f₁)).app (op ⦋n⦌)) xm = xj := hxm1
    have hxm2' : ((p.app m).app (op ⦋n⦌)) xm = s := hxm2
    refine ⟨xm, ?_, hxm2'⟩
    have step1 : ((colimit.ι G m).app (op ⦋n⦌)) xm =
        ((colimit.ι G j).app (op ⦋n⦌)) xj := by
      rw [← app_comp_eq (colimit_map_ι (φm ≫ f₁)) n xm, hxm1']
    have step2 : ((colimit.ι G j).app (op ⦋n⦌)) xj =
        ((colimit.ι G l₀).app (op ⦋n⦌)) xl₀ :=
      app_comp_eq (colimit_map_ι f₁) n xl₀
    rw [step1, step2, e1]

/-- The colimit squares of Lemma 4.3 are pullbacks. -/
theorem isPullback_colimit_ι
    (hsq : ∀ {m k : ℕ} (φ : m ⟶ k),
      IsPullback (G.map φ) (p.app m) (p.app k) (F.map φ))
    (hmono : ∀ {m k : ℕ} (φ : m ⟶ k), Mono (G.map φ)) (m : ℕ) :
    IsPullback (colimit.ι G m) (p.app m) (colimitDescOfNatTrans p)
      (colimit.ι F m) :=
  isPullback_of_isPullback_app (fun n => isPullback_app_colimit_ι hsq hmono m n)

/-- A map from a finite simplicial set into a sequential
colimit factors through some stage (finite presentability,
`Mathlib.AlgebraicTopology.SimplicialSet.Presentable`). -/
private theorem exists_comp_colimit_ι_eq {A : SSet.{u}} [A.Finite]
    {H : ℕ ⥤ SSet.{u}} (f : A ⟶ colimit H) :
    ∃ (j : ℕ) (f_j : A ⟶ H.obj j), f_j ≫ colimit.ι H j = f := by
  have := Cardinal.fact_isRegular_aleph0.{u}
  have : IsCardinalFiltered ℕ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff ℕ).mpr inferInstance
  exact IsCardinalPresentable.exists_hom_of_isColimit
    Cardinal.aleph0.{u} (colimit.isColimit H) f

/-- Two maps from a finite simplicial set into a stage of a
sequential colimit that become equal in the colimit become
equal at some later stage (finite presentability). -/
private theorem exists_map_eq_of_colimit_ι_eq {A : SSet.{u}}
    [A.Finite] {H : ℕ ⥤ SSet.{u}} {m : ℕ} (α β : A ⟶ H.obj m)
    (h : α ≫ colimit.ι H m = β ≫ colimit.ι H m) :
    ∃ (j : ℕ) (w : m ⟶ j), α ≫ H.map w = β ≫ H.map w := by
  have := Cardinal.fact_isRegular_aleph0.{u}
  have : IsCardinalFiltered ℕ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff ℕ).mpr inferInstance
  exact IsCardinalPresentable.exists_eq_of_isColimit'
    Cardinal.aleph0.{u} (colimit.isColimit H) α β h

/-- Horn lifting against the colimit map of Lemma 4.3: the
lifting problem factors through a single stage (Stevenson's
diagram (6)), where the stage map is an inner fibration. -/
theorem hasLiftingProperty_horn_colimitDescOfNatTrans
    (hp : ∀ m : ℕ, InnerFibration (p.app m))
    {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    HasLiftingProperty Λ[n + 2, i].ι (colimitDescOfNatTrans p) where
  sq_hasLift {top bottom} hsq := by
    obtain ⟨j1, top1, htop1⟩ := exists_comp_colimit_ι_eq top
    obtain ⟨j2, bot2, hbot2⟩ := exists_comp_colimit_ι_eq bottom
    set m := max j1 j2 with hm
    let φ1 : j1 ⟶ m := homOfLE (Nat.le_max_left j1 j2)
    let φ2 : j2 ⟶ m := homOfLE (Nat.le_max_right j1 j2)
    let top_m : (Λ[n + 2, i] : SSet.{u}) ⟶ G.obj m := top1 ≫ G.map φ1
    let bot_m : Δ[n + 2] ⟶ F.obj m := bot2 ≫ F.map φ2
    have htop_m : top_m ≫ colimit.ι G m = top := by
      change (top1 ≫ G.map φ1) ≫ colimit.ι G m = top
      rw [Category.assoc, colimit_map_ι, htop1]
    have hbot_m : bot_m ≫ colimit.ι F m = bottom := by
      change (bot2 ≫ F.map φ2) ≫ colimit.ι F m = bottom
      rw [Category.assoc, colimit_map_ι, hbot2]
    have hαβ : (top_m ≫ p.app m) ≫ colimit.ι F m =
        (Λ[n + 2, i].ι ≫ bot_m) ≫ colimit.ι F m := by
      have e1 : top_m ≫ p.app m ≫ colimit.ι F m =
          top ≫ colimitDescOfNatTrans p := by
        rw [← colimit_ι_colimitDescOfNatTrans, ← Category.assoc,
          htop_m]
      simp only [Category.assoc]
      rw [e1, hsq.w, hbot_m]
    obtain ⟨j, w, hw⟩ :=
      exists_map_eq_of_colimit_ι_eq _ _ hαβ
    let top_j : (Λ[n + 2, i] : SSet.{u}) ⟶ G.obj j := top_m ≫ G.map w
    let bot_j : Δ[n + 2] ⟶ F.obj j := bot_m ≫ F.map w
    have hsqj : top_j ≫ p.app j = Λ[n + 2, i].ι ≫ bot_j := by
      calc top_j ≫ p.app j
          = top_m ≫ p.app m ≫ F.map w := by
            change (top_m ≫ G.map w) ≫ p.app j = _
            rw [Category.assoc, p.naturality, ← Category.assoc]
        _ = Λ[n + 2, i].ι ≫ bot_j := by
            rw [← Category.assoc, hw, Category.assoc]
    have hlift : HasLiftingProperty Λ[n + 2, i].ι (p.app j) := by
      have := hp j
      exact InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
    let sqj : CommSq top_j Λ[n + 2, i].ι (p.app j) bot_j :=
      CommSq.mk hsqj
    refine CommSq.HasLift.mk' ⟨sqj.lift ≫ colimit.ι G j, ?_, ?_⟩
    · calc Λ[n + 2, i].ι ≫ sqj.lift ≫ colimit.ι G j
          = top_j ≫ colimit.ι G j := by
            rw [← Category.assoc, sqj.fac_left]
        _ = top := by
            change (top_m ≫ G.map w) ≫ colimit.ι G j = top
            rw [Category.assoc, colimit_map_ι, htop_m]
    · calc (sqj.lift ≫ colimit.ι G j) ≫ colimitDescOfNatTrans p
          = bot_j ≫ colimit.ι F j := by
            rw [Category.assoc, colimit_ι_colimitDescOfNatTrans,
              ← Category.assoc, sqj.fac_right]
        _ = bottom := by
            change (bot_m ≫ F.map w) ≫ colimit.ι F j = bottom
            rw [Category.assoc, colimit_map_ι, hbot_m]

/-- **Remark 4.4**: the induced map `colim X_m → colim S_m` of
Lemma 4.3 is an inner fibration. -/
theorem innerFibration_colimitDescOfNatTrans
    (hp : ∀ m : ℕ, InnerFibration (p.app m)) :
    InnerFibration (colimitDescOfNatTrans p) where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_colimitDescOfNatTrans hp h0 hn

/-- **Stevenson Lemma 4.3**: with every naturality square a
pullback, every `G.map φ` a monomorphism and every `p.app m` an
inner fibration, each `p.app m` satisfies descent along the
canonical map `colimit.ι F m` to the sequential colimit. -/
theorem satisfiesDescent_colimit_ι
    (hsq : ∀ {m k : ℕ} (φ : m ⟶ k),
      IsPullback (G.map φ) (p.app m) (p.app k) (F.map φ))
    (hmono : ∀ {m k : ℕ} (φ : m ⟶ k), Mono (G.map φ))
    (hp : ∀ m : ℕ, InnerFibration (p.app m)) (m : ℕ) :
    SatisfiesDescent (p.app m) (colimit.ι F m) :=
  SatisfiesDescent.of_isPullback
    (innerFibration_colimitDescOfNatTrans hp)
    (isPullback_colimit_ι hsq hmono m)

/-- **Lemma 4.3, inner anodyne form**: if moreover the stage
inclusion `colimit.ι G m` is inner anodyne, descent along
`colimit.ι F m` is inner anodyne descent. (Inner anodyneness of
the `colimit.ι G m` from inner anodyneness of the successor maps is
`SSet.innerAnodyneExtensions_colimit_ι_of_succ` below.) -/
theorem satisfiesInnerAnodyneDescent_colimit_ι
    (hsq : ∀ {m k : ℕ} (φ : m ⟶ k),
      IsPullback (G.map φ) (p.app m) (p.app k) (F.map φ))
    (hmono : ∀ {m k : ℕ} (φ : m ⟶ k), Mono (G.map φ))
    (hp : ∀ m : ℕ, InnerFibration (p.app m)) (m : ℕ)
    (hg : innerAnodyneExtensions (colimit.ι G m)) :
    SatisfiesInnerAnodyneDescent (p.app m) (colimit.ι F m) :=
  SatisfiesInnerAnodyneDescent.of_isPullback
    (innerFibration_colimitDescOfNatTrans hp)
    (isPullback_colimit_ι hsq hmono m) hg

/-- The transfinite composition structure on a sequential
diagram whose successor maps are inner anodyne: the diagram
itself, with the chosen colimit cocone. -/
noncomputable def transfiniteCompositionOfSequence
    (G : ℕ ⥤ SSet.{u})
    (hsucc : ∀ m : ℕ,
      innerAnodyneExtensions (G.map (homOfLE (Nat.le_succ m)))) :
    innerAnodyneExtensions.TransfiniteCompositionOfShape ℕ
      (colimit.ι G 0) :=
  { F := G
    isoBot := Iso.refl _
    incl := (colimit.cocone G).ι
    isColimit := colimit.isColimit G
    fac := by simp
    map_mem := by
      intro j _
      have heq : (homOfLE (Order.le_succ j) : j ⟶ Order.succ j) =
          homOfLE (Nat.le_succ j) := Subsingleton.elim _ _
      rw [heq]
      exact hsucc j }

/-- If the successor maps of a sequential diagram are inner
anodyne, every canonical map `colimit.ι G m` to the colimit is
inner anodyne (transfinite composition). -/
theorem innerAnodyneExtensions_colimit_ι_of_succ
    (G : ℕ ⥤ SSet.{u})
    (hsucc : ∀ m : ℕ,
      innerAnodyneExtensions (G.map (homOfLE (Nat.le_succ m))))
    (m : ℕ) :
    innerAnodyneExtensions (colimit.ι G m) :=
  (transfiniteCompositionOfSequence G hsucc).mem_incl_app m

/-- If the successor maps of a sequential diagram are inner
anodyne, every transition map `G.map φ` is inner anodyne. -/
theorem innerAnodyneExtensions_map_of_succ
    (G : ℕ ⥤ SSet.{u})
    (hsucc : ∀ m : ℕ,
      innerAnodyneExtensions (G.map (homOfLE (Nat.le_succ m))))
    {m k : ℕ} (φ : m ⟶ k) :
    innerAnodyneExtensions (G.map φ) :=
  (transfiniteCompositionOfSequence G hsucc).mem_map φ

/-- **Lemma 4.3, inner anodyne form from successor maps**: with
pullback naturality squares, inner fibration stages, and inner
anodyne successor maps in the top row (which give inner
anodyneness of all top transition maps, hence their
monomorphicity, and of the colimit inclusions), each
`p.app m` satisfies inner anodyne descent along
`colimit.ι F m`. -/
theorem satisfiesInnerAnodyneDescent_colimit_ι_of_succ
    (hsq : ∀ {m k : ℕ} (φ : m ⟶ k),
      IsPullback (G.map φ) (p.app m) (p.app k) (F.map φ))
    (hp : ∀ m : ℕ, InnerFibration (p.app m))
    (hsucc : ∀ m : ℕ,
      innerAnodyneExtensions (G.map (homOfLE (Nat.le_succ m))))
    (m : ℕ) :
    SatisfiesInnerAnodyneDescent (p.app m) (colimit.ι F m) :=
  satisfiesInnerAnodyneDescent_colimit_ι hsq
    (fun φ => innerAnodyneExtensions_le_monomorphisms_of_llp _
      (innerAnodyneExtensions_map_of_succ G hsucc φ)) hp m
    (innerAnodyneExtensions_colimit_ι_of_succ G hsucc m)

end Lemma43

/-!
### (iv) Proposition 4.7: from stagewise descent to descent
along `S → colim S(m)`

Given a tower `F : ℕ ⥤ SSet` (Stevenson's `S = S(0) → S(1) →
⋯`) such that every inner fibration over every stage satisfies
inner anodyne descent along the successor map (the conclusion
of the one-step cell attachment; its derivation from Lemma 4.8
and Proposition 4.11 through Lemma 4.5 is the named input
`SSet.HornDescent412` plus the additional comparison obligation below), an
inner fibration over `F.obj 0` assembles, by dependent choice,
into a tower of inner fibrations with pullback squares and
inner anodyne successor maps; Lemma 4.3 then gives inner
anodyne descent along `colimit.ι F 0`.
-/

section Prop47

variable {F : ℕ ⥤ SSet.{u}} {X₀ : SSet.{u}}
variable (hstage : ∀ (m : ℕ) {Y : SSet.{u}} (q : Y ⟶ F.obj m),
  InnerFibration q →
    SatisfiesInnerAnodyneDescent q (F.map (homOfLE (Nat.le_succ m))))

include hstage in
/-- One step of the dependent choice in Proposition 4.7 always
exists: if `q` is an inner fibration it is the descent datum
supplied by `hstage`; otherwise it is junk data never used
along the constructed tower. -/
theorem exists_towerStepData (m : ℕ) (Y : SSet.{u})
    (q : Y ⟶ F.obj m) :
    ∃ (s : Σ (Y' : SSet.{u}) (_q' : Y' ⟶ F.obj (m + 1)), Y ⟶ Y'),
      InnerFibration q → InnerFibration s.2.1 ∧
        IsPullback s.2.2 q s.2.1 (F.map (homOfLE (Nat.le_succ m))) ∧
        innerAnodyneExtensions s.2.2 := by
  by_cases h : InnerFibration q
  · obtain ⟨Y', q', g, h1, h2, h3⟩ := hstage m q h
    exact ⟨⟨Y', q', g⟩, fun _ => ⟨h1, h2, h3⟩⟩
  · exact ⟨⟨Y, q ≫ F.map (homOfLE (Nat.le_succ m)), 𝟙 Y⟩,
      fun hh => absurd hh h⟩

/-- The chosen one-step data of Proposition 4.7: a simplicial
set over the next stage, its inner fibration, and the
comparison map. -/
noncomputable def towerStepData (m : ℕ) (Y : SSet.{u})
    (q : Y ⟶ F.obj m) :
    Σ (Y' : SSet.{u}) (_q' : Y' ⟶ F.obj (m + 1)), Y ⟶ Y' :=
  Classical.choose (exists_towerStepData hstage m Y q)

/-- The chosen one-step data is a genuine inner anodyne
descent datum whenever the input map is an inner fibration. -/
theorem towerStepData_spec {m : ℕ} (Y : SSet.{u})
    (q : Y ⟶ F.obj m) (h : InnerFibration q) :
    InnerFibration (towerStepData hstage m Y q).2.1 ∧
      IsPullback (towerStepData hstage m Y q).2.2 q
        (towerStepData hstage m Y q).2.1
        (F.map (homOfLE (Nat.le_succ m))) ∧
      innerAnodyneExtensions (towerStepData hstage m Y q).2.2 :=
  Classical.choose_spec (exists_towerStepData hstage m Y q) h

/-- The stage-`m` state of the tower built from `p₀` by
dependent choice: a simplicial set over `F.obj m`. -/
-- Written with an explicit `match`: arms after the signature
-- currently misparse under this import closure.
noncomputable def towerState (p₀ : X₀ ⟶ F.obj 0) :
    (m : ℕ) → Σ (Y : SSet.{u}), Y ⟶ F.obj m := fun m =>
  match m with
  | 0 => ⟨X₀, p₀⟩
  | m + 1 =>
    let s := towerState p₀ m
    let d := towerStepData hstage m s.1 s.2
    ⟨d.1, d.2.1⟩

/-- The tower starts at the given inner fibration. -/
theorem towerState_zero (p₀ : X₀ ⟶ F.obj 0) :
    towerState hstage p₀ 0 = ⟨X₀, p₀⟩ := rfl

/-- Every stage map of the constructed tower is an inner
fibration. -/
theorem innerFibration_towerState_snd (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    InnerFibration (towerState hstage p₀ m).2 := by
  induction m with
  | zero => exact inferInstanceAs (InnerFibration p₀)
  | succ m ih => exact (towerStepData_spec hstage _ _ ih).1

/-- The successor comparison map of the constructed tower. -/
noncomputable def towerStepMap (p₀ : X₀ ⟶ F.obj 0) (m : ℕ) :
    (towerState hstage p₀ m).1 ⟶ (towerState hstage p₀ (m + 1)).1 :=
  (towerStepData hstage m _ _).2.2

/-- The successor squares of the constructed tower are
pullbacks. -/
theorem isPullback_towerStepMap (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    IsPullback (towerStepMap hstage p₀ m) (towerState hstage p₀ m).2
      (towerState hstage p₀ (m + 1)).2
      (F.map (homOfLE (Nat.le_succ m))) :=
  (towerStepData_spec hstage _ _
    (innerFibration_towerState_snd hstage p₀ m)).2.1

/-- The successor maps of the constructed tower are inner
anodyne. -/
theorem innerAnodyneExtensions_towerStepMap (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    innerAnodyneExtensions (towerStepMap hstage p₀ m) :=
  (towerStepData_spec hstage _ _
    (innerFibration_towerState_snd hstage p₀ m)).2.2

/-- The constructed tower as a functor `ℕ ⥤ SSet`. -/
noncomputable def towerFunctor (p₀ : X₀ ⟶ F.obj 0) :
    ℕ ⥤ SSet.{u} :=
  Functor.ofSequence (towerStepMap hstage p₀)

/-- The constructed tower lies over `F`. -/
noncomputable def towerNatTrans (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] : towerFunctor hstage p₀ ⟶ F :=
  NatTrans.ofSequence (fun m => (towerState hstage p₀ m).2) (fun m => by
    have hsucc := (isPullback_towerStepMap hstage p₀ m).w
    have e1 : (towerFunctor hstage p₀).map
        (homOfLE (Nat.le_add_right m 1)) = towerStepMap hstage p₀ m :=
      Functor.ofSequence_map_homOfLE_succ (towerStepMap hstage p₀) m
    have e2 : (homOfLE (Nat.le_add_right m 1) : m ⟶ m + 1) =
        homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
    rw [e1, e2]
    exact hsucc)

/-- The successor squares of the constructed tower, in functor
form, are pullbacks. -/
theorem isPullback_tower_succ (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    IsPullback
      ((towerFunctor hstage p₀).map (homOfLE (Nat.le_succ m)))
      ((towerNatTrans hstage p₀).app m)
      ((towerNatTrans hstage p₀).app (m + 1))
      (F.map (homOfLE (Nat.le_succ m))) := by
  have e1 : (towerFunctor hstage p₀).map (homOfLE (Nat.le_succ m)) =
      towerStepMap hstage p₀ m := by
    have e2 : (homOfLE (Nat.le_succ m) : m ⟶ m + 1) =
        homOfLE (Nat.le_add_right m 1) := Subsingleton.elim _ _
    rw [e2]
    exact Functor.ofSequence_map_homOfLE_succ (towerStepMap hstage p₀) m
  rw [e1]
  exact isPullback_towerStepMap hstage p₀ m

/-- Every naturality square of the constructed tower is a
pullback, by pasting successor pullbacks. -/
theorem isPullback_tower_map (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] {m k : ℕ} (φ : m ⟶ k) :
    IsPullback ((towerFunctor hstage p₀).map φ)
      ((towerNatTrans hstage p₀).app m)
      ((towerNatTrans hstage p₀).app k) (F.map φ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
  obtain rfl : φ = homOfLE (Nat.le_add_right m d) :=
    Subsingleton.elim _ _
  induction d generalizing m with
  | zero =>
    simp only [Nat.add_zero]
    have eG : (towerFunctor hstage p₀).map
        (homOfLE (Nat.le_add_right m 0)) = 𝟙 _ := by
      rw [show (homOfLE (Nat.le_add_right m 0) : m ⟶ m + 0) = 𝟙 m from
        Subsingleton.elim _ _]
      simp
    have eF : F.map (homOfLE (Nat.le_add_right m 0)) = 𝟙 _ := by
      rw [show (homOfLE (Nat.le_add_right m 0) : m ⟶ m + 0) = 𝟙 m from
        Subsingleton.elim _ _]
      simp
    rw [eG, eF]
    exact IsPullback.of_id_fst
  | succ d ih =>
    have hcompG : (homOfLE (Nat.le_add_right m (d + 1)) :
        m ⟶ m + (d + 1)) =
        homOfLE (Nat.le_add_right m d) ≫
          homOfLE (show m + d ≤ m + (d + 1) by omega) :=
      Subsingleton.elim _ _
    have esucc : (homOfLE (show m + d ≤ m + (d + 1) by omega) :
        m + d ⟶ m + (d + 1)) = homOfLE (Nat.le_succ (m + d)) :=
      Subsingleton.elim _ _
    rw [hcompG, Functor.map_comp, Functor.map_comp, esucc]
    exact IsPullback.paste_horiz (ih (m := m))
      (isPullback_tower_succ hstage p₀ (m + d))

/-- The transfinite composition structure of the constructed
tower: its successor maps are inner anodyne. -/
noncomputable def towerTransfinite (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] :
    innerAnodyneExtensions.TransfiniteCompositionOfShape ℕ
      (colimit.ι (towerFunctor hstage p₀) 0) :=
  { F := towerFunctor hstage p₀
    isoBot := Iso.refl _
    incl := (colimit.cocone _).ι
    isColimit := colimit.isColimit _
    fac := by simp
    map_mem := by
      intro j _
      have e1 : (towerFunctor hstage p₀).map
          (homOfLE (Order.le_succ j)) = towerStepMap hstage p₀ j := by
        have e2 : (homOfLE (Order.le_succ j) : j ⟶ Order.succ j) =
            homOfLE (Nat.le_add_right j 1) := Subsingleton.elim _ _
        rw [e2]
        exact Functor.ofSequence_map_homOfLE_succ
          (towerStepMap hstage p₀) j
      rw [e1]
      exact innerAnodyneExtensions_towerStepMap hstage p₀ j }

include hstage in
/-- **Stevenson Proposition 4.7, formal core**: if every inner
fibration over every stage of the tower `F` satisfies inner
anodyne descent along the successor map, then every inner
fibration over `F.obj 0` satisfies inner anodyne descent along
`colimit.ι F 0 : F.obj 0 ⟶ colimit F`. The top tower is built
by dependent choice, its transition maps and colimit inclusions
are inner anodyne by transfinite composition (hence the
transition maps are monomorphisms), and Lemma 4.3 concludes. -/
theorem satisfiesInnerAnodyneDescent_colimit_zero_of_stagewise
    (p₀ : X₀ ⟶ F.obj 0) [InnerFibration p₀] :
    SatisfiesInnerAnodyneDescent p₀ (colimit.ι F 0) := by
  have hg : innerAnodyneExtensions
      (colimit.ι (towerFunctor hstage p₀) 0) :=
    MorphismProperty.transfiniteCompositionsOfShape_le
      innerAnodyneExtensions ℕ _ (towerTransfinite hstage p₀).mem
  have hmono : ∀ {m k : ℕ} (φ : m ⟶ k),
      Mono ((towerFunctor hstage p₀).map φ) := by
    intro m k φ
    exact innerAnodyneExtensions_le_monomorphisms_of_llp _
      ((towerTransfinite hstage p₀).mem_map φ)
  have hdesc := satisfiesInnerAnodyneDescent_colimit_ι
    (F := F) (G := towerFunctor hstage p₀)
    (p := towerNatTrans hstage p₀)
    (fun φ => isPullback_tower_map hstage p₀ φ) hmono
    (fun m => innerFibration_towerState_snd hstage p₀ m) 0 hg
  exact hdesc

end Prop47

/-!
### (iv) Selected-horn descent and pre-fibrant replacement

`SSet.HornDescent412` records descent for the selected two-dimensional and
constant-back-face horn cells. `SSet.SelectiveTower412Exists` records a tower
with stagewise descent and pre-fibrant colimit. Given this tower, the dependent
sequential assembly above proves the pre-fibrant replacement property. The
one-step construction from the horn-cell hypothesis is in `SelectiveTower.lean`.
Neither statement requires a quasicategory replacement preserving naive mapping
spaces.
-/

set_option linter.unusedVariables false in
/-- The joint conclusion of Stevenson's Lemma 4.8 and
Proposition 4.11 for the cells of Proposition 4.12: for every
horn map `α : Λ[n+2, i] ⟶ S` with `n = 0` (i.e. `Λ²₁`) or with
`d₀α` a constant simplex, and every inner fibration `pz` over
`S`, the pullback `α*pz` satisfies inner anodyne descent along
the horn inclusion. Neither Lemma 4.8 (the additional comparison obligation) nor
Proposition 4.11 (the additional comparison obligation, §8 of the paper, needing
(co)cartesian edges of inner fibrations) is formalized; this
predicate names exactly their needed output. -/
def HornDescent412 : Prop :=
  ∀ {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i)
    (hn : i < Fin.last (n + 2)) {S : SSet.{u}}
    (α : (Λ[n + 2, i] : SSet.{u}) ⟶ S),
    (n = 0 ∨ IsConstantSimplex (hornFaceZero α (ne_of_lt h0))) →
    ∀ {Z : SSet.{u}} (pz : Z ⟶ S), InnerFibration pz →
      SatisfiesInnerAnodyneDescent (pullback.snd pz α) Λ[n + 2, i].ι

/-- The output of Stevenson's selective small object argument
(§4.2) for Proposition 4.12, with the stagewise descent
conclusion needed by Proposition 4.7: for every simplicial set
`S` a tower `F` with `F.obj 0 = S`, pre-fibrant colimit, inner
anodyne successor maps, and inner anodyne descent of every
inner fibration along every successor map. The construction of
`F` (attaching the cells `A_m`) is the additional comparison obligation;
the stagewise clause follows from `SSet.HornDescent412` by
Lemma 4.5 over a coproduct of cells (the additional comparison obligation). -/
def SelectiveTower412Exists : Prop :=
  ∀ S : SSet.{u}, ∃ (F : ℕ ⥤ SSet.{u}),
    F.obj 0 = S ∧ IsPreFibrant (colimit F) ∧
    (∀ m : ℕ, innerAnodyneExtensions (F.map (homOfLE (Nat.le_succ m)))) ∧
    ∀ (m : ℕ) {Z : SSet.{u}} (pz : Z ⟶ F.obj m), InnerFibration pz →
      SatisfiesInnerAnodyneDescent pz (F.map (homOfLE (Nat.le_succ m)))

/-- **Stevenson Proposition 4.12, from the selective tower**:
the uniform replacement hypothesis
`SSet.PreFibrantDescentReplacementExists`
follows from `SSet.SelectiveTower412Exists`. Given `S`, take
`T := colimit F` and `f := colimit.ι F 0`: `f` is inner
anodyne by transfinite composition
(`SSet.innerAnodyneExtensions_colimit_ι_of_succ`), every inner
fibration over `S` descends along `f` by Proposition 4.7's
formal core
(`SSet.satisfiesInnerAnodyneDescent_colimit_zero_of_stagewise`),
and vertex bijectivity is automatic (§0). -/
theorem preFibrantDescentReplacementExists_of_selectiveTower
    (h : SelectiveTower412Exists.{u}) :
    PreFibrantDescentReplacementExists.{u} := by
  apply preFibrantDescentReplacementExists_of_innerAnodyne
  intro S
  obtain ⟨F, hF0, hpre, hsucc, hstage⟩ := h S
  subst hF0
  refine ⟨colimit F, colimit.ι F 0,
    innerAnodyneExtensions_colimit_ι_of_succ F hsucc 0, hpre, ?_⟩
  intro Z pz hpz
  have : InnerFibration pz := hpz
  exact satisfiesInnerAnodyneDescent_colimit_zero_of_stagewise
    hstage pz

end SSet

end
