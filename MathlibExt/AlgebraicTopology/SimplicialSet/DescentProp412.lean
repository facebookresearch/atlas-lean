/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
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
# Pullback descent, sequential towers, and conditional replacement comparisons

Pullback descent for inner fibrations is stable under the stated pushout and sequential
colimit hypotheses. Stagewise inner-anodyne descent along a base tower constructs a
dependent tower of inner fibrations with pullback squares and inner-anodyne successor
maps, giving descent from the initial stage to the colimit.

Selected-horn descent and selective towers provide conditions for prefibrant-target
descent replacement. Separately, a pointwise mapping-preserving quasicategory
replacement is an inner-anodyne map to a quasicategory inducing isomorphisms on all
left mapping spaces. The categorical-equivalence comparisons here retain this
replacement data and the stated Kan and quasicategory criteria as explicit hypotheses.
Campbell's prefibrant counterexample prevents uniform existence of that stronger
mapping-preserving replacement condition.

See Stevenson, Notes on the Joyal model structure, arXiv:1810.05233v1, §4, and
Campbell, A counterexample in quasi-category theory, arXiv:1904.04965v3,
Definition 2.1, Lemma 2.3, and Theorem 2.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {S T X Y Z : SSet.{u}}

/-!
## Vertices of inner-anodyne maps

Inner horn inclusions are bijective on vertices, and this property is preserved
by their weak saturation. Thus every inner-anodyne base map has the vertex
bijectivity used in prefibrant descent data.
-/

/--
Every inner-anodyne map of simplicial sets is bijective on zero-simplices.
-/
theorem bijective_app_zero_of_innerAnodyneExtensions {f : X ⟶ Y}
    (hf : innerAnodyneExtensions f) :
    Function.Bijective (f.app (op ⦋0⦌)) :=
  (isVertexBijective_iff f).mp
    (isVertexBijective_of_innerAnodyneExtensions hf)

/--
Inner-anodyne descent of `p : X → S` along an inner-anodyne map `S → T` with
prefibrant target gives a prefibrant descent datum for `p`. Vertex bijectivity of
the base map follows from inner anodyneness.
-/
theorem hasPreFibrantDescentDatum_of_innerAnodyne {p : X ⟶ S}
    {f : S ⟶ T} (hf : innerAnodyneExtensions f) [IsPreFibrant T]
    (h : SatisfiesInnerAnodyneDescent p f) :
    HasPreFibrantDescentDatum p :=
  ⟨T, f, hf, inferInstance,
    bijective_app_zero_of_innerAnodyneExtensions hf, h⟩

/--
If every simplicial set admits an inner-anodyne map to a prefibrant target along
which every inner fibration has inner-anodyne descent, then uniform prefibrant
descent replacement exists; vertex bijectivity of the base maps is automatic.
-/
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
## Left mapping-space homotopy criteria

A left mapping-space map is described by postcomposition on its successor-simplex
coordinates. With Kan source and target mapping spaces, bijectivity on connected
components and positive based homotopy groups gives a realization weak equivalence.
The resulting full-faithfulness predicate is closed under composition and the stated
cancellation operations.
-/

/--
The condition that `Homᴸ_X(a,b)` is a Kan complex for every pair of vertices
`a,b : Δ[0] → X`.
-/
def LeftMappingSpacesKan (X : SSet.{u}) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X, KanComplex (mappingSpaceLeft X a b)

namespace mappingSpaceLeft

variable (X : SSet.{u}) (a b : (Δ[0] : SSet.{u}) ⟶ X)

/--
When an `n`-simplex of a left mapping space is represented as an `(n + 1)`-simplex
of `X`, the mapping-space map induced by `F : X → Y` is postcomposition with `F`.
-/
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

/--
If all relevant source and target left mapping spaces are Kan complexes and each
induced map is bijective on connected components and all positive based homotopy
groups, the simplicial map is fully faithful on left mapping spaces.
-/
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

/--
If `f ≫ g` and `g ≫ f` are both fully faithful on left mapping spaces, then `f`
is fully faithful on left mapping spaces.
-/
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

/--
The condition that a simplicial map is essentially surjective on homotopy categories
and fully faithful on left mapping spaces.
-/
def isDwyerKanEquivalenceLeft (f : X ⟶ Y) : Prop :=
  dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithfulLeft f

/--
A left mapping-space Dwyer–Kan equivalence is essentially surjective on homotopy
categories.
-/
theorem isDwyerKanEquivalenceLeft.dwyerKanEssentiallySurjective
    (h : isDwyerKanEquivalenceLeft f) :
    dwyerKanEssentiallySurjective f :=
  h.1

/--
A left mapping-space Dwyer–Kan equivalence is fully faithful on left mapping spaces.
-/
theorem isDwyerKanEquivalenceLeft.dwyerKanFullyFaithfulLeft
    (h : isDwyerKanEquivalenceLeft f) :
    dwyerKanFullyFaithfulLeft f :=
  h.2

/--
A categorical equivalence is a left Dwyer–Kan equivalence if its relevant left
mapping spaces are Kan and their induced maps are bijective on connected components
and every positive based homotopy group.
-/
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
## Pointwise mapping-preserving quasicategory replacements

An inner-anodyne map to a quasicategory that induces isomorphisms on all left
mapping spaces gives pointwise replacement data. Comparison across two such replacements
requires the indicated Kan mapping-space hypotheses and the corresponding criterion
between quasicategories; prefibrancy is retained where present in the statement.
-/

/--
The condition that `S` admits an inner-anodyne map to a quasicategory which induces
isomorphisms on all left mapping spaces at pairs of vertices of `S`.
-/
def HasProp35Replacement (S : SSet.{u}) : Prop :=
  ∃ (T : SSet.{u}) (u : S ⟶ T),
    innerAnodyneExtensions u ∧ Quasicategory T ∧
      ∀ a b : (Δ[0] : SSet.{u}) ⟶ S,
        IsIso (mappingSpaceLeft.map S a b u)

/--
A map inducing isomorphisms on every left mapping space is fully faithful on left
mapping spaces when all left mapping spaces of the source and target are Kan.
-/
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

/--
Every map `X → Z` to a quasicategory extends along an inner-anodyne map `X → Y`
to a map `Y → Z`.
-/
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

/--
Every vertex map `Δ[0] → Y` factors through a simplicial map `X → Y` which is
bijective on vertices.
-/
theorem exists_comp_eq_of_bijective_app_zero {u : X ⟶ Y}
    (hu0 : Function.Bijective (u.app (op ⦋0⦌)))
    (a' : (Δ[0] : SSet.{u}) ⟶ Y) :
    ∃ a : (Δ[0] : SSet.{u}) ⟶ X, a ≫ u = a' := by
  obtain ⟨x, hx⟩ := hu0.2 (yonedaEquiv a')
  refine ⟨const x, yonedaEquiv.injective ?_⟩
  rw [yonedaEquiv_comp, yonedaEquiv_const, hx]

/--
If `v : Y → Z` is fully faithful on left mapping spaces, then `f ≫ v` is fully
faithful on left mapping spaces exactly when `f : X → Y` is.
-/
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

/--
If `u : X → Y` is vertex-bijective and fully faithful on left mapping spaces,
then `u ≫ ψ` is fully faithful on left mapping spaces exactly when `ψ : Y → Z` is.
-/
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

/--
For a vertex-bijective map, choose inner-anodyne maps from its source and target to
quasicategories preserving all left mapping spaces. Assuming Kan left mapping spaces
for these four objects and the forward vertex-bijective quasicategory criterion,
categorical equivalence implies left mapping-space full faithfulness.
-/
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

/--
For a vertex-bijective map with mapping-preserving inner-anodyne quasicategory
replacements and Kan left mapping spaces, the biconditional quasicategory criterion
implies that categorical equivalence is equivalent to left mapping-space full faithfulness.
-/
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

/--
For a vertex-bijective map of prefibrant simplicial sets, assume pointwise
mapping-preserving quasicategory replacements, Kan left mapping spaces for the two
sets and all quasicategories, and the forward vertex-bijective quasicategory criterion.
Then categorical equivalence implies left Dwyer–Kan equivalence.
-/
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

/--
For a vertex-bijective map of prefibrant simplicial sets with pointwise
mapping-preserving replacements and the stated Kan and biconditional quasicategory
criteria, categorical equivalence is equivalent to left Dwyer–Kan equivalence.
-/
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
## Pullback descent across a pushout

For two pullback squares over a span with monomorphic base leg, the induced map on
pushouts has pullback side squares. If the two leg maps are inner fibrations, the
pushout map is an inner fibration and gives descent along both base inclusions.
Inner anodyneness of the opposite top span leg gives the respective inner-anodyne
descent conclusion. See Stevenson, Lemma 4.5.
-/

section Lemma45

variable {S₀ S₁ S₂ X₀ X₁ X₂ : SSet.{u}}
  {a : S₀ ⟶ S₁} {b : S₀ ⟶ S₂} {aX : X₀ ⟶ X₁} {bX : X₀ ⟶ X₂}
  {p₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}

/--
The simplicial map `X₁ ∪_(X₀) X₂ → S₁ ∪_(S₀) S₂` induced by two pullback
squares over the span `S₁ ← S₀ → S₂`.
-/
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

/--
The left pushout inclusion followed by the induced map on pushouts equals `p₁`
followed by the left inclusion of the base pushout.
-/
@[reassoc (attr := simp)]
theorem pushoutMapOfPullbacks_inl (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) :
    pushout.inl aX bX ≫ pushoutMapOfPullbacks sq1 sq2 =
      p₁ ≫ pushout.inl a b :=
  pushout.inl_desc _ _ _

/--
The right pushout inclusion followed by the induced map on pushouts equals `p₂`
followed by the right inclusion of the base pushout.
-/
@[reassoc (attr := simp)]
theorem pushoutMapOfPullbacks_inr (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) :
    pushout.inr aX bX ≫ pushoutMapOfPullbacks sq1 sq2 =
      p₂ ≫ pushout.inr a b :=
  pushout.inr_desc _ _ _

/--
For two given pullback squares over a span with monomorphic base map `S₀ → S₂`,
both squares from a span leg to the induced map on pushouts are pullbacks.
-/
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

/--
If `S₀ → S₂` is monomorphic, the square from `X₁ → S₁` to the induced map on
pushouts is a pullback.
-/
theorem isPullback_pushoutInl_mapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] :
    IsPullback (pushout.inl aX bX) p₁ (pushoutMapOfPullbacks sq1 sq2)
      (pushout.inl a b) :=
  (isPullback_pushoutMapOfPullbacks sq1 sq2).1

/--
If `S₀ → S₂` is monomorphic, the square from `X₂ → S₂` to the induced map on
pushouts is a pullback.
-/
theorem isPullback_pushoutInr_mapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] :
    IsPullback (pushout.inr aX bX) p₂ (pushoutMapOfPullbacks sq1 sq2)
      (pushout.inr a b) :=
  (isPullback_pushoutMapOfPullbacks sq1 sq2).2

end Lemma45

/--
Every degree-`n` simplex of a simplicial-set pushout is the image of a degree-`n`
simplex from one of its two legs.
-/
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

/--
With two pullback squares, monomorphic base leg `S₀ → S₂`, and inner-fibration
maps over the two other base objects, every inner horn lifts against the induced
map on pushouts.
-/
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

/--
The induced map on pushouts is an inner fibration when the base leg `S₀ → S₂`
is monomorphic and the two leg maps `p₁,p₂` are inner fibrations.
-/
theorem innerFibration_pushoutMapOfPullbacks
    (sq1 : IsPullback aX p₀ p₁ a) (sq2 : IsPullback bX p₀ p₂ b)
    [Mono b] [InnerFibration p₁] [InnerFibration p₂] :
    InnerFibration (pushoutMapOfPullbacks sq1 sq2) where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_pushoutMapOfPullbacks sq1 sq2 h0 hn

/--
Under the two pullback-square, monomorphic-leg, and inner-fibration hypotheses,
`p₁ : X₁ → S₁` satisfies descent along the left base pushout inclusion.
-/
theorem satisfiesDescent_pushout_inl (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) [Mono b] [InnerFibration p₁]
    [InnerFibration p₂] :
    SatisfiesDescent p₁ (pushout.inl a b) :=
  SatisfiesDescent.of_isPullback
    (innerFibration_pushoutMapOfPullbacks sq1 sq2)
    (isPullback_pushoutInl_mapOfPullbacks sq1 sq2)

/--
Under the two pullback-square, monomorphic-leg, and inner-fibration hypotheses,
`p₂ : X₂ → S₂` satisfies descent along the right base pushout inclusion.
-/
theorem satisfiesDescent_pushout_inr (sq1 : IsPullback aX p₀ p₁ a)
    (sq2 : IsPullback bX p₀ p₂ b) [Mono b] [InnerFibration p₁]
    [InnerFibration p₂] :
    SatisfiesDescent p₂ (pushout.inr a b) :=
  SatisfiesDescent.of_isPullback
    (innerFibration_pushoutMapOfPullbacks sq1 sq2)
    (isPullback_pushoutInr_mapOfPullbacks sq1 sq2)

/--
In the pushout descent construction, if the top span leg `X₀ → X₁` is also
inner anodyne, then `p₂` has inner-anodyne descent along the right base inclusion.
-/
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

/--
In the pushout descent construction, if the top span leg `X₀ → X₂` is also
inner anodyne, then `p₁` has inner-anodyne descent along the left base inclusion.
-/
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
## Pullback descent across sequential colimits

For a sequential natural transformation with pullback naturality squares and
monomorphic top transitions, the stage-to-colimit squares are pullbacks. Inner-fibration
stage maps give an inner-fibration colimit map. Inner-anodyne successor maps in the
top row yield inner-anodyne stage-to-colimit descent. See Stevenson, Lemma 4.3.
-/

/--
The map `colimit G → colimit F` induced by a natural transformation of sequential
simplicial-set diagrams `p : G ⟶ F`.
-/
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

/--
The stage-`k` colimit inclusion of `G`, followed by the induced colimit map, equals
`p_k` followed by the stage-`k` colimit inclusion of `F`.
-/
@[reassoc (attr := simp)]
theorem colimit_ι_colimitDescOfNatTrans {F G : ℕ ⥤ SSet.{u}}
    (p : G ⟶ F) (k : ℕ) :
    colimit.ι G k ≫ colimitDescOfNatTrans p =
      p.app k ≫ colimit.ι F k :=
  colimit.ι_desc _ _

/--
A transition `F_i → F_j` followed by the stage-`j` colimit inclusion equals the
stage-`i` colimit inclusion.
-/
theorem colimit_map_ι {F : ℕ ⥤ SSet.{u}} {i j : ℕ} (φ : i ⟶ j) :
    F.map φ ≫ colimit.ι F j = colimit.ι F i :=
  (colimit.cocone F).w φ

/--
A commutative square of simplicial sets is a pullback if its evaluated square is
a pullback of sets in every simplicial degree.
-/
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

/--
If the naturality squares of `p : G ⟶ F` are pullbacks and the transition maps
of `G` are monomorphisms, every stage-to-colimit square is a pullback in each
simplicial degree.
-/
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

/--
For a sequential natural transformation with pullback naturality squares and
monomorphic transitions in `G`, the square from any stage to the induced colimit
map is a pullback.
-/
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

/--
If every stage map of a sequential natural transformation is an inner fibration,
then every inner horn lifts against its induced map on colimits.
-/
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

/--
The induced map on sequential colimits is an inner fibration when every stage map
is an inner fibration.
-/
theorem innerFibration_colimitDescOfNatTrans
    (hp : ∀ m : ℕ, InnerFibration (p.app m)) :
    InnerFibration (colimitDescOfNatTrans p) where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_colimitDescOfNatTrans hp h0 hn

/--
With pullback naturality squares, monomorphic top transitions, and inner-fibration
stage maps, each stage map satisfies descent along its base colimit inclusion.
-/
theorem satisfiesDescent_colimit_ι
    (hsq : ∀ {m k : ℕ} (φ : m ⟶ k),
      IsPullback (G.map φ) (p.app m) (p.app k) (F.map φ))
    (hmono : ∀ {m k : ℕ} (φ : m ⟶ k), Mono (G.map φ))
    (hp : ∀ m : ℕ, InnerFibration (p.app m)) (m : ℕ) :
    SatisfiesDescent (p.app m) (colimit.ι F m) :=
  SatisfiesDescent.of_isPullback
    (innerFibration_colimitDescOfNatTrans hp)
    (isPullback_colimit_ι hsq hmono m)

/--
Under the sequential descent hypotheses, a stage has inner-anodyne descent along
its base colimit inclusion if its top colimit inclusion is inner anodyne.
-/
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

/--
The transfinite composition structure on the initial colimit inclusion of a
sequential diagram whose successor maps are inner anodyne.
-/
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

/--
If every successor map of a sequential diagram is inner anodyne, each stage
inclusion into its colimit is inner anodyne.
-/
theorem innerAnodyneExtensions_colimit_ι_of_succ
    (G : ℕ ⥤ SSet.{u})
    (hsucc : ∀ m : ℕ,
      innerAnodyneExtensions (G.map (homOfLE (Nat.le_succ m))))
    (m : ℕ) :
    innerAnodyneExtensions (colimit.ι G m) :=
  (transfiniteCompositionOfSequence G hsucc).mem_incl_app m

/--
If every successor map of a sequential diagram is inner anodyne, every transition
map of the diagram is inner anodyne.
-/
theorem innerAnodyneExtensions_map_of_succ
    (G : ℕ ⥤ SSet.{u})
    (hsucc : ∀ m : ℕ,
      innerAnodyneExtensions (G.map (homOfLE (Nat.le_succ m))))
    {m k : ℕ} (φ : m ⟶ k) :
    innerAnodyneExtensions (G.map φ) :=
  (transfiniteCompositionOfSequence G hsucc).mem_map φ

/--
For a natural transformation with pullback squares and inner-fibration stages,
inner-anodyne successor maps in the top diagram give inner-anodyne descent from
each stage along its base colimit inclusion.
-/
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
## Dependent assembly of stagewise descent

Suppose every inner fibration over each base stage descends inner-anodynely along
its successor map. Starting from an inner fibration at stage zero, successive choices
construct a tower over the base with inner-fibration stage maps, pullback naturality
squares, and inner-anodyne successor maps. Its colimit supplies inner-anodyne descent
along the initial base inclusion. See Stevenson, Proposition 4.7.
-/

section Prop47

variable {F : ℕ ⥤ SSet.{u}} {X₀ : SSet.{u}}
variable (hstage : ∀ (m : ℕ) {Y : SSet.{u}} (q : Y ⟶ F.obj m),
  InnerFibration q →
    SatisfiesInnerAnodyneDescent q (F.map (homOfLE (Nat.le_succ m))))

include hstage in
/--
Under stagewise descent along the successor base map, there is a choice of next-stage
object, map, and comparison for any `q`; if `q` is an inner fibration, this choice
is a pullback descent datum with inner-anodyne comparison and inner-fibration target.
-/
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

/--
The selected next-stage object and map over the successor base, together with a
comparison from the current object. Its descent properties hold when the current
map is an inner fibration.
-/
noncomputable def towerStepData (m : ℕ) (Y : SSet.{u})
    (q : Y ⟶ F.obj m) :
    Σ (Y' : SSet.{u}) (_q' : Y' ⟶ F.obj (m + 1)), Y ⟶ Y' :=
  Classical.choose (exists_towerStepData hstage m Y q)

/--
For an inner-fibration input, the selected next-stage map is an inner fibration,
the comparison square is a pullback, and the top comparison map is inner anodyne.
-/
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


/--
The sequence of simplicial objects with maps to the corresponding base stages,
starting at `(X₀,p₀)` and taking successive states from the selected one-stage data.
-/
noncomputable def towerState (p₀ : X₀ ⟶ F.obj 0) :
    (m : ℕ) → Σ (Y : SSet.{u}), Y ⟶ F.obj m := fun m =>
  match m with
  | 0 => ⟨X₀, p₀⟩
  | m + 1 =>
    let s := towerState p₀ m
    let d := towerStepData hstage m s.1 s.2
    ⟨d.1, d.2.1⟩

/--
The zero state of the dependent tower is exactly the specified pair `(X₀,p₀)`.
-/
theorem towerState_zero (p₀ : X₀ ⟶ F.obj 0) :
    towerState hstage p₀ 0 = ⟨X₀, p₀⟩ := rfl

/--
If the initial map is an inner fibration, every map to a base stage in the
constructed dependent tower is an inner fibration.
-/
theorem innerFibration_towerState_snd (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    InnerFibration (towerState hstage p₀ m).2 := by
  induction m with
  | zero => exact inferInstanceAs (InnerFibration p₀)
  | succ m ih => exact (towerStepData_spec hstage _ _ ih).1

/--
The comparison from one selected tower state to the next, supplied by the selected
one-stage descent data.
-/
noncomputable def towerStepMap (p₀ : X₀ ⟶ F.obj 0) (m : ℕ) :
    (towerState hstage p₀ m).1 ⟶ (towerState hstage p₀ (m + 1)).1 :=
  (towerStepData hstage m _ _).2.2

/--
For an inner-fibration initial map, the comparison between each pair of successive
tower states forms a pullback square over the successor base map.
-/
theorem isPullback_towerStepMap (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    IsPullback (towerStepMap hstage p₀ m) (towerState hstage p₀ m).2
      (towerState hstage p₀ (m + 1)).2
      (F.map (homOfLE (Nat.le_succ m))) :=
  (towerStepData_spec hstage _ _
    (innerFibration_towerState_snd hstage p₀ m)).2.1

/--
For an inner-fibration initial map, every successor comparison of the dependent
tower is inner anodyne.
-/
theorem innerAnodyneExtensions_towerStepMap (p₀ : X₀ ⟶ F.obj 0)
    [InnerFibration p₀] (m : ℕ) :
    innerAnodyneExtensions (towerStepMap hstage p₀ m) :=
  (towerStepData_spec hstage _ _
    (innerFibration_towerState_snd hstage p₀ m)).2.2

/--
The sequential diagram of the selected tower states and their successor comparison
maps.
-/
noncomputable def towerFunctor (p₀ : X₀ ⟶ F.obj 0) :
    ℕ ⥤ SSet.{u} :=
  Functor.ofSequence (towerStepMap hstage p₀)

/--
For an inner-fibration initial map, the natural transformation from the selected
tower diagram to the base diagram, with each selected stage map as its component.
-/
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

/--
For an inner-fibration initial map, every successor naturality square of the tower
map to its base is a pullback.
-/
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

/--
For an inner-fibration initial map, every naturality square of the tower map to
its base is a pullback, for any transition in the sequential index category.
-/
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

/--
For an inner-fibration initial map, the initial colimit inclusion of the dependent
tower carries a transfinite composition structure with inner-anodyne successors.
-/
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
/--
If every inner fibration over every base stage has inner-anodyne descent along
the successor base map, every inner fibration over the initial stage has
inner-anodyne descent along the initial base colimit inclusion.
-/
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
## Selected horns and prefibrant descent tower conditions

The selected-horn condition concerns inner horns in dimension two and inner horns
whose zero face is constant. A selective tower starts at the given simplicial set,
has a prefibrant colimit and inner-anodyne successors, and supports stagewise descent.
Such towers imply uniform prefibrant descent replacement; mapping-preserving
quasicategory replacement is a separate pointwise condition.
-/

set_option linter.unusedVariables false in
/--
The condition that pullbacks of inner fibrations along selected inner-horn maps
have inner-anodyne descent across the horn inclusion: the selected maps have
dimension two, or have constant zero face.
-/
def HornDescent412 : Prop :=
  ∀ {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i)
    (hn : i < Fin.last (n + 2)) {S : SSet.{u}}
    (α : (Λ[n + 2, i] : SSet.{u}) ⟶ S),
    (n = 0 ∨ IsConstantSimplex (hornFaceZero α (ne_of_lt h0))) →
    ∀ {Z : SSet.{u}} (pz : Z ⟶ S), InnerFibration pz →
      SatisfiesInnerAnodyneDescent (pullback.snd pz α) Λ[n + 2, i].ι

/--
The condition that every simplicial set is exactly the initial object of a sequential
tower with prefibrant colimit, inner-anodyne successor maps, and inner-anodyne descent
of every inner fibration along each successor base map.
-/
def SelectiveTower412Exists : Prop :=
  ∀ S : SSet.{u}, ∃ (F : ℕ ⥤ SSet.{u}),
    F.obj 0 = S ∧ IsPreFibrant (colimit F) ∧
    (∀ m : ℕ, innerAnodyneExtensions (F.map (homOfLE (Nat.le_succ m)))) ∧
    ∀ (m : ℕ) {Z : SSet.{u}} (pz : Z ⟶ F.obj m), InnerFibration pz →
      SatisfiesInnerAnodyneDescent pz (F.map (homOfLE (Nat.le_succ m)))

/--
The selective-tower existence condition implies uniform prefibrant descent
replacement, using the initial colimit inclusion and the stagewise descent assembly.
-/
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
