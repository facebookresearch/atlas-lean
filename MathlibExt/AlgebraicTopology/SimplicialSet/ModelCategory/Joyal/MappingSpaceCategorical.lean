/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree
public import Mathlib.CategoryTheory.Whiskering

/-!
# Mapping-space full-faithfulness reductions

The homotopy-category and mapping-space reductions retain their stated
hypotheses. The unconditional right-mapping criterion is supplied by
`RightMappingBrown` and `DwyerKanRecognition`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}

/-!
## The `π₀` shadow: full faithfulness on homotopy categories
-/

/-- The `π₀`-level (homotopy-category) shadow of Stevenson
Definition 2.16(ii): `f` induces a bijection on morphism sets
`(mk x ⟶ mk y) → (mk (f x) ⟶ mk (f y))` of ordinary homotopy
categories for all vertices `x y`. For a quasicategory these morphism
sets are the standard identification of `π₀` of the mapping spaces;
this file states the property in homotopy-category form, and the
transport to `π₀ (mappingSpaceRight X _ _)` itself is
`SSet.mappingSpaceRight.piZeroEquiv` downstream
(`MappingSpacePi.lean`). Compare
`SSet.dwyerKanFullyFaithful`, the full mapping-space
statement. -/
def dwyerKanFullyFaithfulPiZero (f : X ⟶ Y) : Prop :=
  ∀ x y : X _⦋0⦌, Function.Bijective
    ((mapHomotopyCategory f).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) →
        (HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
          HomotopyCategory.mk (f.app (op ⦋0⦌) y)))

/-- A categorical equivalence induces a fully faithful functor on
ordinary homotopy categories (as a `Functor.FullyFaithful`
structure). This restates
`SSet.categoricalEquivalences.isEquivalence_mapHomotopyCategory`
through `Functor.FullyFaithful.ofFullyFaithful`; no quasicategory
hypothesis is needed. -/
noncomputable def categoricalEquivalences.fullyFaithful_mapHomotopyCategory
    (hf : categoricalEquivalences f) :
    (mapHomotopyCategory f).FullyFaithful := by
  have : (mapHomotopyCategory f).IsEquivalence :=
    hf.isEquivalence_mapHomotopyCategory
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- The morphism-set equivalence induced by a categorical equivalence
at a pair of vertices: `(mk x ⟶ mk y) ≃ (mk (f x) ⟶ mk (f y))`. -/
noncomputable def categoricalEquivalences.homEquiv_mapHomotopyCategory_mk
    (hf : categoricalEquivalences f) (x y : X _⦋0⦌) :
    (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) ≃
      (HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
        HomotopyCategory.mk (f.app (op ⦋0⦌) y)) :=
  hf.fullyFaithful_mapHomotopyCategory.homEquiv

/-- **A categorical equivalence is fully faithful at the `π₀`
level**: it induces bijections on all morphism sets of ordinary
homotopy categories between vertex objects. This is the
`π₀` shadow of the mapping-space statement
`SSet.dwyerKanFullyFaithful`; see the module header for the inputs
still missing for the full statement. -/
theorem categoricalEquivalences.dwyerKanFullyFaithfulPiZero
    (hf : categoricalEquivalences f) :
    dwyerKanFullyFaithfulPiZero f :=
  fun _ _ ↦ hf.fullyFaithful_mapHomotopyCategory.map_bijective _ _

/-- **Fullness on edges** at the `π₀` level: if `X` is a
quasicategory and `f` satisfies `SSet.dwyerKanFullyFaithfulPiZero`,
then every edge of `Y` between `f`-image vertices is homotopic
(equal after `SSet.Edge.toHoHom`) to the image of an edge of `X`.
The quasicategory hypothesis is used only to represent the
preimage morphism by a single edge
(`SSet.Edge.exists_homMk_eq`). -/
theorem dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq
    [Quasicategory X] (hf : dwyerKanFullyFaithfulPiZero f)
    {x y : X _⦋0⦌} (e' : Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : Edge x y, HomotopyCategory.homMk (e.map f) = HomotopyCategory.homMk e' := by
  obtain ⟨φ, hφ⟩ := (hf x y).surjective (HomotopyCategory.homMk e')
  obtain ⟨e, rfl⟩ := Edge.exists_homMk_eq φ
  refine ⟨e, ?_⟩
  rw [← mapHomotopyCategory_map_homMk]
  exact hφ

/-- **Faithfulness on edges** at the `π₀` level: if `f` satisfies
`SSet.dwyerKanFullyFaithfulPiZero` and two edges of `X` have
homotopic images in `Y`, then they are homotopic in `X` (their
classes `SSet.Edge.toHoHom` agree). No quasicategory hypothesis is
needed. -/
theorem dwyerKanFullyFaithfulPiZero.edge_map_toHoHom_injective
    (hf : dwyerKanFullyFaithfulPiZero f) {x y : X _⦋0⦌}
    {e₁ e₂ : Edge x y}
    (h : HomotopyCategory.homMk (e₁.map f) = HomotopyCategory.homMk (e₂.map f)) :
    HomotopyCategory.homMk e₁ = HomotopyCategory.homMk e₂ := by
  rw [← mapHomotopyCategory_map_homMk, ← mapHomotopyCategory_map_homMk] at h
  exact (hf x y).injective h

/-!
## The induced map on mapping-space simplices
-/

namespace mappingSpaceRight

variable (X : SSet.{u}) (a b : (Δ[0] : SSet.{u}) ⟶ X)

/-- Under the transport `SSet.mappingSpaceRight.simplexEquivSucc`
(an `n`-simplex of the right mapping space read as an
`(n + 1)`-simplex of `X`), the induced map
`SSet.mappingSpaceRight.map X a b F` is postcomposition with `F`.
For `n = 0` this says that the representing `1`-simplex of a
`0`-simplex of the mapping space is sent to its postcomposition
with `F`; identifying that `1`-simplex with an `SSet.Edge` is
`SSet.mappingSpaceRight.zeroSimplexEquivEdge` downstream
(`MappingSpacePi.lean`, formerly
the additional comparison obligation). -/
theorem simplexEquivSucc_map_app_val {Y : SSet.{u}} (F : X ⟶ Y)
    (n : ℕ) (σ : (mappingSpaceRight X a b).obj (op ⦋n⦌)) :
    ((simplexEquivSucc Y (a ≫ F) (b ≫ F) n)
        ((map X a b F).app (op ⦋n⦌) σ)).1 =
      ((simplexEquivSucc X a b n) σ).1 ≫ F := by
  change (SSet.joinStdSimplexIso n 0).inv ≫ (σ.1 ≫ F) =
    ((SSet.joinStdSimplexIso n 0).inv ≫ σ.1) ≫ F
  rw [Category.assoc]

end mappingSpaceRight

/-!
## Two-out-of-six (the formal half of Stevenson Lemma 2.17)

The generic two-out-of-six closure for `SSet.KanComplex.W` and
for `SSet.realizationWeakEquivalences`
(`SSet.KanComplex.W.left_of_comp_comp`,
`SSet.realizationWeakEquivalences.left_of_comp_comp`) lives in
`KanComplexWTwoOfThree.lean`; this section records only its
mapping-space application.
-/

/-- **Two-out-of-six for full faithfulness on mapping spaces** (the
formal conclusion of Stevenson's proof of Lemma 2.17): if
`f ≫ g` and `g ≫ f` are fully faithful in the sense of
`SSet.dwyerKanFullyFaithful`, then `f` is. At vertices `a b` this
applies `SSet.realizationWeakEquivalences.left_of_comp_comp`
to the chain of
mapping-space maps at `a`, `a ≫ f` and `(a ≫ f) ≫ g`, whose two
consecutive composites are the mapping-space maps of `f ≫ g` and
`g ≫ f` by `SSet.mappingSpaceRight.map_comp`. -/
theorem dwyerKanFullyFaithful.of_comp_comp {g : Y ⟶ X}
    (hfg : dwyerKanFullyFaithful (f ≫ g))
    (hgf : dwyerKanFullyFaithful (g ≫ f)) :
    dwyerKanFullyFaithful f := by
  intro a b
  have hab : realizationWeakEquivalences (mappingSpaceRight.map X a b f ≫
      mappingSpaceRight.map Y (a ≫ f) (b ≫ f) g) := by
    rw [← mappingSpaceRight.map_comp]
    exact hfg a b
  have hbc : realizationWeakEquivalences (mappingSpaceRight.map Y (a ≫ f) (b ≫ f) g ≫
      mappingSpaceRight.map X ((a ≫ f) ≫ g) ((b ≫ f) ≫ g) f) := by
    rw [← mappingSpaceRight.map_comp]
    exact hgf (a ≫ f) (b ≫ f)
  exact realizationWeakEquivalences.left_of_comp_comp hab hbc

/-- A categorical equivalence whose two composites with some
`g : Y ⟶ X` are fully faithful on mapping spaces is a Dwyer–Kan
equivalence: essential surjectivity is
`SSet.categoricalEquivalences.dwyerKanEssentiallySurjective`
(the supporting results) and full faithfulness is
`SSet.dwyerKanFullyFaithful.of_comp_comp`. Supplying the two
composite hypotheses for the homotopy inverse of
`SSet.categoricalEquivalences.hasHoInverse` is
the additional comparison obligation. -/
theorem categoricalEquivalences.isDwyerKanEquivalence_of_comp_comp
    (hf : categoricalEquivalences f) {g : Y ⟶ X}
    (hfg : dwyerKanFullyFaithful (f ≫ g))
    (hgf : dwyerKanFullyFaithful (g ≫ f)) :
    isDwyerKanEquivalence f :=
  ⟨hf.dwyerKanEssentiallySurjective,
    dwyerKanFullyFaithful.of_comp_comp hfg hgf⟩

/-!
## Whitehead assembly point
-/

/-- **Whitehead criterion for full faithfulness**: if all right
mapping spaces of `X` and all the target right mapping spaces are
Kan complexes, and for every pair of vertices the induced map
`SSet.mappingSpaceRight.map X a b f` induces an equivalence of
fundamental groupoids and bijections on all based homotopy groups,
then `f` is fully faithful on mapping spaces. This is
`SSet.KanComplex.W.mk` applied pointwise and transported along
`SSet.dwyerKanFullyFaithful.of_kanComplexW`; it isolates exactly the
hypotheses (Kan-ness — discharged for quasicategories by
`SSet.kanComplex_mappingSpaceRight` downstream, formerly
the additional comparison obligation — and the higher-homotopy input,
the additional comparison obligation) that remain between a categorical
equivalence and `SSet.dwyerKanFullyFaithful`. -/
theorem dwyerKanFullyFaithful.of_kan_bijective_piMap
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (hFG : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      (SSet.mapFundamentalGroupoid
        (mappingSpaceRight.map X a b f)).IsEquivalence)
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n) (x := σ))) :
    dwyerKanFullyFaithful f :=
  dwyerKanFullyFaithful.of_kanComplexW hKanX hKanY
    (fun a b => KanComplex.W.mk _ (hKanX a b) (hKanY a b) (hFG a b) (hπ a b))

end SSet

end
