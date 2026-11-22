/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleBridges
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Skeletal closure and the pointwise criterion (the supporting results)

This module closes the additional comparison obligation and the additional comparison obligation of
`ShuffleBridges.lean` (lines 505–521 there; §3–§4 of that header
give the outline, `PrismCobase.lean` §3 and
`CobaseUnconditional.lean` §3 the earlier versions). Following
the method of the earlier packets, this header first gives the
complete informal proofs; the formal content then proves them
in dependency order. As in `ShuffleBridges.lean`, **no
statement here claims the unconditional stability instance**
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet.{u})`: every result that
depends on shuffle filling names the cell inputs
`SSet.ShuffleHornZeroCellExtension` /
`SSet.ShuffleHornTwoCellExtension` (the additional comparison obligation, external in
`ShuffleCobase.lean`) as hypotheses, in the hypothesis style of
`ShuffleBridges.lean`. the additional comparison obligation (the `Δ[2]`-prism correction
transporting to `SSet.CompCorrection`) is untouched.

Each property `Q(i)` asserts only existence of prism
extensions (the `Δ[1]` properties also conclude the vertical
equivalences that make steps compose; the `Δ[2]` properties
need no vertical conclusion because at every skeletal step
the special simplex lies in the horn factor, whose verticals
are hypothesized globally over the final base `B` and only
ever restrict). Hence all three are stable under the formal
gluing operations:
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-!
## Whiskering of horn verticals

Horn vertical simplices are preserved by whiskering in the
base (by `σ`-naturality in the first factor), so the
horn-vertical equivalence hypotheses of the `Δ[2]` extension
properties restrict along any base map.
-/

section HornVerticalWhisker

variable {A B C : SSet.{u}}

/-- Whiskering sends horn-zero vertical simplices to horn
vertical simplices at the image vertices. -/
lemma whiskerRight_app_hornVertZeroSimplex (f : A ⟶ B)
    (x : A _⦋0⦌) :
    (f ▷ (Λ[2, 0] : SSet.{u})).app _ (hornVertZeroSimplex x) =
      hornVertZeroSimplex (f.app _ x) := by
  apply Prod.ext
  · change f.app _ (A.σ 0 x) = B.σ 0 (f.app _ x)
    exact σ_naturality_apply f 0 x
  · rfl

/-- Whiskering sends horn-two vertical simplices to horn
vertical simplices at the image vertices. -/
lemma whiskerRight_app_hornVertTwoSimplex (f : A ⟶ B)
    (x : A _⦋0⦌) :
    (f ▷ (Λ[2, 2] : SSet.{u})).app _ (hornVertTwoSimplex x) =
      hornVertTwoSimplex (f.app _ x) := by
  apply Prod.ext
  · change f.app _ (A.σ 0 x) = B.σ 0 (f.app _ x)
    exact σ_naturality_apply f 0 x
  · rfl

/-- Horn-zero vertical equivalences restrict along
whiskering in the base. -/
lemma hornZeroVerticals_whiskerRight_comp (f : A ⟶ B)
    (PΛ : B ⊗ (Λ[2, 0] : SSet.{u}) ⟶ C)
    (h : ∀ x : B _⦋0⦌,
      (Edge.mk' (PΛ.app _ (hornVertZeroSimplex x))).IsEquivalence) :
    ∀ x : A _⦋0⦌,
      (Edge.mk' (((f ▷ (Λ[2, 0] : SSet.{u})) ≫ PΛ).app _
        (hornVertZeroSimplex x))).IsEquivalence := by
  intro x
  refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (h (f.app _ x))
  change ((f ▷ (Λ[2, 0] : SSet.{u})) ≫ PΛ).app _
      (hornVertZeroSimplex x) =
    PΛ.app _ (hornVertZeroSimplex (f.app _ x))
  simp only [NatTrans.comp_app, types_comp_apply,
    whiskerRight_app_hornVertZeroSimplex]

/-- Horn-two vertical equivalences restrict along whiskering
in the base. -/
lemma hornTwoVerticals_whiskerRight_comp (f : A ⟶ B)
    (PΛ : B ⊗ (Λ[2, 2] : SSet.{u}) ⟶ C)
    (h : ∀ x : B _⦋0⦌,
      (Edge.mk' (PΛ.app _ (hornVertTwoSimplex x))).IsEquivalence) :
    ∀ x : A _⦋0⦌,
      (Edge.mk' (((f ▷ (Λ[2, 2] : SSet.{u})) ≫ PΛ).app _
        (hornVertTwoSimplex x))).IsEquivalence := by
  intro x
  refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (h (f.app _ x))
  change ((f ▷ (Λ[2, 2] : SSet.{u})) ≫ PΛ).app _
      (hornVertTwoSimplex x) =
    PΛ.app _ (hornVertTwoSimplex (f.app _ x))
  simp only [NatTrans.comp_app, types_comp_apply,
    whiskerRight_app_hornVertTwoSimplex]

end HornVerticalWhisker

/-!
## `Δ[1]`: composition and the uniform cell case

`PrismOneExtensionAt.comp` is `PrismSrcExtension.comp`
uniformly in `κ`, and the cell case is uniform because every
`κ : Fin 2` is `0` or `1`.
-/

section PrismOneCompCell

variable {A B C D : SSet.{u}} {i : A ⟶ B} {j : B ⟶ D}
  {κ : Fin 2} {n : ℕ}

/-- **`Δ[1]`-prism extension is stable under composition**,
uniformly in the prescribed vertex `κ`: extend in two steps. -/
theorem PrismOneExtensionAt.comp (hi : PrismOneExtensionAt κ i C)
    (hj : PrismOneExtensionAt κ j C) :
    PrismOneExtensionAt κ (i ≫ j) C := by
  intro H g hagree hVert
  obtain ⟨F₁, hF₁r, hF₁s, hF₁v⟩ := hi H (j ≫ g)
    (by rw [hagree, Category.assoc]) hVert
  obtain ⟨F₂, hF₂r, hF₂s, hF₂v⟩ := hj F₁ g hF₁s hF₁v
  refine ⟨F₂, ?_, hF₂s, hF₂v⟩
  calc ((i ≫ j) ▷ Δ[1]) ≫ F₂
      = (i ▷ Δ[1]) ≫ ((j ▷ Δ[1]) ≫ F₂) := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = H := by rw [hF₂r, hF₁r]

/-- Every vertex `κ : Fin 2` of `Δ[1]` is `0` or `1`. -/
lemma fin_two_eq_zero_or_one (κ : Fin 2) : κ = 0 ∨ κ = 1 := by
  have h : κ.val = 0 ∨ κ.val = 1 := by have h2 := κ.2; omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- **`Δ[1]`-prism extension along `∂Δ[n].ι` at either
vertex**, unconditionally: the two cell bridges of
`ShuffleBridges.lean` read at `κ = 0, 1`. -/
theorem prismOneExtensionAt_boundary [Quasicategory C] (κ : Fin 2) :
    PrismOneExtensionAt κ ∂Δ[n].ι C := by
  rcases fin_two_eq_zero_or_one κ with rfl | rfl
  · exact prismSrcExtension_iff_oneExtensionAt_zero.1
      prismSrcExtension_boundary
  · exact prismTgtExtension_iff_oneExtensionAt_one.1
      prismTgtExtension_boundary

end PrismOneCompCell

/-!
## `Δ[2]`: composition and cobase change

Composition restricts the horn datum to the middle base,
extends along the first map, then along the second. Cobase
change restricts to the original map, extends there, and
glues along the tensored pushout; the horn face of the glued
prism is checked by joint epimorphy over the other tensored
pushout, with whisker exchange moving the horn inclusion
past the base maps. No vertex argument is needed, since the
`Δ[2]` properties have no vertical conclusion.
-/

section PrismTwoCompPushout

variable {A B C D X Y : SSet.{u}} {i : A ⟶ B} {j : B ⟶ D}
  {f : A ⟶ X} {f' : B ⟶ Y} {j' : X ⟶ Y}

/-- **Horn-zero `Δ[2]`-prism extension is stable under
composition:** restrict the horn prism to the middle base,
extend along `i`, then along `j`. -/
theorem PrismTwoHornZeroExtension.comp
    (hi : PrismTwoHornZeroExtension i C)
    (hj : PrismTwoHornZeroExtension j C) :
    PrismTwoHornZeroExtension (i ≫ j) C := by
  intro P_A P_Λ hagree hVert
  have hagreei : (A ◁ Λ[2, 0].ι) ≫ P_A =
      (i ▷ (Λ[2, 0] : SSet.{u})) ≫
        ((j ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) := by
    rw [hagree, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight]
  obtain ⟨P_B, hPB_r, hPB_Λ⟩ := hi P_A
    ((j ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) hagreei
    (hornZeroVerticals_whiskerRight_comp j P_Λ hVert)
  obtain ⟨P_D, hPD_r, hPD_Λ⟩ := hj P_B P_Λ hPB_Λ hVert
  refine ⟨P_D, ?_, hPD_Λ⟩
  calc ((i ≫ j) ▷ Δ[2]) ≫ P_D
      = (i ▷ Δ[2]) ≫ ((j ▷ Δ[2]) ≫ P_D) := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = P_A := by rw [hPD_r, hPB_r]

/-- **Horn-two `Δ[2]`-prism extension is stable under
composition** (the mirror). -/
theorem PrismTwoHornTwoExtension.comp
    (hi : PrismTwoHornTwoExtension i C)
    (hj : PrismTwoHornTwoExtension j C) :
    PrismTwoHornTwoExtension (i ≫ j) C := by
  intro P_A P_Λ hagree hVert
  have hagreei : (A ◁ Λ[2, 2].ι) ≫ P_A =
      (i ▷ (Λ[2, 2] : SSet.{u})) ≫
        ((j ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) := by
    rw [hagree, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight]
  obtain ⟨P_B, hPB_r, hPB_Λ⟩ := hi P_A
    ((j ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) hagreei
    (hornTwoVerticals_whiskerRight_comp j P_Λ hVert)
  obtain ⟨P_D, hPD_r, hPD_Λ⟩ := hj P_B P_Λ hPB_Λ hVert
  refine ⟨P_D, ?_, hPD_Λ⟩
  calc ((i ≫ j) ▷ Δ[2]) ≫ P_D
      = (i ▷ Δ[2]) ≫ ((j ▷ Δ[2]) ≫ P_D) := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = P_A := by rw [hPD_r, hPB_r]

/-- **Horn-zero `Δ[2]`-prism extension is stable under
cobase change:** restrict the data to `i`, extend there, and
glue along the tensored pushout; the horn face is checked
over the `Λ`-tensored pushout by whisker exchange. -/
theorem PrismTwoHornZeroExtension.of_isPushout
    (sq : IsPushout i f f' j') (h : PrismTwoHornZeroExtension i C) :
    PrismTwoHornZeroExtension j' C := by
  intro P_X P_Λ hagree hVert
  have hagreei : (A ◁ Λ[2, 0].ι) ≫ ((f ▷ Δ[2]) ≫ P_X) =
      (i ▷ (Λ[2, 0] : SSet.{u})) ≫
        ((f' ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) := by
    calc (A ◁ Λ[2, 0].ι) ≫ ((f ▷ Δ[2]) ≫ P_X)
        = (f ▷ (Λ[2, 0] : SSet.{u})) ≫
            ((X ◁ Λ[2, 0].ι) ≫ P_X) := by
          rw [← Category.assoc,
            MonoidalCategory.whisker_exchange, Category.assoc]
      _ = ((f ≫ j') ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
          rw [hagree, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight]
      _ = (i ▷ (Λ[2, 0] : SSet.{u})) ≫
            ((f' ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) := by
          rw [← sq.w, MonoidalCategory.comp_whiskerRight,
            Category.assoc]
  obtain ⟨P_B, hPB_r, hPB_Λ⟩ := h ((f ▷ Δ[2]) ≫ P_X)
    ((f' ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) hagreei
    (hornZeroVerticals_whiskerRight_comp f' P_Λ hVert)
  set sq₂ := (tensorRight Δ[2]).map_isPushout sq with hsq₂
  set P_Y := sq₂.desc P_B P_X hPB_r with hP_Y
  have hPf' : (f' ▷ Δ[2]) ≫ P_Y = P_B := sq₂.inl_desc P_B P_X hPB_r
  have hPj' : (j' ▷ Δ[2]) ≫ P_Y = P_X := sq₂.inr_desc P_B P_X hPB_r
  refine ⟨P_Y, hPj', ?_⟩
  apply ((tensorRight (Λ[2, 0] : SSet.{u})).map_isPushout sq).hom_ext
  · calc (f' ▷ (Λ[2, 0] : SSet.{u})) ≫ ((Y ◁ Λ[2, 0].ι) ≫ P_Y)
        = (B ◁ Λ[2, 0].ι) ≫ ((f' ▷ Δ[2]) ≫ P_Y) := by
          rw [← Category.assoc,
            ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (f' ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
          rw [hPf', hPB_Λ]
  · calc (j' ▷ (Λ[2, 0] : SSet.{u})) ≫ ((Y ◁ Λ[2, 0].ι) ≫ P_Y)
        = (X ◁ Λ[2, 0].ι) ≫ ((j' ▷ Δ[2]) ≫ P_Y) := by
          rw [← Category.assoc,
            ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (j' ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
          rw [hPj', hagree]

/-- **Horn-two `Δ[2]`-prism extension is stable under cobase
change** (the mirror). -/
theorem PrismTwoHornTwoExtension.of_isPushout
    (sq : IsPushout i f f' j') (h : PrismTwoHornTwoExtension i C) :
    PrismTwoHornTwoExtension j' C := by
  intro P_X P_Λ hagree hVert
  have hagreei : (A ◁ Λ[2, 2].ι) ≫ ((f ▷ Δ[2]) ≫ P_X) =
      (i ▷ (Λ[2, 2] : SSet.{u})) ≫
        ((f' ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) := by
    calc (A ◁ Λ[2, 2].ι) ≫ ((f ▷ Δ[2]) ≫ P_X)
        = (f ▷ (Λ[2, 2] : SSet.{u})) ≫
            ((X ◁ Λ[2, 2].ι) ≫ P_X) := by
          rw [← Category.assoc,
            MonoidalCategory.whisker_exchange, Category.assoc]
      _ = ((f ≫ j') ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
          rw [hagree, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight]
      _ = (i ▷ (Λ[2, 2] : SSet.{u})) ≫
            ((f' ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) := by
          rw [← sq.w, MonoidalCategory.comp_whiskerRight,
            Category.assoc]
  obtain ⟨P_B, hPB_r, hPB_Λ⟩ := h ((f ▷ Δ[2]) ≫ P_X)
    ((f' ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) hagreei
    (hornTwoVerticals_whiskerRight_comp f' P_Λ hVert)
  set sq₂ := (tensorRight Δ[2]).map_isPushout sq with hsq₂
  set P_Y := sq₂.desc P_B P_X hPB_r with hP_Y
  have hPf' : (f' ▷ Δ[2]) ≫ P_Y = P_B := sq₂.inl_desc P_B P_X hPB_r
  have hPj' : (j' ▷ Δ[2]) ≫ P_Y = P_X := sq₂.inr_desc P_B P_X hPB_r
  refine ⟨P_Y, hPj', ?_⟩
  apply ((tensorRight (Λ[2, 2] : SSet.{u})).map_isPushout sq).hom_ext
  · calc (f' ▷ (Λ[2, 2] : SSet.{u})) ≫ ((Y ◁ Λ[2, 2].ι) ≫ P_Y)
        = (B ◁ Λ[2, 2].ι) ≫ ((f' ▷ Δ[2]) ≫ P_Y) := by
          rw [← Category.assoc,
            ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (f' ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
          rw [hPf', hPB_Λ]
  · calc (j' ▷ (Λ[2, 2] : SSet.{u})) ≫ ((Y ◁ Λ[2, 2].ι) ≫ P_Y)
        = (X ◁ Λ[2, 2].ι) ≫ ((j' ▷ Δ[2]) ≫ P_Y) := by
          rw [← Category.assoc,
            ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (j' ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
          rw [hPj', hagree]

end PrismTwoCompPushout

/-!
## Coproducts

Vertices of a coproduct come from a summand, and each
extension property is stable under coproducts of maps:
restrict to summands, extend there, and descend along the
coproduct cocone preserved by `tensorRight`
(`isColimitCofanMkObjOfIsColimit` of `coproductIsCoproduct`).
-/

section Coproducts

variable {ι : Type u} {Aseq Bseq : ι → SSet.{u}} {C : SSet.{u}}
  {κ : Fin 2}

/-- Vertices of a coproduct of simplicial sets come from a
summand: evaluation at `⦋0⦌` preserves the coproduct, and
the coprojections in `Type` are jointly surjective. -/
lemma exists_sigma_ι_app_eq_zero (Bseq : ι → SSet.{u})
    (y : (∐ Bseq) _⦋0⦌) :
    ∃ (k : ι) (x : Bseq k _⦋0⦌), (Sigma.ι Bseq k).app _ x = y :=
  Cofan.inj_jointly_surjective_of_isColimit
    (isColimitCofanMkObjOfIsColimit
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)) Bseq _
      (coproductIsCoproduct _)) y

/-- **`Δ[1]`-prism extension is stable under coproducts:**
extend in each summand and descend along the tensored
coproduct cocone; verticals come from summands. -/
theorem PrismOneExtensionAt.sigmaMap
    {i : ∀ k, Aseq k ⟶ Bseq k}
    (h : ∀ k, PrismOneExtensionAt κ (i k) C) :
    PrismOneExtensionAt κ (Limits.Sigma.map i) C := by
  intro H g hagree hVert
  have hagree_k : ∀ k, prismSectionAt (Aseq k) κ ≫
        ((Sigma.ι Aseq k ▷ Δ[1]) ≫ H) =
      (i k) ≫ (Sigma.ι Bseq k ≫ g) := by
    intro k
    calc prismSectionAt (Aseq k) κ ≫
          ((Sigma.ι Aseq k ▷ Δ[1]) ≫ H)
        = Sigma.ι Aseq k ≫ (prismSectionAt (∐ Aseq) κ ≫ H) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = (i k) ≫ (Sigma.ι Bseq k ≫ g) := by
          rw [hagree, ← Category.assoc, Limits.Sigma.ι_map, Category.assoc]
  have key : ∀ k, ∃ F : Bseq k ⊗ Δ[1] ⟶ C,
      (i k ▷ Δ[1]) ≫ F = (Sigma.ι Aseq k ▷ Δ[1]) ≫ H ∧
        prismSectionAt (Bseq k) κ ≫ F = Sigma.ι Bseq k ≫ g ∧
          PrismOneVerticalsEquivalences F :=
    fun k ↦ h k _ _ (hagree_k k)
      (prismOneVerticalsEquivalences_whiskerRight_comp _ H hVert)
  choose Fseq hF using key
  set hcB := isColimitCofanMkObjOfIsColimit (tensorRight Δ[1])
    Bseq _ (coproductIsCoproduct _) with hhcB
  set F := hcB.desc (Cofan.mk C Fseq) with hFdef
  have hFfac : ∀ k, (Sigma.ι Bseq k ▷ Δ[1]) ≫ F = Fseq k :=
    fun k ↦ hcB.fac _ ⟨k⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · apply (isColimitCofanMkObjOfIsColimit (tensorRight Δ[1])
      Aseq _ (coproductIsCoproduct _)).hom_ext
    rintro ⟨k⟩
    change (Sigma.ι Aseq k ▷ Δ[1]) ≫ ((Limits.Sigma.map i ▷ Δ[1]) ≫ F) =
      (Sigma.ι Aseq k ▷ Δ[1]) ≫ H
    calc (Sigma.ι Aseq k ▷ Δ[1]) ≫ ((Limits.Sigma.map i ▷ Δ[1]) ≫ F)
        = (i k ▷ Δ[1]) ≫ ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F) := by
          rw [← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Limits.Sigma.ι_map,
            MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (Sigma.ι Aseq k ▷ Δ[1]) ≫ H := by
          rw [hFfac, (hF k).1]
  · refine Sigma.hom_ext _ _ (fun k ↦ ?_)
    calc Sigma.ι Bseq k ≫ (prismSectionAt (∐ Bseq) κ ≫ F)
        = prismSectionAt (Bseq k) κ ≫
            ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F) := by
          rw [← Category.assoc,
            ← prismSectionAt_comp_whiskerRight, Category.assoc]
      _ = Sigma.ι Bseq k ≫ g := by rw [hFfac, (hF k).2.1]
  · intro y
    obtain ⟨k, x, hx⟩ := exists_sigma_ι_app_eq_zero Bseq y
    refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
        Edge.mk' ((Fseq k).app _ (verticalOneSimplex x))) ?_).2
      ((hF k).2.2 x)
    change F.app _ (verticalOneSimplex y) =
      (Fseq k).app _ (verticalOneSimplex x)
    calc F.app _ (verticalOneSimplex y)
        = ((Sigma.ι Bseq k ▷ Δ[1]) ≫ F).app _
            (verticalOneSimplex x) := by
          change F.app _ (verticalOneSimplex y) =
            F.app _ ((Sigma.ι Bseq k ▷ Δ[1]).app _
              (verticalOneSimplex x))
          rw [whiskerRight_app_verticalOneSimplex, hx]
      _ = (Fseq k).app _ (verticalOneSimplex x) :=
          congr($(hFfac k).app _ (verticalOneSimplex x))

/-- **Horn-zero `Δ[2]`-prism extension is stable under
coproducts:** extend in each summand and descend; restriction
and horn face are checked over the two tensored cocones. -/
theorem PrismTwoHornZeroExtension.sigmaMap
    {i : ∀ k, Aseq k ⟶ Bseq k}
    (h : ∀ k, PrismTwoHornZeroExtension (i k) C) :
    PrismTwoHornZeroExtension (Limits.Sigma.map i) C := by
  intro P_A P_Λ hagree hVert
  have hagree_k : ∀ k, (Aseq k ◁ Λ[2, 0].ι) ≫
        ((Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A) =
      (i k ▷ (Λ[2, 0] : SSet.{u})) ≫
        ((Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) := by
    intro k
    calc (Aseq k ◁ Λ[2, 0].ι) ≫ ((Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A)
        = (Sigma.ι Aseq k ▷ (Λ[2, 0] : SSet.{u})) ≫
            (((∐ Aseq) ◁ Λ[2, 0].ι) ≫ P_A) := by
          rw [← Category.assoc,
            MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (i k ▷ (Λ[2, 0] : SSet.{u})) ≫
            ((Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ) := by
          rw [hagree, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Limits.Sigma.ι_map,
            MonoidalCategory.comp_whiskerRight, Category.assoc]
  have key : ∀ k, ∃ P : Bseq k ⊗ Δ[2] ⟶ C,
      (i k ▷ Δ[2]) ≫ P = (Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A ∧
        (Bseq k ◁ Λ[2, 0].ι) ≫ P =
          (Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ :=
    fun k ↦ h k _ _ (hagree_k k)
      (hornZeroVerticals_whiskerRight_comp _ P_Λ hVert)
  choose Pseq hP using key
  set hcB := isColimitCofanMkObjOfIsColimit (tensorRight Δ[2])
    Bseq _ (coproductIsCoproduct _) with hhcB
  set P := hcB.desc (Cofan.mk C Pseq) with hPdef
  have hPfac : ∀ k, (Sigma.ι Bseq k ▷ Δ[2]) ≫ P = Pseq k :=
    fun k ↦ hcB.fac _ ⟨k⟩
  refine ⟨P, ?_, ?_⟩
  · apply (isColimitCofanMkObjOfIsColimit (tensorRight Δ[2])
      Aseq _ (coproductIsCoproduct _)).hom_ext
    rintro ⟨k⟩
    change (Sigma.ι Aseq k ▷ Δ[2]) ≫
        ((Limits.Sigma.map i ▷ Δ[2]) ≫ P) =
      (Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A
    calc (Sigma.ι Aseq k ▷ Δ[2]) ≫
          ((Limits.Sigma.map i ▷ Δ[2]) ≫ P)
        = (i k ▷ Δ[2]) ≫ ((Sigma.ι Bseq k ▷ Δ[2]) ≫ P) := by
          rw [← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Limits.Sigma.ι_map,
            MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A := by
          rw [hPfac, (hP k).1]
  · apply (isColimitCofanMkObjOfIsColimit
      (tensorRight (Λ[2, 0] : SSet.{u})) Bseq _
      (coproductIsCoproduct _)).hom_ext
    rintro ⟨k⟩
    change (Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫
        (((∐ Bseq) ◁ Λ[2, 0].ι) ≫ P) =
      (Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ
    calc (Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫
          (((∐ Bseq) ◁ Λ[2, 0].ι) ≫ P)
        = (Bseq k ◁ Λ[2, 0].ι) ≫ ((Sigma.ι Bseq k ▷ Δ[2]) ≫ P) := by
          rw [← Category.assoc,
            ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (Sigma.ι Bseq k ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
          rw [hPfac, (hP k).2]

/-- **Horn-two `Δ[2]`-prism extension is stable under
coproducts** (the mirror). -/
theorem PrismTwoHornTwoExtension.sigmaMap
    {i : ∀ k, Aseq k ⟶ Bseq k}
    (h : ∀ k, PrismTwoHornTwoExtension (i k) C) :
    PrismTwoHornTwoExtension (Limits.Sigma.map i) C := by
  intro P_A P_Λ hagree hVert
  have hagree_k : ∀ k, (Aseq k ◁ Λ[2, 2].ι) ≫
        ((Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A) =
      (i k ▷ (Λ[2, 2] : SSet.{u})) ≫
        ((Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) := by
    intro k
    calc (Aseq k ◁ Λ[2, 2].ι) ≫ ((Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A)
        = (Sigma.ι Aseq k ▷ (Λ[2, 2] : SSet.{u})) ≫
            (((∐ Aseq) ◁ Λ[2, 2].ι) ≫ P_A) := by
          rw [← Category.assoc,
            MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (i k ▷ (Λ[2, 2] : SSet.{u})) ≫
            ((Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ) := by
          rw [hagree, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Limits.Sigma.ι_map,
            MonoidalCategory.comp_whiskerRight, Category.assoc]
  have key : ∀ k, ∃ P : Bseq k ⊗ Δ[2] ⟶ C,
      (i k ▷ Δ[2]) ≫ P = (Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A ∧
        (Bseq k ◁ Λ[2, 2].ι) ≫ P =
          (Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ :=
    fun k ↦ h k _ _ (hagree_k k)
      (hornTwoVerticals_whiskerRight_comp _ P_Λ hVert)
  choose Pseq hP using key
  set hcB := isColimitCofanMkObjOfIsColimit (tensorRight Δ[2])
    Bseq _ (coproductIsCoproduct _) with hhcB
  set P := hcB.desc (Cofan.mk C Pseq) with hPdef
  have hPfac : ∀ k, (Sigma.ι Bseq k ▷ Δ[2]) ≫ P = Pseq k :=
    fun k ↦ hcB.fac _ ⟨k⟩
  refine ⟨P, ?_, ?_⟩
  · apply (isColimitCofanMkObjOfIsColimit (tensorRight Δ[2])
      Aseq _ (coproductIsCoproduct _)).hom_ext
    rintro ⟨k⟩
    change (Sigma.ι Aseq k ▷ Δ[2]) ≫
        ((Limits.Sigma.map i ▷ Δ[2]) ≫ P) =
      (Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A
    calc (Sigma.ι Aseq k ▷ Δ[2]) ≫
          ((Limits.Sigma.map i ▷ Δ[2]) ≫ P)
        = (i k ▷ Δ[2]) ≫ ((Sigma.ι Bseq k ▷ Δ[2]) ≫ P) := by
          rw [← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Limits.Sigma.ι_map,
            MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (Sigma.ι Aseq k ▷ Δ[2]) ≫ P_A := by
          rw [hPfac, (hP k).1]
  · apply (isColimitCofanMkObjOfIsColimit
      (tensorRight (Λ[2, 2] : SSet.{u})) Bseq _
      (coproductIsCoproduct _)).hom_ext
    rintro ⟨k⟩
    change (Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫
        (((∐ Bseq) ◁ Λ[2, 2].ι) ≫ P) =
      (Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ
    calc (Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫
          (((∐ Bseq) ◁ Λ[2, 2].ι) ≫ P)
        = (Bseq k ◁ Λ[2, 2].ι) ≫ ((Sigma.ι Bseq k ▷ Δ[2]) ≫ P) := by
          rw [← Category.assoc,
            ← MonoidalCategory.whisker_exchange, Category.assoc]
      _ = (Sigma.ι Bseq k ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
          rw [hPfac, (hP k).2]

end Coproducts

/-!
## The `skeletonOfMono` tower: setup and steps

The tower is `relativeCellComplexOfMono i`: its functor is
`d ↦ (skeletonOfMono i d : SSet)`, its cocone legs are the
subcomplex inclusions, its step maps are
`relativeCellComplexOfMono.r i d`, and its bottom
isomorphism identifies `A` with stage `0` with
`isoBot.inv ≫ incl_0 = i` (`fac`). Each step satisfies each
extension property granted the cell cases, by coproduct +
cobase change along `relativeCellComplexOfMono.isPushout`.
-/

section SkeletonSetup

variable {A B C : SSet.{u}} (i : A ⟶ B) [Mono i] {κ : Fin 2}

/-- Stage `d` of the relative cell complex of `i` is the
subcomplex `skeletonOfMono i d` as a simplicial set. -/
lemma skeletonTower_obj (d : ℕ) :
    (relativeCellComplexOfMono i).F.obj d =
      ((skeletonOfMono i d : B.Subcomplex) : SSet.{u}) :=
  rfl

/-- The cocone leg at stage `d` is the subcomplex inclusion. -/
lemma skeletonTower_incl_app (d : ℕ) :
    (relativeCellComplexOfMono i).incl.app d =
      (skeletonOfMono i d).ι :=
  rfl

/-- The step map of the tower is
`relativeCellComplexOfMono.r i d`. -/
lemma skeletonTower_map_succ (d : ℕ) :
    (relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) =
      relativeCellComplexOfMono.r i d :=
  rfl

/-- The bottom inclusion factors through `i`:
`isoBot.hom ≫ i = incl_0`, from `fac`. -/
lemma skeletonTower_isoBot_hom_comp :
    (relativeCellComplexOfMono i).isoBot.hom ≫ i =
      (relativeCellComplexOfMono i).incl.app ⊥ := by
  calc (relativeCellComplexOfMono i).isoBot.hom ≫ i
      = (relativeCellComplexOfMono i).isoBot.hom ≫
          ((relativeCellComplexOfMono i).isoBot.inv ≫
            (relativeCellComplexOfMono i).incl.app ⊥) := by
        rw [(relativeCellComplexOfMono i).fac]
    _ = (relativeCellComplexOfMono i).incl.app ⊥ := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Naturality of the tower cocone at a step:
`step ≫ incl_{d+1} = incl_d`. -/
lemma skeletonTower_map_succ_comp_incl (d : ℕ) :
    (relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ≫
        (relativeCellComplexOfMono i).incl.app (d + 1) =
      (relativeCellComplexOfMono i).incl.app d := by
  have h : (relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ≫
        (relativeCellComplexOfMono i).incl.app (d + 1) =
      (relativeCellComplexOfMono i).incl.app d ≫ 𝟙 B :=
    (relativeCellComplexOfMono i).incl.naturality
      (homOfLE (Nat.le_succ d))
  exact h.trans (Category.comp_id _)

omit [Mono i] in
/-- **`Δ[1]`-prism extension along a skeleton step**,
unconditionally: the step is a pushout of a coproduct of
boundary inclusions. -/
theorem prismOneExtensionAt_skeletonStep [Quasicategory C] (d : ℕ) :
    PrismOneExtensionAt κ (relativeCellComplexOfMono.r i d) C := by
  have hl : PrismOneExtensionAt κ
      (relativeCellComplexOfMono.l i d) C :=
    PrismOneExtensionAt.sigmaMap
      (ι := relativeCellComplexOfMono.Cell i d)
      (Aseq := fun _ ↦ (∂Δ[d] : SSet.{u})) (Bseq := fun _ ↦ Δ[d])
      (i := fun _ ↦ ∂Δ[d].ι)
      (fun _ ↦ prismOneExtensionAt_boundary (n := d) κ)
  exact PrismOneExtensionAt.of_isPushout
    (relativeCellComplexOfMono.isPushout i d).flip hl

omit [Mono i] in
/-- **Horn-zero `Δ[2]` extension along a skeleton step**,
granted the cell shuffle input at `d`. -/
theorem prismTwoHornZeroExtension_skeletonStep [Quasicategory C]
    (hcell : ∀ n, ShuffleHornZeroCellExtension n C) (d : ℕ) :
    PrismTwoHornZeroExtension (relativeCellComplexOfMono.r i d) C := by
  have hl : PrismTwoHornZeroExtension
      (relativeCellComplexOfMono.l i d) C :=
    PrismTwoHornZeroExtension.sigmaMap
      (ι := relativeCellComplexOfMono.Cell i d)
      (Aseq := fun _ ↦ (∂Δ[d] : SSet.{u})) (Bseq := fun _ ↦ Δ[d])
      (i := fun _ ↦ ∂Δ[d].ι) (fun _ ↦
        prismTwoHornZeroExtension_boundary_of_shuffleCell (hcell d))
  exact PrismTwoHornZeroExtension.of_isPushout
    (relativeCellComplexOfMono.isPushout i d).flip hl

omit [Mono i] in
/-- **Horn-two `Δ[2]` extension along a skeleton step**,
granted the cell shuffle input at `d` (the mirror). -/
theorem prismTwoHornTwoExtension_skeletonStep [Quasicategory C]
    (hcell : ∀ n, ShuffleHornTwoCellExtension n C) (d : ℕ) :
    PrismTwoHornTwoExtension (relativeCellComplexOfMono.r i d) C := by
  have hl : PrismTwoHornTwoExtension
      (relativeCellComplexOfMono.l i d) C :=
    PrismTwoHornTwoExtension.sigmaMap
      (ι := relativeCellComplexOfMono.Cell i d)
      (Aseq := fun _ ↦ (∂Δ[d] : SSet.{u})) (Bseq := fun _ ↦ Δ[d])
      (i := fun _ ↦ ∂Δ[d].ι) (fun _ ↦
        prismTwoHornTwoExtension_boundary_of_shuffleCell (hcell d))
  exact PrismTwoHornTwoExtension.of_isPushout
    (relativeCellComplexOfMono.isPushout i d).flip hl

end SkeletonSetup

/-!
## The tower: `Δ[1]` extension along a monomorphism

Compatible prisms over the stages are chosen by recursion
(`Nat.rec` on the subtype of prisms with the prescribed
section and equivalence verticals, fed by the step
existence), descended along the colimit preserved by
`tensorRight Δ[1]`, and checked at stage `0` (restriction,
through `fac`), at every stage (section, by joint
epimorphy), and at stage `1` (verticals, since every vertex
already lies there).
-/

section SkeletonTowerOne

variable {A B C : SSet.{u}} {κ : Fin 2}

/-- **`Δ[1]`-prism extension along every monomorphism**,
unconditionally for a quasicategory `C`: the cell cases of
`ShuffleBridges.lean` closed under coproducts, cobase
change, and the `skeletonOfMono` tower. -/
theorem prismOneExtensionAt_of_mono (κ : Fin 2) (i : A ⟶ B)
    [Mono i] [Quasicategory C] :
    PrismOneExtensionAt κ i C := by
  intro H g hagree hVert
  have fac0 : (relativeCellComplexOfMono i).isoBot.inv ≫
        (relativeCellComplexOfMono i).incl.app 0 = i :=
    (relativeCellComplexOfMono i).fac
  have hhom0 : (relativeCellComplexOfMono i).isoBot.hom ≫ i =
      (relativeCellComplexOfMono i).incl.app 0 :=
    skeletonTower_isoBot_hom_comp i
  have hstep : ∀ d, PrismOneExtensionAt κ
      ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d))) C := by
    intro d
    rw [skeletonTower_map_succ]
    exact prismOneExtensionAt_skeletonStep i d
  set H0 : (relativeCellComplexOfMono i).F.obj 0 ⊗ Δ[1] ⟶ C :=
    ((relativeCellComplexOfMono i).isoBot.hom ▷ Δ[1]) ≫ H with hH0def
  have hH0sec : prismSectionAt ((relativeCellComplexOfMono i).F.obj 0) κ ≫ H0 =
      (relativeCellComplexOfMono i).incl.app 0 ≫ g := by
    calc prismSectionAt ((relativeCellComplexOfMono i).F.obj 0) κ ≫ H0
        = (relativeCellComplexOfMono i).isoBot.hom ≫
            (prismSectionAt A κ ≫ H) := by
          rw [hH0def, ← Category.assoc,
            prismSectionAt_comp_whiskerRight, Category.assoc]
      _ = (relativeCellComplexOfMono i).incl.app 0 ≫ g := by
          rw [hagree, ← Category.assoc, hhom0]
  have hH0vert : PrismOneVerticalsEquivalences H0 :=
    prismOneVerticalsEquivalences_whiskerRight_comp _ H hVert
  have stepEx : ∀ (d : ℕ)
      (Fd : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[1] ⟶ C),
      prismSectionAt ((relativeCellComplexOfMono i).F.obj d) κ ≫ Fd =
          (relativeCellComplexOfMono i).incl.app d ≫ g →
      PrismOneVerticalsEquivalences Fd →
      ∃ F' : (relativeCellComplexOfMono i).F.obj (d + 1) ⊗ Δ[1] ⟶ C,
        ((relativeCellComplexOfMono i).F.map
            (homOfLE (Nat.le_succ d)) ▷ Δ[1]) ≫ F' = Fd ∧
          prismSectionAt ((relativeCellComplexOfMono i).F.obj (d + 1)) κ ≫ F' =
            (relativeCellComplexOfMono i).incl.app (d + 1) ≫ g ∧
            PrismOneVerticalsEquivalences F' := by
    intro d Fd hsec hvert
    have hagree' : prismSectionAt ((relativeCellComplexOfMono i).F.obj d) κ ≫ Fd =
        (relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ≫
          ((relativeCellComplexOfMono i).incl.app (d + 1) ≫ g) := by
      rw [hsec, ← Category.assoc, skeletonTower_map_succ_comp_incl]
    exact hstep d Fd _ hagree' hvert
  choose next hnext using stepEx
  set tower : ∀ d, { F : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[1] ⟶ C //
      prismSectionAt ((relativeCellComplexOfMono i).F.obj d) κ ≫ F =
          (relativeCellComplexOfMono i).incl.app d ≫ g ∧
        PrismOneVerticalsEquivalences F } :=
    fun d ↦ Nat.rec (motive := fun d ↦
      { F : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[1] ⟶ C //
        prismSectionAt ((relativeCellComplexOfMono i).F.obj d) κ ≫ F =
            (relativeCellComplexOfMono i).incl.app d ≫ g ∧
          PrismOneVerticalsEquivalences F })
      ⟨H0, hH0sec, hH0vert⟩
      (fun d ih ↦ ⟨next d ih.1 ih.2.1 ih.2.2,
        (hnext d ih.1 ih.2.1 ih.2.2).2⟩) d with htowerdef
  have hFsec : ∀ d,
      prismSectionAt ((relativeCellComplexOfMono i).F.obj d) κ ≫ (tower d).1 =
        (relativeCellComplexOfMono i).incl.app d ≫ g :=
    fun d ↦ (tower d).2.1
  have hFvert : ∀ d, PrismOneVerticalsEquivalences (tower d).1 :=
    fun d ↦ (tower d).2.2
  have hF0 : (tower 0).1 = H0 := rfl
  have hFsucc : ∀ d,
      ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ▷ Δ[1]) ≫
          (tower (d + 1)).1 = (tower d).1 :=
    fun d ↦ (hnext d (tower d).1 (hFsec d) (hFvert d)).1
  have hcompat : ∀ {d e : ℕ} (h : d ≤ e),
      ((relativeCellComplexOfMono i).F.map (homOfLE h) ▷ Δ[1]) ≫
          (tower e).1 = (tower d).1 := by
    intro d e h
    induction h with
    | refl =>
      have e1 : (relativeCellComplexOfMono i).F.map
          (homOfLE (Nat.le.refl (n := d))) =
          𝟙 ((relativeCellComplexOfMono i).F.obj d) := by
        rw [show homOfLE (Nat.le.refl (n := d)) = 𝟙 d from
          Subsingleton.elim _ _]
        exact CategoryTheory.Functor.map_id _ _
      rw [e1]
      change (tensorRight Δ[1]).map (𝟙 _) ≫ (tower d).1 = (tower d).1
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    | step hde ih =>
      have e2 : (relativeCellComplexOfMono i).F.map
          (homOfLE (Nat.le.step hde)) =
          (relativeCellComplexOfMono i).F.map (homOfLE hde) ≫
            (relativeCellComplexOfMono i).F.map
              (homOfLE (Nat.le_succ _)) := by
        rw [← CategoryTheory.Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)
      rw [e2, MonoidalCategory.comp_whiskerRight, Category.assoc,
        hFsucc, ih]
  set hc := isColimitOfPreserves (tensorRight Δ[1])
    (relativeCellComplexOfMono i).isColimit with hhcdef
  set F : B ⊗ Δ[1] ⟶ C := hc.desc
    { pt := C,
      ι := { app := fun d ↦ (tower d).1,
             naturality := by
               intro d e h
               have hh : h = homOfLE (leOfHom h) := Subsingleton.elim _ _
               rw [hh]
               exact (hcompat (leOfHom h)).trans
                 (Category.comp_id _).symm } } with hFdef
  have hfac : ∀ d,
      ((relativeCellComplexOfMono i).incl.app d ▷ Δ[1]) ≫ F = (tower d).1 :=
    fun d ↦ hc.fac _ d
  refine ⟨F, ?_, ?_, ?_⟩
  · calc (i ▷ Δ[1]) ≫ F
        = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[1]) ≫ H0 := by
          calc (i ▷ Δ[1]) ≫ F
              = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[1]) ≫
                  (((relativeCellComplexOfMono i).incl.app 0 ▷ Δ[1]) ≫ F) := by
                rw [← Category.assoc,
                  ← MonoidalCategory.comp_whiskerRight, fac0]
            _ = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[1]) ≫ H0 := by
                rw [hfac, hF0]
      _ = H := by
          rw [hH0def, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id]
          change (tensorRight Δ[1]).map (𝟙 _) ≫ H = H
          rw [CategoryTheory.Functor.map_id, Category.id_comp]
  · apply (relativeCellComplexOfMono i).isColimit.hom_ext
    intro d
    change (relativeCellComplexOfMono i).incl.app d ≫
        (prismSectionAt B κ ≫ F) =
      (relativeCellComplexOfMono i).incl.app d ≫ g
    calc (relativeCellComplexOfMono i).incl.app d ≫
          (prismSectionAt B κ ≫ F)
        = prismSectionAt ((relativeCellComplexOfMono i).F.obj d) κ ≫
            (((relativeCellComplexOfMono i).incl.app d ▷ Δ[1]) ≫ F) := by
          rw [← Category.assoc (prismSectionAt _ κ) _ F,
            ← Category.assoc]
          exact congrArg (· ≫ F) (prismSectionAt_comp_whiskerRight
            ((relativeCellComplexOfMono i).incl.app d) (m := 1) κ).symm
      _ = (relativeCellComplexOfMono i).incl.app d ≫ g := by
          rw [hfac, hFsec]
  · intro y
    have hmem : y ∈ (skeletonOfMono i 1).obj (op ⦋0⦌) := by
      rw [skeletonOfMono_obj_eq_top i (show 0 < 1 by norm_num)]
      trivial
    set x1 : (relativeCellComplexOfMono i).F.obj 1 _⦋0⦌ :=
      ⟨y, hmem⟩ with hx1def
    have hx1 : ((relativeCellComplexOfMono i).incl.app 1).app _ x1 = y :=
      rfl
    refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
        Edge.mk' ((tower 1).1.app _ (verticalOneSimplex x1))) ?_).2
      (hFvert 1 x1)
    change F.app _ (verticalOneSimplex y) =
      (tower 1).1.app _ (verticalOneSimplex x1)
    calc F.app _ (verticalOneSimplex y)
        = (((relativeCellComplexOfMono i).incl.app 1 ▷ Δ[1]) ≫ F).app _
            (verticalOneSimplex x1) := by
          change F.app _ (verticalOneSimplex y) =
            F.app _ (((relativeCellComplexOfMono i).incl.app 1 ▷ Δ[1]).app _
              (verticalOneSimplex x1))
          rw [whiskerRight_app_verticalOneSimplex, hx1]
      _ = (tower 1).1.app _ (verticalOneSimplex x1) :=
          congr($(hfac 1).app _ (verticalOneSimplex x1))

/-- **Source-prescribed `Δ[1]`-prism extension along every
monomorphism**, unconditionally. -/
theorem prismSrcExtension_of_mono (i : A ⟶ B) [Mono i]
    [Quasicategory C] :
    PrismSrcExtension i C :=
  prismSrcExtension_iff_oneExtensionAt_zero.2
    (prismOneExtensionAt_of_mono 0 i)

/-- **Target-prescribed `Δ[1]`-prism extension along every
monomorphism**, unconditionally. -/
theorem prismTgtExtension_of_mono (i : A ⟶ B) [Mono i]
    [Quasicategory C] :
    PrismTgtExtension i C :=
  prismTgtExtension_iff_oneExtensionAt_one.2
    (prismOneExtensionAt_of_mono 1 i)

end SkeletonTowerOne

/-!
## The tower: `Δ[2]` extension along a monomorphism

The same recursion with the horn face in place of the
section, and with the horn verticals at every stage the
restrictions of the global ones. The descended prism is
checked at stage `0` (restriction) and over the
`Λ`-tensored colimit (horn face). Both theorems are
implications from the cell shuffle inputs, in the hypothesis
style of `ShuffleBridges.lean`.
-/

section SkeletonTowerTwo

variable {A B C : SSet.{u}}

/-- **Horn-zero `Δ[2]`-prism extension along every
monomorphism, granted the horn-zero cell shuffle inputs:**
the cell bridge of `ShuffleBridges.lean` closed under
coproducts, cobase change, and the `skeletonOfMono` tower. -/
theorem prismTwoHornZeroExtension_of_mono_of_shuffleCell
    (i : A ⟶ B) [Mono i] [Quasicategory C]
    (hcell : ∀ n, ShuffleHornZeroCellExtension n C) :
    PrismTwoHornZeroExtension i C := by
  intro P_A P_Λ hagree hVert
  have fac0 : (relativeCellComplexOfMono i).isoBot.inv ≫
        (relativeCellComplexOfMono i).incl.app 0 = i :=
    (relativeCellComplexOfMono i).fac
  have hhom0 : (relativeCellComplexOfMono i).isoBot.hom ≫ i =
      (relativeCellComplexOfMono i).incl.app 0 :=
    skeletonTower_isoBot_hom_comp i
  have hstep : ∀ d, PrismTwoHornZeroExtension
      ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d))) C := by
    intro d
    rw [skeletonTower_map_succ]
    exact prismTwoHornZeroExtension_skeletonStep i hcell d
  set P0 : (relativeCellComplexOfMono i).F.obj 0 ⊗ Δ[2] ⟶ C :=
    ((relativeCellComplexOfMono i).isoBot.hom ▷ Δ[2]) ≫ P_A with hP0def
  have hP0face : ((relativeCellComplexOfMono i).F.obj 0 ◁ Λ[2, 0].ι) ≫ P0 =
      ((relativeCellComplexOfMono i).incl.app 0 ▷
        (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
    calc ((relativeCellComplexOfMono i).F.obj 0 ◁ Λ[2, 0].ι) ≫ P0
        = ((relativeCellComplexOfMono i).isoBot.hom ▷
            (Λ[2, 0] : SSet.{u})) ≫ ((A ◁ Λ[2, 0].ι) ≫ P_A) := by
          rw [hP0def, ← Category.assoc,
            MonoidalCategory.whisker_exchange, Category.assoc]
      _ = ((relativeCellComplexOfMono i).incl.app 0 ▷
            (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
          rw [hagree, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, hhom0]
  have stepEx : ∀ (d : ℕ)
      (Pd : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[2] ⟶ C),
      ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 0].ι) ≫ Pd =
          ((relativeCellComplexOfMono i).incl.app d ▷
            (Λ[2, 0] : SSet.{u})) ≫ P_Λ →
      ∃ P' : (relativeCellComplexOfMono i).F.obj (d + 1) ⊗ Δ[2] ⟶ C,
        ((relativeCellComplexOfMono i).F.map
            (homOfLE (Nat.le_succ d)) ▷ Δ[2]) ≫ P' = Pd ∧
          ((relativeCellComplexOfMono i).F.obj (d + 1) ◁ Λ[2, 0].ι) ≫ P' =
            ((relativeCellComplexOfMono i).incl.app (d + 1) ▷
              (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
    intro d Pd hface
    have hagree' : ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 0].ι) ≫ Pd =
        ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ▷
          (Λ[2, 0] : SSet.{u})) ≫
          (((relativeCellComplexOfMono i).incl.app (d + 1) ▷
            (Λ[2, 0] : SSet.{u})) ≫ P_Λ) := by
      rw [hface, ← Category.assoc,
        ← MonoidalCategory.comp_whiskerRight,
        skeletonTower_map_succ_comp_incl]
    exact hstep d Pd _ hagree'
      (hornZeroVerticals_whiskerRight_comp _ P_Λ hVert)
  choose next hnext using stepEx
  set tower : ∀ d, { P : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[2] ⟶ C //
      ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 0].ι) ≫ P =
        ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 0] : SSet.{u})) ≫ P_Λ } :=
    fun d ↦ Nat.rec (motive := fun d ↦
      { P : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[2] ⟶ C //
        ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 0].ι) ≫ P =
          ((relativeCellComplexOfMono i).incl.app d ▷
            (Λ[2, 0] : SSet.{u})) ≫ P_Λ })
      ⟨P0, hP0face⟩
      (fun d ih ↦ ⟨next d ih.1 ih.2, (hnext d ih.1 ih.2).2⟩) d with htowerdef
  have hPface : ∀ d,
      ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 0].ι) ≫ (tower d).1 =
        ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 0] : SSet.{u})) ≫ P_Λ :=
    fun d ↦ (tower d).2
  have hP0 : (tower 0).1 = P0 := rfl
  have hPsucc : ∀ d,
      ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ▷ Δ[2]) ≫
          (tower (d + 1)).1 = (tower d).1 :=
    fun d ↦ (hnext d (tower d).1 (hPface d)).1
  have hcompat : ∀ {d e : ℕ} (h : d ≤ e),
      ((relativeCellComplexOfMono i).F.map (homOfLE h) ▷ Δ[2]) ≫
          (tower e).1 = (tower d).1 := by
    intro d e h
    induction h with
    | refl =>
      have e1 : (relativeCellComplexOfMono i).F.map
          (homOfLE (Nat.le.refl (n := d))) =
          𝟙 ((relativeCellComplexOfMono i).F.obj d) := by
        rw [show homOfLE (Nat.le.refl (n := d)) = 𝟙 d from
          Subsingleton.elim _ _]
        exact CategoryTheory.Functor.map_id _ _
      rw [e1]
      change (tensorRight Δ[2]).map (𝟙 _) ≫ (tower d).1 = (tower d).1
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    | step hde ih =>
      have e2 : (relativeCellComplexOfMono i).F.map
          (homOfLE (Nat.le.step hde)) =
          (relativeCellComplexOfMono i).F.map (homOfLE hde) ≫
            (relativeCellComplexOfMono i).F.map
              (homOfLE (Nat.le_succ _)) := by
        rw [← CategoryTheory.Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)
      rw [e2, MonoidalCategory.comp_whiskerRight, Category.assoc,
        hPsucc, ih]
  set hc := isColimitOfPreserves (tensorRight Δ[2])
    (relativeCellComplexOfMono i).isColimit with hhcdef
  set P : B ⊗ Δ[2] ⟶ C := hc.desc
    { pt := C,
      ι := { app := fun d ↦ (tower d).1,
             naturality := by
               intro d e h
               have hh : h = homOfLE (leOfHom h) := Subsingleton.elim _ _
               rw [hh]
               exact (hcompat (leOfHom h)).trans
                 (Category.comp_id _).symm } } with hPdef
  have hfac : ∀ d,
      ((relativeCellComplexOfMono i).incl.app d ▷ Δ[2]) ≫ P = (tower d).1 :=
    fun d ↦ hc.fac _ d
  refine ⟨P, ?_, ?_⟩
  · calc (i ▷ Δ[2]) ≫ P
        = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[2]) ≫ P0 := by
          calc (i ▷ Δ[2]) ≫ P
              = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[2]) ≫
                  (((relativeCellComplexOfMono i).incl.app 0 ▷ Δ[2]) ≫ P) := by
                rw [← Category.assoc,
                  ← MonoidalCategory.comp_whiskerRight, fac0]
            _ = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[2]) ≫ P0 := by
                rw [hfac, hP0]
      _ = P_A := by
          rw [hP0def, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id]
          change (tensorRight Δ[2]).map (𝟙 _) ≫ P_A = P_A
          rw [CategoryTheory.Functor.map_id, Category.id_comp]
  · apply (isColimitOfPreserves (tensorRight (Λ[2, 0] : SSet.{u}))
      (relativeCellComplexOfMono i).isColimit).hom_ext
    intro d
    change ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 0] : SSet.{u})) ≫ ((B ◁ Λ[2, 0].ι) ≫ P) =
        ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 0] : SSet.{u})) ≫ P_Λ
    calc ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 0] : SSet.{u})) ≫ ((B ◁ Λ[2, 0].ι) ≫ P)
        = ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 0].ι) ≫
            (((relativeCellComplexOfMono i).incl.app d ▷ Δ[2]) ≫ P) := by
          rw [← Category.assoc
              (((relativeCellComplexOfMono i).F.obj d) ◁ Λ[2, 0].ι) _ P,
            ← Category.assoc]
          exact congrArg (· ≫ P) (MonoidalCategory.whisker_exchange
            ((relativeCellComplexOfMono i).incl.app d) Λ[2, 0].ι).symm
      _ = ((relativeCellComplexOfMono i).incl.app d ▷
            (Λ[2, 0] : SSet.{u})) ≫ P_Λ := by
          rw [hfac, hPface]


/-- **Horn-two `Δ[2]`-prism extension along every
monomorphism, granted the horn-two cell shuffle inputs:**
the mirror of `prismTwoHornZeroExtension_of_mono_of_shuffleCell`. -/
theorem prismTwoHornTwoExtension_of_mono_of_shuffleCell
    (i : A ⟶ B) [Mono i] [Quasicategory C]
    (hcell : ∀ n, ShuffleHornTwoCellExtension n C) :
    PrismTwoHornTwoExtension i C := by
  intro P_A P_Λ hagree hVert
  have fac0 : (relativeCellComplexOfMono i).isoBot.inv ≫
        (relativeCellComplexOfMono i).incl.app 0 = i :=
    (relativeCellComplexOfMono i).fac
  have hhom0 : (relativeCellComplexOfMono i).isoBot.hom ≫ i =
      (relativeCellComplexOfMono i).incl.app 0 :=
    skeletonTower_isoBot_hom_comp i
  have hstep : ∀ d, PrismTwoHornTwoExtension
      ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d))) C := by
    intro d
    rw [skeletonTower_map_succ]
    exact prismTwoHornTwoExtension_skeletonStep i hcell d
  set P0 : (relativeCellComplexOfMono i).F.obj 0 ⊗ Δ[2] ⟶ C :=
    ((relativeCellComplexOfMono i).isoBot.hom ▷ Δ[2]) ≫ P_A with hP0def
  have hP0face : ((relativeCellComplexOfMono i).F.obj 0 ◁ Λ[2, 2].ι) ≫ P0 =
      ((relativeCellComplexOfMono i).incl.app 0 ▷
        (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
    calc ((relativeCellComplexOfMono i).F.obj 0 ◁ Λ[2, 2].ι) ≫ P0
        = ((relativeCellComplexOfMono i).isoBot.hom ▷
            (Λ[2, 2] : SSet.{u})) ≫ ((A ◁ Λ[2, 2].ι) ≫ P_A) := by
          rw [hP0def, ← Category.assoc,
            MonoidalCategory.whisker_exchange, Category.assoc]
      _ = ((relativeCellComplexOfMono i).incl.app 0 ▷
            (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
          rw [hagree, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, hhom0]
  have stepEx : ∀ (d : ℕ)
      (Pd : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[2] ⟶ C),
      ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 2].ι) ≫ Pd =
          ((relativeCellComplexOfMono i).incl.app d ▷
            (Λ[2, 2] : SSet.{u})) ≫ P_Λ →
      ∃ P' : (relativeCellComplexOfMono i).F.obj (d + 1) ⊗ Δ[2] ⟶ C,
        ((relativeCellComplexOfMono i).F.map
            (homOfLE (Nat.le_succ d)) ▷ Δ[2]) ≫ P' = Pd ∧
          ((relativeCellComplexOfMono i).F.obj (d + 1) ◁ Λ[2, 2].ι) ≫ P' =
            ((relativeCellComplexOfMono i).incl.app (d + 1) ▷
              (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
    intro d Pd hface
    have hagree' : ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 2].ι) ≫ Pd =
        ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ▷
          (Λ[2, 2] : SSet.{u})) ≫
          (((relativeCellComplexOfMono i).incl.app (d + 1) ▷
            (Λ[2, 2] : SSet.{u})) ≫ P_Λ) := by
      rw [hface, ← Category.assoc,
        ← MonoidalCategory.comp_whiskerRight,
        skeletonTower_map_succ_comp_incl]
    exact hstep d Pd _ hagree'
      (hornTwoVerticals_whiskerRight_comp _ P_Λ hVert)
  choose next hnext using stepEx
  set tower : ∀ d, { P : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[2] ⟶ C //
      ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 2].ι) ≫ P =
        ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 2] : SSet.{u})) ≫ P_Λ } :=
    fun d ↦ Nat.rec (motive := fun d ↦
      { P : (relativeCellComplexOfMono i).F.obj d ⊗ Δ[2] ⟶ C //
        ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 2].ι) ≫ P =
          ((relativeCellComplexOfMono i).incl.app d ▷
            (Λ[2, 2] : SSet.{u})) ≫ P_Λ })
      ⟨P0, hP0face⟩
      (fun d ih ↦ ⟨next d ih.1 ih.2, (hnext d ih.1 ih.2).2⟩) d with htowerdef
  have hPface : ∀ d,
      ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 2].ι) ≫ (tower d).1 =
        ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 2] : SSet.{u})) ≫ P_Λ :=
    fun d ↦ (tower d).2
  have hP0 : (tower 0).1 = P0 := rfl
  have hPsucc : ∀ d,
      ((relativeCellComplexOfMono i).F.map (homOfLE (Nat.le_succ d)) ▷ Δ[2]) ≫
          (tower (d + 1)).1 = (tower d).1 :=
    fun d ↦ (hnext d (tower d).1 (hPface d)).1
  have hcompat : ∀ {d e : ℕ} (h : d ≤ e),
      ((relativeCellComplexOfMono i).F.map (homOfLE h) ▷ Δ[2]) ≫
          (tower e).1 = (tower d).1 := by
    intro d e h
    induction h with
    | refl =>
      have e1 : (relativeCellComplexOfMono i).F.map
          (homOfLE (Nat.le.refl (n := d))) =
          𝟙 ((relativeCellComplexOfMono i).F.obj d) := by
        rw [show homOfLE (Nat.le.refl (n := d)) = 𝟙 d from
          Subsingleton.elim _ _]
        exact CategoryTheory.Functor.map_id _ _
      rw [e1]
      change (tensorRight Δ[2]).map (𝟙 _) ≫ (tower d).1 = (tower d).1
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    | step hde ih =>
      have e2 : (relativeCellComplexOfMono i).F.map
          (homOfLE (Nat.le.step hde)) =
          (relativeCellComplexOfMono i).F.map (homOfLE hde) ≫
            (relativeCellComplexOfMono i).F.map
              (homOfLE (Nat.le_succ _)) := by
        rw [← CategoryTheory.Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)
      rw [e2, MonoidalCategory.comp_whiskerRight, Category.assoc,
        hPsucc, ih]
  set hc := isColimitOfPreserves (tensorRight Δ[2])
    (relativeCellComplexOfMono i).isColimit with hhcdef
  set P : B ⊗ Δ[2] ⟶ C := hc.desc
    { pt := C,
      ι := { app := fun d ↦ (tower d).1,
             naturality := by
               intro d e h
               have hh : h = homOfLE (leOfHom h) := Subsingleton.elim _ _
               rw [hh]
               exact (hcompat (leOfHom h)).trans
                 (Category.comp_id _).symm } } with hPdef
  have hfac : ∀ d,
      ((relativeCellComplexOfMono i).incl.app d ▷ Δ[2]) ≫ P = (tower d).1 :=
    fun d ↦ hc.fac _ d
  refine ⟨P, ?_, ?_⟩
  · calc (i ▷ Δ[2]) ≫ P
        = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[2]) ≫ P0 := by
          calc (i ▷ Δ[2]) ≫ P
              = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[2]) ≫
                  (((relativeCellComplexOfMono i).incl.app 0 ▷ Δ[2]) ≫ P) := by
                rw [← Category.assoc,
                  ← MonoidalCategory.comp_whiskerRight, fac0]
            _ = ((relativeCellComplexOfMono i).isoBot.inv ▷ Δ[2]) ≫ P0 := by
                rw [hfac, hP0]
      _ = P_A := by
          rw [hP0def, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id]
          change (tensorRight Δ[2]).map (𝟙 _) ≫ P_A = P_A
          rw [CategoryTheory.Functor.map_id, Category.id_comp]
  · apply (isColimitOfPreserves (tensorRight (Λ[2, 2] : SSet.{u}))
      (relativeCellComplexOfMono i).isColimit).hom_ext
    intro d
    change ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 2] : SSet.{u})) ≫ ((B ◁ Λ[2, 2].ι) ≫ P) =
        ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 2] : SSet.{u})) ≫ P_Λ
    calc ((relativeCellComplexOfMono i).incl.app d ▷
          (Λ[2, 2] : SSet.{u})) ≫ ((B ◁ Λ[2, 2].ι) ≫ P)
        = ((relativeCellComplexOfMono i).F.obj d ◁ Λ[2, 2].ι) ≫
            (((relativeCellComplexOfMono i).incl.app d ▷ Δ[2]) ≫ P) := by
          rw [← Category.assoc
              (((relativeCellComplexOfMono i).F.obj d) ◁ Λ[2, 2].ι) _ P,
            ← Category.assoc]
          exact congrArg (· ≫ P) (MonoidalCategory.whisker_exchange
            ((relativeCellComplexOfMono i).incl.app d) Λ[2, 2].ι).symm
      _ = ((relativeCellComplexOfMono i).incl.app d ▷
            (Λ[2, 2] : SSet.{u})) ≫ P_Λ := by
          rw [hfac, hPface]

end SkeletonTowerTwo

/-!
## The two-inverse criterion and prism endpoints

The shuffle extensions output two a priori different inverse
prisms; the two `CompStruct` witnesses give the two
`toHoHom` inverse equations, and the standard left/right
inverse computation identifies the two inverses. Endpoints
of prisms are read through the sections (for the lifted
prism) and through the simplicial identities `δδ` (for
faces of `Δ[2]`-prisms).
-/

section TwoInverseEndpoints

variable {A B C X : SSet.{u}} {x₀ x₁ : ((ihom B).obj C) _⦋0⦌}

/-- **A prism edge with two one-sided inverse `Δ[2]`-prisms
is an equivalence.** The two-inverse form of the supporting result
`edgeOfPrism_isEquivalence_of_compPrisms`: `P` witnesses
`F ≫ G₁ = id` and `Q` witnesses `G₂ ≫ F = id` at the level
of `Edge.toHoHom`, so the two inverse edges have equal
`toHoHom` and `F`'s edge is an isomorphism. -/
theorem edgeOfPrism_isEquivalence_of_twoCompPrisms
    (F G₁ G₂ : B ⊗ Δ[1] ⟶ C)
    (hF₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism F) = x₀)
    (hF₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) = x₁)
    (hG₁₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism G₁) = x₁)
    (hG₁₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism G₁) = x₀)
    (hG₂₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism G₂) = x₁)
    (hG₂₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism G₂) = x₀)
    (P Q : B ⊗ Δ[2] ⟶ C)
    (hP₂ : (B ◁ stdSimplex.δ 2) ≫ P = F)
    (hP₀ : (B ◁ stdSimplex.δ 0) ≫ P = G₁)
    (hP₁ : (B ◁ stdSimplex.δ 1) ≫ P =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F)
    (hQ₂ : (B ◁ stdSimplex.δ 2) ≫ Q = G₂)
    (hQ₀ : (B ◁ stdSimplex.δ 0) ≫ Q = F)
    (hQ₁ : (B ◁ stdSimplex.δ 1) ≫ Q =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ G₂) :
    (edgeOfPrism F hF₀ hF₁).IsEquivalence := by
  have hcompP : Edge.CompStruct (edgeOfPrism F hF₀ hF₁)
      (edgeOfPrism G₁ hG₁₀ hG₁₁) (Edge.id x₀) :=
    Edge.CompStruct.mk (ihomSimplexOfPrism P)
      (by rw [δ_ihomSimplexOfPrism, hP₂, edgeOfPrism_edge])
      (by rw [δ_ihomSimplexOfPrism, hP₀, edgeOfPrism_edge])
      (by
        rw [δ_ihomSimplexOfPrism, hP₁, ← σ_ihomSimplexOfPrism,
          ← δ_ihomSimplexOfPrism, hF₀, Edge.id_edge])
  have hcompQ : Edge.CompStruct (edgeOfPrism G₂ hG₂₀ hG₂₁)
      (edgeOfPrism F hF₀ hF₁) (Edge.id x₁) :=
    Edge.CompStruct.mk (ihomSimplexOfPrism Q)
      (by rw [δ_ihomSimplexOfPrism, hQ₂, edgeOfPrism_edge])
      (by rw [δ_ihomSimplexOfPrism, hQ₀, edgeOfPrism_edge])
      (by
        rw [δ_ihomSimplexOfPrism, hQ₁, ← σ_ihomSimplexOfPrism,
          ← δ_ihomSimplexOfPrism, hG₂₀, Edge.id_edge])
  have h1 : (edgeOfPrism F hF₀ hF₁).toHoHom ≫
      (edgeOfPrism G₁ hG₁₀ hG₁₁).toHoHom =
      𝟙 (HomotopyCategory.mk x₀) := by
    rw [Edge.toHoHom_comp hcompP, Edge.toHoHom_id]
  have h2 : (edgeOfPrism G₂ hG₂₀ hG₂₁).toHoHom ≫
      (edgeOfPrism F hF₀ hF₁).toHoHom =
      𝟙 (HomotopyCategory.mk x₁) := by
    rw [Edge.toHoHom_comp hcompQ, Edge.toHoHom_id]
  have heq : (edgeOfPrism G₁ hG₁₀ hG₁₁).toHoHom =
      (edgeOfPrism G₂ hG₂₀ hG₂₁).toHoHom := by
    calc (edgeOfPrism G₁ hG₁₀ hG₁₁).toHoHom
        = (𝟙 (HomotopyCategory.mk x₁)) ≫
            (edgeOfPrism G₁ hG₁₀ hG₁₁).toHoHom :=
          (Category.id_comp _).symm
      _ = (edgeOfPrism G₂ hG₂₀ hG₂₁).toHoHom := by
          rw [← h2, Category.assoc, h1, Category.comp_id]
  exact ⟨⟨(edgeOfPrism G₁ hG₁₀ hG₁₁).toHoHom, h1, heq ▸ h2⟩⟩

/-- The vertex classified by the source section of a prism
is the `δ₁`-face of its simplex. -/
lemma ihomVertexEquiv_prismSectionAt_zero_comp (F : X ⊗ Δ[1] ⟶ C) :
    ihomVertexEquiv X C (prismSectionAt X 0 ≫ F) =
      ((ihom X).obj C).δ 1 (ihomSimplexOfPrism F) := by
  rw [δ_one_ihomSimplexOfPrism, ← Category.assoc,
    prismSectionZero_whiskerLeft_δ_one]

/-- The vertex classified by the target section of a prism
is the `δ₀`-face of its simplex. -/
lemma ihomVertexEquiv_prismSectionAt_one_comp (F : X ⊗ Δ[1] ⟶ C) :
    ihomVertexEquiv X C (prismSectionAt X 1 ≫ F) =
      ((ihom X).obj C).δ 0 (ihomSimplexOfPrism F) := by
  rw [δ_zero_ihomSimplexOfPrism, ← Category.assoc,
    prismSectionZero_whiskerLeft_δ_zero]

/-- Simplicial identity `δ₁δ₀ = δ₀δ₂` on `2`-simplices:
the source of the `δ₀`-face is the target of the
`δ₂`-face. -/
lemma delta_one_delta_zero_apply (s : X _⦋2⦌) :
    X.δ 1 (X.δ 0 s) = X.δ 0 (X.δ 2 s) := by
  have h := δ_comp_δ_apply (S := X) (n := 0) (i := (0 : Fin 2))
    (j := (1 : Fin 2)) (by decide) s
  rw [show (1 : Fin 2).succ = (2 : Fin 3) by decide,
    show (0 : Fin 2).castSucc = (0 : Fin 3) by decide] at h
  exact h.symm

/-- Simplicial identity `δ₀δ₀ = δ₀δ₁` on `2`-simplices:
the targets of the `δ₀`- and `δ₁`-faces agree. -/
lemma delta_zero_delta_zero_apply (s : X _⦋2⦌) :
    X.δ 0 (X.δ 0 s) = X.δ 0 (X.δ 1 s) := by
  have h := δ_comp_δ_self_apply (S := X) (n := 0)
    (i := (0 : Fin 2)) s
  rwa [show (0 : Fin 2).castSucc = (0 : Fin 3) by decide,
    show (0 : Fin 2).succ = (1 : Fin 3) by decide] at h

/-- Simplicial identity `δ₁δ₂ = δ₁δ₁` on `2`-simplices:
the sources of the `δ₂`- and `δ₁`-faces agree. -/
lemma delta_one_delta_two_apply (s : X _⦋2⦌) :
    X.δ 1 (X.δ 2 s) = X.δ 1 (X.δ 1 s) := by
  have h := δ_comp_δ_apply (S := X) (n := 0) (i := (1 : Fin 2))
    (j := (1 : Fin 2)) (by decide) s
  rwa [show (1 : Fin 2).succ = (2 : Fin 3) by decide,
    show (1 : Fin 2).castSucc = (1 : Fin 3) by decide] at h

end TwoInverseEndpoints

/-!
## Horn faces, horn verticals, and uncurrying

The value of a horn face is the corresponding shuffle edge
(through `Subfunctor.lift` and `yonedaEquiv`), so the
whiskered horn face inclusion sends vertical simplices to
horn vertical simplices. Faces of an uncurried horn map are
read off by currying (`curry_natural_left`, `curry_pre_app`).
-/

section HornUncurry

variable {A B C W : SSet.{u}} {i : A ⟶ B} {n : ℕ}

/-- Extensionality for simplices of a standard simplex via
`stdSimplex.asOrderHom`. Local copy: the lemma of this name in
`CoherentIsoEndpoint.lean` and `ShuffleBridges.lean` is
`private` in the landed versions. -/
private lemma stdSimplex_ext_asOrderHom {m : ℕ}
    {Δ : SimplexCategoryᵒᵖ} {x y : (Δ[m] : SSet.{u}).obj Δ}
    (h : ∀ k : Fin (Δ.unop.len + 1),
      (stdSimplex.asOrderHom x) k = (stdSimplex.asOrderHom y) k) :
    x = y := by
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  exact OrderHom.ext _ _ (funext fun k => h k)

/-- The value of the `δ₂`-face of `Λ[2,0]` is the
`(0 ⟶ 1)`-edge of `Δ[2]`. -/
lemma horn_face_zero_two_val :
    (horn.face (0 : Fin 3) (2 : Fin 3) (by decide)).val =
      shuffleEdge01 := by
  have hval : (horn.face (0 : Fin 3) (2 : Fin 3) (by decide)).val =
      yonedaEquiv (stdSimplex.δ (2 : Fin 3)) := by
    change (Λ[2, (0 : Fin 3)].ι).app _
        (horn.face (0 : Fin 3) (2 : Fin 3) (by decide)) = _
    simp only [horn.face]
    rw [← yonedaEquiv_comp, Subfunctor.lift_ι]
  rw [hval]
  apply stdSimplex_ext_asOrderHom
  intro t
  fin_cases t <;> rfl

/-- The value of the `δ₀`-face of `Λ[2,2]` is the
`(1 ⟶ 2)`-edge of `Δ[2]`. -/
lemma horn_face_two_zero_val :
    (horn.face (2 : Fin 3) (0 : Fin 3) (by decide)).val =
      shuffleEdge12 := by
  have hval : (horn.face (2 : Fin 3) (0 : Fin 3) (by decide)).val =
      yonedaEquiv (stdSimplex.δ (0 : Fin 3)) := by
    change (Λ[2, (2 : Fin 3)].ι).app _
        (horn.face (2 : Fin 3) (0 : Fin 3) (by decide)) = _
    simp only [horn.face]
    rw [← yonedaEquiv_comp, Subfunctor.lift_ι]
  rw [hval]
  apply stdSimplex_ext_asOrderHom
  intro t
  fin_cases t <;> rfl

/-- The whiskered `δ₂`-face inclusion of `Λ[2,0]` sends
vertical simplices to horn-zero vertical simplices. -/
lemma whiskerLeft_horn_ι_zero_app_vertical (x : B _⦋0⦌) :
    (B ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)).app _
        (verticalOneSimplex x) =
      hornVertZeroSimplex x := by
  have h2 : ((B ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)).app _
        (verticalOneSimplex x)).2 =
      horn.face (0 : Fin 3) (2 : Fin 3) (by decide) := by
    change (horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)).app _
        (yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
    rw [← yonedaEquiv_comp, Category.id_comp, horn.yonedaEquiv_ι]
  apply Prod.ext
  · rfl
  · rw [h2]
    exact Subtype.ext (horn_face_zero_two_val.trans
      (hornVertZeroSimplex_snd_val x).symm)

/-- The whiskered `δ₀`-face inclusion of `Λ[2,2]` sends
vertical simplices to horn-two vertical simplices. -/
lemma whiskerLeft_horn_ι_two_app_vertical (x : B _⦋0⦌) :
    (B ◁ horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)).app _
        (verticalOneSimplex x) =
      hornVertTwoSimplex x := by
  have h2 : ((B ◁ horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)).app _
        (verticalOneSimplex x)).2 =
      horn.face (2 : Fin 3) (0 : Fin 3) (by decide) := by
    change (horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)).app _
        (yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
    rw [← yonedaEquiv_comp, Category.id_comp, horn.yonedaEquiv_ι]
  apply Prod.ext
  · rfl
  · rw [h2]
    exact Subtype.ext (horn_face_two_zero_val.trans
      (hornVertTwoSimplex_snd_val x).symm)

/-- The simplex of a face of an uncurried map is the
corresponding face map: currying by
`curry_natural_left`/`curry_uncurry`. -/
lemma ihomSimplexOfPrism_whiskerLeft_comp_uncurry
    (h : W ⟶ (ihom B).obj C) (φ : Δ[n] ⟶ W) :
    ihomSimplexOfPrism ((B ◁ φ) ≫ MonoidalClosed.uncurry h) =
      yonedaEquiv (φ ≫ h) := by
  change yonedaEquiv (MonoidalClosed.curry
      ((B ◁ φ) ≫ MonoidalClosed.uncurry h)) = yonedaEquiv (φ ≫ h)
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_uncurry]

/-- Currying a whiskered uncurried map precomposes in the
internal hom. -/
lemma curry_whiskerRight_comp_uncurry (h : W ⟶ (ihom B).obj C) :
    MonoidalClosed.curry ((i ▷ W) ≫ MonoidalClosed.uncurry h) =
      h ≫ (pre i).app C := by
  rw [← MonoidalClosed.curry_pre_app, MonoidalClosed.curry_uncurry]

/-- Currying the prism of a simplex recovers its Yoneda
name. -/
lemma curry_ihomPrismOfSimplex (s : ((ihom A).obj C) _⦋n⦌) :
    MonoidalClosed.curry (ihomPrismOfSimplex s) = yonedaEquiv.symm s :=
  MonoidalClosed.curry_uncurry _

/-- **The `Λ[2,0]` horn datum of an edge and the degenerate
edge at its source is compatible:** the unique pair
`(1, 2)` in `Fin 3` checks the common source vertex. -/
lemma hornIsCompatible_zero_of_edge {b b' : ((ihom B).obj C) _⦋0⦌}
    (ε : Edge b b') :
    horn.IsCompatible (i := (0 : Fin 3)) (fun j _ ↦
      if j = 2 then yonedaEquiv.symm ε.edge
      else yonedaEquiv.symm (Edge.id b).edge) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj0 : j.val ≠ 0 := fun hv ↦ hj (Fin.ext hv)
  have hk0 : k.val ≠ 0 := fun hv ↦ hk (Fin.ext hv)
  have hjkv : j.val < k.val := hjk
  have hj2 := j.2
  have hk2 := k.2
  have hjv : j.val = 1 := by omega
  have hkv : k.val = 2 := by omega
  have hj1 : j = 1 := Fin.ext hjv
  have hk2' : k = 2 := Fin.ext hkv
  subst hj1
  subst hk2'
  change stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm (Edge.id b).edge =
    stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm ε.edge
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    stdSimplex.δ_comp_yonedaEquiv_symm, (Edge.id b).src_eq, ε.src_eq]

/-- **The `Λ[2,2]` horn datum of an edge and the degenerate
edge at its target is compatible:** the unique pair
`(0, 1)` checks the common target vertex. -/
lemma hornIsCompatible_two_of_edge {b b' : ((ihom B).obj C) _⦋0⦌}
    (ε : Edge b b') :
    horn.IsCompatible (i := (2 : Fin 3)) (fun j _ ↦
      if j = 0 then yonedaEquiv.symm ε.edge
      else yonedaEquiv.symm (Edge.id b').edge) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj2' : j.val ≠ 2 := fun hv ↦ hj (Fin.ext hv)
  have hk2' : k.val ≠ 2 := fun hv ↦ hk (Fin.ext hv)
  have hjkv : j.val < k.val := hjk
  have hjb := j.2
  have hkb := k.2
  have hjv : j.val = 0 := by omega
  have hkv : k.val = 1 := by omega
  have hj0 : j = 0 := Fin.ext hjv
  have hk1 : k = 1 := Fin.ext hkv
  subst hj0
  subst hk1
  change stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm ε.edge =
    stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm (Edge.id b').edge
  rw [stdSimplex.δ_comp_yonedaEquiv_symm,
    stdSimplex.δ_comp_yonedaEquiv_symm, ε.tgt_eq, (Edge.id b').tgt_eq]

end HornUncurry

/-!
## The pointwise criterion

An edge of `Fun(B, C)` whose prism restricts strictly to an
equivalence edge of `Fun(A, C)` and whose verticals are
equivalences is an equivalence, granted the two `Δ[2]`
horn-prism extensions along `i`: glue the two horn data in
`Fun(B, C)`, check agreement over `A` by `horn.hom_ext'`
after currying, extend, read endpoints by the simplicial
identities, and conclude by the two-inverse criterion.
-/

section PointwiseCriterion

variable {A B C : SSet.{u}} {i : A ⟶ B}
  {b b' : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}

/-- **The pointwise criterion:** granted horn-zero and
horn-two `Δ[2]`-prism extension along `i`, a prism `F` over
`B` with equivalence verticals whose strict restriction is
the prism of an equivalence edge `e` has equivalence edge. -/
theorem edgeOfPrism_isEquivalence_of_strictRestriction_pointwise
    [Quasicategory C]
    (hTwo0 : PrismTwoHornZeroExtension i C)
    (hTwo2 : PrismTwoHornTwoExtension i C)
    (e : Edge (((pre i).app C).app _ b) a') (he : e.IsEquivalence)
    (F : B ⊗ Δ[1] ⟶ C)
    (hFr : (i ▷ Δ[1]) ≫ F = ihomPrismOfSimplex e.edge)
    (hFv : PrismOneVerticalsEquivalences F)
    (h0 : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism F) = b)
    (h1 : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) = b')
    (hb' : ((pre i).app C).app _ b' = a') :
    (edgeOfPrism F h0 h1).IsEquivalence := by
  set ε : Edge b b' := edgeOfPrism F h0 h1 with hεdef
  have hεedge : ε.edge = ihomSimplexOfPrism F := edgeOfPrism_edge _ _ _
  have hεpre : ((pre i).app C).app _ ε.edge = e.edge := by
    rw [hεedge, ihomSimplexOfPrism_pre_app, hFr,
      ihomSimplexOfPrism_ihomPrismOfSimplex]
  have hsymm : ∀ t : ((ihom B).obj C) _⦋1⦌,
      yonedaEquiv.symm t ≫ (pre i).app C =
        yonedaEquiv.symm (((pre i).app C).app _ t) := by
    intro t
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have hidpre : ((pre i).app C).app _ (Edge.id b).edge =
      (Edge.id (((pre i).app C).app _ b)).edge := by
    rw [Edge.id_edge, Edge.id_edge]
    exact σ_naturality_apply ((pre i).app C) 0 b
  have hidpre' : ((pre i).app C).app _ (Edge.id b').edge =
      (Edge.id a').edge := by
    rw [Edge.id_edge, Edge.id_edge, σ_naturality_apply, hb']
  obtain ⟨I⟩ := he.nonempty_invStruct
  set PA : A ⊗ Δ[2] ⟶ C := ihomPrismOfSimplex I.homInvId.simplex
    with hPAdef
  set QA : A ⊗ Δ[2] ⟶ C := ihomPrismOfSimplex I.invHomId.simplex
    with hQAdef
  -- Horn-zero side.
  set hf0 := hornIsCompatible_zero_of_edge ε with hhf0def
  set hP : (Λ[2, 0] : SSet.{u}) ⟶ (ihom B).obj C := hf0.desc with hhPdef
  set PΛ : B ⊗ (Λ[2, 0] : SSet.{u}) ⟶ C :=
    MonoidalClosed.uncurry hP with hPΛdef
  have hPΛ2 : (B ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)) ≫ PΛ = F := by
    apply (ihomSimplexEquiv B C 1).injective
    change ihomSimplexOfPrism
        ((B ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)) ≫ PΛ) =
      ihomSimplexOfPrism F
    rw [hPΛdef, ihomSimplexOfPrism_whiskerLeft_comp_uncurry, hhPdef,
      horn.IsCompatible.ι_desc hf0 (2 : Fin 3) (by decide)]
    change yonedaEquiv (yonedaEquiv.symm ε.edge) = ihomSimplexOfPrism F
    rw [Equiv.apply_symm_apply]
    exact hεedge
  have hPΛ1 : (B ◁ horn.ι (0 : Fin 3) (1 : Fin 3) (by decide)) ≫ PΛ =
      ihomPrismOfSimplex (Edge.id b).edge := by
    apply (ihomSimplexEquiv B C 1).injective
    change ihomSimplexOfPrism
        ((B ◁ horn.ι (0 : Fin 3) (1 : Fin 3) (by decide)) ≫ PΛ) =
      ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge)
    rw [hPΛdef, ihomSimplexOfPrism_whiskerLeft_comp_uncurry, hhPdef,
      horn.IsCompatible.ι_desc hf0 (1 : Fin 3) (by decide)]
    change yonedaEquiv (yonedaEquiv.symm (Edge.id b).edge) =
      ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge)
    rw [Equiv.apply_symm_apply, ihomSimplexOfPrism_ihomPrismOfSimplex]
  have hdegen : ihomPrismOfSimplex (Edge.id b).edge =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F := by
    apply (ihomSimplexEquiv B C 1).injective
    change ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b).edge) =
      ihomSimplexOfPrism ((B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F)
    rw [ihomSimplexOfPrism_ihomPrismOfSimplex, ← σ_ihomSimplexOfPrism,
      ← δ_ihomSimplexOfPrism, h0, Edge.id_edge]
  have hPΛvert : ∀ x : B _⦋0⦌,
      (Edge.mk' (PΛ.app _ (hornVertZeroSimplex x))).IsEquivalence := by
    intro x
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hFv x)
    change PΛ.app _ (hornVertZeroSimplex x) =
      F.app _ (verticalOneSimplex x)
    calc PΛ.app _ (hornVertZeroSimplex x)
        = ((B ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)) ≫ PΛ).app _
            (verticalOneSimplex x) := by
          change PΛ.app _ (hornVertZeroSimplex x) =
            PΛ.app _ ((B ◁ horn.ι (0 : Fin 3) (2 : Fin 3)
              (by decide)).app _ (verticalOneSimplex x))
          rw [whiskerLeft_horn_ι_zero_app_vertical]
      _ = F.app _ (verticalOneSimplex x) :=
          congr($(hPΛ2).app _ (verticalOneSimplex x))
  have hagree0 : (A ◁ Λ[2, 0].ι) ≫ PA =
      (i ▷ (Λ[2, 0] : SSet.{u})) ≫ PΛ := by
    have hcurry : MonoidalClosed.curry ((A ◁ Λ[2, 0].ι) ≫ PA) =
        MonoidalClosed.curry ((i ▷ (Λ[2, 0] : SSet.{u})) ≫ PΛ) := by
      rw [hPΛdef, curry_whiskerRight_comp_uncurry,
        MonoidalClosed.curry_natural_left, hPAdef,
        curry_ihomPrismOfSimplex, hhPdef]
      have hL : ∀ (j : Fin 3) (hj : j ≠ (0 : Fin 3)),
          horn.ι (0 : Fin 3) j hj ≫
              (Λ[2, 0].ι ≫ yonedaEquiv.symm I.homInvId.simplex) =
            yonedaEquiv.symm (((ihom A).obj C).δ j I.homInvId.simplex) := by
        intro j hj
        rw [← Category.assoc, horn.ι_ι,
          stdSimplex.δ_comp_yonedaEquiv_symm]
      apply horn.hom_ext'
      intro j hj
      have hR : horn.ι (0 : Fin 3) j hj ≫ (hf0.desc ≫ (pre i).app C) =
          (fun j _ ↦ if j = 2 then yonedaEquiv.symm ε.edge
            else yonedaEquiv.symm (Edge.id b).edge) j hj ≫
            (pre i).app C := by
        rw [← Category.assoc, horn.IsCompatible.ι_desc]
      have hj0 : j.val ≠ 0 := fun hv ↦ hj (Fin.ext hv)
      have hjb := j.2
      have hj01 : j = 1 ∨ j = 2 := by
        have hv : j.val = 1 ∨ j.val = 2 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rw [hL, hR]
      rcases hj01 with rfl | rfl
      · change yonedaEquiv.symm (((ihom A).obj C).δ 1 I.homInvId.simplex) =
          yonedaEquiv.symm (Edge.id b).edge ≫ (pre i).app C
        rw [hsymm, I.homInvId.d₁, hidpre]
      · change yonedaEquiv.symm (((ihom A).obj C).δ 2 I.homInvId.simplex) =
          yonedaEquiv.symm ε.edge ≫ (pre i).app C
        rw [hsymm, I.homInvId.d₂, hεpre]
    have h2 := congrArg MonoidalClosed.uncurry hcurry
    rwa [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry] at h2
  obtain ⟨P, hPr, hPface⟩ := hTwo0 PA PΛ hagree0 hPΛvert
  have hP2 : (B ◁ stdSimplex.δ 2) ≫ P = F := by
    calc (B ◁ stdSimplex.δ 2) ≫ P
        = (B ◁ horn.ι (0 : Fin 3) (2 : Fin 3) (by decide)) ≫
            ((B ◁ Λ[2, 0].ι) ≫ P) := by
          rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
            horn.ι_ι]
      _ = F := by rw [hPface, hPΛ2]
  have hP1 : (B ◁ stdSimplex.δ 1) ≫ P =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F := by
    calc (B ◁ stdSimplex.δ 1) ≫ P
        = (B ◁ horn.ι (0 : Fin 3) (1 : Fin 3) (by decide)) ≫
            ((B ◁ Λ[2, 0].ι) ≫ P) := by
          rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
            horn.ι_ι]
      _ = (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ F := by
          rw [hPface, hPΛ1, hdegen]
  set G₁ : B ⊗ Δ[1] ⟶ C := (B ◁ stdSimplex.δ 0) ≫ P with hG₁def
  have hG10 : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism G₁) = b' := by
    rw [hG₁def, ← δ_ihomSimplexOfPrism, delta_one_delta_zero_apply,
      δ_ihomSimplexOfPrism, hP2]
    exact h1
  have hG11 : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism G₁) = b := by
    rw [hG₁def, ← δ_ihomSimplexOfPrism, delta_zero_delta_zero_apply,
      δ_ihomSimplexOfPrism, hP1, ← hdegen,
      ihomSimplexOfPrism_ihomPrismOfSimplex]
    exact (Edge.id b).tgt_eq
  -- Horn-two side.
  set hf2 := hornIsCompatible_two_of_edge ε with hhf2def
  set hQ : (Λ[2, 2] : SSet.{u}) ⟶ (ihom B).obj C := hf2.desc with hhQdef
  set QΛ : B ⊗ (Λ[2, 2] : SSet.{u}) ⟶ C :=
    MonoidalClosed.uncurry hQ with hQΛdef
  have hQΛ0 : (B ◁ horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)) ≫ QΛ = F := by
    apply (ihomSimplexEquiv B C 1).injective
    change ihomSimplexOfPrism
        ((B ◁ horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)) ≫ QΛ) =
      ihomSimplexOfPrism F
    rw [hQΛdef, ihomSimplexOfPrism_whiskerLeft_comp_uncurry, hhQdef,
      horn.IsCompatible.ι_desc hf2 (0 : Fin 3) (by decide)]
    change yonedaEquiv (yonedaEquiv.symm ε.edge) = ihomSimplexOfPrism F
    rw [Equiv.apply_symm_apply]
    exact hεedge
  have hQΛ1 : (B ◁ horn.ι (2 : Fin 3) (1 : Fin 3) (by decide)) ≫ QΛ =
      ihomPrismOfSimplex (Edge.id b').edge := by
    apply (ihomSimplexEquiv B C 1).injective
    change ihomSimplexOfPrism
        ((B ◁ horn.ι (2 : Fin 3) (1 : Fin 3) (by decide)) ≫ QΛ) =
      ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b').edge)
    rw [hQΛdef, ihomSimplexOfPrism_whiskerLeft_comp_uncurry, hhQdef,
      horn.IsCompatible.ι_desc hf2 (1 : Fin 3) (by decide)]
    change yonedaEquiv (yonedaEquiv.symm (Edge.id b').edge) =
      ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id b').edge)
    rw [Equiv.apply_symm_apply, ihomSimplexOfPrism_ihomPrismOfSimplex]
  have hQΛvert : ∀ x : B _⦋0⦌,
      (Edge.mk' (QΛ.app _ (hornVertTwoSimplex x))).IsEquivalence := by
    intro x
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hFv x)
    change QΛ.app _ (hornVertTwoSimplex x) =
      F.app _ (verticalOneSimplex x)
    calc QΛ.app _ (hornVertTwoSimplex x)
        = ((B ◁ horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)) ≫ QΛ).app _
            (verticalOneSimplex x) := by
          change QΛ.app _ (hornVertTwoSimplex x) =
            QΛ.app _ ((B ◁ horn.ι (2 : Fin 3) (0 : Fin 3)
              (by decide)).app _ (verticalOneSimplex x))
          rw [whiskerLeft_horn_ι_two_app_vertical]
      _ = F.app _ (verticalOneSimplex x) :=
          congr($(hQΛ0).app _ (verticalOneSimplex x))
  have hagree2 : (A ◁ Λ[2, 2].ι) ≫ QA =
      (i ▷ (Λ[2, 2] : SSet.{u})) ≫ QΛ := by
    have hcurry : MonoidalClosed.curry ((A ◁ Λ[2, 2].ι) ≫ QA) =
        MonoidalClosed.curry ((i ▷ (Λ[2, 2] : SSet.{u})) ≫ QΛ) := by
      rw [hQΛdef, curry_whiskerRight_comp_uncurry,
        MonoidalClosed.curry_natural_left, hQAdef,
        curry_ihomPrismOfSimplex, hhQdef]
      have hL : ∀ (j : Fin 3) (hj : j ≠ (2 : Fin 3)),
          horn.ι (2 : Fin 3) j hj ≫
              (Λ[2, 2].ι ≫ yonedaEquiv.symm I.invHomId.simplex) =
            yonedaEquiv.symm (((ihom A).obj C).δ j I.invHomId.simplex) := by
        intro j hj
        rw [← Category.assoc, horn.ι_ι,
          stdSimplex.δ_comp_yonedaEquiv_symm]
      apply horn.hom_ext'
      intro j hj
      have hR : horn.ι (2 : Fin 3) j hj ≫ (hf2.desc ≫ (pre i).app C) =
          (fun j _ ↦ if j = 0 then yonedaEquiv.symm ε.edge
            else yonedaEquiv.symm (Edge.id b').edge) j hj ≫
            (pre i).app C := by
        rw [← Category.assoc, horn.IsCompatible.ι_desc]
      have hj2' : j.val ≠ 2 := fun hv ↦ hj (Fin.ext hv)
      have hjb := j.2
      have hj01 : j = 0 ∨ j = 1 := by
        have hv : j.val = 0 ∨ j.val = 1 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rw [hL, hR]
      rcases hj01 with rfl | rfl
      · change yonedaEquiv.symm (((ihom A).obj C).δ 0 I.invHomId.simplex) =
          yonedaEquiv.symm ε.edge ≫ (pre i).app C
        rw [hsymm, I.invHomId.d₀, hεpre]
      · change yonedaEquiv.symm (((ihom A).obj C).δ 1 I.invHomId.simplex) =
          yonedaEquiv.symm (Edge.id b').edge ≫ (pre i).app C
        rw [hsymm, I.invHomId.d₁, hidpre']
    have h2 := congrArg MonoidalClosed.uncurry hcurry
    rwa [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry] at h2
  obtain ⟨Q, hQr, hQface⟩ := hTwo2 QA QΛ hagree2 hQΛvert
  have hQ0 : (B ◁ stdSimplex.δ 0) ≫ Q = F := by
    calc (B ◁ stdSimplex.δ 0) ≫ Q
        = (B ◁ horn.ι (2 : Fin 3) (0 : Fin 3) (by decide)) ≫
            ((B ◁ Λ[2, 2].ι) ≫ Q) := by
          rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
            horn.ι_ι]
      _ = F := by rw [hQface, hQΛ0]
  have hQ1raw : (B ◁ stdSimplex.δ 1) ≫ Q =
      ihomPrismOfSimplex (Edge.id b').edge := by
    calc (B ◁ stdSimplex.δ 1) ≫ Q
        = (B ◁ horn.ι (2 : Fin 3) (1 : Fin 3) (by decide)) ≫
            ((B ◁ Λ[2, 2].ι) ≫ Q) := by
          rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
            horn.ι_ι]
      _ = ihomPrismOfSimplex (Edge.id b').edge := by
          rw [hQface, hQΛ1]
  set G₂ : B ⊗ Δ[1] ⟶ C := (B ◁ stdSimplex.δ 2) ≫ Q with hG₂def
  have hG20 : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism G₂) = b' := by
    rw [hG₂def, ← δ_ihomSimplexOfPrism, delta_one_delta_two_apply,
      δ_ihomSimplexOfPrism, hQ1raw,
      ihomSimplexOfPrism_ihomPrismOfSimplex]
    exact (Edge.id b').src_eq
  have hG21 : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism G₂) = b := by
    rw [hG₂def, ← δ_ihomSimplexOfPrism, ← delta_one_delta_zero_apply,
      δ_ihomSimplexOfPrism, hQ0]
    exact h0
  have hQ1 : (B ◁ stdSimplex.δ 1) ≫ Q =
      (B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ G₂ := by
    apply (ihomSimplexEquiv B C 1).injective
    change ihomSimplexOfPrism ((B ◁ stdSimplex.δ 1) ≫ Q) =
      ihomSimplexOfPrism ((B ◁ stdSimplex.σ 0) ≫ (B ◁ stdSimplex.δ 1) ≫ G₂)
    rw [hQ1raw, ihomSimplexOfPrism_ihomPrismOfSimplex,
      ← σ_ihomSimplexOfPrism, ← δ_ihomSimplexOfPrism, hG20, Edge.id_edge]
  exact edgeOfPrism_isEquivalence_of_twoCompPrisms F G₁ G₂ h0 h1
    hG10 hG11 hG20 hG21 P Q hP2 hG₁def.symm hP1 hG₂def.symm hQ0 hQ1

end PointwiseCriterion

/-!
## Assembly of (A): prism strict extension, conditional form

Given `(e, b)` as in `HoPrePrismStrictExtension`: the
`Δ[1]` tower (§1, unconditional) produces the prism `F`
extending `H` with source `b♯` and equivalence verticals,
and the pointwise criterion (granted the `Δ[2]` inputs
through §1) shows its edge is an equivalence. the supporting result then gives
the isofibration form.
-/

section Assembly

variable {A B C : SSet.{u}}

/-- **Prism strict extension (A) along every monomorphism,
granted the two cell shuffle inputs:** the `Δ[1]` extension
is unconditional (`prismSrcExtension_of_mono`), the
`Δ[2]` extensions are
`prismTwoHornZero/TwoExtension_of_mono_of_shuffleCell`, and
the lifted edge is an equivalence by the pointwise
criterion. This closes the additional comparison obligation as an implication from
the additional comparison obligation. -/
theorem hoPrePrismStrictExtension_of_mono_of_shuffleCell
    (i : A ⟶ B) [Mono i] (C : SSet.{u}) [Quasicategory C]
    (hcell0 : ∀ n, ShuffleHornZeroCellExtension n C)
    (hcell2 : ∀ n, ShuffleHornTwoCellExtension n C) :
    HoPrePrismStrictExtension i C := by
  intro b a' e he
  set bsharp : B ⟶ C := (ihomVertexEquiv B C).symm b with hbsharp
  have hbv : ihomVertexEquiv B C bsharp = b :=
    Equiv.apply_symm_apply _ _
  set H : A ⊗ Δ[1] ⟶ C := ihomPrismOfSimplex e.edge with hHdef
  have hagree : prismSectionAt A 0 ≫ H = i ≫ bsharp := by
    apply (ihomVertexEquiv A C).injective
    rw [hHdef, ihomVertexEquiv_prismSectionAt_zero_comp,
      ihomSimplexOfPrism_ihomPrismOfSimplex, e.src_eq,
      ← ihomVertexEquiv_pre_app, hbv]
  have hHvert : PrismOneVerticalsEquivalences H :=
    prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence e he
  obtain ⟨F, hFr, hFs, hFv⟩ :=
    prismSrcExtension_of_mono i H bsharp hagree hHvert
  set b' : ((ihom B).obj C) _⦋0⦌ :=
    ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) with hb'def
  have h0 : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism F) = b := by
    rw [← ihomVertexEquiv_prismSectionAt_zero_comp, hFs, hbv]
  have h1 : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) = b' := rfl
  have hb' : ((pre i).app C).app _ b' = a' := by
    calc ((pre i).app C).app _ b'
        = ((ihom A).obj C).δ 0
            (((pre i).app C).app _ (ihomSimplexOfPrism F)) := by
          rw [hb'def]
          exact δ_naturality_apply ((pre i).app C) 0 _
      _ = a' := by
          rw [ihomSimplexOfPrism_pre_app, hFr, hHdef,
            ihomSimplexOfPrism_ihomPrismOfSimplex, e.tgt_eq]
  have hε : (edgeOfPrism F h0 h1).IsEquivalence :=
    edgeOfPrism_isEquivalence_of_strictRestriction_pointwise
      (prismTwoHornZeroExtension_of_mono_of_shuffleCell i hcell0)
      (prismTwoHornTwoExtension_of_mono_of_shuffleCell i hcell2)
      e he F hFr hFv h0 h1 hb'
  exact ⟨F, b', hb', h0, h1, hε, hFr⟩

/-- **Precomposition with a monomorphism is an isofibration
on homotopy categories, granted the two cell shuffle
inputs** (the additional comparison obligation in conditional form, discharged
unconditionally in `DwyerKanFinal.lean`): the supporting result
`hoFunctor_pre_isIsofibration_of_prismStrictExtension`
applied to `hoPrePrismStrictExtension_of_mono_of_shuffleCell`. -/
theorem hoFunctor_pre_isIsofibration_of_mono_of_shuffleCell
    (i : A ⟶ B) [Mono i] (C : SSet.{u}) [Quasicategory C]
    (hcell0 : ∀ n, ShuffleHornZeroCellExtension n C)
    (hcell2 : ∀ n, ShuffleHornTwoCellExtension n C) :
    (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration :=
  hoFunctor_pre_isIsofibration_of_prismStrictExtension C
    (hoPrePrismStrictExtension_of_mono_of_shuffleCell i C hcell0 hcell2)

end Assembly

end SSet

end
