/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEquivalences
public import MathlibExt.AlgebraicTopology.Quasicategory.TwoHornPrism
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalRightLifting

/-!
# Endpoint evaluation on the finite Joyal interval

In a quasicategory, a whole prescribed map on `A ⊗ J` extends along a
monomorphism while retaining either prescribed endpoint on `B`. Extend
the forward equivalence prism, then both complete inverse triangles, and
glue using the finite interval's presentation. This proves monomorphism
RLP for the canonical endpoint evaluation.

The finite presentation is Cisinski, *Higher Categories and Homotopical
Algebra*, July 30, 2026, Construction 3.3.1 and Definition 3.3.3 (printed
pp.92–94). Endpoint evaluation is a consequence in the proof of Theorem
3.6.1 (printed pp.112–113); the proof here uses the accepted full prism
extensions directly.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
  CartesianMonoidalCategory
open scoped Simplicial

universe u

namespace SSet.joyalInterval

variable {A B C : SSet.{u}}

private lemma section_forward (A : SSet.{u}) (ε : Fin 2) :
    prismSectionAt A ε ≫ (A ◁ forward) = (ρ_ A).inv ≫ (A ◁ unitPoint ε) := by
  fin_cases ε <;>
    simp only [prismSectionAt, unitPoint, Category.assoc, ← whiskerLeft_comp] <;> rfl

private lemma forward_verticals (T : A ⊗ joyalInterval ⟶ C) :
    PrismOneVerticalsEquivalences ((A ◁ forward) ≫ T) := by
  intro a
  let t : joyalInterval ⟶ C := lift (SSet.const a) (𝟙 _) ≫ T
  have he := isEquivalence_forward t
  have h : yonedaEquiv (forward ≫ t) =
      (((A ◁ forward) ≫ T).app _ (verticalOneSimplex a)) := by
    have hs : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ 0 := by
      exact Subsingleton.elim _ _
    simp only [t, yonedaEquiv_comp]
    change T.app _ (A.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op a, yonedaEquiv forward) =
      T.app _ (A.σ 0 a, forward.app _ (yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
    rw [hs]
    rfl
  rw [h] at he
  exact he

/-- Extend the whole finite-interval map along a monomorphism with either
specified endpoint. Both full inverse triangles of the original map are retained. -/
theorem exists_extension_of_mono (i : A ⟶ B) [Mono i] [Quasicategory C]
    (ε : Fin 2) (T_A : A ⊗ joyalInterval ⟶ C) (c : B ⟶ C)
    (hε : (ρ_ A).inv ≫ (A ◁ unitPoint ε) ≫ T_A = i ≫ c) :
    ∃ T_B : B ⊗ joyalInterval ⟶ C,
      (i ▷ joyalInterval) ≫ T_B = T_A ∧
        (ρ_ B).inv ≫ (B ◁ unitPoint ε) ≫ T_B = c := by
  let f_A := (A ◁ forward) ≫ T_A
  let L_A := (A ◁ leftTriangle) ≫ T_A
  let R_A := (A ◁ rightTriangle) ≫ T_A
  have hε' : prismSectionAt A ε ≫ f_A = i ≫ c := by
    simpa only [f_A, ← Category.assoc, section_forward] using hε
  obtain ⟨f_B, hf, hend, hvert⟩ :
      ∃ f_B : B ⊗ Δ[1] ⟶ C,
        (i ▷ Δ[1]) ≫ f_B = f_A ∧ prismSectionAt B ε ≫ f_B = c ∧
          PrismOneVerticalsEquivalences f_B := by
    fin_cases ε
    · exact prismSrcExtension_of_mono i f_A c hε' (forward_verticals T_A)
    · exact prismTgtExtension_of_mono i f_A c hε' (forward_verticals T_A)
  let f := curry f_B
  have hfi : f ≫ (pre i).app C = curry f_A := by
    rw [curry_pre_app, hf]
  have hL₂ : stdSimplex.δ (2 : Fin 3) ≫ curry L_A = curry f_A := by
    rw [← curry_natural_left]
    congr 1
    dsimp [L_A, f_A]
    rw [← Category.assoc, ← whiskerLeft_comp, δ_two_leftTriangle]
  have hL₁ : stdSimplex.δ (1 : Fin 3) ≫ curry L_A = constSource ≫ curry f_A := by
    rw [← curry_natural_left, ← curry_natural_left]
    congr 1
    dsimp [L_A, f_A]
    rw [← Category.assoc, ← whiskerLeft_comp, δ_one_leftTriangle,
      whiskerLeft_comp, Category.assoc]
  have hR₀ : stdSimplex.δ (0 : Fin 3) ≫ curry R_A = curry f_A := by
    rw [← curry_natural_left]
    congr 1
    dsimp [R_A, f_A]
    rw [← Category.assoc, ← whiskerLeft_comp, δ_zero_rightTriangle]
  have hR₁ : stdSimplex.δ (1 : Fin 3) ≫ curry R_A = constTarget ≫ curry f_A := by
    rw [← curry_natural_left, ← curry_natural_left]
    congr 1
    dsimp [R_A, f_A]
    rw [← Category.assoc, ← whiskerLeft_comp, δ_one_rightTriangle,
      whiskerLeft_comp, Category.assoc]
  let p₀ : (Λ[2, 0] : SSet.{u}) ⟶ (ihom B).obj C :=
    horn₂₀.isPushout.desc f (constSource ≫ f) (by simp)
  let p₂ : (Λ[2, 2] : SSet.{u}) ⟶ (ihom B).obj C :=
    horn₂₂.isPushout.desc (constTarget ≫ f) f (by simp)
  have hp₀₀₁ : horn₂₀.ι₀₁ ≫ p₀ = f := horn₂₀.isPushout.inl_desc ..
  have hp₀₀₂ : horn₂₀.ι₀₂ ≫ p₀ = constSource ≫ f := horn₂₀.isPushout.inr_desc ..
  have hp₂₀₂ : horn₂₂.ι₀₂ ≫ p₂ = constTarget ≫ f := horn₂₂.isPushout.inl_desc ..
  have hp₂₁₂ : horn₂₂.ι₁₂ ≫ p₂ = f := horn₂₂.isPushout.inr_desc ..
  have hcomm₀ : (A ◁ Λ[2, 0].ι) ≫ L_A = (i ▷ (Λ[2, 0] : SSet.{u})) ≫ uncurry p₀ := by
    apply curry_injective
    rw [curry_natural_left, ← curry_pre_app, curry_uncurry]
    apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, ← Category.assoc, horn.ι_ι, hL₂, hp₀₀₁, hfi]
    · rw [← Category.assoc, ← Category.assoc, horn.ι_ι, hL₁, hp₀₀₂,
        Category.assoc, hfi]
  have hcomm₂ : (A ◁ Λ[2, 2].ι) ≫ R_A = (i ▷ (Λ[2, 2] : SSet.{u})) ≫ uncurry p₂ := by
    apply curry_injective
    rw [curry_natural_left, ← curry_pre_app, curry_uncurry]
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, ← Category.assoc, horn.ι_ι, hR₁, hp₂₀₂,
        Category.assoc, hfi]
    · rw [← Category.assoc, ← Category.assoc, horn.ι_ι, hR₀, hp₂₁₂, hfi]
  have hvert₀ : ∀ b : B _⦋0⦌,
      (Edge.mk' ((uncurry p₀).app _ (hornVertZeroSimplex b))).IsEquivalence := by
    intro b
    have h : (B ◁ horn₂₀.ι₀₁) ≫ uncurry p₀ = f_B := by
      rw [← uncurry_natural_left, hp₀₀₁, uncurry_curry]
    have hb := congrArg (fun g => g.app _ (verticalOneSimplex b)) h
    have hm : (B ◁ horn₂₀.ι₀₁).app _ (verticalOneSimplex b) = hornVertZeroSimplex b := by
      simp only [verticalOneSimplex, hornVertZeroSimplex]
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        ext k
        fin_cases k <;> rfl
    simp only [NatTrans.comp_app, types_comp_apply, hm] at hb
    rw [hb]
    exact hvert b
  have hvert₂ : ∀ b : B _⦋0⦌,
      (Edge.mk' ((uncurry p₂).app _ (hornVertTwoSimplex b))).IsEquivalence := by
    intro b
    have h : (B ◁ horn₂₂.ι₁₂) ≫ uncurry p₂ = f_B := by
      rw [← uncurry_natural_left, hp₂₁₂, uncurry_curry]
    have hb := congrArg (fun g => g.app _ (verticalOneSimplex b)) h
    have hm : (B ◁ horn₂₂.ι₁₂).app _ (verticalOneSimplex b) = hornVertTwoSimplex b := by
      simp only [verticalOneSimplex, hornVertTwoSimplex]
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        ext k
        fin_cases k <;> rfl
    simp only [NatTrans.comp_app, types_comp_apply, hm] at hb
    rw [hb]
    exact hvert b
  obtain ⟨L_B, hLsource, hLhorn⟩ := prismTwoHornZeroExtension_of_mono i L_A
    (uncurry p₀) hcomm₀ hvert₀
  obtain ⟨R_B, hRsource, hRhorn⟩ := prismTwoHornTwoExtension_of_mono i R_A
    (uncurry p₂) hcomm₂ hvert₂
  have hLhorn' : Λ[2, 0].ι ≫ curry L_B = p₀ := by
    simpa only [curry_natural_left, curry_uncurry] using congrArg curry hLhorn
  have hRhorn' : Λ[2, 2].ι ≫ curry R_B = p₂ := by
    simpa only [curry_natural_left, curry_uncurry] using congrArg curry hRhorn
  have hLB₂ : stdSimplex.δ (2 : Fin 3) ≫ curry L_B = f := by
    rw [← horn.ι_ι (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide), Category.assoc,
      hLhorn', hp₀₀₁]
  have hLB₁ : stdSimplex.δ (1 : Fin 3) ≫ curry L_B = constSource ≫ f := by
    rw [← horn.ι_ι (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide), Category.assoc,
      hLhorn', hp₀₀₂]
  have hRB₀ : stdSimplex.δ (0 : Fin 3) ≫ curry R_B = f := by
    rw [← horn.ι_ι (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide), Category.assoc,
      hRhorn', hp₂₁₂]
  have hRB₁ : stdSimplex.δ (1 : Fin 3) ≫ curry R_B = constTarget ≫ f := by
    rw [← horn.ι_ι (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide), Category.assoc,
      hRhorn', hp₂₀₂]
  let t := desc f (curry L_B) (curry R_B) hLB₂ hLB₁ hRB₀ hRB₁
  refine ⟨uncurry t, ?_, ?_⟩
  · apply curry_injective
    rw [← curry_pre_app, curry_uncurry]
    apply hom_ext
    · rw [← Category.assoc, forward_desc, hfi, ← curry_natural_left]
    · rw [← Category.assoc, leftTriangle_desc, curry_pre_app, hLsource,
        ← curry_natural_left]
    · rw [← Category.assoc, rightTriangle_desc, curry_pre_app, hRsource,
        ← curry_natural_left]
  · have ht : (B ◁ forward) ≫ uncurry t = f_B := by
      rw [← uncurry_natural_left, forward_desc, uncurry_curry]
    rw [← Category.assoc, ← section_forward, Category.assoc, ht, hend]

private lemma curry_endpoint (F : joyalInterval ⊗ A ⟶ C) (ε : Fin 2) :
    curry F ≫ endpointEvaluation C ε = (λ_ A).inv ≫ (unitPoint ε ▷ A) ≫ F := by
  rw [endpointEvaluation, ← Category.assoc, curry_pre_app]
  change curry ((unitPoint ε ▷ A) ≫ F) ≫
    ((λ_ ((ihom (𝟙_ SSet.{u})).obj C)).inv ≫ (ihom.ev (𝟙_ SSet.{u})).app C) = _
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc,
    whiskerLeft_curry_ihom_ev_app]

private lemma curry_braiding_endpoint (T : A ⊗ joyalInterval ⟶ C) (ε : Fin 2) :
    curry ((β_ joyalInterval A).hom ≫ T) ≫ endpointEvaluation C ε =
      (ρ_ A).inv ≫ (A ◁ unitPoint ε) ≫ T := by
  rw [curry_endpoint]
  ext n x
  rfl

/-- The canonical endpoint evaluation has lifting against every monomorphism
when its target is a quasicategory. No fibrancy assumption on the source of
the square is needed. -/
theorem hasLiftingProperty_endpointEvaluation (i : A ⟶ B) [Mono i]
    [Quasicategory C] (ε : Fin 2) : HasLiftingProperty i (endpointEvaluation C ε) := by
  constructor
  intro a c sq
  let T_A : A ⊗ joyalInterval ⟶ C := (β_ joyalInterval A).inv ≫ uncurry a
  have ha : curry ((β_ joyalInterval A).hom ≫ T_A) = a := by
    dsimp [T_A]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, curry_uncurry]
  have hε : (ρ_ A).inv ≫ (A ◁ unitPoint ε) ≫ T_A = i ≫ c := by
    rw [← curry_braiding_endpoint, ha, sq.w]
  obtain ⟨T_B, hsource, hendpoint⟩ := exists_extension_of_mono i ε T_A c hε
  refine ⟨⟨{
    l := curry ((β_ joyalInterval B).hom ≫ T_B)
    fac_left := ?_
    fac_right := (curry_braiding_endpoint T_B ε).trans hendpoint
  }⟩⟩
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc, hsource]
  dsimp [T_A]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Monomorphism RLP for both canonical finite-interval endpoint evaluations
in every quasicategory. -/
theorem endpointEvaluation_mem_rlp_monomorphisms (C : SSet.{u}) [Quasicategory C]
    (ε : Fin 2) : (MorphismProperty.monomorphisms SSet).rlp (endpointEvaluation C ε) := by
  intro A B i hi
  have : Mono i := hi
  exact hasLiftingProperty_endpointEvaluation i ε

end SSet.joyalInterval
