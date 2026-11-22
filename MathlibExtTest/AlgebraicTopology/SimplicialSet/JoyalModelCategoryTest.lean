/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory

/-!
# Joyal Model Category Test
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped JoyalSSet.ModelCategory

universe u

namespace JoyalSSet.FinalTest

private abbrev I : MorphismProperty JoyalSSet.{u} :=
  .ofHoms (fun n : ℕ => ofSSet.{u}.map (SSet.boundary.{u} n).ι)

private abbrev W : MorphismProperty JoyalSSet.{u} :=
  SSet.categoricalEquivalences.{u}.inverseImage forget.{u}

private lemma actual_diagonal
    (L R : MorphismProperty JoyalSSet.{u})
    (h : IsWeakFactorizationSystem L R)
    {A B X Y : JoyalSSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : L i) (hp : R p) (a : A ⟶ X) (b : B ⟶ Y)
    (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  let _ : IsWeakFactorizationSystem L R := h
  let _ : HasLiftingProperty i p := hasLiftingProperty_of_wfs i p hi hp
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

private lemma actual_factorization
    (L R : MorphismProperty JoyalSSet.{u})
    (h : IsWeakFactorizationSystem L R)
    {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : JoyalSSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      L i ∧ R p ∧ i ≫ p = f := by
  let _ : IsWeakFactorizationSystem L R := h
  let d := factorizationData L R f
  exact ⟨d.Z, d.i, d.p, d.hi, d.hp, d.fac⟩

/-- The chosen model supplies diagonals for both genuine lifting systems,
factorizations of every original arrow, and literal named generation data.
Both original equations of each square and each composite are retained. -/
theorem native_joyal_model_consumers :
    let C := JoyalSSet.{u}
    let Monos := monomorphisms C
    let F := SSet.categoricalFibrations.{u}.inverseImage forget.{u}
    ∃ (s : SmithModelStructureData.{u} (C := C) I.{u} W.{u})
      (M : ModelCategory C),
      letI : ModelCategory C := M
      ∃ κ : Cardinal.{u},
      ∃ regular : Fact κ.IsRegular,
      letI : Fact κ.IsRegular := regular
      ∃ bottom : OrderBot κ.ord.ToType,
      letI : OrderBot κ.ord.ToType := bottom
      ∃ cg : CofibrantGenerationData C κ,
        M.categoryWithCofibrations.cofibrations = Monos ∧
        M.categoryWithWeakEquivalences.weakEquivalences = W ∧
        M.categoryWithFibrations.fibrations = F ∧
        (∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
          Mono i → I.rlp p → ∀ (a : A ⟶ X) (b : B ⟶ Y),
          CommSq a i p b → ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b) ∧
        (∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y),
          Mono i → W i → F p → ∀ (a : A ⟶ X) (b : B ⟶ Y),
          CommSq a i p b → ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b) ∧
        (∀ {X Y : C} (f : X ⟶ Y),
          ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y),
            Mono i ∧ I.rlp p ∧ i ≫ p = f) ∧
        (∀ {X Y : C} (f : X ⟶ Y),
          ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y),
            Mono i ∧ W i ∧ F p ∧ i ≫ p = f) ∧
        cg.I = I ∧ cg.J = s.J ∧
        cg.I.rlp = trivialFibrations C ∧ cg.J.rlp = fibrations C ∧
        cg.I (ofSSet.map (SSet.boundary.{u} 0).ι) ∧
        (∀ {X Y : C} (g : X ⟶ Y), s.J g → Mono g ∧ W g) ∧
        IsCardinalLocallyPresentable C κ ∧
        I.{u}.IsCardinalForSmallObjectArgument κ ∧
        s.J.IsCardinalForSmallObjectArgument κ ∧
        IsCombinatorialModelCategory.{u} C ∧
        (∀ X : C, IsFibrant X ↔ SSet.Quasicategory (forget.obj X)) ∧
        (∀ {A B : SSet.{u}} (g : A ⟶ B),
          WeakEquivalence (ofSSet.map g) ↔ SSet.categoricalEquivalences g) ∧
        (∀ {A B : SSet.{u}} (g : A ⟶ B),
          Fibration (ofSSet.map g) ↔ SSet.categoricalFibrations g) := by
  let s := exists_joyal_modelCategory.{u}.choose
  let M := JoyalSSet.modelCategory.{u}
  have h := exists_joyal_modelCategory.{u}.choose_spec.choose_spec
  obtain ⟨κ, regular, h⟩ := h
  let _ : Fact κ.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  let _ : OrderBot κ.ord.ToType := bottom
  obtain ⟨cg, h⟩ := h
  rcases h with ⟨_, _, _, _, _, _, _, _, hFirst, hSecond, _, hLeft,
    hG, _, _, _, _, hLP, hIκ, hGκ, hcgI, hcgG, hComb, hFibrant⟩
  refine ⟨s, M, κ, regular, bottom, cg,
    JoyalSSet.modelCategory_cofibrations,
    JoyalSSet.modelCategory_weakEquivalences,
    JoyalSSet.modelCategory_fibrations, ?_, ?_, ?_, ?_, hcgI, hcgG,
    cg.I_rlp, cg.J_rlp, ?_, ?_, hLP, hIκ, hGκ, hComb, hFibrant, ?_, ?_⟩
  · intro A B X Y i p hi hp a b sq
    exact actual_diagonal (monomorphisms _) I.rlp hFirst i p hi hp a b sq
  · intro A B X Y i p hi hw hp a b sq
    exact actual_diagonal (monomorphisms _ ⊓ W) _ hSecond i p
      ⟨hi, hw⟩ hp a b sq
  · intro X Y f
    exact actual_factorization (monomorphisms _) I.rlp hFirst f
  · intro X Y f
    obtain ⟨Z, i, p, hi, hp, hfac⟩ :=
      actual_factorization (monomorphisms _ ⊓ W) _ hSecond f
    exact ⟨Z, i, p, hi.1, hi.2, hp, hfac⟩
  · rw [hcgI]
    exact .mk 0
  · intro X Y g hg
    exact hG g hg

  · intro A B g
    rw [weakEquivalence_iff]
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (ofSSet.map g) ↔ _
    rw [JoyalSSet.modelCategory_weakEquivalences]
    rfl
  · intro A B g
    rw [fibration_iff]
    change JoyalSSet.modelCategory.categoryWithFibrations.fibrations
      (ofSSet.map g) ↔ _
    rw [JoyalSSet.modelCategory_fibrations]
    rfl

end JoyalSSet.FinalTest
