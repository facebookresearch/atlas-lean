/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrantHomotopy
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTesting

/-!
# Anodyne maps are homotopy-class testing equivalences

For a fixed exact functorial precylinder and its anodyne system, a homotopy
on the source of an anodyne map extends while keeping both prescribed
endpoints and its entire cylinder restriction. This makes precomposition
bijective on the actual chosen-cylinder homotopy classes into every naive
fibrant target.

The proof uses the specified boundary pushout and the single-homotopy
criterion. It applies in any category with binary coproducts, pushouts and
a terminal object, with independent object, morphism and colimit universes.

## References

- Cisinski, *Higher Categories and Homotopical Algebra*, July 30, 2026,
  Proposition 2.4.25, using Lemma 2.4.24.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C]
  [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- Extend the specified native homotopy across an anodyne map, keeping
both endpoints and the whole original cylinder restriction. -/
theorem extendLeftHomotopy_of_anodyne {X Y T : C} (i : X ⟶ Y) (hi : An i)
    (hT : An.naiveFibrantObjects T) (a₀ a₁ : Y ⟶ T)
    (H : (P.app X).LeftHomotopy (i ≫ a₀) (i ≫ a₁)) :
    ∃ K : (P.app Y).LeftHomotopy a₀ a₁, P.I.map i ≫ K.h = H.h := by
  have overlap : coprod.map i i ≫ coprod.desc a₀ a₁ = (P.app X).i ≫ H.h := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ (coprod.map i i ≫ coprod.desc a₀ a₁) = i ≫ a₀ := by
          simp only [coprod.inl_map_assoc, coprod.inl_desc]
        _ = coprod.inl ≫ ((P.app X).i ≫ H.h) := by
          rw [← Category.assoc, (P.app X).inl_i, H.h₀]
    · calc
        coprod.inr ≫ (coprod.map i i ≫ coprod.desc a₀ a₁) = i ≫ a₁ := by
          simp only [coprod.inr_map_assoc, coprod.inr_desc]
        _ = coprod.inr ≫ ((P.app X).i ≫ H.h) := by
          rw [← Category.assoc, (P.app X).inr_i, H.h₁]
  have hAn : An (P.boundaryCorner i) := boundary_corner i hi
  obtain ⟨F, hF⟩ := (An.naiveFibrantObjects_iff_extensions T).mp hT
    (P.boundaryCorner i) hAn (pushout.desc (coprod.desc a₀ a₁) H.h overlap)
  have boundary_eq : (P.app Y).i ≫ F = coprod.desc a₀ a₁ := by
    have q := congrArg ((pushout.inl (coprod.map i i) (P.app X).i) ≫ ·) hF
    simpa only [inl_boundaryCorner_assoc, pushout.inl_desc] using q
  have restriction : P.I.map i ≫ F = H.h := by
    have q := congrArg ((pushout.inr (coprod.map i i) (P.app X).i) ≫ ·) hF
    simpa only [inr_boundaryCorner_assoc, pushout.inr_desc] using q
  refine ⟨{ h := F, h₀ := ?_, h₁ := ?_ }, restriction⟩
  · have q := congrArg ((coprod.inl : Y ⟶ Y ⨿ Y) ≫ ·) boundary_eq
    simpa only [← Category.assoc, (P.app Y).inl_i, coprod.inl_desc] using q
  · have q := congrArg ((coprod.inr : Y ⟶ Y ⨿ Y) ≫ ·) boundary_eq
    simpa only [← Category.assoc, (P.app Y).inr_i, coprod.inr_desc] using q

/-- Every anodyne map induces a bijection on the actual quotient classes
into any naive fibrant target, with no fibrancy assumption on its source. -/
theorem bijective_homotopyClassPrecomp_of_anodyne {X Y T : C}
    (i : X ⟶ Y) (hi : An i) (hT : An.naiveFibrantObjects T) :
    Function.Bijective (P.homotopyClassPrecomp i T) := by
  constructor
  · intro c₀ c₁ hc
    obtain ⟨a₀, ha₀⟩ := P.homotopyQuotientFunctor.map_surjective c₀
    obtain ⟨a₁, ha₁⟩ := P.homotopyQuotientFunctor.map_surjective c₁
    have restricted_eq : P.homotopyQuotientFunctor.map (i ≫ a₀) =
        P.homotopyQuotientFunctor.map (i ≫ a₁) := by
      simpa only [← ha₀, ← ha₁, P.homotopyClassPrecomp_map] using hc
    obtain ⟨H⟩ := (homotopyQuotientFunctor_map_eq_iff_nonempty_leftHomotopy
      P An hT (i ≫ a₀) (i ≫ a₁)).mp restricted_eq
    obtain ⟨K, _⟩ := extendLeftHomotopy_of_anodyne P An i hi hT a₀ a₁ H
    exact ha₀.symm.trans ((P.homotopyQuotientFunctor_map_eq K).trans ha₁)
  · intro c
    obtain ⟨f, hf⟩ := P.homotopyQuotientFunctor.map_surjective c
    obtain ⟨g, hg⟩ := (An.naiveFibrantObjects_iff_extensions T).mp hT i hi f
    refine ⟨P.homotopyQuotientFunctor.map g, ?_⟩
    rw [P.homotopyClassPrecomp_map, hg]
    exact hf

/-- The whole anodyne class lies in the testing class for this same
cylinder and this same specified naive fibrancy predicate. -/
theorem anodyne_le_testingEquivalences : An ≤ P.testingEquivalences An := by
  intro X Y i hi
  exact (P.testingEquivalences_iff An i).mpr
    (fun T hT ↦ bijective_homotopyClassPrecomp_of_anodyne P An i hi hT)

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
