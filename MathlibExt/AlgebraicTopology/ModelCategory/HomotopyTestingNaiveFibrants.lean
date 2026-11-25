/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyYoneda
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrantHomotopy

/-!
# Testing equivalences between naive fibrant objects

Testing at the two endpoints supplies an actual inverse representative in
the chosen-cylinder quotient. For a fixed exact anodyne system, both inverse
class equations have elementary homotopy witnesses for that same cylinder.

This is the two-target form of Cisinski, *Higher Categories and Homotopical
Algebra*, July 30, 2026, Proposition 2.4.26 (printed p.59). The fixed-cylinder
witnesses use Lemma 2.4.24 (printed pp.58–59).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) (An : MorphismProperty C) {X Y : C}

/-- The two endpoint tests detect invertibility in the actual quotient when
both objects are naive fibrant. No exactness or model hypothesis is needed. -/
theorem testingEquivalences_iff_homotopyEquivalences (f : X ⟶ Y)
    (hX : An.naiveFibrantObjects X) (hY : An.naiveFibrantObjects Y) :
    P.testingEquivalences An f ↔ P.homotopyEquivalences f := by
  constructor
  · intro hf
    have htest := (P.testingEquivalences_iff An f).mp hf
    obtain ⟨a, ha⟩ := (htest X hX).surjective (𝟙 _)
    change P.homotopyQuotientFunctor.map f ≫ a = 𝟙 _ at ha
    let g : Y ⟶ X := P.homotopyQuotientFunctor.preimage a
    have hfg : P.homotopyQuotientFunctor.map f ≫
        P.homotopyQuotientFunctor.map g = 𝟙 _ := by
      simpa only [g, Functor.map_preimage] using ha
    have hgf : P.homotopyQuotientFunctor.map g ≫
        P.homotopyQuotientFunctor.map f = 𝟙 _ := by
      apply (htest Y hY).injective
      change P.homotopyQuotientFunctor.map f ≫
          (P.homotopyQuotientFunctor.map g ≫ P.homotopyQuotientFunctor.map f) =
        P.homotopyQuotientFunctor.map f ≫ 𝟙 _
      rw [← Category.assoc, hfg, Category.id_comp, Category.comp_id]
    rw [P.homotopyEquivalences_iff]
    exact ⟨P.homotopyQuotientFunctor.map g, hfg, hgf⟩
  · exact P.homotopyEquivalences_le_testingEquivalences An f

namespace IsAnodyneSystem

variable [HasBinaryCoproducts C] [HasPushouts C] [P.IsExact.{w}]
  [P.IsAnodyneSystem.{w} An]

/-- Testing equivalence between naive fibrants has an original inverse and
both identity-to-composite homotopies for the given fixed cylinder. -/
theorem testingEquivalences_iff_exists_leftHomotopy_inverse (f : X ⟶ Y)
    (hX : An.naiveFibrantObjects X) (hY : An.naiveFibrantObjects Y) :
    P.testingEquivalences An f ↔
      ∃ g : Y ⟶ X, Nonempty ((P.app X).LeftHomotopy (𝟙 X) (f ≫ g)) ∧
        Nonempty ((P.app Y).LeftHomotopy (𝟙 Y) (g ≫ f)) := by
  constructor
  · intro hf
    have he := (P.testingEquivalences_iff_homotopyEquivalences An f hX hY).mp hf
    obtain ⟨g, hfg, hgf⟩ := (P.homotopyEquivalences_iff_exists_inverse f).mp he
    refine ⟨g, ?_, ?_⟩
    · apply (homotopyQuotientFunctor_map_eq_iff_nonempty_leftHomotopy P An hX
        (𝟙 X) (f ≫ g)).mp
      exact ((P.homotopyQuotientFunctor_map_eq_iff _ _).mpr hfg).symm
    · apply (homotopyQuotientFunctor_map_eq_iff_nonempty_leftHomotopy P An hY
        (𝟙 Y) (g ≫ f)).mp
      exact ((P.homotopyQuotientFunctor_map_eq_iff _ _).mpr hgf).symm
  · rintro ⟨g, ⟨H⟩, ⟨K⟩⟩
    apply (P.testingEquivalences_iff_homotopyEquivalences An f hX hY).mpr
    apply (P.homotopyEquivalences_iff_exists_inverse f).mpr
    exact ⟨g,
      (P.homotopyQuotientFunctor_map_eq_iff _ _).mp
        (P.homotopyQuotientFunctor_map_eq H).symm,
      (P.homotopyQuotientFunctor_map_eq_iff _ _).mp
        (P.homotopyQuotientFunctor_map_eq K).symm⟩

end IsAnodyneSystem

end HomotopicalAlgebra.Precylinder
