/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTesting

/-!
# Yoneda criteria for chosen-cylinder homotopy equivalences

The actual quotient functor is full, so an inverse class has an original
morphism representative. Invertibility is also detected by postcomposition
and precomposition on classes for every original object. Restricting the
targets to naive fibrant objects gives membership in the testing class.

These are Cisinski Proposition 2.4.15 and the homotopy-equivalence inclusion
in Remark 2.4.21, in the July 30, 2026 version. The primitive criteria use
any functorial precylinder; the exact presheaf cylinder is the source case.
The inverse equations concern generated classes, not elementary homotopies.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C)) {X Y : C}

/-- A homotopy equivalence has an original inverse with both generated-class equations. -/
lemma homotopyEquivalences_iff_exists_inverse (f : X ⟶ Y) :
    P.homotopyEquivalences f ↔
      ∃ g : Y ⟶ X, P.homotopyRel (f ≫ g) (𝟙 X) ∧
        P.homotopyRel (g ≫ f) (𝟙 Y) := by
  rw [P.homotopyEquivalences_iff]
  constructor
  · intro hf
    have := hf
    let g : Y ⟶ X := P.homotopyQuotientFunctor.preimage
      (inv (P.homotopyQuotientFunctor.map f))
    refine ⟨g, ?_, ?_⟩
    · apply (P.homotopyQuotientFunctor_map_eq_iff (f ≫ g) (𝟙 X)).1
      rw [P.homotopyQuotientFunctor.map_id]
      simp only [Functor.map_comp, g, Functor.map_preimage, IsIso.hom_inv_id]
    · apply (P.homotopyQuotientFunctor_map_eq_iff (g ≫ f) (𝟙 Y)).1
      rw [P.homotopyQuotientFunctor.map_id]
      simp only [Functor.map_comp, g, Functor.map_preimage, IsIso.inv_hom_id]
  · rintro ⟨g, hfg, hgf⟩
    refine ⟨P.homotopyQuotientFunctor.map g, ?_, ?_⟩
    · have h := (P.homotopyQuotientFunctor_map_eq_iff (f ≫ g) (𝟙 X)).2 hfg
      rw [P.homotopyQuotientFunctor.map_comp, P.homotopyQuotientFunctor.map_id] at h
      exact h
    · have h := (P.homotopyQuotientFunctor_map_eq_iff (g ≫ f) (𝟙 Y)).2 hgf
      rw [P.homotopyQuotientFunctor.map_comp, P.homotopyQuotientFunctor.map_id] at h
      exact h

/-- Postcomposition on classes into the quotient is bijective at every original source. -/
lemma homotopyEquivalences_iff_postcomp_bijective (f : X ⟶ Y) :
    P.homotopyEquivalences f ↔
      ∀ T : C, Function.Bijective
        (fun a : P.HomotopyClass T X ↦ a ≫ P.homotopyQuotientFunctor.map f) := by
  rw [P.homotopyEquivalences_iff]
  constructor
  · intro hf T
    exact (isIso_iff_yoneda_map_bijective (P.homotopyQuotientFunctor.map f)).1 hf
      (P.homotopyQuotientFunctor.obj T)
  · intro h
    apply (isIso_iff_yoneda_map_bijective (P.homotopyQuotientFunctor.map f)).2
    rintro ⟨T⟩
    exact h T

/-- Precomposition on classes is bijective at every original target. -/
lemma homotopyEquivalences_iff_precomp_bijective (f : X ⟶ Y) :
    P.homotopyEquivalences f ↔
      ∀ T : C, Function.Bijective (P.homotopyClassPrecomp f T) := by
  rw [P.homotopyEquivalences_iff]
  constructor
  · intro hf T
    change Function.Bijective
      (fun a : P.HomotopyClass Y T ↦ P.homotopyQuotientFunctor.map f ≫ a)
    exact (isIso_iff_coyoneda_map_bijective (P.homotopyQuotientFunctor.map f)).1 hf
      (P.homotopyQuotientFunctor.obj T)
  · intro h
    apply (isIso_iff_coyoneda_map_bijective (P.homotopyQuotientFunctor.map f)).2
    rintro ⟨T⟩
    exact h T

/-- The four source criteria, with invertibility of the actual quotient map as common clause. -/
lemma homotopyEquivalences_criterion (f : X ⟶ Y) :
    (IsIso (P.homotopyQuotientFunctor.map f) ↔
      ∃ g : Y ⟶ X, P.homotopyRel (f ≫ g) (𝟙 X) ∧ P.homotopyRel (g ≫ f) (𝟙 Y)) ∧
    (IsIso (P.homotopyQuotientFunctor.map f) ↔
      ∀ T : C, Function.Bijective
        (fun a : P.HomotopyClass T X ↦ a ≫ P.homotopyQuotientFunctor.map f)) ∧
    (IsIso (P.homotopyQuotientFunctor.map f) ↔
      ∀ T : C, Function.Bijective (P.homotopyClassPrecomp f T)) :=
  ⟨(P.homotopyEquivalences_iff f).symm.trans (P.homotopyEquivalences_iff_exists_inverse f),
    (P.homotopyEquivalences_iff f).symm.trans (P.homotopyEquivalences_iff_postcomp_bijective f),
    (P.homotopyEquivalences_iff f).symm.trans (P.homotopyEquivalences_iff_precomp_bijective f)⟩

/-- Testing against the naive fibrant objects includes every homotopy equivalence. -/
lemma homotopyEquivalences_le_testingEquivalences (An : MorphismProperty C)
    [HasTerminal C] : P.homotopyEquivalences ≤ P.testingEquivalences An := by
  intro X Y f hf
  apply (P.testingEquivalences_iff An f).2
  exact fun T _ ↦ (P.homotopyEquivalences_iff_precomp_bijective f).1 hf T

end HomotopicalAlgebra.Precylinder
