/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.MatchingOne
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # Public consumers of the two labelled matching-one comparisons -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite
open scoped Simplicial

namespace MatchingOneTest

section Generic

variable {C : Type u} [Category.{v} C]
  [HasBinaryProducts C] [HasLimitsOfShape (matchingIndex 1) C]

/-- Whole original arrows have the same degree-one source in both comparison directions and
both labelled orders, in independent coefficient universes. -/
theorem original_sources (X : SimplicialObject C) :
    (matchingOneArrowIso.app X).hom.left = 𝟙 (X.obj (op ⦋1⦌)) ∧
    (matchingOneArrowIso.app X).inv.left = 𝟙 (X.obj (op ⦋1⦌)) ∧
    (matchingOneSourceTargetArrowIso.app X).hom.left = 𝟙 (X.obj (op ⦋1⦌)) ∧
    (matchingOneSourceTargetArrowIso.app X).inv.left = 𝟙 (X.obj (op ⦋1⦌)) :=
  ⟨matchingOneArrowIso_hom_left X, matchingOneArrowIso_inv_left X,
    matchingOneSourceTargetArrowIso_hom_left X, matchingOneSourceTargetArrowIso_inv_left X⟩

/-- Both inverse routes recover their original matching face, with the swap made explicit. -/
theorem inverse_labelled_legs (X : SimplicialObject C) :
    (matchingOneIso.app X).inv ≫ matchingπ X 1 (matchingOneFace 0) = prod.fst ∧
    (matchingOneIso.app X).inv ≫ matchingπ X 1 (matchingOneFace 1) = prod.snd ∧
    (matchingOneSourceTargetIso.app X).inv ≫ matchingπ X 1 (matchingOneFace 1) = prod.fst ∧
    (matchingOneSourceTargetIso.app X).inv ≫ matchingπ X 1 (matchingOneFace 0) = prod.snd :=
  ⟨matchingOneIso_inv_fst X, matchingOneIso_inv_snd X,
    matchingOneSourceTargetIso_inv_fst X, matchingOneSourceTargetIso_inv_snd X⟩

/-- Every raw morphism, with both original endpoints varying, has both whole naturality squares. -/
theorem raw_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (matchingMapArrowFunctor 1).map f ≫ (matchingOneArrowIso.app Y).hom =
        (matchingOneArrowIso.app X).hom ≫ matchingOnePairArrowFunctor.map f ∧
    matchingOnePairArrowFunctor.map f ≫ (matchingOneArrowIso.app Y).inv =
        (matchingOneArrowIso.app X).inv ≫ (matchingMapArrowFunctor 1).map f ∧
    (matchingMapArrowFunctor 1).map f ≫ (matchingOneSourceTargetArrowIso.app Y).hom =
        (matchingOneSourceTargetArrowIso.app X).hom ≫ matchingOneSourceTargetArrowFunctor.map f ∧
    matchingOneSourceTargetArrowFunctor.map f ≫ (matchingOneSourceTargetArrowIso.app Y).inv =
        (matchingOneSourceTargetArrowIso.app X).inv ≫ (matchingMapArrowFunctor 1).map f :=
  ⟨matchingOneArrowIso_hom_naturality f, matchingOneArrowIso_inv_naturality f,
    matchingOneSourceTargetArrowIso_hom_naturality f,
    matchingOneSourceTargetArrowIso_inv_naturality f⟩

end Generic

/-- The identity edge of the nonconstant interval has target/source values 1/0 in the chosen
product, and source/target values 0/1 after the explicit swap. -/
theorem asymmetric_face_values :
    let X : SimplicialObject (Type 0) := (Δ[1] : SSet.{0})
    let e : X.obj (op ⦋1⦌) := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
    SSet.stdSimplex.obj₀Equiv
      (((matchingMap X 1 ≫ (matchingOneIso.app X).hom) ≫ prod.fst) e) = (1 : Fin 2) ∧
    SSet.stdSimplex.obj₀Equiv
      (((matchingMap X 1 ≫ (matchingOneIso.app X).hom) ≫ prod.snd) e) = (0 : Fin 2) ∧
    SSet.stdSimplex.obj₀Equiv
      (((matchingMap X 1 ≫ (matchingOneSourceTargetIso.app X).hom) ≫ prod.fst) e) =
        (0 : Fin 2) ∧
    SSet.stdSimplex.obj₀Equiv
      (((matchingMap X 1 ≫ (matchingOneSourceTargetIso.app X).hom) ≫ prod.snd) e) =
        (1 : Fin 2) := by
  dsimp only
  have first (i j : Fin 2) :
      SSet.stdSimplex.obj₀Equiv
        ((prod.lift ((Δ[1] : SSet.{0}).δ i) ((Δ[1] : SSet.{0}).δ j) ≫ prod.fst)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) =
        (SimplexCategory.δ i).toOrderHom 0 := by
    rw [prod.lift_fst]
    change SSet.stdSimplex.obj₀Equiv
      ((Δ[1] : SSet.{0}).map (SimplexCategory.δ i).op
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) = _
    rw [SSet.stdSimplex.map_objEquiv_symm]
    simp only [Category.comp_id]
    rfl
  have second (i j : Fin 2) :
      SSet.stdSimplex.obj₀Equiv
        ((prod.lift ((Δ[1] : SSet.{0}).δ i) ((Δ[1] : SSet.{0}).δ j) ≫ prod.snd)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) =
        (SimplexCategory.δ j).toOrderHom 0 := by
    rw [prod.lift_snd]
    change SSet.stdSimplex.obj₀Equiv
      ((Δ[1] : SSet.{0}).map (SimplexCategory.δ j).op
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) = _
    rw [SSet.stdSimplex.map_objEquiv_symm]
    simp only [Category.comp_id]
    rfl
  simp only [Iso.app_hom]
  rw [matchingOneIso_matchingMap, matchingOneSourceTargetIso_matchingMap]
  exact ⟨first 0 1, second 0 1, first 1 0, second 1 0⟩

/-- The collapsing degeneracy is genuinely non-monic and still satisfies the whole naturality
equations, without a model or a fibrancy hypothesis. -/
theorem nonmono_collapse_naturality :
    let f : (Δ[1] : SSet.{0}) ⟶ Δ[0] := SSet.stdSimplex.σ (0 : Fin 1)
    ¬ Mono f ∧
    (matchingMapArrowFunctor 1).map f ≫ (matchingOneArrowIso.app (Δ[0] : SSet.{0})).hom =
        (matchingOneArrowIso.app (Δ[1] : SSet.{0})).hom ≫ matchingOnePairArrowFunctor.map f ∧
    matchingOneSourceTargetArrowFunctor.map f ≫
        (matchingOneSourceTargetArrowIso.app (Δ[0] : SSet.{0})).inv =
      (matchingOneSourceTargetArrowIso.app (Δ[1] : SSet.{0})).inv ≫
        (matchingMapArrowFunctor 1).map f := by
  dsimp only
  refine ⟨?_, matchingOneArrowIso_hom_naturality _,
    matchingOneSourceTargetArrowIso_inv_naturality _⟩
  intro h
  let _ : Mono (SSet.stdSimplex.σ (0 : Fin 1) : (Δ[1] : SSet.{0}) ⟶ Δ[0]) := h
  have hi : Function.Injective ((SSet.stdSimplex.σ (0 : Fin 1)).app (op ⦋0⦌)) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  have hv : (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{0}).obj (op ⦋0⦌)) =
      SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    apply hi
    apply SSet.stdSimplex.obj₀Equiv.injective
    have heq (a b : Fin (0 + 1)) : a = b := by
      apply Fin.ext
      exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ a.isLt)).trans
        (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ b.isLt)).symm
    exact heq _ _
  have h01 : (0 : Fin 2) = 1 := by
    simpa only [Equiv.apply_symm_apply] using congrArg SSet.stdSimplex.obj₀Equiv hv
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- The same natural comparison is available with raised coefficient object and hom universes. -/
theorem raised_universe_scope (X : SimplicialObject (Type (u + 1))) :
    (matchingOneArrowIso.app X).hom.left = 𝟙 (X.obj (op ⦋1⦌)) ∧
    (matchingOneSourceTargetIso.app X).inv ≫ matchingπ X 1 (matchingOneFace 0) = prod.snd :=
  ⟨matchingOneArrowIso_hom_left X, matchingOneSourceTargetIso_inv_snd X⟩

end MatchingOneTest
