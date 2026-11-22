/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Edge-invariant full subcomplexes have Kan-fibration inclusions

A full subcomplex whose vertex condition is invariant across every whole
original edge lifts all horns. Higher horns already contain every vertex;
in dimension one, the supplied original edge transports the single horn
vertex condition. The ambient simplicial set need not be Kan.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Subcomplex

/-- An original one-simplex lies in a full subcomplex exactly when both endpoints do. -/
theorem mem_full_obj_one_iff {X : SSet.{u}} (V : Set (X _⦋0⦌)) (z : X _⦋1⦌) :
    z ∈ (full (X := X) V).obj (op ⦋1⦌) ↔ X.δ 1 z ∈ V ∧ X.δ 0 z ∈ V := by
  rw [mem_full_obj_iff]
  constructor
  · intro h
    exact ⟨h (SimplexCategory.δ 1), h (SimplexCategory.δ 0)⟩
  · intro h φ
    obtain ⟨i, rfl⟩ := SimplexCategory.exists_eq_const_of_zero φ
    fin_cases i
    · have he : SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
        ext i
        fin_cases i
        rfl
      change X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2)).op z ∈ V
      rw [he]
      exact h.1
    · have he : SimplexCategory.const ⦋0⦌ ⦋1⦌ (1 : Fin 2) = SimplexCategory.δ (0 : Fin 2) := by
        ext i
        fin_cases i
        rfl
      change X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ (1 : Fin 2)).op z ∈ V
      rw [he]
      exact h.2

/-- The original one-dimensional horns lift through an edge-invariant full subcomplex. -/
theorem hasLiftingProperty_one_horn_full_ι {X : SSet.{u}} (V : Set (X _⦋0⦌))
    (hV : ∀ z : X _⦋1⦌, X.δ 1 z ∈ V ↔ X.δ 0 z ∈ V) (j : Fin 2) :
    HasLiftingProperty (horn.{u} 1 j).ι (full (X := X) V).ι where
  sq_hasLift {a b} sq := by
    have he : yonedaEquiv b ∈ (full (X := X) V).obj (op ⦋1⦌) := by
      rw [mem_full_obj_one_iff]
      fin_cases j
      · let v : (Δ[0] : SSet.{u}) ⟶ (full (X := X) V : SSet.{u}) :=
          horn.ι (0 : Fin 2) (1 : Fin 2) (by decide) ≫ a
        have hv : X.δ 1 (yonedaEquiv b) ∈ V := by
          have hv' : (yonedaEquiv v).val ∈ V := mem_full_obj_zero_iff.mp (yonedaEquiv v).property
          have hw : v ≫ (full (X := X) V).ι = stdSimplex.δ (1 : Fin 2) ≫ b := by
            dsimp only [v]
            rw [Category.assoc, sq.w]
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (fun t => t ≫ b) (horn.ι_ι (0 : Fin 2) (1 : Fin 2) (by decide)))
          have hvb := congrArg yonedaEquiv hw
          rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp] at hvb
          exact hvb ▸ hv'
        exact ⟨hv, (hV _).mp hv⟩
      · let v : (Δ[0] : SSet.{u}) ⟶ (full (X := X) V : SSet.{u}) :=
          horn.ι (1 : Fin 2) (0 : Fin 2) (by decide) ≫ a
        have hv : X.δ 0 (yonedaEquiv b) ∈ V := by
          have hv' : (yonedaEquiv v).val ∈ V := mem_full_obj_zero_iff.mp (yonedaEquiv v).property
          have hw : v ≫ (full (X := X) V).ι = stdSimplex.δ (0 : Fin 2) ≫ b := by
            dsimp only [v]
            rw [Category.assoc, sq.w]
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (fun t => t ≫ b) (horn.ι_ι (1 : Fin 2) (0 : Fin 2) (by decide)))
          have hvb := congrArg yonedaEquiv hw
          rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp] at hvb
          exact hvb ▸ hv'
        exact ⟨(hV _).mpr hv, hv⟩
    let l : (Δ[1] : SSet.{u}) ⟶ (full (X := X) V : SSet.{u}) := yonedaEquiv.symm ⟨yonedaEquiv b, he⟩
    have hl : l ≫ (full (X := X) V).ι = b := by
      rw [yonedaEquiv_symm_comp]
      exact yonedaEquiv.symm_apply_apply b
    refine CommSq.HasLift.mk' ⟨l, ?_, hl⟩
    apply (cancel_mono (full (X := X) V).ι).mp
    rw [Category.assoc, hl]
    exact sq.w.symm

/-- The original full-subcomplex inclusion lifts all horns if its vertex condition is edge-invariant. -/
theorem fibration_full_ι_of_edge_invariant {X : SSet.{u}} (V : Set (X _⦋0⦌))
    (hV : ∀ z : X _⦋1⦌, X.δ 1 z ∈ V ↔ X.δ 0 z ∈ V) :
    HomotopicalAlgebra.Fibration (full (X := X) V).ι := by
  apply (modelCategoryQuillen.fibration_iff ((full (X := X) V).ι)).mpr
  intro A D i hi
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨j⟩⟩ := hi
  cases n with
  | succ n => exact hasLiftingProperty_horn_full_ι V j
  | zero => exact hasLiftingProperty_one_horn_full_ι V hV j

end SSet.Subcomplex
