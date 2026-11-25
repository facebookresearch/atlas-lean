/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Actual Kan fibrations to constant simplicial sets

A map from a Kan simplicial set to a constant simplicial set is a Kan
fibration. Native horn filling first constructs the original filler. Its
base map is determined by any prescribed face, because maps from a standard
simplex into a constant set are determined by their single Yoneda value.
The original commuting lifting square therefore forces the filler over the
given base map. No filler, base-compatible homotopy or fibration certificate
is input.

This general native horn-lifting provider is needed to identify the actual
canonical polynomial augmentation as a trivial fibration.
Candidate source; UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- Into a constant set, one original face determines the whole standard-simplex map. -/
theorem homToConstant_ext_of_face {A : Type u} {n : ℕ} (i : Fin (n + 2))
    {f g : (Δ[n + 1] : SSet.{u}) ⟶ (SimplicialObject.const (Type u)).obj A}
    (h : (SSet.stdSimplex.δ i) ≫ f = (SSet.stdSimplex.δ i) ≫ g) : f = g := by
  apply SSet.yonedaEquiv.injective
  have h' := congrArg SSet.yonedaEquiv h
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.stdSimplex.yonedaEquiv_δ_comp] at h'
  exact h'

/-- The original Kan horn filler automatically lies over the actual constant base map. -/
theorem hasLiftingProperty_horn_to_constant {A : Type u} {E : SSet.{u}} [KanComplex E]
    (p : E ⟶ (SimplicialObject.const (Type u)).obj A) (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn (n + 1) i).ι p := by
  constructor
  intro f g sq
  obtain ⟨l, hl⟩ := SSet.KanComplex.hornFilling f
  refine CommSq.HasLift.mk' ⟨l, hl.symm, ?_⟩
  let j : Fin (n + 2) := if i = 0 then ⟨1, by omega⟩ else 0
  have hji : j ≠ i := by
    dsimp [j]
    split_ifs with h
    · subst i
      intro he
      have hv := congrArg Fin.val he
      norm_num at hv
    · exact Ne.symm h
  apply homToConstant_ext_of_face j
  calc
    SSet.stdSimplex.δ j ≫ (l ≫ p) =
        SSet.horn.ι i j hji ≫ (((SSet.horn (n + 1) i).ι ≫ l) ≫ p) := by
      rw [← SSet.horn.ι_ι i j hji, Category.assoc, Category.assoc]
    _ = SSet.horn.ι i j hji ≫ (f ≫ p) := by rw [← hl]
    _ = SSet.horn.ι i j hji ≫ ((SSet.horn (n + 1) i).ι ≫ g) := by rw [sq.w]
    _ = SSet.stdSimplex.δ j ≫ g := by rw [← Category.assoc, SSet.horn.ι_ι]

/-- Every actual map from a Kan simplicial set to constant A is a native fibration. -/
theorem fibration_to_constant {A : Type u} {E : SSet.{u}} [KanComplex E]
    (p : E ⟶ (SimplicialObject.const (Type u)).obj A) : Fibration p := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro K L f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact hasLiftingProperty_horn_to_constant p n i

end SSet

end
