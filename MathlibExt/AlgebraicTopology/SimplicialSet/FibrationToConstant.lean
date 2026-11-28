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
# Kan fibrations to constant simplicial sets

Let `E : SSet.{u}` be a Kan complex and `A : Type u`. Every simplicial map `E → const A` is a
Kan fibration. For each positive-dimensional horn lifting square, a Kan filler of the source
lies over the given map to the constant target.

A map `Δ[n+1] → const A` is determined by its restriction to any face. This gives the base-map
equality required for each horn filler.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- Let `A : Type u`, `n : ℕ`, and `i : Fin(n+2)`. For `f,g : Δ[n+1] → const A`, if their
restrictions along the face inclusion `stdSimplex.δ i : Δ[n] → Δ[n+1]` are equal, then `f=g`. -/
theorem homToConstant_ext_of_face {A : Type u} {n : ℕ} (i : Fin (n + 2))
    {f g : (Δ[n + 1] : SSet.{u}) ⟶ (SimplicialObject.const (Type u)).obj A}
    (h : (SSet.stdSimplex.δ i) ≫ f = (SSet.stdSimplex.δ i) ≫ g) : f = g := by
  apply SSet.yonedaEquiv.injective
  have h' := congrArg SSet.yonedaEquiv h
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.stdSimplex.yonedaEquiv_δ_comp] at h'
  exact h'

/-- Let `E : SSet.{u}` be a Kan complex, `A : Type u`, and `p : E → const A`. For every `n : ℕ`
and `i : Fin(n+2)`, the horn inclusion `Λ_i[n+1] → Δ[n+1]` has the left lifting property
against `p`. Thus every such commuting square has a filler over its prescribed constant-target
simplex. -/
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

/-- For a Kan simplicial set `E : SSet.{u}`, a type `A : Type u`, and any simplicial map `p : E →
const A`, `Fibration p` holds. This is the Kan horn-lifting property in all positive
dimensions. -/
theorem fibration_to_constant {A : Type u} {E : SSet.{u}} [KanComplex E]
    (p : E ⟶ (SimplicialObject.const (Type u)).obj A) : Fibration p := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro K L f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact hasLiftingProperty_horn_to_constant p n i

end SSet

end
