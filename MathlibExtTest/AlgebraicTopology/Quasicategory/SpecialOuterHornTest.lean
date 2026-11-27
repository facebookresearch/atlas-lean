/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHorn
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
# Tests for three-dimensional special outer horn filling

Public clients exercise the simplex-level inner-horn fillers for
quasicategories (the general filler and its public
three-dimensional forms; the four-dimensional forms are private
to `SpecialOuterHorn.lean`, so the `Λ[4, 2]` statement below is
derived from the general filler instead), special outer horn
filling in dimension `3` on both sides, the packaging with
dimension `2` as filling in dimensions `2` and `3`, and the
interaction with the maximal core: a three-dimensional outer horn
factoring through the core fills in the ambient quasicategory
because its distinguished edge is an equivalence. Only public
declarations are used.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory
namespace SpecialOuterHornTest

open SSet

section Signatures

#check @SSet.exists_simplex_of_isCompatible
#check @SSet.exists_simplex_three_missing_two
#check @SSet.exists_simplex_three_missing_one
#check @SSet.exists_fill_horn_three_zero_of_isEquivalence
#check @SSet.exists_fill_horn_three_last_of_isEquivalence
#check @SSet.exists_fill_horn_left_of_isEquivalence_of_le_one
#check @SSet.exists_fill_horn_right_of_isEquivalence_of_le_one

end Signatures

section SimplexFillers

variable {X : SSet.{u}} [Quasicategory X]

/-- A `Λ[3, 2]`-shaped family of `2`-simplices in a quasicategory
is the family of prescribed faces of a `3`-simplex. -/
example {s₀ s₁ s₃ : X _⦋2⦌}
    (h₀₁ : X.δ (0 : Fin 3) s₀ = X.δ (0 : Fin 3) s₁)
    (h₀₃ : X.δ (2 : Fin 3) s₀ = X.δ (0 : Fin 3) s₃)
    (h₁₃ : X.δ (2 : Fin 3) s₁ = X.δ (1 : Fin 3) s₃) :
    ∃ σ : X _⦋3⦌, X.δ (0 : Fin 4) σ = s₀ ∧ X.δ (1 : Fin 4) σ = s₁ ∧
      X.δ (3 : Fin 4) σ = s₃ :=
  exists_simplex_three_missing_two h₀₁ h₀₃ h₁₃

/-- A `Λ[3, 1]`-shaped family of `2`-simplices in a quasicategory
is the family of prescribed faces of a `3`-simplex. -/
example {s₀ s₂ s₃ : X _⦋2⦌}
    (h₀₂ : X.δ (1 : Fin 3) s₀ = X.δ (0 : Fin 3) s₂)
    (h₀₃ : X.δ (2 : Fin 3) s₀ = X.δ (0 : Fin 3) s₃)
    (h₂₃ : X.δ (2 : Fin 3) s₂ = X.δ (2 : Fin 3) s₃) :
    ∃ σ : X _⦋3⦌, X.δ (0 : Fin 4) σ = s₀ ∧ X.δ (2 : Fin 4) σ = s₂ ∧
      X.δ (3 : Fin 4) σ = s₃ :=
  exists_simplex_three_missing_one h₀₂ h₀₃ h₂₃

/-- A `Λ[4, 2]`-shaped family of `3`-simplices in a quasicategory
is the family of prescribed faces of a `4`-simplex. The
four-dimensional form of the filler is private to
`SpecialOuterHorn.lean`, so this is derived from the public
general filler `exists_simplex_of_isCompatible`. -/
example {s₀ s₁ s₃ s₄ : X _⦋3⦌}
    (h₀₁ : X.δ (0 : Fin 4) s₀ = X.δ (0 : Fin 4) s₁)
    (h₀₃ : X.δ (2 : Fin 4) s₀ = X.δ (0 : Fin 4) s₃)
    (h₀₄ : X.δ (3 : Fin 4) s₀ = X.δ (0 : Fin 4) s₄)
    (h₁₃ : X.δ (2 : Fin 4) s₁ = X.δ (1 : Fin 4) s₃)
    (h₁₄ : X.δ (3 : Fin 4) s₁ = X.δ (1 : Fin 4) s₄)
    (h₃₄ : X.δ (3 : Fin 4) s₃ = X.δ (3 : Fin 4) s₄) :
    ∃ σ : X _⦋4⦌, X.δ (0 : Fin 5) σ = s₀ ∧ X.δ (1 : Fin 5) σ = s₁ ∧
      X.δ (3 : Fin 5) σ = s₃ ∧ X.δ (4 : Fin 5) σ = s₄ := by
  obtain ⟨σ, hσ⟩ := exists_simplex_of_isCompatible (X := X)
    (i := (2 : Fin 5)) (by decide) (by decide)
    (fun j _ ↦ ![s₀, s₁, s₀, s₃, s₄] j)
    (by
      intro j k hj hk hjk
      fin_cases j <;> fin_cases k <;>
        simp only [Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
          Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;>
          first | (simp_all; done) | (simp_all; rfl))
  exact ⟨σ, by simpa using hσ 0 (by decide), by simpa using hσ 1 (by decide),
    by simpa using hσ 3 (by decide), by simpa using hσ 4 (by decide)⟩

/-- The faces of any `3`-simplex of a quasicategory, omitting the
`2`-face, refill to a `3`-simplex with the same prescribed faces:
the simplex-level filler applied to a compatible family coming
from an inner horn. -/
example {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    (s : ∀ (j : Fin (n + 3)) (_ : j ≠ i), X _⦋n + 1⦌)
    (hs : ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (s j hj) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (s k hk)) :
    ∃ σ : X _⦋n + 2⦌, ∀ (j : Fin (n + 3)) (hj : j ≠ i),
      X.δ j σ = s j hj :=
  exists_simplex_of_isCompatible h0 hn s hs

end SimplexFillers

section ThreeDimensional

variable {X : SSet.{u}} [Quasicategory X]

/-- Horn form of `Λ[3, 0]` special filling in a quasicategory. -/
example (σ₀ : (Λ[3, (0 : Fin 4)] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ X, σ₀ = Λ[3, (0 : Fin 4)].ι ≫ σ :=
  exists_fill_horn_three_zero_of_isEquivalence σ₀ h

/-- Horn form of `Λ[3, 3]` special filling in a quasicategory. -/
example (σ₀ : (Λ[3, Fin.last 3] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ X, σ₀ = Λ[3, Fin.last 3].ι ≫ σ :=
  exists_fill_horn_three_last_of_isEquivalence σ₀ h

/-- A left outer horn of the core in dimension `3` fills in `X`:
its first edge is an equivalence because it factors through the
core. -/
example (τ : (Λ[3, (0 : Fin 4)] : SSet.{u}) ⟶ (core X : SSet.{u})) :
    ∃ σ : Δ[3] ⟶ X, (τ ≫ (core X).ι) = Λ[3, (0 : Fin 4)].ι ≫ σ :=
  exists_fill_horn_three_zero_of_isEquivalence _
    (leftHornEdge_isEquivalence_of_factor_core τ)

/-- A right outer horn of the core in dimension `3` fills in `X`:
its last edge is an equivalence because it factors through the
core. -/
example (τ : (Λ[3, Fin.last 3] : SSet.{u}) ⟶ (core X : SSet.{u})) :
    ∃ σ : Δ[3] ⟶ X, (τ ≫ (core X).ι) = Λ[3, Fin.last 3].ι ≫ σ :=
  exists_fill_horn_three_last_of_isEquivalence _
    (rightHornEdge_isEquivalence_of_factor_core τ)

end ThreeDimensional

section UpToThree

variable {X : SSet.{u}} [Quasicategory X] {n : ℕ}

/-- Left special outer horn filling in dimensions `2` and `3`,
left case in dimension `2` included. -/
example (hn : n ≤ 1)
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence_of_le_one hn σ₀ h

/-- Right special outer horn filling in dimensions `2` and `3`. -/
example (hn : n ≤ 1)
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence_of_le_one hn σ₀ h

/-- The packaged form specializes to the `Λ[3, 0]` theorem. -/
example (σ₀ : (Λ[3, (0 : Fin 4)] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ X, σ₀ = Λ[3, (0 : Fin 4)].ι ≫ σ :=
  exists_fill_horn_left_of_isEquivalence_of_le_one (n := 1) le_rfl σ₀ h

/-- The packaged form specializes to the `Λ[2, 2]` theorem of
`CoreKan.lean`. -/
example (σ₀ : (Λ[2, Fin.last 2] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2] ⟶ X, σ₀ = Λ[2, Fin.last 2].ι ≫ σ :=
  exists_fill_horn_right_of_isEquivalence_of_le_one (n := 0) (Nat.zero_le 1) σ₀ h

end UpToThree

section NerveGate

variable {C : Type u} [Category.{v} C]

/-- In a nerve, a `Λ[3, 0]` horn whose `(0, 1)`-edge is an
equivalence fills: this is the three-dimensional theorem applied
to the nerve, which is a quasicategory. -/
example (σ₀ : (Λ[3, (0 : Fin 4)] : SSet) ⟶ nerve C)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ nerve C, σ₀ = Λ[3, (0 : Fin 4)].ι ≫ σ :=
  exists_fill_horn_three_zero_of_isEquivalence σ₀ h

/-- In a nerve, a `Λ[3, 3]` horn whose `(2, 3)`-edge is an
equivalence fills. -/
example (σ₀ : (Λ[3, Fin.last 3] : SSet) ⟶ nerve C)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[3] ⟶ nerve C, σ₀ = Λ[3, Fin.last 3].ι ≫ σ :=
  exists_fill_horn_three_last_of_isEquivalence σ₀ h

end NerveGate

end SpecialOuterHornTest
end MathlibExtTest.AlgebraicTopology.Quasicategory
