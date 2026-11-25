/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRightExtraDegeneracy

/-!
# Left/right extra degeneracies via augmented reversal

Genuine augmented simplex reversal `rev` exchanges the two handednesses:
a right extra degeneracy on `X` gives Mathlib's left-handed
`Augmented.ExtraDegeneracy` on `rev X`, and vice versa, preserving `s'` and `s`,
so right-handed objects reuse the left-handed consequences.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Augmented

variable {C : Type u} [Category.{v} C]

namespace RightExtraDegeneracy

/-- Right extra-degeneracy on `X` gives left `ExtraDegeneracy` on `rev X`,
preserving the underlying `s'` and `s`. -/
def toExtraDegeneracyRev {X : Augmented C} (R : RightExtraDegeneracy X) :
    ExtraDegeneracy (rev X) where
  s' := R.s'
  s := R.s
  s'_comp_ε := by
    simp only [rev_hom_app_mk]
    exact R.s'_comp_ε
  s₀_comp_δ₁ := by
    have h_rev : (1 : Fin 2).rev = (0 : Fin 2) := by
      have h_eq : (1 : Fin 2) = Fin.last 1 := rfl
      rw [h_eq, Fin.rev_last]
    rw [rev_left_δ, h_rev, rev_hom_app_mk]
    exact R.s₀_comp_δ₀
  s_comp_δ₀ := by
    intro n
    rw [rev_left_δ, Fin.rev_zero]
    exact R.s_comp_δ_last n
  s_comp_δ := by
    intro n i
    rw [rev_left_δ, Fin.rev_succ, rev_left_δ]
    exact R.s_comp_δ n i.rev
  s_comp_σ := by
    intro n i
    rw [rev_left_σ, Fin.rev_succ, rev_left_σ]
    exact R.s_comp_σ n i.rev

@[simp]
theorem toExtraDegeneracyRev_s' {X : Augmented C} (R : RightExtraDegeneracy X) :
    (R.toExtraDegeneracyRev).s' = R.s' :=
  rfl

@[simp]
theorem toExtraDegeneracyRev_s {X : Augmented C} (R : RightExtraDegeneracy X) (n : ℕ) :
    (R.toExtraDegeneracyRev).s n = R.s n :=
  rfl

end RightExtraDegeneracy

namespace ExtraDegeneracy

/-- Left `ExtraDegeneracy` on `X` gives right extra-degeneracy on `rev X`,
preserving the underlying `s'` and `s`. -/
def toRightExtraDegeneracyRev {X : Augmented C} (L : ExtraDegeneracy X) :
    RightExtraDegeneracy (rev X) where
  s' := L.s'
  s := L.s
  s'_comp_ε := by
    simp only [rev_hom_app_mk]
    exact L.s'_comp_ε
  s₀_comp_δ₀ := by
    rw [rev_left_δ, Fin.rev_zero, rev_hom_app_mk]
    exact L.s₀_comp_δ₁
  s_comp_δ_last := by
    intro n
    rw [rev_left_δ, Fin.rev_last]
    exact L.s_comp_δ₀ n
  s_comp_δ := by
    intro n i
    rw [rev_left_δ, Fin.rev_castSucc, rev_left_δ]
    exact L.s_comp_δ n i.rev
  s_comp_σ := by
    intro n i
    rw [rev_left_σ, Fin.rev_castSucc, rev_left_σ]
    exact L.s_comp_σ n i.rev

@[simp]
theorem toRightExtraDegeneracyRev_s' {X : Augmented C} (L : ExtraDegeneracy X) :
    (L.toRightExtraDegeneracyRev).s' = L.s' :=
  rfl

@[simp]
theorem toRightExtraDegeneracyRev_s {X : Augmented C} (L : ExtraDegeneracy X) (n : ℕ) :
    (L.toRightExtraDegeneracyRev).s n = L.s n :=
  rfl

end ExtraDegeneracy

end Augmented
end SimplicialObject
end CategoryTheory

end
