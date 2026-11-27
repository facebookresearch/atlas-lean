/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRightExtraDegeneracy

/-!
# Extra degeneracies under augmented simplicial reversal

Reversing the simplex order exchanges left and right extra degeneracies of an
augmented simplicial object in an arbitrary category. The augmentation section `s'`
and each extra-degeneracy map `s_n` stay the same underlying morphisms; reversal
changes the face and degeneracy indices in their identities.

Thus a right extra degeneracy on `X` supplies a left extra degeneracy on `rev X`,
and a left extra degeneracy on `X` supplies a right extra degeneracy on `rev X`.
Object and morphism universes of the category are independent.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Augmented

variable {C : Type u} [Category.{v} C]

namespace RightExtraDegeneracy

/--
The left extra degeneracy on the reversed augmented object `rev X` associated to
a right extra degeneracy on `X`, with the same underlying section and extra maps.
-/
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

/--
The augmentation section of the left extra degeneracy obtained by reversal is the
same morphism `s'` as that of the given right extra degeneracy.
-/
@[simp]
theorem toExtraDegeneracyRev_s' {X : Augmented C} (R : RightExtraDegeneracy X) :
    (R.toExtraDegeneracyRev).s' = R.s' :=
  rfl

/--
In each degree `n`, the extra map of the reversed left extra degeneracy equals
the given right extra-degeneracy map `s_n`.
-/
@[simp]
theorem toExtraDegeneracyRev_s {X : Augmented C} (R : RightExtraDegeneracy X) (n : ℕ) :
    (R.toExtraDegeneracyRev).s n = R.s n :=
  rfl

end RightExtraDegeneracy

namespace ExtraDegeneracy

/--
The right extra degeneracy on `rev X` associated to a left extra degeneracy on `X`,
with the same underlying section and extra maps.
-/
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

/--
The augmentation section of the right extra degeneracy obtained by reversal is the
same morphism `s'` as that of the given left extra degeneracy.
-/
@[simp]
theorem toRightExtraDegeneracyRev_s' {X : Augmented C} (L : ExtraDegeneracy X) :
    (L.toRightExtraDegeneracyRev).s' = L.s' :=
  rfl

/--
In each degree `n`, the extra map of the reversed right extra degeneracy equals
the given left extra-degeneracy map `s_n`.
-/
@[simp]
theorem toRightExtraDegeneracyRev_s {X : Augmented C} (L : ExtraDegeneracy X) (n : ℕ) :
    (L.toRightExtraDegeneracyRev).s n = L.s n :=
  rfl

end ExtraDegeneracy

end Augmented
end SimplicialObject
end CategoryTheory

end
