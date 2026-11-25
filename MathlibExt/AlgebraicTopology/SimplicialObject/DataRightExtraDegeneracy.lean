/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.DataAugmentedRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataExtraDegeneracy

/-!
Right-handed extra degeneracy for augmented simplicial data.

`Augmented.RightExtraDegeneracy` mirrors `Augmented.ExtraDegeneracy` with the
last face `Fin.last` as the distinguished identity and `Fin.castSucc`
commuting face/degeneracy relations. It supplies the data-level input for the
reversal conversions below and the later data-to-genuine transport.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Data
namespace Augmented

variable {C : Type u} [Category.{v} C]

/--
Right-handed extra-degeneracy structure for augmented simplicial data,
mirroring `Data.Augmented.ExtraDegeneracy` with distinguished terminal face
`Fin.last (n + 1)` and nonterminal equations using `Fin.castSucc`.
-/
@[ext]
structure RightExtraDegeneracy (X : Augmented C) where
  /-- A section from the augmentation point to degree zero -/
  s' : X.right ⟶ X.left.obj 0
  /-- Extra degeneracies `X_n ⟶ X_{n+1}` -/
  s : ∀ n : ℕ, X.left.obj n ⟶ X.left.obj (n + 1)
  /-- Section / augmentation identity -/
  s'_comp_ε : s' ≫ X.hom.app 0 = 𝟙 X.right := by cat_disch
  /-- Degree-zero compatibility with face `0` -/
  s₀_comp_δ₀ : s 0 ≫ X.left.δ (0 : Fin 2) = X.hom.app 0 ≫ s' := by cat_disch
  /-- Distinguished terminal-face identity -/
  s_comp_δ_last : ∀ n : ℕ, s n ≫ X.left.δ (Fin.last (n + 1) : Fin (n + 2)) = 𝟙 _ := by cat_disch
  /-- Compatibility with all nonterminal faces -/
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.castSucc = X.left.δ i ≫ s n := by
    cat_disch
  /-- Compatibility with all nonterminal degeneracies -/
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.castSucc = X.left.σ i ≫ s (n + 1) := by
    cat_disch

namespace RightExtraDegeneracy

attribute [reassoc] s₀_comp_δ₀ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ_last

/--
Right extra-degeneracy on `X` gives left `ExtraDegeneracy` on `rev X`,
preserving the underlying `s'` and `s`.
-/
def toExtraDegeneracyRev {X : Augmented C} (R : RightExtraDegeneracy X) :
    ExtraDegeneracy (rev X) where
  s' := R.s'
  s := R.s
  s'_comp_ε := by
    simp only [rev_hom_app]
    exact R.s'_comp_ε
  s₀_comp_δ₁ := by
    have h_rev : (1 : Fin 2).rev = (0 : Fin 2) := by
      have h_eq : (1 : Fin 2) = Fin.last 1 := rfl
      rw [h_eq, Fin.rev_last]
    rw [rev_obj_left_δ, h_rev, rev_hom_app]
    exact R.s₀_comp_δ₀
  s_comp_δ₀ := by
    intro n
    rw [rev_obj_left_δ, Fin.rev_zero]
    exact R.s_comp_δ_last n
  s_comp_δ := by
    intro n i
    rw [rev_obj_left_δ, Fin.rev_succ, rev_obj_left_δ]
    exact R.s_comp_δ n i.rev
  s_comp_σ := by
    intro n i
    rw [rev_obj_left_σ, Fin.rev_succ, rev_obj_left_σ]
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

/--
Left `ExtraDegeneracy` on `X` gives right extra-degeneracy on `rev X`,
preserving the underlying `s'` and `s`.
-/
def toRightExtraDegeneracyRev {X : Augmented C} (L : ExtraDegeneracy X) :
    RightExtraDegeneracy (rev X) where
  s' := L.s'
  s := L.s
  s'_comp_ε := by
    simp only [rev_hom_app]
    exact L.s'_comp_ε
  s₀_comp_δ₀ := by
    rw [rev_obj_left_δ, Fin.rev_zero, rev_hom_app]
    exact L.s₀_comp_δ₁
  s_comp_δ_last := by
    intro n
    rw [rev_obj_left_δ, Fin.rev_last]
    exact L.s_comp_δ₀ n
  s_comp_δ := by
    intro n i
    rw [rev_obj_left_δ, Fin.rev_castSucc, rev_obj_left_δ]
    exact L.s_comp_δ n i.rev
  s_comp_σ := by
    intro n i
    rw [rev_obj_left_σ, Fin.rev_castSucc, rev_obj_left_σ]
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
end Data
end SimplicialObject
end CategoryTheory

end
