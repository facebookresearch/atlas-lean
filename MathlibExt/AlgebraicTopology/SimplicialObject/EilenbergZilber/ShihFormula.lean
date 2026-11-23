/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihIndex

/-!
# The explicit Eilenberg--Mac Lane homotopy formula

We use the displayed formula for `SHI` in R. González-Díaz and P. Real,
"A combinatorial method for computing Steenrod squares",
*J. Pure Appl. Algebra* 139 (1999), 89--108, p. 95
([DOI](https://doi.org/10.1016/S0022-4049(99)00006-7);
[open manuscript, p. 7](https://arxiv.org/abs/math/0110308)).

For the source's input degree `m`, this file writes `n`; the source's
`\bar m = m - p - q` is `ShihIndex.gap`. Its `(p + 1, q)`-shuffle
`(α, β)` is `ShihIndex.shuffle`: `α` is the increasing enumeration of
`shuffle.leftPositions`, and `β` is the increasing enumeration of
`shuffle.rightPositions`. Thus `leftHom` encodes the first-factor operator
indexed by `β`, `rightHom` encodes the second-factor operator indexed by `α`,
and `ShihIndex.sign` is the source coefficient
`(-1)^(\bar m + sig(α, β) + 1)`.

The definitions are category-first: applying an arbitrary simplicial object
and taking the signed tensor gives the degreewise Shih operator, with
naturality formal from functoriality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

def suffixInput {n : ℕ} (i : ShihIndex n) (k : Fin (n + 2))
    (hk : i.gap ≤ k) : Fin (i.p + 1 + i.q + 1) :=
  ⟨k - i.gap, by
    have hi := i.p_add_q_add_gap
    have hk' := k.isLt
    omega⟩

/-- The first-factor simplex operator
`s_(β_q+gap) ... s_(β_1+gap) s_(gap-1) ∂_(n-q+1) ... ∂_n`
in the cited `SHI` formula, where `β` increasingly enumerates
`i.shuffle.rightPositions`. -/
def leftHom {n : ℕ} (i : ShihIndex n) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun k =>
      if hk : k < i.gap then
        ⟨k, by
          have hi := i.p_add_q_add_gap
          omega⟩
      else
        ⟨i.gap - 1 + i.shuffle.leftHom.toOrderHom (i.suffixInput k (by omega)), by
          have hi := i.p_add_q_add_gap
          have hm := i.gap_pos
          have hs :=
            (i.shuffle.leftHom.toOrderHom (i.suffixInput k (by omega))).isLt
          change (i.shuffle.leftHom.toOrderHom
            (i.suffixInput k (by omega))).val < (i.p : ℕ) + 2 at hs
          change i.gap - 1 + (i.shuffle.leftHom.toOrderHom
            (i.suffixInput k (by omega))).val < n + 1
          omega⟩
    monotone' := by
      intro a b hab
      simp only [Fin.le_iff_val_le_val]
      by_cases ha : (a : ℕ) < i.gap
      · by_cases hb : (b : ℕ) < i.gap
        · simp only [ha, hb, ↓reduceDIte]
          exact Fin.le_iff_val_le_val.mp hab
        · simp only [ha, hb, ↓reduceDIte]
          have hm := i.gap_pos
          omega
      · have hb : ¬(b : ℕ) < i.gap := by
          intro hb
          exact ha (lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hab) hb)
        simp only [ha, hb, ↓reduceDIte]
        have hs : i.suffixInput a (by omega) ≤ i.suffixInput b (by omega) := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [suffixInput]
          omega
        exact Nat.add_le_add_left
          (Fin.le_iff_val_le_val.mp (i.shuffle.leftHom.toOrderHom.monotone hs)) _ }

/-- The second-factor simplex operator
`s_(α_(p+1)+gap) ... s_(α_1+gap) ∂_gap ... ∂_(n-q-1)`
in the cited `SHI` formula, where `α` increasingly enumerates
`i.shuffle.leftPositions`. -/
def rightHom {n : ℕ} (i : ShihIndex n) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun k =>
      if hk : k < i.gap then
        ⟨k, by
          have hi := i.p_add_q_add_gap
          omega⟩
      else
        ⟨i.gap + i.p +
            i.shuffle.rightHom.toOrderHom (i.suffixInput k (by omega)), by
          have hi := i.p_add_q_add_gap
          have hs :=
            (i.shuffle.rightHom.toOrderHom (i.suffixInput k (by omega))).isLt
          change (i.shuffle.rightHom.toOrderHom
            (i.suffixInput k (by omega))).val < (i.q : ℕ) + 1 at hs
          change i.gap + (i.p : ℕ) + (i.shuffle.rightHom.toOrderHom
            (i.suffixInput k (by omega))).val < n + 1
          omega⟩
    monotone' := by
      intro a b hab
      simp only [Fin.le_iff_val_le_val]
      by_cases ha : (a : ℕ) < i.gap
      · by_cases hb : (b : ℕ) < i.gap
        · simp only [ha, hb, ↓reduceDIte]
          exact Fin.le_iff_val_le_val.mp hab
        · simp only [ha, hb, ↓reduceDIte]
          omega
      · have hb : ¬(b : ℕ) < i.gap := by
          intro hb
          exact ha (lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hab) hb)
        simp only [ha, hb, ↓reduceDIte]
        have hs : i.suffixInput a (by omega) ≤ i.suffixInput b (by omega) := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [suffixInput]
          omega
        exact Nat.add_le_add_left
          (Fin.le_iff_val_le_val.mp (i.shuffle.rightHom.toOrderHom.monotone hs)) _ }

end ShihIndex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- One signed summand in the explicit Eilenberg--Mac Lane homotopy. -/
def shihSummand (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) :=
  i.sign • (X.map i.leftHom.op ⊗ₘ Y.map i.rightHom.op)

/-- The degree-`n` component of the explicit Eilenberg--Mac Lane homotopy. -/
def shihComponent (X Y : SimplicialObject C) (n : ℕ) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) :=
  ∑ i : ShihIndex n, shihSummand X Y i

@[reassoc]
theorem shihSummand_naturality {X X' Y Y' : SimplicialObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') {n : ℕ} (i : ShihIndex n) :
    shihSummand X Y i ≫
        (f.app (Opposite.op ⦋n + 1⦌) ⊗ₘ g.app (Opposite.op ⦋n + 1⦌)) =
      (f.app (Opposite.op ⦋n⦌) ⊗ₘ g.app (Opposite.op ⦋n⦌)) ≫
        shihSummand X' Y' i := by
  dsimp only [shihSummand]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, f.naturality, g.naturality]

@[reassoc]
theorem shihComponent_naturality {X X' Y Y' : SimplicialObject C}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    shihComponent X Y n ≫
        (f.app (Opposite.op ⦋n + 1⦌) ⊗ₘ g.app (Opposite.op ⦋n + 1⦌)) =
      (f.app (Opposite.op ⦋n⦌) ⊗ₘ g.app (Opposite.op ⦋n⦌)) ≫
        shihComponent X' Y' n := by
  dsimp only [shihComponent]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun i _ => shihSummand_naturality f g i

end AlgebraicTopology.EilenbergZilber
