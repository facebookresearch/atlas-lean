/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Parity
public import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraph
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Normal form of Type 2 exact covering system digraphs

Translation by the first offset gives offsets `0` and `3 * a₁ + a₂`.
Reflection makes the second offset positive when necessary.
-/

namespace MetaMathlibExt

/-- **Normal form of Type 2 exact covering system digraphs.** Let $a_1, a_2 \in \mathbb{Z}$ with
$a_1 - a_2$ odd, and write $G(2n + a_1, -2n + a_2)$ for the exact covering system digraph on
$\mathbb{Z}$ with an edge $m \to n$ exactly when $n = 2m + a_1$ or $n = -2m + a_2$. Then there is
an odd natural number $a$ such that $G(2n + a_1, -2n + a_2)$ is isomorphic as a digraph to
$G(2n, -2n + a)$, the digraph on $\mathbb{Z}$ with an edge $m \to n$ exactly when $n = 2m$ or
$n = -2m + a$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 4
(`integers-2026-A107-thm-4`). -/
public theorem ecsd_type_two_relIso (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) :
    ∃ a : ℕ, Odd a ∧ Nonempty (ecsdAdj ![2, -2] ![a₁, a₂] ≃r ecsdAdj ![2, -2] ![0, (a : ℤ)]) := by
  let b := 3 * a₁ + a₂
  have hb : Odd b := by
    rw [Int.odd_iff] at h ⊢
    dsimp [b]
    omega
  refine ⟨b.natAbs, hb.natAbs, ?_⟩
  by_cases hsign : 0 ≤ b
  · rw [Int.natAbs_of_nonneg hsign]
    refine ⟨⟨Equiv.addRight a₁, ?_⟩⟩
    intro m n
    change ecsdAdj _ _ (m + a₁) (n + a₁) ↔ ecsdAdj _ _ m n
    rw [ecsdAdj_two, ecsdAdj_two]
    dsimp [b]
    omega
  · rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hsign)]
    obtain ⟨e, _⟩ := ecsdAdj_neg_shift_relIso ![2, -2] ![a₁, a₂] a₁
    have offsets : (fun i : Fin 2 => -(![a₁, a₂] i) + (![(2 : ℤ), -2] i - 1) * a₁) =
        ![0, -b] := by
      apply funext
      rw [Fin.forall_fin_two]
      constructor <;> dsimp [b] <;> omega
    exact ⟨offsets ▸ e⟩

end MetaMathlibExt
