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
# Normal form of Type 1 exact covering system digraphs

Translation by the first offset gives offsets `0` and `a₂ - a₁`.
Reflection gives offsets `0` and `a₁ - a₂` when `a₁ - a₂` is negative.

Statements from Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and
Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107.
-/

namespace MetaMathlibExt

/-- **Normal form of the ECSDs $G(2n + a_1, 2n + a_2)$.** For all integers $a_1, a_2$ with
$a_1 - a_2$ odd, the exact covering system digraph $G(2n + a_1, 2n + a_2)$, with an edge
$m \to 2m + a_1$ and an edge $m \to 2m + a_2$ for every integer $m$, is isomorphic as a digraph
to $G(2n, 2n - a)$ for some odd natural number $a$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 3
(`integers-2026-A107-thm-3`). -/
public theorem ecsd_type_one_relIso (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) :
    ∃ a : ℕ, Odd a ∧ Nonempty (ecsdAdj ![2, 2] ![a₁, a₂] ≃r ecsdAdj ![2, 2] ![0, -(a : ℤ)]) := by
  refine ⟨(a₁ - a₂).natAbs, h.natAbs, ?_⟩
  by_cases hsign : 0 ≤ a₁ - a₂
  · rw [Int.natAbs_of_nonneg hsign]
    refine ⟨⟨Equiv.addRight a₁, ?_⟩⟩
    intro m n
    change ecsdAdj _ _ (m + a₁) (n + a₁) ↔ ecsdAdj _ _ m n
    rw [ecsdAdj_two, ecsdAdj_two]
    omega
  · have hb : ((a₁ - a₂).natAbs : ℤ) = -(a₁ - a₂) :=
      Int.ofNat_natAbs_of_nonpos (le_of_not_ge hsign)
    obtain ⟨e, _⟩ := ecsdAdj_neg_shift_relIso ![2, 2] ![a₁, a₂] a₁
    have offsets : (fun i : Fin 2 => -(![a₁, a₂] i) + (![(2 : ℤ), 2] i - 1) * a₁) =
        ![0, -(((a₁ - a₂).natAbs : ℕ) : ℤ)] := by
      apply funext
      rw [Fin.forall_fin_two]
      constructor <;> dsimp <;> omega
    exact ⟨offsets ▸ e⟩

end MetaMathlibExt
