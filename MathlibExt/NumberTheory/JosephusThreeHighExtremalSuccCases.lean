/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.JosephusThreeHighExtremalRecurrences

/-!
# Four cases for the next high extremal point of the Josephus function

The parity and survivor deficit of a high extremal point of `J₃` give the position and
survivor deficit of its successor via `josephusThree_highExtremal_succ_cases`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Successive high extremal points of $J_3$.** For every natural number $i$, let $a$ and $b$ be
the $(i+1)$-th and $(i+2)$-th smallest high extremal points of the Josephus function $J_3$, and
put $f = a - J_3(a)$, $f' = b - J_3(b)$ and $r = a \bmod 2$. If $(f, r) = (1, 0)$, then
$2b = 3a + 2$ and $f' = 0$; if $(f, r) = (1, 1)$, then $2b = 3a + 1$ and $f' = 1$; if
$(f, r) = (0, 0)$, then $2b = 3a$ and $f' = 1$; if $(f, r) = (0, 1)$, then $2b = 3a + 1$ and
$f' = 0$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Theorem 1
(`integers-2024-A115-thm-1`). -/
public theorem josephusThree_highExtremal_succ_cases (i : ℕ) :
    let a := Nat.nth IsJosephusThreeHighExtremal i
    let b := Nat.nth IsJosephusThreeHighExtremal (i + 1)
    (a - josephus 3 a = 1 → a % 2 = 0 → 2 * b = 3 * a + 2 ∧ b - josephus 3 b = 0) ∧
    (a - josephus 3 a = 1 → a % 2 = 1 → 2 * b = 3 * a + 1 ∧ b - josephus 3 b = 1) ∧
    (a - josephus 3 a = 0 → a % 2 = 0 → 2 * b = 3 * a ∧ b - josephus 3 b = 1) ∧
    (a - josephus 3 a = 0 → a % 2 = 1 → 2 * b = 3 * a + 1 ∧ b - josephus 3 b = 0) := by
  intro a b
  have hbound (n : ℕ) : josephus 3 n ≤ n := by
    cases n with
    | zero => simp [josephus]
    | succ n => exact (josephus_range 3 (n + 1) (by decide) (Nat.succ_pos n)).2
  have hnext : 2 * (b : ℤ) = 3 * a + 1 + (1 - (a : ℤ) % 2) *
      (2 * ((a : ℤ) - josephus 3 a) - 1) := (josephusThree_highExtremal_recurrences i).1
  have hdefect : (b : ℤ) - josephus 3 b =
      (a : ℤ) - josephus 3 a - (1 - (a : ℤ) % 2) * (2 * ((a : ℤ) - josephus 3 a) - 1) :=
    (josephusThree_highExtremal_recurrences i).2.2.1
  -- The integer differences are casts of the natural defects, with no truncation.
  have hmod : ((a % 2 : ℕ) : ℤ) = (a : ℤ) % 2 := Int.natCast_emod a 2
  rw [← Int.ofNat_sub (hbound a), ← hmod] at hnext hdefect
  rw [← Int.ofNat_sub (hbound b)] at hdefect
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hf hr <;>
    rw [hf, hr] at hnext hdefect <;> constructor <;> omega

end

end MetaMathlibExt
