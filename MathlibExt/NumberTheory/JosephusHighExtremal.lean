/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

/-!
# Linear growth of the Josephus function after a high extremal point

The theorem `josephus_add_eq_of_high` shows that, starting at the successor of a
high extremal point, the Josephus function increases by the step size at each
step up to an explicit bound.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Low extremal point of the Josephus function.** For natural numbers $k$ and $m$, the point
$m$ is a low extremal point of the Josephus function $J_k$ if $1 \le J_k(m) \le k - 1$, where
$k - 1$ is truncated at $0$. -/
def IsLowExtremal (k m : ℕ) : Prop :=
  1 ≤ MetaMathlibExt.josephus k m ∧
    MetaMathlibExt.josephus k m ≤ k - 1

/-- **High extremal point of the Josephus function.** For natural numbers $k$ and $m$, the point
$m$ is a high extremal point of the Josephus function $J_k$ if $m + 1$ is a low extremal point
of $J_k$, that is, if $1 \le J_k(m + 1) \le k - 1$. -/
def IsHighExtremal (k m : ℕ) : Prop := IsLowExtremal k (m + 1)

/-- **Linear growth of the Josephus function after a high extremal point.** Let $k \ge 2$ and
$n_e \ge 2k - 3$ be natural numbers such that $n_e$ is a high extremal point of the Josephus
function $J_k$, that is, $1 \le J_k(n_e + 1) \le k - 1$, and write $j = J_k(n_e + 1)$. Then
$J_k(n_e + 1 + m) = j + km$ for every natural number
$m \le \lfloor (n_e - (j - 1)) / (k - 1) \rfloor$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 9. -/
theorem josephus_add_eq_of_high (k ne m : ℕ)
    (hk : 2 ≤ k) (hne : 2 * k - 3 ≤ ne)
    (hhigh : IsHighExtremal k ne)
    (hm : m ≤ (ne - (MetaMathlibExt.josephus k (ne + 1) - 1)) / (k - 1)) :
    MetaMathlibExt.josephus k (ne + 1 + m) =
      MetaMathlibExt.josephus k (ne + 1) + k * m := by
  obtain ⟨hj_pos, hj_le⟩ := hhigh
  induction m with
  | zero => simp
  | succ m ih =>
    -- The floor bound ensures that adding k once more stays within the new circle.
    have hstep := (Nat.le_div_iff_mul_le (by omega : 0 < k - 1)).mp hm
    rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm (m + 1) k, Nat.mul_succ] at hstep
    rw [Nat.add_succ, MetaMathlibExt.josephus_succ k _ hk (by omega), ih (by omega),
      Nat.mul_succ, Nat.mod_eq_of_lt (by omega)]
    omega

end MathlibExt.NumberTheory.JosephusWanted
