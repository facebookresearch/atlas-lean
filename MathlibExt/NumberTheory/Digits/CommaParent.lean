/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import MathlibExt.NumberTheory.CommaSequence

/-!
# Parents in the comma-child graph

`MetaMathlibExt.exists_commaParent_of_sq_le` shows that in every base `b ≥ 2`,
each natural number `n ≥ b ^ 2` is a comma-child of a positive integer.
-/

namespace MetaMathlibExt

/-- **Every number at least the square of the base is a comma-child.** Let $b \ge 2$ and
$n \ge b^2$. Then there are a positive integer $k$ and a comma candidate digit $y$ of $k$ in
base $b$ with $n = k + b\,(k \bmod b) + y$, that is, $n$ is a comma-child of $k$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.5 (`fq-2024-sloane05302024-thm-5.5`). -/
public theorem exists_commaParent_of_sq_le (b n : ℕ) (hb : 2 ≤ b) (hn : b ^ 2 ≤ n) :
    ∃ k : ℕ, 0 < k ∧ ∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val := by
  let f := commaMsd b n
  have hf : f < b := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega : 0 < b))).2
    simpa only [Nat.pow_succ'] using Nat.lt_pow_succ_log_self hb n
  let x := (n - f) % b
  have hx : x < b := Nat.mod_lt _ (by omega)
  have hstep : b * x + f < n := calc
    b * x + f < b * x + b := Nat.add_lt_add_left hf _
    _ = b * (x + 1) := (Nat.mul_succ b x).symm
    _ ≤ b * b := Nat.mul_le_mul_left b hx
    _ ≤ n := by simpa only [Nat.pow_two] using hn
  let k := n - f - b * x
  have hsum : k + b * x = n - f := Nat.sub_add_cancel (by omega)
  have hmod : k % b = x := calc
    k % b = (k + b * x) % b := by simp
    _ = x := by rw [hsum]
  have hchild : k + b * (k % b) + f = n := by
    rw [hmod, hsum]
    omega
  refine ⟨k, Nat.sub_pos_of_lt (by omega), ⟨f, hf⟩, ?_, hchild.symm⟩
  change 0 < k + b * (k % b) + f ∧ commaMsd b (k + b * (k % b) + f) = f
  rw [hchild]
  exact ⟨by omega, rfl⟩

end MetaMathlibExt
