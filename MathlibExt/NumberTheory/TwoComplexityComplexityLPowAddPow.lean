/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoComplexity
import MathlibExt.NumberTheory.TwoComplexityMax

/-!
# The complexity of a sum of two powers

The theorem `complexityL_pow_add_pow` computes the complexity of a sum of two positive
powers of the base.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive Integers", *INTEGERS* 24 (2024),
Article A109 (<https://math.colgate.edu/~integers/vol24.html>), Corollary 1.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

private theorem canBuild_mul_pow {l k n : ℕ} (h : CanBuild l k n) (d : ℕ) :
    CanBuild l (k + d) (n * l ^ d) := by
  induction d with
  | zero => simpa using h
  | succ d ih => simpa only [pow_succ, ← mul_assoc, Nat.add_succ] using ih.mul CanBuild.base

/-- **The $l$-complexity of $l^m + l^{m'}$.** Write $\|n\|_l$ for the $l$-complexity of $n$.
For natural numbers $l > 1$ and $m \ge m' \ge 1$, $\|l^m + l^{m'}\|_l = m + 1$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 1. -/
public theorem complexityL_pow_add_pow (l m m' : ℕ)
    (hl : 1 < l) (h : m' ≤ m) (hm' : 1 ≤ m') :
    complexityL l (l ^ m + l ^ m') = m + 1 := by
  have hbuild := canBuild_mul_pow
    ((canBuild_max l (m - m' + 1) hl (by omega)).1.add CanBuild.base) (m' - 1)
  have hb : CanBuild l (m + 1) (l ^ m + l ^ m') := by
    convert hbuild using 1
    · omega
    · rw [add_mul, ← pow_add, ← pow_succ']
      congr 1 <;> congr 1 <;> omega
  apply Nat.le_antisymm (complexityL_min_le hb)
  have hspec := complexityL_spec ⟨m + 1, hb⟩
  have hmax := (canBuild_max l _ hl hspec.one_le).2 _ hspec
  have hpos : 0 < l ^ m' := pow_pos (by omega) _
  have hlt : m < complexityL l (l ^ m + l ^ m') := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by omega : 0 < l)
      (by omega : complexityL l (l ^ m + l ^ m') ≤ m)
    omega
  omega

end MathlibExt.NumberTheory.TwoComplexityWanted
