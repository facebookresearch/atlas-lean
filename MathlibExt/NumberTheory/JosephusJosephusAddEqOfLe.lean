/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

/-!
# Linear growth of the Josephus function before a wrap-around

The theorem `josephus_add_eq_of_le` proves linear growth of the Josephus function
when the final linear value is at most the final circle size.

Source: Yunier Bello-Cruz and Roy
Quintero-Contreras, "Analytical Study and Efficient
Evaluation of the Josephus Function", *Journal of Integer
Sequences* 27 (2024), Article 24.3.8, Lemma 6
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Cruz/cruz4.html>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Linear growth of the Josephus function before a wrap-around.** Let $k \ge 2$, $n \ge 1$
and $m$ be natural numbers, let $J_k$ be the Josephus function and write $p = J_k(n)$. If
$p + km \le n + m$, then $J_k(n + m) = p + km$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 6. -/
public theorem josephus_add_eq_of_le (k n m : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n)
    (h : MetaMathlibExt.josephus k n + k * m ≤ n + m) :
    MetaMathlibExt.josephus k (n + m) =
      MetaMathlibExt.josephus k n + k * m
    := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ] at h
    rw [Nat.add_succ, MetaMathlibExt.josephus_succ k _ hk (by omega), ih (by omega),
      Nat.mul_succ, Nat.mod_eq_of_lt (by omega)]
    omega

end MathlibExt.NumberTheory.JosephusWanted
