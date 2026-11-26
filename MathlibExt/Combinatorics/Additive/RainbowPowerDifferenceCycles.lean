/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Logic.Function.Iterate

/-!
# Cycles in the power digraph

The proof uses the finite self-map argument: two of the first `p + 1` iterates coincide, so the
repeated vertex is periodic. If two forward orbits meet and one starts at a periodic vertex,
continue from the meeting point until that orbit returns to its starting vertex.

## References

* Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and
  Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, pp. 1–16, Lemma 12.
* Caroline Lucheta, Eli Miller and Clifford Reiter, *Digraphs from Powers Modulo p*,
  The Fibonacci Quarterly 34(3) (1996), pp. 226–239, Lemmas 8 and 9.
-/

namespace MetaMathlibExt

/-- **Each component of the power digraph has exactly one cycle.** Let $p$ be a prime and $k$ a
natural number, and let $G^k_p$ be the digraph on $\mathbb{Z}/p\mathbb{Z}$ with edges
$a \to a^k$, so that $m$ steps lead from $a$ to $a^{k^m}$. Call $a$ a cycle vertex if
$a^{k^r} = a$ for some $r > 0$, and say that $a$ and $b$ lie in the same component if
$a^{k^m} = b^{k^n}$ for some $m, n \ge 0$. Then every $a$ has a cycle vertex $a^{k^m}$ among its
iterates, and if two cycle vertices $a$ and $b$ lie in the same component, then $b = a^{k^m}$
for some $m \ge 0$. Thus every component of $G^k_p$ contains exactly one cycle.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 12
(`integers-2024-A105-lem-12`). -/
public theorem powMap_component_unique_cycle (p k : ℕ) [Fact p.Prime] :
    (∀ a : ZMod p, ∃ m : ℕ, ∃ r : ℕ, 0 < r ∧ (a ^ k ^ m) ^ k ^ r = a ^ k ^ m) ∧
      ∀ a b : ZMod p, (∃ r : ℕ, 0 < r ∧ a ^ k ^ r = a) → (∃ r : ℕ, 0 < r ∧ b ^ k ^ r = b) →
        (∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) → ∃ m : ℕ, a ^ k ^ m = b := by
  let f : ZMod p → ZMod p := (· ^ k)
  have hiterate (m : ℕ) (a : ZMod p) : f^[m] a = a ^ k ^ m := by
    induction m with
    | zero => simp only [Function.iterate_zero_apply, pow_zero, pow_one]
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      change (a ^ k ^ m) ^ k = a ^ k ^ (m + 1)
      rw [pow_succ k m, pow_mul]
  simp only [← hiterate]
  constructor
  · intro a
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    -- Among the first `p + 1` iterates at least two have the same value.
    obtain ⟨i, j, hne, hij⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (p + 1) ↦ f^[i.val] a)
      (by simpa only [Fintype.card_fin, ZMod.card] using Nat.lt_succ_self p)
    obtain ⟨m, n, hmn, h⟩ : ∃ m n : ℕ, m < n ∧ f^[m] a = f^[n] a := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨i.val, j.val, hlt, hij⟩
      · exact ⟨j.val, i.val, hgt, hij.symm⟩
    refine ⟨m, n - m, Nat.sub_pos_of_lt hmn, ?_⟩
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hmn.le, eq_comm]
  · rintro a b - ⟨r, hr, hperiod⟩ ⟨m, n, h⟩
    -- Extend the common iterate to a multiple of `b`'s period on its orbit.
    let t := r - n % r
    have ht : t + n = r * (n / r + 1) := by
      have hmod := Nat.mod_lt n hr
      have hdiv := Nat.mod_add_div n r
      rw [Nat.mul_succ]
      dsimp [t]
      omega
    have hb : f^[t + n] b = b := by
      rw [ht]
      exact (show Function.IsPeriodicPt f r b from hperiod).mul_const _
    refine ⟨t + m, ?_⟩
    rw [Function.iterate_add_apply, h, ← Function.iterate_add_apply, hb]

end MetaMathlibExt
