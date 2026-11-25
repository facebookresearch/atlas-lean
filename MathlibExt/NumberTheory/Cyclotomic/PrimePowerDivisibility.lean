/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.Cyclotomic.PrimeDivisorCongruence

/-! # A cyclotomic divisibility criterion for prime powers -/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

-- The induction works without coprimality; retain the source's named hypothesis.
set_option linter.unusedVariables false in
/-- **Divisibility of $x^{rp^a} - 1$ by $p$.** Let $p$ be a prime, let $r$ and $a$ be natural
numbers with $r$ coprime to $p$, let $x$ be a positive integer, and let $\Phi_p$ be the $p$-th
cyclotomic polynomial with integer coefficients. Then $p \mid x^{rp^a} - 1$ if and only if
$p \mid x^r - 1$ and $p \mid \Phi_p(x^{rp^{i-1}})$ for every $i \in \{1, \dots, a\}$.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Lemma 4 (`integers-2026-A95-lem-4`). -/
public theorem prime_dvd_pow_sub_one_iff_cyclotomic {p r a : ℕ} (hp : p.Prime)
    (hr : r.Coprime p) {x : ℤ} (hx : 0 < x) :
    (p : ℤ) ∣ x ^ (r * p ^ a) - 1 ↔
      (p : ℤ) ∣ x ^ r - 1 ∧
        ∀ i ∈ Finset.Icc 1 a, (p : ℤ) ∣ (cyclotomic p ℤ).eval (x ^ (r * p ^ (i - 1))) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hpow : x ^ (r * p ^ (a + 1)) = (x ^ (r * p ^ a)) ^ p := by
      rw [pow_succ p a, ← Nat.mul_assoc, pow_mul]
    have hstep := prime_dvd_pow_self_sub_one_iff hp (pow_pos hx (r * p ^ a))
    rw [hpow, hstep, ih]
    constructor
    · rintro ⟨⟨hbase, hprev⟩, hlast⟩
      refine ⟨hbase, fun i hi => ?_⟩
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      by_cases hia : i ≤ a
      · exact hprev i (Finset.mem_Icc.mpr ⟨hlo, hia⟩)
      · have hi' : i = a + 1 := by omega
        simpa only [hi', Nat.add_sub_cancel] using hlast
    · rintro ⟨hbase, hall⟩
      refine ⟨⟨hbase, fun i hi => hall i ?_⟩, ?_⟩
      · obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨hlo, hhi.trans (Nat.le_succ a)⟩
      · simpa only [Nat.add_sub_cancel] using
          hall (a + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos a, le_rfl⟩)

end

end MetaMathlibExt
