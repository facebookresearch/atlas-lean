/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MaximumNimJosephus

/-!
# One-step floor reduction in Maximum Nim

For $k = nt + h$ with $t \ge 1$, $1 \le h \le n$, and $1 \le i \le n$, the pile size $nk - i$
has quotient $n-1$ and nonzero remainder modulo $k$. The flat-rule recurrence identifies the
Grundy values at $nk - i$ and $n(k-1)-i$.

## References

* Shoei Takahashi, Hikaru Manabe and Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
  INTEGERS 24 (2024), Article G5, pp. 1–16, Lemma 5(ii.1). The reduction uses the recurrence
  of Lemma 1(ii), the floor identity of Lemma 2 and the non-divisibility in Lemma 4(i).
* Lionel Levine, *Fractal Sequences and Restricted Nim*, Ars Combinatoria 80 (2006),
  pp. 113–127, Lemma 2.1, the original regular-rule recurrence credited by Lemma 1.
-/

namespace MetaMathlibExt

/-- **Floor-rule Maximum Nim: one-step Grundy reduction when k = nt + h.** Let $n$, $t$, $h$ be
natural numbers with $t \ge 1$ and $1 \le h \le n$, and let $k = nt + h$. Write $G(x)$ for the
Grundy number of a pile of $x$ stones in Maximum Nim with rule function
$f(y) = \lfloor y/k \rfloor$, and let $F(x) = \lfloor (k-1)x/k \rfloor$. Then for every natural
number $i$ with $1 \le i \le n$,
$$G(nk - i) = G(F(nk - i)) = G(n(k - 1) - i).$$

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 5(ii.1) (`integers-2024-G5-lem-5`). -/
public theorem maximumNimGrundy_mul_sub_eq_F_eq_pred (k n t h i : ℕ)
    (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hdecomp : k = n * t + h) (hhn : h ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    maximumNimGrundy (· / k) (n * k - i) =
        maximumNimGrundy (· / k) ((k - 1) * (n * k - i) / k) ∧
      maximumNimGrundy (· / k) ((k - 1) * (n * k - i) / k) =
        maximumNimGrundy (· / k) (n * (k - 1) - i) := by
  let S := n * k - i
  have hn : 1 ≤ n := hi.trans hin
  have hnt : n ≤ n * t := Nat.le_mul_of_pos_right n ht
  have hnk : n < k := by omega
  have hk : 2 ≤ k := by omega
  have hk₀ : 0 < k := by omega
  have hnd : ¬ k ∣ S := by
    simpa only [S, Nat.sub_zero] using
      maximumNim_not_dvd_mul_sub_of_lt k n t h 0 i hh hdecomp hhn ht hi hin
  have hmul : n * (k - 1) + n = n * k := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  have hib : i ≤ n * (k - 1) := hin.trans (Nat.le_mul_of_pos_right n (by omega))
  have hnS : n ≤ S := by dsimp [S]; omega
  have hstep (m : ℕ) (hm : 1 ≤ m) : (m - 1) / k ≤ m / k ∧ m / k ≤ (m - 1) / k + 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_div]
    split <;> omega
  have hflat : S / k = (S - 1) / k := by
    obtain ⟨j, hj⟩ : ∃ j, S = j + 1 := ⟨S - 1, by omega⟩
    rw [hj] at hnd ⊢
    rw [Nat.add_sub_cancel, Nat.succ_div_of_not_dvd hnd]
  have hF := maximumNim_sub_div_sub_one_eq k S hk hnd
  refine ⟨(maximumNimGrundy_eq_sub_rule_succ (· / k) (by simp) hstep S (hn.trans hnS) hflat).trans
    (congrArg (maximumNimGrundy (· / k)) hF), ?_⟩
  -- The quotient of `S` is `n - 1` because `0 < i < k`.
  have hq : S / k = n - 1 := by
    have hbase : (n - 1) * k + k = n * k := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    have hlo : (n - 1) * k ≤ S := by dsimp [S]; omega
    have hhi : S < n * k := by dsimp [S]; omega
    have := (Nat.le_div_iff_mul_le hk₀).2 hlo
    have := (Nat.div_lt_iff_lt_mul hk₀).2 hhi
    omega
  change maximumNimGrundy (· / k) ((k - 1) * S / k) = _
  rw [← hF, hq]
  congr 1
  dsimp [S]
  omega

end MetaMathlibExt
