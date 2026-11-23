/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Round
public import MathlibExt.NumberTheory.FloorCeilingSums
import Mathlib.Data.Nat.Choose.Sum

/-!
# Periodicity of Tverberg's sum

Adding a multiple of the modulus translates the rounded values by the same integer on all
affected subsets. The alternating signs on those subsets sum to zero.
-/

namespace MetaMathlibExt

namespace tverbergSum_periodic

open Finset

-- Taking complements turns the supersets of `s` into the subsets of its nonempty complement.
private theorem sum_sign_mul_ite {ℓ : ℕ} (s : Finset (Fin ℓ)) (hs : s.card < ℓ) (q : ℤ) :
    (∑ T : Finset (Fin ℓ), (-1 : ℤ) ^ (ℓ - T.card) * (if s ⊆ T then q else 0)) = 0 := by
  have hne : sᶜ.Nonempty := card_pos.mp (by simpa [card_compl] using Nat.sub_pos_of_lt hs)
  calc
    _ = ∑ U : Finset (Fin ℓ), if U ∈ sᶜ.powerset then (-1 : ℤ) ^ U.card * q else 0 := by
      refine Fintype.sum_equiv compl_involutive.toPerm _ _ fun T ↦ ?_
      change _ = if Tᶜ ∈ sᶜ.powerset then (-1 : ℤ) ^ Tᶜ.card * q else 0
      simp [card_compl, mul_ite]
    _ = (∑ U ∈ sᶜ.powerset, (-1 : ℤ) ^ U.card) * q := by
      rw [sum_ite_mem_eq, sum_mul]
    _ = 0 := by rw [sum_powerset_neg_one_pow_card_of_nonempty hne, zero_mul]

end tverbergSum_periodic

open tverbergSum_periodic in
/-- **Periodicity of Tverberg's sum.** Let $\ell \ge 2$ and let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. For every index $i$ and every integer $q$, replacing
$a_i$ by $a_i + q m$ does not change $f(a, m, k)$, and $f(a, m, k + q m) = f(a, m, k)$.

The hypothesis $\ell \ge 2$ is needed: for $\ell = 1$, $F = \lfloor \cdot \rfloor$ and $m \ge 1$,
$f((a), m, k) = \lfloor (k + a)/m \rfloor - \lfloor k/m \rfloor$ increases by $q$ when $a$ is
replaced by $a + q m$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 3. -/
public theorem tverbergSum_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) (i : Fin ℓ) (q : ℤ) :
    tverbergSum F (Function.update a i (a i + q * m)) m k = tverbergSum F a m k ∧
      tverbergSum F a m (k + q * m) = tverbergSum F a m k := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have htranslate (x : ℝ) : F (x + q) = F x + q := by
    rcases hF with rfl | rfl | rfl | h
    · exact Int.floor_add_intCast _ _
    · exact Int.ceil_add_intCast _ _
    · exact round_add_intCast _ _
    · obtain rfl := Set.mem_singleton_iff.mp h
      simpa only [add_sub_right_comm] using Int.ceil_add_intCast (x - 1 / 2) q
  have hshift (z : ℤ) : F (((z + q * m : ℤ) : ℝ) / m) = F ((z : ℝ) / m) + q := by
    simpa [Int.cast_add, Int.cast_mul, add_div, Nat.cast_ne_zero.mpr hm] using htranslate (z / m)
  have hupdate (T : Finset (Fin ℓ)) :
      F (((k + ∑ j ∈ T, Function.update a i (a i + q * m) j : ℤ) : ℝ) / m) =
        F (((k + ∑ j ∈ T, a j : ℤ) : ℝ) / m) + if {i} ⊆ T then q else 0 := by
    by_cases hi : i ∈ T
    · rw [Finset.sum_update_of_mem hi, Finset.sum_eq_add_sum_sdiff_singleton_of_mem hi a]
      simp only [Finset.singleton_subset_iff, hi, ite_true]
      simpa only [add_assoc, add_left_comm, add_comm] using
        hshift (k + (a i + ∑ j ∈ T \ {i}, a j))
    · simp [Finset.sum_update_of_notMem hi, hi]
  constructor
  · simp only [tverbergSum, hupdate, mul_add, Finset.sum_add_distrib]
    rw [sum_sign_mul_ite {i} (by simpa using Nat.lt_of_succ_le hℓ) q, add_zero]
  · simp only [tverbergSum, add_right_comm k (q * m), hshift, mul_add, Finset.sum_add_distrib]
    have hzero := sum_sign_mul_ite (∅ : Finset (Fin ℓ)) (by simp; omega) q
    simpa using hzero

end MetaMathlibExt
