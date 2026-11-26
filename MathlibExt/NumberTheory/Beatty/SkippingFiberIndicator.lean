/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Data.Set.Card
import MathlibExt.NumberTheory.Beatty.FloorFiberIndicator
import MathlibExt.NumberTheory.Beatty.SelfBetween
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Multiplicities of Polanco's skipping sequence

The skipping counts are the Beatty sequence of slope `γ = β - 2`. The coordinate
`s = t / (1 - t)` turns `t ↦ 2 - 1 / t` into `s ↦ s - 1`. This identifies Polanco's
iterated slope with the explicit slope `(γ⁻¹ - (k - 1))⁻¹` from the floor-fiber formula.

## References

* Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*, INTEGERS **25**
  (2025), Article A104, pp. 1–19, Theorem 4, Corollary 2 and Lemma 6 (pp. 13–15).
-/

namespace MetaMathlibExt

open Set

/-- In the coordinate `t = s / (s + 1)`, the map `t ↦ 2 - 1 / t` subtracts one from `s`.
The bound on `i` keeps the coordinates and the iterates positive. -/
private theorem iterate_two_sub_one_div (s : ℝ) (i : ℕ) (hi : (i : ℝ) < s) :
    (fun x : ℝ ↦ 2 - 1 / x)^[i] (s / (s + 1)) = (s - i) / (s - i + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.cast_succ] at hi ⊢
    rw [Function.iterate_succ_apply', ih (by linarith)]
    have hnum : 0 < s - i := by linarith
    have hden : 0 < s - i + 1 := by positivity
    have hnext : 0 < s - ((i : ℝ) + 1) + 1 := by linarith
    field_simp [hnum.ne', hden.ne', hnext.ne']
    ring

/-- Casting the positive indices from `ℕ` to `ℤ` preserves the cardinality of a Beatty fiber. -/
private theorem ncard_beattySeq_fiber_eq_nat (γ : ℝ) (m : ℕ) :
    {n : ℤ | 0 < n ∧ beattySeq γ n = (m : ℤ)}.ncard =
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * γ⌋ = (m : ℤ)}.ncard := by
  have himage : (fun n : ℕ ↦ (n : ℤ)) '' {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * γ⌋ = (m : ℤ)} =
      {n : ℤ | 0 < n ∧ beattySeq γ n = (m : ℤ)} := by
    ext n
    constructor
    · rintro ⟨j, ⟨hj, hfloor⟩, rfl⟩
      refine ⟨?_, by simpa only [beattySeq, Int.cast_natCast] using hfloor⟩
      change 0 < (j : ℤ)
      exact_mod_cast hj
    · intro hn
      change 0 < n ∧ _ at hn
      lift n to ℕ using hn.1.le
      refine ⟨n, ⟨?_, by simpa only [beattySeq, Int.cast_natCast] using hn.2⟩, rfl⟩
      exact_mod_cast hn.1
  rw [← himage, ncard_image_of_injective _ Nat.cast_injective]

/-- For a slope greater than one, a positive-index Beatty fiber is either a singleton or empty. -/
private theorem ncard_beattySeq_fiber_eq_indicator {γ : ℝ} (hγ : 1 < γ) (m : ℤ) :
    {n : ℤ | 0 < n ∧ beattySeq γ n = m}.ncard =
      {beattySeq γ j | j > 0}.indicator (1 : ℤ → ℕ) m := by
  have hmono : StrictMono (beattySeq γ) := by
    apply strictMono_int_of_lt_succ
    intro n
    simp only [beattySeq, Int.cast_add, Int.cast_one, add_mul, one_mul]
    rw [← Int.add_one_le_iff, ← Int.floor_add_one]
    exact Int.floor_mono (add_le_add_right hγ.le _)
  by_cases hm : m ∈ {beattySeq γ j | j > 0}
  · rw [indicator_of_mem hm, Pi.one_apply, ncard_eq_one]
    obtain ⟨j, hj, hjm⟩ := hm
    refine ⟨j, ?_⟩
    ext n
    constructor
    · rintro ⟨_, hnm⟩
      exact hmono.injective (hnm.trans hjm.symm)
    · rintro (rfl : n = j)
      exact ⟨hj, hjm⟩
  · rw [indicator_of_notMem hm]
    have hempty : {n : ℤ | 0 < n ∧ beattySeq γ n = m} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro n ⟨hn, hnm⟩
      exact hm ⟨n, hn, hnm⟩
    rw [hempty, ncard_empty]

/-- **Multiplicities of Polanco's skipping sequence.** Let $k \ge 1$ be an integer, let
$\alpha$ be an irrational real number with $(2k - 1)/k < \alpha < (2k + 1)/(k + 1)$, and let
$\beta$ be a real number with $\alpha^{-1} + \beta^{-1} = 1$. Let
$A = \{\lfloor j\alpha \rfloor : j \ge 1\}$ and, for each positive integer $n$, let $c_n$ be
the number of elements of $A$ strictly between $\lfloor n\alpha \rfloor$ and
$\lfloor n\beta \rfloor$. Let $f(x) = 2 - 1/x$, let $f^{k-1}$ be its $(k-1)$-fold iterate, and
let $\delta = -1 + 1/f^{k-1}(\alpha - 1)$, that is,
$\delta = -1 + 1/(2 - 1/(2 - \cdots - 1/(\alpha - 1)))$ with $k - 1$ twos. Then for every
non-negative integer $m$, the number of positive integers $n$ with $c_n = m$ is $k$ if
$m = \lfloor j\delta \rfloor$ for some integer $j \ge 1$, and $k - 1$ otherwise, where an
infinite set is counted as having $0$ elements.

For $k = 1$ this gives $\delta = 1/(\alpha - 1) - 1 = \beta - 2$, and the multiplicity is one
or zero.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 6 (`integers-2025-A104-lem-6`). -/
public theorem beatty_skipping_card_eq_add_indicator {α β : ℝ} {k : ℕ}
    (hirr : Irrational α) (hk : 1 ≤ k) (hk1 : (2 * (k : ℝ) - 1) / k < α)
    (hk2 : α < (2 * (k : ℝ) + 1) / ((k : ℝ) + 1)) (hαβ : α⁻¹ + β⁻¹ = 1) (m : ℕ) :
    {n : ℤ | 0 < n ∧
        (Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α j | j > 0}).ncard = m}.ncard =
      (k - 1) + {beattySeq (-1 + 1 / (fun x : ℝ ↦ 2 - 1 / x)^[k - 1] (α - 1)) j | j > 0}.indicator
        (1 : ℤ → ℕ) m := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hα1 : 1 < α := lt_of_le_of_lt ((le_div_iff₀ hk0).2 (by linarith)) hk1
  have hα2 : α < 2 := hk2.trans ((div_lt_iff₀ hk1R).2 (by linarith))
  have ht : 0 < α - 1 := sub_pos.mpr hα1
  have hc := Real.holderConjugate_iff.mpr ⟨hα1, hαβ⟩
  let γ : ℝ := β - 2
  have hγ : γ = (α - 1)⁻¹ - 1 := by
    dsimp [γ]
    rw [hc.conjugate_eq]
    field_simp [ht.ne']
    ring
  have hγdiv : γ = (2 - α) / (α - 1) := by
    rw [hγ]
    field_simp [ht.ne']
    ring
  have hlo := (div_lt_iff₀ hk0).1 hk1
  have hhi := (lt_div_iff₀ hk1R).1 hk2
  have hγlo : 1 / (k : ℝ) < γ := by
    rw [div_lt_iff₀ hk0, hγdiv, div_mul_eq_mul_div, lt_div_iff₀ ht]
    linarith only [hhi]
  have hγpos : 0 < γ := lt_trans (by positivity) hγlo
  have hfiber : {n : ℤ | 0 < n ∧
        (Ioo (beattySeq α n) (beattySeq β n) ∩ {beattySeq α j | j > 0}).ncard = m} =
      {n : ℤ | 0 < n ∧ beattySeq γ n = (m : ℤ)} := by
    ext n
    apply and_congr_right
    intro hn
    rw [← beatty_card_self_between_eq_floor hirr hα1 hα2 hαβ hn]
    exact_mod_cast Iff.rfl
  rw [hfiber]
  by_cases hk_eq : k = 1
  · have hlarge : 1 < γ := by simpa [hk_eq] using hγlo
    have hslope : -1 + 1 / (α - 1) = γ := by rw [hγ, one_div]; ring
    simpa only [hk_eq, Nat.sub_self, Function.iterate_zero_apply, hslope, zero_add] using
      ncard_beattySeq_fiber_eq_indicator hlarge (m : ℤ)
  have hk_sub_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  have hγhi : γ < 1 / ((k - 1 : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hk_sub_pos, hγdiv, div_mul_eq_mul_div, div_lt_iff₀ ht, hcast]
    linarith only [hlo]
  have hγirr : Irrational γ := by
    have ht_irr : Irrational (α - 1) := by simpa only [Nat.cast_one] using hirr.sub_natCast 1
    rw [hγ]
    simpa only [Nat.cast_one] using ht_irr.inv.sub_natCast 1
  have hγlo' : 1 / (((k - 1 : ℕ) : ℝ) + 1) < γ := by
    rwa [hcast, sub_add_cancel]
  -- In the new coordinate the initial value is `γ⁻¹`, and it stays positive through `k - 1` steps.
  have hcoord : α - 1 = γ⁻¹ / (γ⁻¹ + 1) := by
    calc
      α - 1 = (γ + 1)⁻¹ := by rw [hγ, sub_add_cancel, inv_inv]
      _ = γ⁻¹ / (γ⁻¹ + 1) := by
        field_simp [hγpos.ne', (by positivity : 0 < γ + 1).ne',
          (by positivity : 0 < γ⁻¹ + 1).ne']
        ring
  have hstep : ((k - 1 : ℕ) : ℝ) < γ⁻¹ :=
    (lt_inv_comm₀ hk_sub_pos hγpos).2 (by simpa only [one_div] using hγhi)
  have hslope : -1 + 1 / (fun x : ℝ ↦ 2 - 1 / x)^[k - 1] (α - 1) =
      (γ⁻¹ - ((k - 1 : ℕ) : ℝ))⁻¹ := by
    rw [hcoord, iterate_two_sub_one_div _ _ hstep]
    have hdiff := sub_pos.mpr hstep
    rw [one_div_div, add_div, div_self hdiff.ne', one_div]
    ring
  rw [hslope, ncard_beattySeq_fiber_eq_nat]
  exact (beatty_floor_fiber_card_eq_add_indicator_explicit hγirr hγlo' hγhi).2.2 m

end MetaMathlibExt
