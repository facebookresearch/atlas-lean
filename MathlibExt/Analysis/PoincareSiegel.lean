/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ComplexAnalysis/PoincareSiegel.lean` (leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `poincare_siegel_linearisation`:
the definition of `IsDiophantine` and the statement of `poincare_siegel`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
lean-eval ships no `NOTICE` file. ATLAS placed the statements in the namespace below,
revised their documentation, and supplied the proof of the linearisation theorem.
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Poincaré–Siegel linearisation theorem

If `f : ℂ → ℂ` is holomorphic near `0` with `f 0 = 0` and multiplier
`f'(0) = λ = e^{2πiα}` for a Diophantine `α`, then `f` is locally
analytically conjugate to the rotation `z ↦ λ z`: there is a holomorphic
germ `u(z) = z + O(z²)` with `f(u(z)) = u(λ z)` near `0` — an analytic
solution of the Schröder equation.
-/

@[expose] public section

namespace MathlibExt.Analysis.PoincareSiegelWanted.ComplexAnalysis

/-- **Diophantine real numbers.** A real number $\alpha$ is Diophantine if there are real numbers
$C > 0$ and $\tau$ such that $C / |q|^{\tau} \le |\alpha - p/q|$ for all integers $p$ and $q$
with $q \neq 0$.

Any such exponent $\tau$ is at least $2$, by Dirichlet's approximation theorem. A Diophantine
$\alpha$ is irrational, so $e^{2\pi i \alpha}$ is not a root of unity. -/
def IsDiophantine (α : ℝ) : Prop :=
  ∃ C τ : ℝ, 0 < C ∧ ∀ p q : ℤ, q ≠ 0 →
    C / |(q : ℝ)| ^ τ ≤ |α - (p : ℝ) / (q : ℝ)|

noncomputable section

open Finset FormalMultilinearSeries Filter
open scoped Topology NNReal ENNReal

/-! ### Diophantine separation on the unit circle -/

private lemma chord (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1‖ := by
  let t := x - round x
  have hτ : |t| ≤ 1 / 2 := abs_sub_round x
  have e : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    have eq : 2 * Real.pi * Complex.I * (x : ℂ) =
        Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) + (round x : ℂ) * (2 * Real.pi * Complex.I) := by
      dsimp [t]
      push_cast
      ring
    rw [eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have eq : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [eq]
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * t) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [mul_le_mul_of_nonneg_left hτ Real.pi_pos.le])
  rw [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at hs
  change 4 * |t| ≤ _
  norm_num at *
  linarith

private lemma dyadic_denominator_bound {α : ℝ} (hα : IsDiophantine α)
    {l : ℂ} (hl : l = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))) :
    ∃ B : ℝ, 1 < B ∧ ∀ j k : ℕ, 0 < k → k ≤ 2 ^ j →
      2 / B ^ (j + 1) ≤ ‖l ^ k - 1‖ := by
  obtain ⟨C, τ, hC, h⟩ := hα
  obtain ⟨d, hd⟩ := exists_nat_gt τ
  let B : ℝ := max 2 (max (2 ^ d) (1 / C))
  have hB : 1 < B := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left ..)
  refine ⟨B, hB, fun j k hk hkj => ?_⟩
  let x : ℝ := k * α
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkr : (0 : ℝ) < k := by positivity
  have h0 := h (round x) k (by exact_mod_cast hk.ne')
  rw [Int.cast_natCast, abs_of_pos hkr] at h0
  have h1 : C / (k : ℝ) ^ d ≤ |α - (round x : ℝ) / k| := by
    refine le_trans (div_le_div_of_nonneg_left hC.le (Real.rpow_pos_of_pos hkr τ) ?_) h0
    simpa using Real.rpow_le_rpow_of_exponent_le hk1 hd.le
  have h2 : C / (k : ℝ) ^ d ≤ |x - round x| := by
    calc
      _ ≤ |α - (round x : ℝ) / k| := h1
      _ ≤ |α - (round x : ℝ) / k| * k := le_mul_of_one_le_right (abs_nonneg _) hk1
      _ = |x - round x| := by
        rw [← abs_of_pos hkr, ← abs_mul, abs_of_pos hkr, sub_mul, div_mul_cancel₀ _ hkr.ne']
        simp [x, mul_comm]
  have h3 : ‖l ^ k - 1‖ = ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1‖ := by
    rw [hl, ← Complex.exp_nat_mul]
    dsimp [x]
    push_cast
    ring_nf
  rw [h3]
  refine le_trans ?_ (chord x)
  have hpow : (k : ℝ) ^ d ≤ B ^ j := calc
    _ ≤ ((2 : ℝ) ^ j) ^ d := by gcongr; exact_mod_cast hkj
    _ = ((2 : ℝ) ^ d) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ _ := by gcongr; exact (le_max_left ..).trans (le_max_right ..)
  have hBC : 1 ≤ B * C := (div_le_iff₀ hC).mp ((le_max_right ..).trans (le_max_right ..))
  have hkp : 0 < (k : ℝ) ^ d := pow_pos hkr _
  have hB0 := zero_lt_one.trans hB
  have hbound : 1 / B ^ (j + 1) ≤ C / (k : ℝ) ^ d := by
    rw [div_le_div_iff₀ (pow_pos hB0 _) hkp, one_mul, pow_succ]
    calc
      _ ≤ B ^ j := hpow
      _ ≤ B ^ j * (B * C) := le_mul_of_one_le_right (by positivity) hBC
      _ = _ := by ring
  rw [← one_add_one_eq_two (R := ℝ), add_div]
  linarith only [hbound.trans h2, abs_nonneg (x - round x)]

/-- At scale `j` the divisor of degree `n` is small compared with the divisors
with exponents up to `2 ^ j`. -/
private def marked (l : ℂ) (B : ℝ) (j n : ℕ) : Prop :=
  2 ≤ n ∧ ‖l ^ (n - 1) - 1‖ < 1 / B ^ (j + 1)

private instance decidableMarked (l : ℂ) (B : ℝ) (j : ℕ) : DecidablePred (marked l B j) :=
  fun n => inferInstanceAs (Decidable (2 ≤ n ∧ _))

private lemma marked_size {l : ℂ} {B : ℝ} (hB : 1 < B)
    (hlb : ∀ j k : ℕ, 0 < k → k ≤ 2 ^ j → 2 / B ^ (j + 1) ≤ ‖l ^ k - 1‖)
    {j n : ℕ} (hn : marked l B j n) : 2 ^ j ≤ n := by
  by_contra! h
  have h2 := hn.1
  have hle := hlb j (n - 1) (by omega) (by omega)
  have hpos : 0 < 1 / B ^ (j + 1) := by positivity [hB.trans' zero_lt_one]
  rw [← one_add_one_eq_two (R := ℝ), add_div] at hle
  linarith only [hle, hn.2, hpos]

private lemma marked_sep {l : ℂ} {B : ℝ} (hl : ‖l‖ = 1)
    (hlb : ∀ j k : ℕ, 0 < k → k ≤ 2 ^ j → 2 / B ^ (j + 1) ≤ ‖l ^ k - 1‖)
    {j a b : ℕ} (ha : marked l B j a) (hb : marked l B j b) (hab : a < b) :
    a + 2 ^ j ≤ b := by
  by_contra! h
  have he := hlb j (b - a) (by omega) (by omega)
  have ha2 := ha.1
  have hdist : ‖l ^ (b - a) - 1‖ = ‖l ^ (b - 1) - l ^ (a - 1)‖ := by
    rw [← show (b - a) + (a - 1) = b - 1 by omega, pow_add]
    rw [← sub_one_mul, norm_mul, norm_pow, hl, one_pow, mul_one]
  have htri := norm_sub_le_norm_sub_add_norm_sub (l ^ (b - 1)) (1 : ℂ) (l ^ (a - 1))
  rw [norm_sub_rev (1 : ℂ)] at htri
  rw [← one_add_one_eq_two (R := ℝ), add_div] at he
  linarith only [hdist, he, htri, ha.2, hb.2]

/-! ### Counting small divisors in compositions

Fix a scale with separation `D`. Give a marked degree `b` the weight `3b - 2D` and carry
that weight forward until the baseline `3n - 3D` catches up. Separation ensures that at a
marked degree `n` the weight exceeds the sum of the weights of any nontrivial composition
by at least `D`. Thus the weight divided by `D` pays for one small divisor at this scale.
All the subtractions in the weight are in the natural numbers. -/

private def weight (bad : ℕ → Prop) [DecidablePred bad] (D n : ℕ) :=
  max (3 * n - 3 * D) (((range (n + 1)).filter bad).sup fun b => 3 * b - 2 * D)

private lemma weight_le {bad : ℕ → Prop} [DecidablePred bad] {D n : ℕ} :
    weight bad D n ≤ 3 * n - 2 * D := by
  classical
  refine max_le (by omega) (Finset.sup_le ?_)
  intro b hb
  have := mem_range.mp (mem_filter.mp hb).1
  omega

private lemma weight_mono (bad : ℕ → Prop) [DecidablePred bad] (D : ℕ) :
    Monotone (weight bad D) := by
  classical
  intro a b hab
  apply max_le_max (by omega)
  exact Finset.sup_mono (filter_subset_filter _ (range_mono (by omega)))

private lemma weight_marked {bad : ℕ → Prop} [DecidablePred bad] {D n : ℕ} (hn : bad n) :
    3 * n - 2 * D ≤ weight bad D n := by
  classical
  exact (Finset.le_sup (f := fun b => 3 * b - 2 * D)
    (mem_filter.mpr ⟨mem_range.mpr (by omega), hn⟩)).trans (le_max_right ..)

private lemma weight_pair {bad : ℕ → Prop} [DecidablePred bad] {D : ℕ}
    (hsize : ∀ n, bad n → D ≤ n) (hsep : ∀ a b, bad a → bad b → a < b → a + D ≤ b)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    weight bad D a + weight bad D b + (if bad (a + b) then D else 0) ≤ weight bad D (a + b) := by
  classical
  have hA := weight_le (bad := bad) (D := D) (n := a)
  have hB := weight_le (bad := bad) (D := D) (n := b)
  have hbase : 3 * (a + b) - 3 * D ≤ weight bad D (a + b) := le_max_left ..
  split_ifs with hm
  · have hN := weight_marked (D := D) hm
    have hND := hsize _ hm
    have hsmall (m : ℕ) (hlt : m < a + b) : weight bad D m ≤ 3 * (a + b) - 3 * D := by
      refine max_le (by omega) (Finset.sup_le ?_)
      intro k hk
      have hkm := mem_range.mp (mem_filter.mp hk).1
      have := hsep k (a + b) (mem_filter.mp hk).2 hm (by omega)
      omega
    have := hsmall a (by omega)
    have := hsmall b (by omega)
    omega
  · have := weight_mono bad D (show a ≤ a + b by omega)
    have := weight_mono bad D (show b ≤ a + b by omega)
    omega

private lemma weight_blocks {bad : ℕ → Prop} [DecidablePred bad] {D n : ℕ}
    (hsize : ∀ n, bad n → D ≤ n) (hsep : ∀ a b, bad a → bad b → a < b → a + D ≤ b)
    (c : Composition n) (hc : 1 < c.length) :
    (∑ i, weight bad D (c.blocksFun i)) + (if bad n then D else 0) ≤ weight bad D n := by
  classical
  have hadd (a b : ℕ) : weight bad D a + weight bad D b ≤ weight bad D (a + b) := by
    have h0 : weight bad D 0 = 0 := Nat.eq_zero_of_le_zero (weight_le.trans (by simp))
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [h0]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [h0]
    exact (Nat.le_add_right ..).trans (weight_pair hsize hsep ha hb)
  have hsum (s : Finset (Fin c.length)) :
      ∑ i ∈ s, weight bad D (c.blocksFun i) ≤ weight bad D (∑ i ∈ s, c.blocksFun i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [sum_insert ha]
      exact (Nat.add_le_add_left ih _).trans (hadd ..)
  let i : Fin c.length := ⟨0, by omega⟩
  let s := (univ : Finset (Fin c.length)).erase i
  have hs : s.Nonempty := ⟨⟨1, hc⟩, mem_erase.mpr ⟨by simp [i, Fin.ext_iff], mem_univ _⟩⟩
  have h1 := c.one_le_blocksFun i
  have h2 : 0 < ∑ j ∈ s, c.blocksFun j := Finset.sum_pos (fun j _ => c.one_le_blocksFun j) hs
  have he : c.blocksFun i + ∑ j ∈ s, c.blocksFun j = n :=
    (add_sum_erase _ _ (mem_univ i)).trans c.sum_blocksFun
  have hp := weight_pair hsize hsep h1 h2
  rw [he] at hp
  have hrest := hsum s
  rw [← add_sum_erase _ _ (mem_univ i)]
  dsimp [s] at hp hrest
  omega

/-- Sum the normalized weights over dyadic scales. The term `n - 1` accounts for
one additional factor of `B` at each nontrivial composition. -/
private def cost (l : ℂ) (B : ℝ) (N n : ℕ) : ℝ :=
  (↑(n - 1) : ℝ) + ∑ j ∈ range N, (weight (marked l B j) (2 ^ j) n : ℝ) / 2 ^ j

private lemma cost_mono (l : ℂ) (B : ℝ) (n : ℕ) : Monotone (fun N => cost l B N n) := by
  intro A N hAN
  unfold cost
  refine add_le_add_right (sum_le_sum_of_subset_of_nonneg (range_mono hAN) ?_) _
  intros; positivity

private lemma cost_bound (l : ℂ) (B : ℝ) (N n : ℕ) : cost l B N n ≤ 7 * n := by
  unfold cost
  have h (j : ℕ) : (weight (marked l B j) (2 ^ j) n : ℝ) / 2 ^ j ≤
      (3 * n : ℝ) * (1 / 2 : ℝ) ^ j := by
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    gcongr
    exact_mod_cast weight_le.trans (Nat.sub_le ..)
  have hf := (sum_le_sum (s := range N) (fun j _ => h j)).trans_eq (mul_sum ..).symm
  have hg := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (show 0 ≤ 3 * (n : ℝ) by positivity)
  have hn : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  linarith

private lemma weight_controls_divisor {l : ℂ} {B : ℝ} (hB : 1 < B) (hl : ‖l‖ = 1)
    (hlb : ∀ j k : ℕ, 0 < k → k ≤ 2 ^ j → 2 / B ^ (j + 1) ≤ ‖l ^ k - 1‖)
    {n : ℕ} (c : Composition n) (hc : 1 < c.length) :
    ‖(l ^ n - l)⁻¹‖ * (∏ i, B ^ cost l B (c.blocksFun i) (c.blocksFun i)) ≤
      B ^ cost l B n n := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hn2 := hc.trans_le c.length_le
  have hsize := fun j n (h : marked l B j n) => marked_size hB hlb h
  have hsep := fun j a b (ha : marked l B j a) (hb : marked l B j b) => marked_sep hl hlb ha hb
  have hnot : ¬ marked l B n n := fun h => n.lt_two_pow_self.not_ge (hsize n n h)
  have hex : ∃ j, ¬ marked l B j n := ⟨n, hnot⟩
  -- At the first unmarked scale the reciprocal divisor is at most `B ^ (k + 1)`.
  let k := Nat.find hex
  have hkn : k ≤ n := Nat.find_min' hex hnot
  have hnk : ¬ marked l B k n := Nat.find_spec hex
  have hgood : 1 / B ^ (k + 1) ≤ ‖l ^ (n - 1) - 1‖ :=
    le_of_not_gt fun h => hnk ⟨hn2, h⟩
  have hnorm : ‖l ^ n - l‖ = ‖l ^ (n - 1) - 1‖ := by
    rw [← show n - 1 + 1 = n by omega, pow_succ, ← sub_one_mul, norm_mul, hl, mul_one]
    congr 2
  have hd : ‖(l ^ n - l)⁻¹‖ ≤ B ^ (k + 1) := by
    rw [norm_inv, hnorm, inv_le_comm₀ (lt_of_lt_of_le (by positivity) hgood) (by positivity)]
    simpa [one_div] using hgood
  let v (j m : ℕ) : ℝ := (weight (marked l B j) (2 ^ j) m : ℝ) / 2 ^ j
  have hstep (j : ℕ) : (∑ i, v j (c.blocksFun i)) + (if j < k then 1 else 0) ≤ v j n := by
    have hp := weight_blocks (hsize j) (hsep j) c hc
    have small (hj : j < k) : marked l B j n := by
      by_contra h; exact (Nat.find_min hex hj) h
    dsimp [v]
    rw [← sum_div]
    by_cases hj : j < k
    · simp only [small hj, ↓reduceIte] at hp
      simp only [hj, ↓reduceIte]
      apply (le_div_iff₀ (by positivity)).mpr
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
      exact_mod_cast hp
    · simp only [hj, ↓reduceIte, add_zero]
      gcongr
      exact_mod_cast (Nat.le_add_right ..).trans hp
  have hsum := sum_le_sum (s := range n) fun j _ => hstep j
  rw [sum_add_distrib, sum_comm] at hsum
  have hcount : (∑ j ∈ range n, if j < k then (1 : ℝ) else 0) = k := by
    rw [← sum_filter]
    have heq : (range n).filter (· < k) = range k := by
      ext j
      simp
      omega
    simp [heq]
  rw [hcount] at hsum
  have hnat : (∑ i, (c.blocksFun i - 1)) + c.length = n := by
    conv_lhs => rhs; rw [show c.length = ∑ _ : Fin c.length, 1 by simp]
    rw [← sum_add_distrib]
    simpa only [Nat.sub_add_cancel (c.one_le_blocksFun _)] using c.sum_blocksFun
  have hreal : (∑ i, ((c.blocksFun i - 1 : ℕ) : ℝ)) + c.length = n := by exact_mod_cast hnat
  have hN (i) : c.blocksFun i ≤ n := c.blocksFun_le i
  have he : (k + 1 : ℝ) + ∑ i, cost l B (c.blocksFun i) (c.blocksFun i) ≤ cost l B n n := by
    have hm := sum_le_sum (s := univ) fun i _ => cost_mono l B (c.blocksFun i) (hN i)
    refine (add_le_add_right hm _).trans ?_
    unfold cost
    rw [sum_add_distrib, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    dsimp [v] at hsum
    have hc' : 2 ≤ (c.length : ℝ) := by exact_mod_cast hc
    linarith
  calc
    _ ≤ B ^ (k + 1) * ∏ i, B ^ cost l B (c.blocksFun i) (c.blocksFun i) := by gcongr
    _ = B ^ ((k + 1 : ℝ) + ∑ i, cost l B (c.blocksFun i) (c.blocksFun i)) := by
      rw [Real.rpow_add hB0, Real.rpow_sum_of_pos hB0, ← Real.rpow_natCast, Nat.cast_add_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB.le he

/-! ### The formal solution of the Schröder equation and its convergence -/

private def splits (n : ℕ) : Finset (Composition n) :=
  {c : Composition n | 1 < c.length}.toFinset

private lemma block_lt {n} {c : Composition n} (hc : c ∈ splits n) (i : Fin c.length) :
    c.blocksFun i < n := by
  have h : 1 < c.length := Set.mem_toFinset.mp hc
  have hn : 0 < n := by have := c.length_le; omega
  have hs : c ≠ Composition.single n hn :=
    fun eq => h.ne' ((Composition.eq_single_iff_length hn).mp eq)
  exact (Composition.ne_single_iff hn).mp hs i

/-- Solve for the coefficient of degree `n ≥ 2` after moving the linear term to the left. -/
private def linCoeff (a : ℕ → ℂ) (l : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => (l ^ (n + 2) - l)⁻¹ * ∑ c ∈ splits (n + 2), a c.length *
      ∏ i, if _h : c.blocksFun i < n + 2 then linCoeff a l (c.blocksFun i) else 0

private lemma linCoeff_rec (a : ℕ → ℂ) (l : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    linCoeff a l n = (l ^ n - l)⁻¹ * ∑ c ∈ splits n, a c.length *
      ∏ i, linCoeff a l (c.blocksFun i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2, linCoeff]
  congr 1
  refine sum_congr rfl fun c hc => ?_
  simp [block_lt hc]

private def absSeries (a : ℕ → ℂ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ofScalars ℝ (fun n => -‖a n‖)

/-- The coefficients of the inverse of `z - ∑_{k ≥ 2} ‖a k‖ z^k`. Mathlib's `rightInv`
uses the specified inverse linear part and only the higher coefficients of `absSeries`. -/
private def majorant (a : ℕ → ℂ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  (absSeries a).rightInv (ContinuousLinearEquiv.refl ℝ ℝ) 0

private lemma majorant_one (a : ℕ → ℂ) : (majorant a).coeff 1 = 1 := by
  simp [majorant, coeff, rightInv_coeff_one]

private lemma majorant_rec (a : ℕ → ℂ) {n} (hn : 2 ≤ n) :
    (majorant a).coeff n =
      ∑ c ∈ splits n, ‖a c.length‖ * ∏ i, (majorant a).coeff (c.blocksFun i) := by
  conv_lhs => rw [coeff, majorant, rightInv_coeff _ _ _ _ hn]
  change -((∑ c ∈ splits n, (absSeries a).compAlongComposition (majorant a) c)
    (fun _ => 1)) = _
  rw [_root_.sum_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun c _ => ?_
  rw [compAlongComposition_apply, apply_eq_prod_smul_coeff]
  simp [absSeries, applyComposition, apply_eq_prod_smul_coeff, Function.comp_def, mul_comm]

private lemma majorant_nonneg (a : ℕ → ℂ) (n : ℕ) : 0 ≤ (majorant a).coeff n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp [majorant, coeff]
    | 1 => simp [majorant_one]
    | m + 2 =>
      rw [majorant_rec _ (by omega)]
      exact sum_nonneg fun c hc => mul_nonneg (norm_nonneg _)
        (prod_nonneg fun i _ => ih _ (block_lt hc i))

private lemma majorize_coefficients {a : ℕ → ℂ} {l : ℂ} {W : ℕ → ℝ}
    (hW : ∀ n, 0 ≤ W n) (h1 : 1 ≤ W 1)
    (hstep : ∀ {n} (c : Composition n), c ∈ splits n →
      ‖(l ^ n - l)⁻¹‖ * ∏ i, W (c.blocksFun i) ≤ W n) (n : ℕ) :
    ‖linCoeff a l n‖ ≤ W n * (majorant a).coeff n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simpa only [linCoeff, norm_zero] using mul_nonneg (hW 0) (majorant_nonneg a 0)
    | 1 => simpa [linCoeff, majorant_one] using h1
    | m + 2 =>
      rw [linCoeff_rec _ _ (by omega), norm_mul, majorant_rec _ (by omega), mul_sum]
      refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)) ?_
      rw [mul_sum]
      refine sum_le_sum fun c hc => ?_
      rw [norm_mul, norm_prod]
      calc
        _ ≤ ‖(l ^ (m + 2) - l)⁻¹‖ * (‖a c.length‖ *
              ∏ i, (W (c.blocksFun i) * (majorant a).coeff (c.blocksFun i))) := by
          gcongr with i; exact ih _ (block_lt hc _)
        _ = (‖(l ^ (m + 2) - l)⁻¹‖ * ∏ i, W (c.blocksFun i)) *
              (‖a c.length‖ * ∏ i, (majorant a).coeff (c.blocksFun i)) := by
                rw [prod_mul_distrib]
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hstep c hc) (mul_nonneg (norm_nonneg _)
          (prod_nonneg fun i _ => majorant_nonneg _ _))

private lemma conjugacy_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) {l : ℂ}
    (h0 : p.coeff 0 = 0) (h1 : p.coeff 1 = l) (hnr : ∀ n : ℕ, 2 ≤ n → l ^ n - l ≠ 0)
    (n : ℕ) :
    (p.comp (ofScalars ℂ (linCoeff p.coeff l))).coeff n = l ^ n * linCoeff p.coeff l n := by
  let b := linCoeff p.coeff l
  let q := ofScalars ℂ b
  match n with
  | 0 => simpa only [coeff, comp_coeff_zero'', linCoeff, mul_zero] using h0
  | 1 =>
    change (p.comp q) 1 1 = _
    rw [comp_coeff_one]
    simp [q, b, h1, linCoeff]
  | m + 2 =>
    let n := m + 2
    have hlin : (l ^ n - l) * b n = ∑ c ∈ splits n, p.coeff c.length * ∏ i, b (c.blocksFun i) := by
      conv_lhs => rhs; rw [show b n = _ from linCoeff_rec _ _ (by dsimp [n]; omega)]
      rw [← mul_assoc, mul_inv_cancel₀ (hnr n (by omega)), one_mul]
    change (p.comp q) n 1 = l ^ n * b n
    rw [comp_rightInv_aux1 (by omega)]
    have hs : ∑ c ∈ splits n, p c.length (q.applyComposition c 1) =
        ∑ c ∈ splits n, p.coeff c.length * ∏ i, b (c.blocksFun i) := by
      refine sum_congr rfl fun c _ => ?_
      simp [q, applyComposition, Function.comp_def, mul_comm]
    change (∑ c ∈ splits n, _) + _ = _
    rw [hs, ← hlin]
    simp [q, h1]
    ring

private lemma linearizer_radius (p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 0 < p.radius)
    {l : ℂ} {W : ℕ → ℝ} (hW : ∀ n, 0 ≤ W n) (h1 : 1 ≤ W 1)
    (hstep : ∀ {n} (c : Composition n), c ∈ splits n →
      ‖(l ^ n - l)⁻¹‖ * ∏ i, W (c.blocksFun i) ≤ W n)
    {K : ℝ} (hK : 0 < K) (hbound : ∀ n, W n ≤ K ^ n) :
    0 < (ofScalars ℂ (linCoeff p.coeff l)).radius := by
  have habs : 0 < (absSeries p.coeff).radius := hp.trans_le (radius_le_of_le fun n => by
    simp [absSeries])
  have hmaj : 0 < (majorant p.coeff).radius := radius_rightInv_pos_of_radius_pos habs
  obtain ⟨C, r, hC, hr, hgeom⟩ := le_mul_pow_of_radius_pos _ hmaj
  let t : ℝ≥0 := ⟨(K * r)⁻¹, by positivity⟩
  have ht : 0 < t := show (0 : ℝ) < (K * r)⁻¹ by positivity
  refine (ENNReal.coe_pos.mpr ht).trans_le (le_radius_of_bound _ C (r := t) fun n => ?_)
  have hq := majorize_coefficients (a := p.coeff) hW h1 hstep n
  have hR : (majorant p.coeff).coeff n ≤ C * r ^ n := by
    simpa only [norm_apply_eq_norm_coef, Real.norm_of_nonneg (majorant_nonneg _ _)] using hgeom n
  rw [ofScalars_norm]
  calc
    _ ≤ (K ^ n * (C * r ^ n)) * (t : ℝ) ^ n := by
      gcongr; exact hq.trans (mul_le_mul (hbound n) hR (majorant_nonneg ..) (by positivity))
    _ = C := by
      change K ^ n * (C * r ^ n) * ((K * r)⁻¹) ^ n = C
      rw [inv_pow, mul_pow]
      field_simp

/-- **Poincaré–Siegel linearisation theorem.** Let $\alpha$ be a Diophantine real number and let
$\lambda = e^{2\pi i \alpha}$. If $f : \mathbb{C} \to \mathbb{C}$ is analytic at $0$ with
$f(0) = 0$ and $f'(0) = \lambda$, then there is a function $u : \mathbb{C} \to \mathbb{C}$,
analytic at $0$ with $u(0) = 0$ and $u'(0) = 1$, such that $f(u(z)) = u(\lambda z)$ for all $z$
in some neighbourhood of $0$.

Source: C. L. Siegel, *Iteration of analytic functions*, Annals of Math. 43 (1942), 607-612. Earlier
formal-power-series version: H. Poincaré thèse (1879). Listed as §83 (additional statement 1) in O.
Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `poincare_siegel_linearisation`. -/
theorem poincare_siegel
    (α : ℝ) (_hα : IsDiophantine α)
    (lam : ℂ) (_hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))
    (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (_hf0 : f 0 = 0)
    (_hmult : deriv f 0 = lam) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), f (u z) = u (lam * z) := by
  obtain ⟨p, hp⟩ := _hf
  obtain ⟨B, hB, hlb⟩ := dyadic_denominator_bound _hα _hlam
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hl : ‖lam‖ = 1 := by rw [_hlam, Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im]
  -- The factor W bounds all the divisors in the coefficient recursion, leaving the
  -- convergent inverse-series majorant to bound the sum over compositions.
  let W (n : ℕ) := B ^ cost lam B n n
  have hW (n : ℕ) : 0 ≤ W n := Real.rpow_nonneg hB0.le _
  have hW1 : 1 ≤ W 1 := Real.one_le_rpow hB.le (by unfold cost; positivity)
  let q := ofScalars ℂ (linCoeff p.coeff lam)
  have hr : 0 < q.radius := by
    refine linearizer_radius p hp.radius_pos hW hW1
      (fun c hc => weight_controls_divisor hB hl hlb c (Set.mem_toFinset.mp hc))
      (K := B ^ 7) (by positivity) (fun n => ?_)
    calc
      W n ≤ B ^ (7 * (n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hB.le (cost_bound ..)
      _ = (B ^ 7) ^ n := by
        simpa using Real.rpow_natCast_mul hB0.le 7 (n : ℝ)
  have hu := (q.hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  have hu0 : q.sum 0 = 0 := by simpa [q, linCoeff] using (hu.coeff_zero 1).symm
  refine ⟨q.sum, hu.analyticAt, hu0, ?_, ?_⟩
  · simpa [q, linCoeff] using hu.deriv
  have hnr (n : ℕ) (hn : 2 ≤ n) : lam ^ n - lam ≠ 0 := by
    have hlower := hlb n (n - 1) (by omega) (by have := n.lt_two_pow_self; omega)
    have hpos : 0 < 2 / B ^ (n + 1) := by positivity
    have hne : lam ^ (n - 1) - 1 ≠ 0 := norm_pos_iff.mp (hpos.trans_le hlower)
    rw [← show n - 1 + 1 = n by omega, pow_succ, ← sub_one_mul]
    exact mul_ne_zero hne (norm_ne_zero_iff.mp (hl.trans_ne one_ne_zero))
  let L : ℂ →L[ℂ] ℂ := lam • ContinuousLinearMap.id ℂ ℂ
  have hcomp : p.comp q = q.compContinuousLinearMap L := by
    ext n
    rw [apply_eq_prod_smul_coeff, apply_eq_prod_smul_coeff]
    congr 1
    have heq := conjugacy_coeff p (l := lam) ((hp.coeff_zero 1).trans _hf0)
      (hp.deriv.symm.trans _hmult) hnr n
    change (p.comp q).coeff n = q n (L ∘ (1 : Fin n → ℂ))
    simpa [L, q, Function.comp_def] using heq
  have hfcomp : HasFPowerSeriesAt (f ∘ q.sum) (p.comp q) 0 :=
    (show HasFPowerSeriesAt f p (q.sum 0) by rwa [hu0]).comp hu
  have hL : HasFPowerSeriesAt q.sum q (L 0) := by rwa [map_zero]
  rw [hcomp] at hfcomp
  have hrot := hL.compContinuousLinearMap
  filter_upwards [hfcomp.eventually_hasSum_sub, hrot.eventually_hasSum_sub]
    with z hz hz' using hz.unique hz'

end

end MathlibExt.Analysis.PoincareSiegelWanted.ComplexAnalysis
