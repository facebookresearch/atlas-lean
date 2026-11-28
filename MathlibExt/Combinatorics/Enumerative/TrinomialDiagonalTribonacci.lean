/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.TrinomialConvolution

/-!
# Diagonal sums of trinomial coefficients

Weight row `m` by `X ^ m`, so degree `d` picks out the diagonal `m + r = d`.
Give the coefficients below the centre sign `+1`, those above it sign `-1`, and the
centre sign `0`. When the row advances, the centre moves by two degrees. Multiplication
by `X + X ^ 2 + X ^ 3` therefore produces a correction only at the new centre and its
neighbors. Reflection cancels the correction at the centre; the neighbors contribute
`X - X ^ 3` times the old central term. This gives Otmani's generating function without
square roots or substitution.
-/

open PowerSeries

namespace MetaMathlibExt

local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "Q" => (x + x ^ 2 + x ^ 3)

private noncomputable def row (m : ℕ) : PowerSeries ℚ := Q ^ m

private theorem coeff_row (m d : ℕ) :
    coeff d (row m) = if m ≤ d then (trinomialCoefficient m (d - m) : ℚ) else 0 := by
  let p : Polynomial ℕ := 1 + Polynomial.X + Polynomial.X ^ 2
  have hp : ((p.map (Nat.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) = 1 + x + x ^ 2 := by
    simp [p]
  rw [row, show Q = (1 + x + x ^ 2) * x by ring, mul_pow, coeff_mul_X_pow', ← hp,
    ← Polynomial.coe_pow, ← Polynomial.map_pow, Polynomial.coeff_coe, Polynomial.coeff_map]
  rfl

private noncomputable def centre (m : ℕ) : PowerSeries ℚ :=
  monomial (2 * m) (trinomialCoefficient m m)

private def rowSign (m d : ℕ) : ℚ :=
  if d < 2 * m then 1 else if 2 * m < d then -1 else 0

private noncomputable def signRow (m : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun d => rowSign m d * coeff d f

@[simp] private theorem coeff_signRow (m d : ℕ) (f : PowerSeries ℚ) :
    coeff d (signRow m f) = rowSign m d * coeff d f := coeff_mk _ _

private theorem signRow_add (m : ℕ) (f g : PowerSeries ℚ) :
    signRow m (f + g) = signRow m f + signRow m g := by
  ext d
  simp [mul_add]

private theorem rowSign_shift_one (m d : ℕ) (h : 1 ≤ d) :
    rowSign (m + 1) d - rowSign m (d - 1) =
      if d = 2 * m + 1 ∨ d = 2 * m + 2 then 1 else 0 := by
  unfold rowSign
  split_ifs <;> first | omega | norm_num

private theorem rowSign_shift_two (m d : ℕ) (h : 2 ≤ d) :
    rowSign (m + 1) d = rowSign m (d - 2) := by
  unfold rowSign
  split_ifs <;> first | omega | rfl

private theorem rowSign_shift_three (m d : ℕ) (h : 3 ≤ d) :
    rowSign (m + 1) d - rowSign m (d - 3) =
      if d = 2 * m + 2 ∨ d = 2 * m + 3 then -1 else 0 := by
  unfold rowSign
  split_ifs <;> first | omega | norm_num

private theorem adjacent_reflection (m : ℕ) :
    (if 3 ≤ 2 * m + 2 then coeff (2 * m + 2 - 3) (row m) else 0) =
      coeff (2 * m + 1) (row m) := by
  cases m with
  | zero => simp [row, coeff_one]
  | succ m =>
    -- Vandermonde convolution against row zero gives reflection of the row.
    have h := sum_trinomialCoefficient_convolution 0 (m + 1) (-(m : ℤ))
    have hterm (k : ℕ) :
        (if 0 ≤ -(m : ℤ) + k then trinomialCoefficient 0 (-(m : ℤ) + k).toNat else 0) =
          if m = k then 1 else 0 := by
      simp only [trinomialCoefficient, pow_zero, Polynomial.coeff_one]
      split_ifs <;> omega
    have hcol : 2 * (↑(m + 1) : ℤ) + -↑m = ↑(m + 2) := by omega
    simp only [hterm, hcol, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Int.natCast_nonneg,
      ite_true, Int.toNat_natCast] at h
    rw [ite_eq_left (by omega), coeff_row, ite_eq_left (by omega), coeff_row,
      ite_eq_left (by omega),
      show 2 * (m + 1) + 2 - 3 - (m + 1) = m by omega,
      show 2 * (m + 1) + 1 - (m + 1) = m + 2 by omega]
    exact_mod_cast (by simpa [show m < 2 * (m + 1) + 1 by omega] using h :
      trinomialCoefficient (m + 1) m = trinomialCoefficient (m + 1) (m + 2))

private theorem coeff_X_mul (f : PowerSeries ℚ) (d : ℕ) :
    coeff d (x * f) = if 1 ≤ d then coeff (d - 1) f else 0 := by
  simpa only [pow_one] using coeff_X_pow_mul' f 1 d

private theorem signRow_shift_one (m : ℕ) :
    signRow (m + 1) (x * row m) - x * signRow m (row m) =
      x * centre m + monomial (2 * m + 2) (coeff (2 * m + 1) (row m)) := by
  ext d
  simp only [map_sub, map_add, coeff_signRow, coeff_X_mul, centre, coeff_monomial]
  by_cases hd : 1 ≤ d
  · simp only [ite_eq_left hd, ← sub_mul, rowSign_shift_one m d hd]
    by_cases h₁ : d = 2 * m + 1
    · subst d
      simp [coeff_row, show 2 * m + 1 - 1 = 2 * m by omega, show m ≤ 2 * m by omega,
        show 2 * m - m = m by omega]
    · by_cases h₂ : d = 2 * m + 2
      · subst d
        simp [show 2 * m + 2 - 1 = 2 * m + 1 by omega]
      · simp [h₁, h₂, show d - 1 ≠ 2 * m by omega]
  · simp [hd, show d ≠ 2 * m + 2 by omega]

private theorem signRow_shift_two (m : ℕ) :
    signRow (m + 1) (x ^ 2 * row m) = x ^ 2 * signRow m (row m) := by
  ext d
  by_cases hd : 2 ≤ d <;> simp [coeff_X_pow_mul', hd, rowSign_shift_two m d]

private theorem signRow_shift_three (m : ℕ) :
    signRow (m + 1) (x ^ 3 * row m) - x ^ 3 * signRow m (row m) =
      -(x ^ 3 * centre m) - monomial (2 * m + 2) (coeff (2 * m + 1) (row m)) := by
  ext d
  simp only [map_sub, map_neg, coeff_signRow, coeff_X_pow_mul', centre, coeff_monomial]
  by_cases h₂ : d = 2 * m + 2
  · subst d
    have h := adjacent_reflection m
    by_cases hd : 3 ≤ 2 * m + 2
    · simp only [ite_eq_left hd] at h
      rw [ite_eq_left hd, ite_eq_left hd, ← sub_mul, rowSign_shift_three m _ hd, h]
      simp [hd, show 2 * m - 1 ≠ 2 * m by omega]
    · simp [hd] at h
      simp [hd, ← h]
  · by_cases hd : 3 ≤ d
    · simp only [ite_eq_left hd, ← sub_mul, rowSign_shift_three m d hd]
      by_cases h₃ : d = 2 * m + 3
      · subst d
        simp [coeff_row, show 2 * m + 3 - 3 = 2 * m by omega, show m ≤ 2 * m by omega,
          show 2 * m - m = m by omega]
      · simp [h₂, h₃, show d - 3 ≠ 2 * m by omega]
    · simp [hd, h₂]

private theorem signRow_row_succ (m : ℕ) :
    signRow (m + 1) (row (m + 1)) = Q * signRow m (row m) + (x - x ^ 3) * centre m := by
  have hrow : row (m + 1) = Q * row m := pow_succ' _ _
  rw [hrow, add_mul, add_mul, signRow_add, signRow_add, signRow_shift_two,
    sub_mul, add_mul, add_mul]
  linear_combination signRow_shift_one m + signRow_shift_three m

-- All series below are locally finite: row `m` has no coefficient below degree `m`.
private noncomputable def sumRows (f : ℕ → PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun d => ∑ m ∈ Finset.range (d + 1), coeff d (f m)

@[simp] private theorem coeff_sumRows (f : ℕ → PowerSeries ℚ) (d : ℕ) :
    coeff d (sumRows f) = ∑ m ∈ Finset.range (d + 1), coeff d (f m) := coeff_mk _ _

private theorem sumRows_succ (f : ℕ → PowerSeries ℚ)
    (hf : ∀ m d, d < m → coeff d (f m) = 0) :
    sumRows f = f 0 + sumRows (fun m => f (m + 1)) := by
  ext d
  simp only [coeff_sumRows, map_add]
  rw [Finset.sum_range_succ', Finset.sum_range_succ (n := d), hf _ _ d.lt_succ_self, add_zero,
    add_comm]

private theorem sumRows_add (f g : ℕ → PowerSeries ℚ) :
    sumRows (fun m => f m + g m) = sumRows f + sumRows g := by
  ext d
  simp [Finset.sum_add_distrib]

private theorem sumRows_sub (f g : ℕ → PowerSeries ℚ) :
    sumRows (fun m => f m - g m) = sumRows f - sumRows g := by
  ext d
  simp [Finset.sum_sub_distrib]

private theorem sumRows_X_pow_mul (j : ℕ) (f : ℕ → PowerSeries ℚ)
    (hf : ∀ m d, d < m → coeff d (f m) = 0) :
    sumRows (fun m => x ^ j * f m) = x ^ j * sumRows f := by
  ext d
  simp only [coeff_sumRows, coeff_X_pow_mul']
  by_cases h : j ≤ d
  · simp only [ite_eq_left h]
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => hf _ _ ?_
    simp only [Finset.mem_range] at hm
    omega
  · simp [h]

private theorem sumRows_mul_Q (f : ℕ → PowerSeries ℚ)
    (hf : ∀ m d, d < m → coeff d (f m) = 0) :
    sumRows (fun m => Q * f m) = Q * sumRows f := by
  simp only [add_mul, sumRows_add, ← sumRows_X_pow_mul 2 f hf, ← sumRows_X_pow_mul 3 f hf]
  rw [← pow_one x, sumRows_X_pow_mul 1 f hf]

private theorem row_supported (m d : ℕ) (h : d < m) : coeff d (row m) = 0 := by
  simp [coeff_row, h.not_ge]

private theorem signRow_supported (m d : ℕ) (h : d < m) :
    coeff d (signRow m (row m)) = 0 := by
  simp [row_supported m d h]

private theorem centre_supported (m d : ℕ) (h : d < m) : coeff d (centre m) = 0 := by
  simp [centre, coeff_monomial, show d ≠ 2 * m by omega]

private noncomputable def tribSeries : PowerSeries ℚ :=
  mk fun d => (tribonacci (d + 2) : ℚ)

@[simp] private theorem coeff_tribSeries (d : ℕ) :
    coeff d tribSeries = (tribonacci (d + 2) : ℚ) := coeff_mk _ _

private theorem tribonacci_rec (n : ℕ) :
    (tribonacci (n + 3) : ℚ) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := by
  exact_mod_cast (show tribonacci (n + 3) = _ from tribonacci.eq_4 n)

private theorem tribSeries_mul : (1 - Q) * tribSeries = 1 := by
  ext d
  simp only [sub_mul, one_mul, add_mul, map_sub, map_add, coeff_X_mul, coeff_X_pow_mul',
    coeff_tribSeries, coeff_one]
  rcases d with _ | _ | _ | d
  · norm_num [tribonacci]
  · norm_num [tribonacci]
  · norm_num [tribonacci]
  · simp only [ite_eq_left (show 1 ≤ d + 3 by omega), ite_eq_left (show 2 ≤ d + 3 by omega),
      ite_eq_left (show 3 ≤ d + 3 by omega), ite_eq_right (show d + 3 ≠ 0 by omega),
      show d + 3 - 1 = d + 2 by omega, show d + 3 - 2 = d + 1 by omega,
      show d + 3 - 3 = d by omega]
    linear_combination tribonacci_rec (d + 2)

private theorem sumRows_row : sumRows row = tribSeries := by
  have h := sumRows_succ row row_supported
  simp only [show row 0 = 1 by simp [row], show ∀ m, row (m + 1) = Q * row m from
    fun m => pow_succ' _ m, sumRows_mul_Q row row_supported] at h
  have hmul : (1 - Q) * sumRows row = 1 := by
    linear_combination h
  calc
    sumRows row = (tribSeries * (1 - Q)) * sumRows row := by
      rw [mul_comm tribSeries, tribSeries_mul, one_mul]
    _ = tribSeries := by rw [mul_assoc, hmul, mul_one]

private theorem sumRows_signed : sumRows (fun m => signRow m (row m)) =
    sumRows centre * ((x - x ^ 3) * tribSeries) := by
  have hzero : signRow 0 (row 0) = 0 := by
    ext d
    cases d <;> simp [rowSign, row, coeff_one]
  have h := sumRows_succ (fun m => signRow m (row m)) signRow_supported
  simp only [hzero, zero_add, signRow_row_succ, sumRows_add, sumRows_mul_Q _ signRow_supported,
    sub_mul, sumRows_sub, sumRows_X_pow_mul 3 centre centre_supported] at h
  have hX : sumRows (fun m => x * centre m) = x * sumRows centre := by
    simpa only [pow_one] using sumRows_X_pow_mul 1 centre centre_supported
  rw [hX] at h
  have hmul : (1 - Q) * sumRows (fun m => signRow m (row m)) = (x - x ^ 3) * sumRows centre := by
    linear_combination h
  calc
    _ = (tribSeries * (1 - Q)) * sumRows (fun m => signRow m (row m)) := by
      rw [mul_comm tribSeries, tribSeries_mul, one_mul]
    _ = _ := by rw [mul_assoc, hmul]; ring

private theorem coeff_central_even (n : ℕ) :
    coeff (2 * n) (sumRows centre) = (trinomialCoefficient n n : ℚ) := by
  rw [coeff_sumRows, Finset.sum_eq_single n]
  · simp [centre]
  · intro k _ hk
    simp [centre, coeff_monomial, show 2 * n ≠ 2 * k by omega]
  · simp [show n < 2 * n + 1 by omega]

private theorem coeff_central_odd (d : ℕ) (h : ¬ 2 ∣ d) : coeff d (sumRows centre) = 0 := by
  rw [coeff_sumRows]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hdk : d ≠ 2 * k := fun e => h ⟨k, e⟩
  simp [centre, coeff_monomial, hdk]

private theorem coeff_correction_even (n : ℕ) :
    coeff (2 * (n + 1)) ((x - x ^ 3) * tribSeries) =
      (tribonacci (2 * (n + 1)) : ℚ) + tribonacci (2 * n) := by
  cases n with
  | zero => norm_num [sub_mul, coeff_X_mul, coeff_X_pow_mul', tribonacci]
  | succ n =>
    change coeff (2 * (n + 1) + 2) ((x - x ^ 3) * tribSeries) = _
    simp only [sub_mul, map_sub, coeff_X_mul, coeff_X_pow_mul',
      ite_eq_left (show 1 ≤ 2 * (n + 1) + 2 by omega),
      ite_eq_left (show 3 ≤ 2 * (n + 1) + 2 by omega), coeff_tribSeries,
      show 2 * (n + 1) + 2 - 1 + 2 = 2 * (n + 1) + 3 by omega,
      show 2 * (n + 1) + 2 - 3 + 2 = 2 * (n + 1) + 1 by omega]
    linear_combination tribonacci_rec (2 * (n + 1))

private theorem coeff_signed_even (n : ℕ) :
    coeff (2 * n) (sumRows (fun m => signRow m (row m))) =
      ∑ k ∈ Finset.range n, (trinomialCoefficient k k : ℚ) *
        ((tribonacci (2 * (n - k)) : ℚ) + tribonacci (2 * (n - 1 - k))) := by
  let f (d : ℕ) := coeff d (sumRows centre) * coeff (2 * n - d) ((x - x ^ 3) * tribSeries)
  let e : ℕ ↪ ℕ := ⟨fun k => 2 * k, fun a b h => by change 2 * a = 2 * b at h; omega⟩
  rw [sumRows_signed, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change ∑ d ∈ Finset.range (2 * n + 1), f d = _
  calc
    _ = ∑ d ∈ (Finset.range n).map e, f d := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro d hd
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hd
        have := Finset.mem_range.mp hk
        exact Finset.mem_range.mpr (by change 2 * k < 2 * n + 1; omega)
      · intro d hd hm
        by_cases hev : 2 ∣ d
        · obtain ⟨k, rfl⟩ := hev
          have hk : k ≤ n := by have := Finset.mem_range.mp hd; omega
          have hkn : k = n := by
            by_contra hne
            exact hm (Finset.mem_map.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩)
          subst k
          simp [f, sub_mul, coeff_X_mul, coeff_X_pow_mul']
        · dsimp only [f]
          rw [coeff_central_odd d hev, zero_mul]
    _ = _ := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn := Finset.mem_range.mp hk
      change coeff (2 * k) (sumRows centre) * coeff (2 * n - 2 * k) ((x - x ^ 3) * tribSeries) = _
      rw [coeff_central_even, show 2 * n - 2 * k = 2 * (n - 1 - k + 1) by omega,
        coeff_correction_even, show n - 1 - k + 1 = n - k by omega]

private theorem two_mul_diagonal (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n + k) (n - k) : ℚ) =
      coeff (2 * n) (sumRows row) + coeff (2 * n) (sumRows centre) +
        coeff (2 * n) (sumRows (fun m => signRow m (row m))) := by
  simp only [coeff_sumRows, ← Finset.sum_add_distrib, coeff_signRow]
  conv_rhs => rw [show 2 * n + 1 = n + (n + 1) by omega, Finset.sum_range_add]
  have hz : (∑ m ∈ Finset.range n,
      (coeff (2 * n) (row m) + coeff (2 * n) (centre m) +
        rowSign m (2 * n) * coeff (2 * n) (row m))) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have := Finset.mem_range.mp hm
    simp [centre, coeff_monomial, rowSign, show ¬ 2 * n < 2 * m by omega,
      show 2 * m < 2 * n by omega, show 2 * n ≠ 2 * m by omega]
  rw [hz, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := Finset.mem_range.mp hk
  rw [coeff_row, ite_eq_left (by omega), show 2 * n - (n + k) = n - k by omega]
  cases k with
  | zero => simp [centre, rowSign, two_mul]
  | succ k =>
    simp only [centre, coeff_monomial, rowSign, two_mul]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), one_mul, add_zero]

/-- **Tribonacci formula for a diagonal sum of trinomial coefficients.**
Write $\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in
$(1 + t + t^2)^n$, and $T_n$ for the Tribonacci numbers, $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$. Then for every $n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \binom{n + k}{n - k}_2 = \frac{T_{2(n+1)}}{2} + \frac{1}{2}\binom{n}{n}_2 +
\frac{1}{2} \sum_{k=0}^{n-1} \binom{k}{k}_2 \left(T_{2(n-k)} + T_{2(n-1-k)}\right).$$

The sequence $(T_{2n})$ is the bisection A099463.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 42 (`jis-2025-25.3.5-cor-42`). -/
public theorem sum_trinomialCoefficient_add_sub_eq_tribonacci (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n + k) (n - k) : ℚ) =
      (tribonacci (2 * (n + 1)) : ℚ) / 2 + (trinomialCoefficient n n : ℚ) / 2 +
        (∑ k ∈ Finset.range n, (trinomialCoefficient k k : ℚ) *
          ((tribonacci (2 * (n - k)) : ℚ) + tribonacci (2 * (n - 1 - k)))) / 2 := by
  have h := two_mul_diagonal n
  rw [sumRows_row, coeff_tribSeries, coeff_central_even, coeff_signed_even,
    show 2 * n + 2 = 2 * (n + 1) by omega] at h
  linear_combination h / 2

end MetaMathlibExt
