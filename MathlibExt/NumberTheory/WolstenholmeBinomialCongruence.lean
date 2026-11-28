/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Binomial congruences for prime multiples

`MetaMathlibExt.ringChoose_mul_prime_sub_congr_sum_d` bounds the valuation of the remainder
for a prime `p`, natural numbers `m, k` with `m + 1 < p`, and an integer `n`, after truncating
the binomial expansion of `choose (n * p) (k * p)` at order `m`. The proof factors `(1 + X)^p`
as `(1 + X^p)(1 + u)` in the integer power series ring, where `u` is divisible by both `p` and `X`.

`MetaMathlibExt.ringChoose_mul_prime_sub_congr_pow_four` takes `p ≥ 7` prime, `k` natural, and `n`
an integer. It computes the first three differences explicitly using Vandermonde's identity and
Pascal's recurrence. The remainder vanishes if $\binom{n}{4} = 0$ and otherwise is divisible by
$p^{4+v_p(\binom{n}{4})}$. This specializes Kehila's Proposition 3 from $p$-adic integers to
ordinary integers and takes the truncation directly from Theorem 3.

## References

* Walid Kehila, *An Extension of Wolstenholme’s Theorem by Binomial Coefficients*,
  INTEGERS 26 (2026), Article A32, pp. 1–28, Theorem 3 and Proposition 3 (equation (8), p. 16).
-/

namespace MetaMathlibExt

open PowerSeries Finset

namespace ringChoose_mul_prime_sub_congr_sum_d

-- The integer power (1 + X^p)^n.
private noncomputable abbrev base (p : ℕ) (hp : p ≠ 0) (n : ℤ) : ℤ⟦X⟧ :=
  expand p hp (binomialSeries ℤ n)

private lemma base_add {p : ℕ} {hp : p ≠ 0} (x y : ℤ) :
    base p hp (x + y) = base p hp x * base p hp y := by simp [base]

private lemma base_one {p : ℕ} {hp : p ≠ 0} : base p hp 1 = 1 + X ^ p := by
  simpa [base] using congrArg (expand p hp (R := ℤ))
    (binomialSeries_nat (R := ℤ) (A := ℤ) 1)

-- The ratio of (1 + X)^p to 1 + X^p differs from 1 by a multiple of pX.
private lemma exists_increment (p : ℕ) (hp : p.Prime) :
    ∃ w : ℤ⟦X⟧, base p hp.ne_zero 1 * (1 + (p : ℤ⟦X⟧) * X * w) = (1 + X) ^ p := by
  obtain ⟨v, hv⟩ := exists_add_pow_prime_eq hp (1 : ℤ⟦X⟧) X
  refine ⟨v * base p hp.ne_zero (-1), ?_⟩
  have hunit : base p hp.ne_zero 1 * base p hp.ne_zero (-1) = 1 := by
    rw [← base_add]
    simp [base]
  rw [hv, one_pow, mul_one, mul_add, mul_one]
  rw [show base p hp.ne_zero 1 * ((p : ℤ⟦X⟧) * X * (v * base p hp.ne_zero (-1))) =
      (p : ℤ⟦X⟧) * X * v * (base p hp.ne_zero 1 * base p hp.ne_zero (-1)) by ring,
    hunit, mul_one, base_one]

-- Multiplicativity in the integer exponent extends the identity at 1 to negative exponents.
private lemma series_factorization {p : ℕ} {hp : p ≠ 0} {u : ℤ⟦X⟧} (hu : HasSubst u)
    (h : base p hp 1 * (1 + u) = (1 + X) ^ p) (n : ℤ) :
    binomialSeries ℤ (n * p) = base p hp n * subst u (binomialSeries ℤ n) := by
  let f : ℤ →+ Additive (ℤ⟦X⟧) :=
    { toFun := fun z => .ofMul (binomialSeries ℤ (z * p))
      map_zero' := by change binomialSeries ℤ (0 * (p : ℤ)) = 1; simp
      map_add' := fun x y => by
        change binomialSeries ℤ ((x + y) * p) = _
        rw [add_mul, binomialSeries_add]; rfl }
  let g : ℤ →+ Additive (ℤ⟦X⟧) :=
    { toFun := fun z => .ofMul (base p hp z * subst u (binomialSeries ℤ z))
      map_zero' := by
        change base p hp 0 * subst u (binomialSeries ℤ (0 : ℤ)) = 1
        simp [base, ← coe_substAlgHom hu]
      map_add' := fun x y => by
        change base p hp (x + y) * subst u (binomialSeries ℤ (x + y)) =
          (base p hp x * _) * (base p hp y * _)
        rw [base_add, binomialSeries_add, subst_mul hu]
        ring }
  have he : f = g := by
    apply AddMonoidHom.ext_int
    change binomialSeries ℤ (1 * (p : ℤ)) = base p hp 1 * subst u (binomialSeries ℤ (1 : ℤ))
    rw [one_mul, binomialSeries_nat, ← Nat.cast_one (R := ℤ), binomialSeries_nat,
      pow_one, ← coe_substAlgHom hu, map_add, map_one, substAlgHom_X]
    exact h.symm
  exact congrArg Additive.toMul (DFunLike.congr_fun he n)

private lemma mixed_power {p : ℕ} {hp : p ≠ 0} {u : ℤ⟦X⟧} (hu : HasSubst u)
    (h : base p hp 1 * (1 + u) = (1 + X) ^ p) (n : ℤ) (j : ℕ) :
    base p hp n * (1 + u) ^ j = binomialSeries ℤ (↑(j * p) : ℤ) * base p hp (n - j) := by
  rw [Nat.cast_mul, series_factorization hu h, binomialSeries_nat, subst_pow hu,
    ← coe_substAlgHom hu, map_add, map_one, substAlgHom_X]
  rw [mul_right_comm, ← base_add]
  simp

-- Read a coefficient of a substituted series after truncating above degree N.
private lemma coeff_mul_subst {u : ℤ⟦X⟧} (hu : constantCoeff u = 0)
    (a f : ℤ⟦X⟧) (N t : ℕ) (ht : N < t) :
    coeff N (a * subst u f) =
      ∑ l ∈ range t, coeff l f * coeff N (a * u ^ l) := by
  let S := substAlgHom (R := ℤ) (HasSubst.of_constantCoeff_zero' hu)
  have hX : S X = u := substAlgHom_X _
  have htr : S (f.trunc t : ℤ⟦X⟧) = ∑ l ∈ range t, C (coeff l f) * u ^ l := by
    rw [show S (f.trunc t : ℤ⟦X⟧) = Polynomial.aeval u (f.trunc t) from substAlgHom_coe _ _]
    exact eval₂_trunc_eq_sum_range u _ t f
  have hd : X ^ t ∣ u ^ t := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hu) _
  have hz (v : ℤ⟦X⟧) : coeff N (a * (u ^ t * v)) = 0 :=
    X_pow_dvd_iff.mp (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _) _ ht
  rw [← coe_substAlgHom (HasSubst.of_constantCoeff_zero' hu)]
  change coeff N (a * S f) = _
  conv_lhs => rw [eq_X_pow_mul_shift_add_trunc t f, map_add S, map_mul S, map_pow S, hX, mul_add,
    map_add, hz, zero_add, htr, Finset.mul_sum, map_sum]
  apply sum_congr rfl
  intro l _
  rw [mul_left_comm, coeff_C_mul]

-- Only multiples of p contribute to this convolution, and the first factor has degree jp.
private lemma mixed_coeff (p : ℕ) (hp : p ≠ 0) (j k : ℕ) (z : ℤ) :
    coeff (k * p) (binomialSeries ℤ (↑(j * p) : ℤ) * base p hp z) =
      ∑ s ∈ range (j + 1), if s ≤ k then
        Ring.choose (↑(j * p) : ℤ) (s * p) * Ring.choose z (k - s) else 0 := by
  let f (i : ℕ) := Ring.choose (↑(j * p) : ℤ) i * coeff (k * p - i) (base p hp z)
  let g (s : ℕ) := Ring.choose (↑(j * p) : ℤ) (s * p) * Ring.choose z (k - s)
  have hfg (s : ℕ) : f (s * p) = g s := by
    simp only [f, g, ← Nat.mul_sub_right_distrib, base, mul_comm (k - s) p, coeff_expand_mul,
      binomialSeries_coeff, zsmul_eq_mul, mul_one, Int.cast_id]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [binomialSeries_coeff, zsmul_eq_mul, mul_one, Int.cast_id]
  change ∑ i ∈ range (k * p + 1), f i = _
  calc
    _ = ∑ s ∈ range (min j k + 1), g s := by
      symm
      apply sum_of_injOn (fun s => s * p) (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_right hp.bot_lt h)
      · intro s hs
        simp only [coe_range, Set.mem_Iio] at hs ⊢
        exact Nat.lt_succ_of_le (Nat.mul_le_mul_right p (by omega))
      · intro i hi hmiss
        have hle : i ≤ k * p := Nat.le_of_lt_succ (mem_range.mp hi)
        by_cases hdiv : p ∣ i
        · obtain ⟨s, rfl⟩ := hdiv
          have hsk : s ≤ k := Nat.le_of_mul_le_mul_right
            (show s * p ≤ k * p by rwa [mul_comm s p]) hp.bot_lt
          have hjs : j < s := by
            by_contra! h
            exact hmiss ⟨s, mem_range.mpr (by omega), mul_comm ..⟩
          have hlt : j * p < p * s := by
            rw [mul_comm p s]
            exact Nat.mul_lt_mul_of_pos_right hjs hp.bot_lt
          simp only [f, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
        · have hd := (Nat.dvd_sub_iff_right hle (dvd_mul_left p k)).not.mpr hdiv
          simp [f, base, coeff_expand_of_not_dvd _ _ _ hd]
      · intro s _
        exact (hfg s).symm
    _ = ∑ s ∈ range (min j k + 1), (if s ≤ k then g s else 0) := by
      apply sum_congr rfl
      intro s hs
      rw [ite_eq_left (show s ≤ k by have := mem_range.mp hs; omega)]
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro s hs hn
      have := mem_range.mp hs
      have := mt mem_range.mpr hn
      rw [ite_eq_right (by omega)]

private lemma difference_coeff (a u : ℤ⟦X⟧) (N l : ℕ) :
    coeff N (a * u ^ l) = ∑ j ∈ range (l + 1),
      (-1 : ℤ) ^ (l - j) * (l.choose j : ℤ) * coeff N (a * (1 + u) ^ j) := by
  have he : u = (1 + u) + (-1) := by ring
  conv_lhs => rw [congrArg (· ^ l) he, add_pow, Finset.mul_sum, map_sum]
  apply sum_congr rfl
  intro j _
  rw [show a * ((1 + u) ^ j * (-1) ^ (l - j) * l.choose j) =
      (((-1 : ℤ) ^ (l - j) * (l.choose j : ℤ) : ℤ) : ℤ⟦X⟧) * (a * (1 + u) ^ j) by
    push_cast; ring, coeff_intCast_mul, Int.cast_id]

-- The denominator arising from choosing r elements out of l costs at most l - r powers of p.
private lemma choose_valuation_le {p r l : ℕ} (hp : p.Prime) (hr : r < p) (hl : r ≤ l) :
    multiplicity p (l.choose r) ≤ l - r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [Nat.add_sub_cancel_left, ← Nat.factorization_def _ hp]
  apply Nat.factorization_choose_le_log.trans
  apply Nat.le_of_lt_succ
  apply Nat.log_lt_of_lt_pow' (Nat.succ_ne_zero _)
  clear hl
  induction t with
  | zero => simpa using hr
  | succ t ih =>
    change r + t < p ^ (t + 1) at ih
    have hpos := pow_pos hp.pos (t + 1)
    rw [pow_succ p (t + 1)]
    have := Nat.mul_le_mul_left (p ^ (t + 1)) hp.two_le
    omega

private lemma tail_term (p r l : ℕ) (hp : p.Prime) (hr : r < p) (hl : r ≤ l) (n b : ℤ) :
    let a : ℚ := (Ring.choose n r : ℤ)
    let q : ℚ := ((Ring.choose n l : ℤ) : ℚ) * ((p : ℚ) ^ l * b)
    q = 0 ∨ (a ≠ 0 ∧ (r : ℤ) + padicValRat p a ≤ padicValRat p q) := by
  dsimp only
  let : Fact p.Prime := ⟨hp⟩
  by_cases h : ((Ring.choose n l : ℤ) : ℚ) * ((p : ℚ) ^ l * b) = 0
  · exact Or.inl h
  obtain ⟨hL, hprod⟩ := mul_ne_zero_iff.mp h
  obtain ⟨hpow, hb⟩ := mul_ne_zero_iff.mp hprod
  have hc : (l.choose r : ℚ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hl
  have hchoose : (l.choose r : ℚ) * ((Ring.choose n l : ℤ) : ℚ) =
      ((Ring.choose n r : ℤ) : ℚ) * ((Ring.choose (n - r) (l - r) : ℤ) : ℚ) := by
    exact_mod_cast (show (l.choose r : ℤ) * Ring.choose n l = _ by
      simpa only [nsmul_eq_mul] using Ring.choose_smul_choose n hl)
  have ⟨ha, hd⟩ := mul_ne_zero_iff.mp (hchoose ▸ mul_ne_zero hc hL)
  refine Or.inr ⟨ha, ?_⟩
  have hv := congrArg (padicValRat p) hchoose
  rw [padicValRat.mul hc hL, padicValRat.mul ha hd, padicValRat.of_nat] at hv
  rw [padicValRat.mul hL hprod, padicValRat.mul hpow hb, padicValRat.pow,
    padicValRat.self hp.one_lt, mul_one]
  have hbound := choose_valuation_le hp hr hl
  rw [padicValRat.of_int (z := Ring.choose (n - r) (l - r))] at hv
  rw [padicValRat.of_int (z := b)]
  omega

private lemma sum_tail (p r : ℕ) (hp : p.Prime) (hr : r < p) (n : ℤ) (s : Finset ℕ)
    (hs : ∀ l ∈ s, r ≤ l) (b : ℕ → ℤ) :
    let a : ℚ := (Ring.choose n r : ℤ)
    let q := ∑ l ∈ s, ((Ring.choose n l : ℤ) : ℚ) * ((p : ℚ) ^ l * b l)
    q = 0 ∨ (a ≠ 0 ∧ (r : ℤ) + padicValRat p a ≤ padicValRat p q) := by
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  apply sum_induction _ (fun q : ℚ => q = 0 ∨ (((Ring.choose n r : ℤ) : ℚ) ≠ 0 ∧
    (r : ℤ) + padicValRat p (↑(Ring.choose n r) : ℚ) ≤ padicValRat p q))
  · intro x y hx hy
    rcases hx with rfl | ⟨ha, hx⟩
    · simpa using hy
    rcases hy with rfl | ⟨_, hy⟩
    · rw [add_zero]; exact Or.inr ⟨ha, hx⟩
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    exact Or.inr ⟨ha, (le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy)⟩
  · exact Or.inl rfl
  · exact fun l hl => tail_term p r l hp hr (hs l hl) n (b l)

end ringChoose_mul_prime_sub_congr_sum_d

open ringChoose_mul_prime_sub_congr_sum_d

/-- **The general congruence for $\binom{np}{kp}$.** Let $p$ be a prime, let $m$ and $k$ be
natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer $x$ and a natural
number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic
valuation on $\mathbb{Q}$. For natural numbers $j$ and $l$ put
$$
c_j = \sum_{s=0}^{\min(j, k)} \binom{jp}{sp} \binom{n-j}{k-s}, \qquad
d_l = \binom{n}{l} \sum_{j=0}^{l} (-1)^{l-j} \binom{l}{j} c_j,
$$
and let $X = \binom{np}{kp} - \binom{n}{k} - (d_1 + \cdots + d_m)$. Then either $X = 0$, or
$\binom{n}{m+1} \ne 0$ and $v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$. That is,
$\binom{np}{kp} - \binom{n}{k} \equiv d_1 + \cdots + d_m$ modulo $p^{m+1+v_p(\binom{n}{m+1})}$,
with equality when $\binom{n}{m+1} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 3
(`integers-2026-A32-thm-3`). -/
public theorem ringChoose_mul_prime_sub_congr_sum_d (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let c : ℕ → ℚ := fun j => ∑ s ∈ Finset.range (j + 1),
      if s ≤ k then C ((j * p : ℕ) : ℤ) (s * p) * C (n - j) (k - s) else 0
    let d : ℕ → ℚ := fun l =>
      C n l * ∑ j ∈ Finset.range (l + 1), (-1) ^ (l - j) * (l.choose j : ℚ) * c j
    let X : ℚ := C (n * p) (k * p) - C n k - ∑ l ∈ Finset.Icc 1 m, d l
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X) := by
  intro C c d X
  obtain ⟨w, hw⟩ := exists_increment p hp
  let u : ℤ⟦X⟧ := (p : ℤ⟦X⟧) * PowerSeries.X * w
  have hu : constantCoeff u = 0 := by simp [u]
  have hsubst := HasSubst.of_constantCoeff_zero' hu
  let a := base p hp.ne_zero n
  let N := k * p
  let t := max (N + 1) (m + 1)
  let D (l : ℕ) : ℚ := C n l * coeff N (a * u ^ l)
  -- The finite differences of c are the coefficients of successive powers of u.
  have hc (j : ℕ) : c j = ((coeff N (a * (1 + u) ^ j) : ℤ) : ℚ) := by
    dsimp only [a, N]
    rw [mixed_power hsubst hw, mixed_coeff]
    simp [c, C, Int.cast_sum, apply_ite (Int.cast : ℤ → ℚ)]
  have hd (l : ℕ) : D l = d l := by
    dsimp only [D, d]
    rw [difference_coeff a u N l]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_natCast, hc]
  have hzero : D 0 = C n k := by
    simp only [D, C, Ring.choose_zero_right, Int.cast_one, one_mul, pow_zero, mul_one]
    rw [show N = p * k by exact Nat.mul_comm .., coeff_expand_mul]
    simp
  -- Truncate past both the requested degree and the last correction term.
  have hsum : C (n * p) N = ∑ l ∈ range t, D l := by
    have h := coeff_mul_subst hu a (binomialSeries ℤ n) N t
      (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left ..))
    rw [← series_factorization hsubst hw] at h
    simp only [binomialSeries_coeff, zsmul_eq_mul, mul_one, Int.cast_id] at h
    dsimp only [C, D]
    exact_mod_cast h
  have hsmall := sum_range_add_sum_Ico D (m := 1) (n := m + 1) (by omega)
  rw [sum_range_one, show Ico 1 (m + 1) = Icc 1 m from Ico_succ_right_eq_Icc .., hzero] at hsmall
  have hsplit := sum_range_add_sum_Ico D (le_max_right (N + 1) (m + 1))
  have hrem : X = ∑ l ∈ Ico (m + 1) t, D l := by
    dsimp only [X]
    rw [← hsum] at hsplit
    simp_rw [← hd]
    linarith
  rw [hrem]
  -- Pull p^l out of each omitted coefficient before applying the valuation estimate.
  let b (l : ℕ) := coeff N (a * (PowerSeries.X * w) ^ l)
  have hD (l : ℕ) : D l = C n l * ((p : ℚ) ^ l * b l) := by
    dsimp only [D, b, u]
    rw [mul_assoc (p : ℤ⟦X⟧), mul_pow, mul_left_comm a, ← Nat.cast_pow, coeff_natCast_mul]
    push_cast
    rfl
  simp_rw [hD]
  exact sum_tail p (m + 1) hp hmp n _ (fun _ hl => (mem_Ico.mp hl).1) b

-- The lower index is k - i, with negative indices interpreted as zero.
private noncomputable def shiftedChoose (x : ℚ) (k i : ℕ) : ℚ :=
  if i ≤ k then Ring.choose x (k - i) else 0

private lemma shiftedChoose_pascal (x : ℚ) (k i : ℕ) :
    shiftedChoose (x + 1) k i = shiftedChoose x k i + shiftedChoose x k (i + 1) := by
  by_cases h : i < k
  · simp only [shiftedChoose, ite_eq_left h.le, ite_eq_left (Nat.succ_le_of_lt h)]
    rw [show k - i = (k - (i + 1)) + 1 by omega, Ring.choose_succ_succ, add_comm]
  · rcases eq_or_lt_of_le (le_of_not_gt h) with rfl | hlt
    · simp [shiftedChoose]
    · simp [shiftedChoose, not_le.mpr hlt, show ¬ i + 1 ≤ k by omega]

private lemma sum_choose_mul_shiftedChoose (x : ℚ) (j k : ℕ) :
    ∑ i ∈ range (j + 1), (j.choose i : ℚ) * shiftedChoose (x - j) k i = Ring.choose x k := by
  let f (i : ℕ) := (j.choose i : ℚ) * shiftedChoose (x - j) k i
  have h := Ring.add_choose_eq k (Commute.all (j : ℚ) (x - j))
  rw [show (j : ℚ) + (x - j) = x by ring, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Ring.choose_natCast] at h
  rw [h]
  calc
    ∑ i ∈ range (j + 1), f i = ∑ i ∈ range (max j k + 1), f i := by
      apply sum_subset (range_mono (Nat.succ_le_succ (le_max_left j k)))
      intro i _ hi
      have hji : j < i := by simpa using hi
      simp [f, Nat.choose_eq_zero_of_lt hji]
    _ = ∑ i ∈ range (k + 1), f i := by
      symm
      apply sum_subset (range_mono (Nat.succ_le_succ (le_max_right j k)))
      intro i _ hi
      have hki : ¬ i ≤ k := by simpa using hi
      simp [f, shiftedChoose, hki]
    _ = _ := by
      refine sum_congr rfl fun i hi => ?_
      simp [f, shiftedChoose, Nat.le_of_lt_succ (mem_range.mp hi)]

private lemma choose_two_mul_shiftedChoose (x : ℚ) (k : ℕ) :
    Ring.choose x 2 * shiftedChoose (x - 2) k 1 = (k : ℚ) * (x - k) / 2 * Ring.choose x k := by
  have hfirst (y : ℚ) (r : ℕ) :
      ((r : ℚ) + 1) * Ring.choose y (r + 1) = y * Ring.choose (y - 1) r := by
    simpa [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right] using
      Ring.choose_smul_choose y (n := r + 1) (k := 1) (Nat.succ_pos r)
  have hlast (y : ℚ) (r : ℕ) :
      (y - r) * Ring.choose y r = y * Ring.choose (y - 1) r := by
    cases r with
    | zero => simp
    | succ r =>
      have hpascal := Ring.choose_succ_succ (y - 1) r
      rw [sub_add_cancel] at hpascal
      rw [Nat.cast_succ, sub_mul, hfirst, hpascal]
      ring
  have htwo : Ring.choose x 2 = x * (x - 1) / 2 := by
    have h := hfirst x 1
    norm_num [Ring.choose_one_right] at h
    linarith only [h]
  cases k with
  | zero => simp [shiftedChoose]
  | succ k =>
    have hk : 1 ≤ k.succ := Nat.succ_le_succ (Nat.zero_le k)
    have h := hlast (x - 1) k
    rw [show x - 1 - 1 = x - 2 by ring] at h
    simp only [shiftedChoose, ite_eq_left hk, Nat.succ_sub_one, Nat.cast_succ, htwo]
    calc
      _ = x * ((x - 1) * Ring.choose (x - 2) k) / 2 := by ring
      _ = (x - ((k : ℚ) + 1)) * (x * Ring.choose (x - 1) k) / 2 := by rw [← h]; ring
      _ = _ := by rw [← hfirst]; ring

-- Compare the scaled rows with Vandermonde, then take the first three finite differences.
private lemma sum_d_three (p k : ℕ) (x : ℚ) :
    let b (j i : ℕ) : ℚ := ((j * p).choose (i * p) : ℚ)
    let c (j : ℕ) := ∑ i ∈ range (j + 1), b j i * shiftedChoose (x - j) k i
    ∑ l ∈ Icc 1 3, Ring.choose x l *
      ∑ j ∈ range (l + 1), (-1) ^ (l - j) * (l.choose j : ℚ) * c j =
        (k : ℚ) * (x - k) / 2 * Ring.choose x k *
          ((x - 4) + (3 - x) * b 2 1 + (x - 2) / 3 * b 3 1) := by
  intro b c
  have bzero (j : ℕ) : b j 0 = 1 := by simp [b]
  have bself (j : ℕ) : b j j = 1 := by simp [b]
  have bsymm : b 3 2 = b 3 1 := by
    have h := Nat.choose_symm (n := 3 * p) (k := p) (by omega)
    rw [show 3 * p - p = 2 * p by omega] at h
    simpa [b] using congrArg (fun a : ℕ => (a : ℚ)) h
  have h32 : (3 : ℕ).choose 2 = 3 := by decide
  have hc0 : c 0 = Ring.choose x k := by
    rw [← sum_choose_mul_shiftedChoose x 0 k]
    norm_num [c, bzero, sum_range_succ]
  have hc1 : c 1 = Ring.choose x k := by
    rw [← sum_choose_mul_shiftedChoose x 1 k]
    norm_num [c, bzero, bself, sum_range_succ]
  have hc2 : c 2 = Ring.choose x k + (b 2 1 - 2) * shiftedChoose (x - 2) k 1 := by
    rw [← sum_choose_mul_shiftedChoose x 2 k]
    norm_num [c, bzero, bself, sum_range_succ]
    ring
  have hc3 : c 3 = Ring.choose x k + (b 3 1 - 3) * shiftedChoose (x - 2) k 1 := by
    rw [← sum_choose_mul_shiftedChoose x 3 k, show x - 2 = x - 3 + 1 by ring, shiftedChoose_pascal]
    norm_num [c, bzero, bself, bsymm, h32, sum_range_succ]
    ring
  have hthree : Ring.choose x 3 = (x - 2) / 3 * Ring.choose x 2 := by
    have h := Ring.choose_smul_choose x (n := 3) (k := 2) (by decide)
    norm_num [h32, nsmul_eq_mul, Ring.choose_one_right] at h
    linarith only [h]
  calc
    _ = Ring.choose x 2 * shiftedChoose (x - 2) k 1 *
        ((b 2 1 - 2) + (x - 2) / 3 * (b 3 1 - 3 * b 2 1 + 3)) := by
      rw [show Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
      norm_num [sum_insert, sum_range_succ, hc0, hc1, hc2, hc3, h32, hthree]
      ring
    _ = _ := by rw [choose_two_mul_shiftedChoose]; ring

/-- **The congruence for $\binom{np}{kp}$ modulo $p^4$ via $\binom{2p}{p}$ and $\binom{3p}{p}$.**
Let $p \ge 7$ be a prime, let $k$ be a natural number and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be
the $p$-adic valuation on $\mathbb{Q}$. Let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \left((n - 4) +
(3 - n) \binom{2p}{p} + \frac{n - 2}{3} \binom{3p}{p}\right).
$$
Then either $X = 0$, or $\binom{n}{4} \ne 0$ and $v_p(X) \ge 4 + v_p\big(\binom{n}{4}\big)$; that
is, $X \equiv 0 \pmod{p^{4+v_p(\binom{n}{4})}}$, and $X = 0$ when $\binom{n}{4} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 3
(`integers-2026-A32-prop-3`). -/
public theorem ringChoose_mul_prime_sub_congr_pow_four (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp7 : 7 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let N : ℚ := n
    let X : ℚ := C (n * p) (k * p) - C n k -
      (k : ℚ) * (N - k) / 2 * C n k *
        ((N - 4) + (3 - N) * ((2 * p).choose p : ℚ) + (N - 2) / 3 * ((3 * p).choose p : ℚ))
    X = 0 ∨ (C n 4 ≠ 0 ∧ 4 + padicValRat p (C n 4) ≤ padicValRat p X) := by
  have hmap (z : ℤ) (r : ℕ) : ((Ring.choose z r : ℤ) : ℚ) = Ring.choose (z : ℚ) r :=
    Ring.map_choose (Int.castRingHom ℚ) z r
  have h := ringChoose_mul_prime_sub_congr_sum_d p 3 k n hp (by omega)
  have hsum := sum_d_three p k (n : ℚ)
  dsimp only at h hsum
  simp only [shiftedChoose, mul_ite, mul_zero, one_mul] at hsum
  simp only [hmap, Int.cast_sub, Int.cast_natCast, Ring.choose_natCast] at h
  rw [hsum] at h
  simpa only [hmap, Nat.reduceAdd, Nat.cast_ofNat] using h

end MetaMathlibExt
