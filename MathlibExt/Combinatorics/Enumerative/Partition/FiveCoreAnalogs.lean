/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionCongruence
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The φ-analog of the 5-core partition counts

The theorem `phiFiveCoreAnalog_five_pow_mul` expresses the coefficient at `5 ^ k * n` in terms of
those at `5 * n` and `n`. The proof first shows that extracting every fifth coefficient twice
gives six times the first extraction minus five times the original series.

For the signed theta series `t = φ(-q)`, put `s = φ(-q⁵)` and `a = φ(-q²⁵)`. Splitting squares
into residues modulo five gives `t = a + b + c` with `b * c = s² - a²`. Gauss's Euler product
evaluates the product of the five twists of `t` at a primitive fifth root of unity. Summing the
twists of the quotient then reduces extraction to identities in `a`, `b` and `c`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Ramanujan's general theta function at powers of q.** For positive integers $i$ and $j$,
$f(q^i, q^j)$ is the integer power series $\sum_{n \in \mathbb{Z}} q^{i n(n+1)/2 + j n(n-1)/2}$,
that is, Ramanujan's $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ at $a = q^i$
and $b = q^j$.

Since $i, j \ge 1$, only integers $n$ with $|n| \le m$ contribute to the coefficient of $q^m$, so
each coefficient is a finite count.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1 (definition of `f(a, b)`). -/
def ramanujanThetaPow (i j : ℕ+) : ℤ⟦X⟧ :=
  mk fun m => (((Finset.Icc (-(m : ℤ)) m).filter fun n =>
    ((i : ℕ) : ℤ) * (n * (n + 1) / 2) + ((j : ℕ) : ℤ) * (n * (n - 1) / 2) = m).card : ℤ)

/-- **The 5-core counts.** For a natural number $n$, $c_5(n)$ is the coefficient of $q^n$ in the
integer power series $f_5^5 / f_1$, where $f_k = \prod_{m \ge 1} (1 - q^{km})$ is the Euler
product. The series $f_5^5 / f_1$ is the generating function of 5-core partitions.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation for `∑ c_t(n) q^n` with `t = 5` (OEIS A053723). -/
noncomputable def fiveCoreCount (n : ℕ) : ℤ :=
  coeff n (qEulerProduct 5 ^ 5 * invOfUnit (pentagonalSeries ℤ) 1)

/-- **The φ-analog of the 5-core partition function.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ be Ramanujan's theta function. For a natural
number $n$, $\bar a_5(n)$ is the coefficient of $q^n$ in the integer power series
$\varphi^5(-q^5)/\varphi(-q)$ (the denominator has constant term $1$, so the quotient is a power
series).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (at) (OEIS A368490). -/
noncomputable def phiFiveCoreAnalog (n : ℕ) : ℤ :=
  coeff n (expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 *
    invOfUnit (rescale (-1) (ramanujanThetaPow 1 1)) 1)

/-- **The ψ-analog of the 5-core partition function.** Let
$\psi(q) = \sum_{n \in \mathbb{Z}} q^{2n^2 - n} = \sum_{n \ge 0} q^{n(n+1)/2}$ be Ramanujan's theta
function. For a natural number $n$, $\bar b_5(n)$ is the coefficient of $q^n$ in the integer
power series $\psi^5(-q^5)/\psi(-q)$ (the denominator has constant term $1$, so the quotient is
a power series).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (bt) (OEIS A368495). -/
noncomputable def psiFiveCoreAnalog (n : ℕ) : ℤ :=
  coeff n (expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 *
    invOfUnit (rescale (-1) (ramanujanThetaPow 1 3)) 1)

/-- **Constant term of Ramanujan's theta function.** For all positive integers $i$ and $j$, the
integer power series $f(q^i, q^j) = \sum_{n \in \mathbb{Z}} q^{i n(n+1)/2 + j n(n-1)/2}$ has
constant term $1$: only $n = 0$ contributes to $q^0$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1. -/
theorem constantCoeff_ramanujanThetaPow (i j : ℕ+) : constantCoeff (ramanujanThetaPow i j) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ramanujanThetaPow, coeff_mk]
  simp [Finset.filter_singleton]

/-- **Generating function of the 5-core counts.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ and
let $c_5(n)$ be the coefficient of $q^n$ in $f_5^5 / f_1$. Then, as integer power series,
$\left(\sum_{n \ge 0} c_5(n) q^n\right) f_1 = f_5^5$, where $f_1$ is written as the pentagonal
series $\sum_{j \in \mathbb{Z}} (-1)^j q^{j(3j-1)/2}$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1. -/
theorem mk_fiveCoreCount_mul : mk fiveCoreCount * pentagonalSeries ℤ = qEulerProduct 5 ^ 5 := by
  have h0 : constantCoeff (pentagonalSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    have := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
    rw [show pentagonal 0 = 0 by simp [pentagonal_def], coeff_zero_eq_constantCoeff_apply] at this
    simpa using this
  have hmk : mk fiveCoreCount = qEulerProduct 5 ^ 5 * invOfUnit (pentagonalSeries ℤ) 1 := by
    ext n; simp [fiveCoreCount]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

/-- **Generating function of the $\varphi$-analog of the 5-core counts.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and let $\bar a_5(n)$ be the coefficient of $q^n$
in $\varphi(-q^5)^5 / \varphi(-q)$. Then, as integer power series,
$\left(\sum_{n \ge 0} \bar a_5(n) q^n\right) \varphi(-q) = \varphi(-q^5)^5$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (at). -/
theorem mk_phiFiveCoreAnalog_mul :
    mk phiFiveCoreAnalog * rescale (-1) (ramanujanThetaPow 1 1) =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 := by
  have h0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 1)) = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have hmk : mk phiFiveCoreAnalog =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 *
      invOfUnit (rescale (-1) (ramanujanThetaPow 1 1)) 1 := by
    ext n; simp [phiFiveCoreAnalog]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

/-- **Generating function of the $\psi$-analog of the 5-core counts.** Let
$\psi(q) = \sum_{n \in \mathbb{Z}} q^{n(2n-1)}$ and let $\bar b_5(n)$ be the coefficient of $q^n$
in $\psi(-q^5)^5 / \psi(-q)$. Then, as integer power series,
$\left(\sum_{n \ge 0} \bar b_5(n) q^n\right) \psi(-q) = \psi(-q^5)^5$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (bt). -/
theorem mk_psiFiveCoreAnalog_mul :
    mk psiFiveCoreAnalog * rescale (-1) (ramanujanThetaPow 1 3) =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 := by
  have h0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 3)) = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have hmk : mk psiFiveCoreAnalog =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 *
      invOfUnit (rescale (-1) (ramanujanThetaPow 1 3)) 1 := by
    ext n; simp [psiFiveCoreAnalog]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

end

namespace phiFiveCoreAnalog_five_pow_mul

open Finset Filter
open scoped PowerSeries.WithPiTopology Topology

private noncomputable abbrev E (d : ℕ) (hd : d ≠ 0) := expand (R := ℂ) d hd

private noncomputable def normFive (z : ℂ) (f : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  ∏ i ∈ range 5, rescale (z ^ i) f

private theorem continuous_expand (d : ℕ) (hd : d ≠ 0) : Continuous (E d hd) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply (WithPiTopology.tendsto_iff_coeff_tendsto ..).mpr
  intro n
  simp only [E, coeff_expand]
  split_ifs
  · exact (WithPiTopology.continuous_coeff ℂ _).continuousAt
  · exact tendsto_const_nhds

private theorem continuous_twist (z : ℂ) : Continuous (rescale z) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply (WithPiTopology.tendsto_iff_coeff_tendsto ..).mpr
  intro n
  simp only [coeff_rescale]
  exact tendsto_const_nhds.mul (WithPiTopology.continuous_coeff ℂ n).continuousAt

private theorem euler_prod (d : ℕ) (hd : d ≠ 0) :
    HasProd (fun n : ℕ => 1 - (X : ℂ⟦X⟧) ^ (d * (n + 1))) (E d hd (pentagonalSeries ℂ)) := by
  simpa [Function.comp_def, E, ← pow_mul] using
    (WithPiTopology.hasProd_one_sub_X_pow ℂ).map (E d hd) (continuous_expand d hd)

-- Insert the factors indexed by multiples of five into the full Euler product.
private theorem sparse_prod (d : ℕ) (hd : d ≠ 0) :
    HasProd (fun n : ℕ => if 5 ∣ n + 1 then 1 - (X : ℂ⟦X⟧) ^ (d * (n + 1)) else 1)
      (E (5 * d) (by positivity) (pentagonalSeries ℂ)) := by
  let g (k : ℕ) := 5 * k + 4
  have hg : Function.Injective g := by intro i j h; dsimp [g] at h; omega
  apply (hg.hasProd_iff ?_).mp
  · apply (euler_prod (5 * d) (by positivity)).congr_fun
    intro k
    simp [g, show 5 * k + 4 + 1 = 5 * (k + 1) by omega, mul_left_comm,
      mul_assoc]
  · intro n hn
    have h : ¬ 5 ∣ n + 1 := by
      intro h
      exact hn ⟨n / 5, by dsimp [g]; omega⟩
    simp [h]

private theorem norm_factor (z : ℂ) (hz : IsPrimitiveRoot z 5) (m : ℕ) :
    normFive z (1 - (X : ℂ⟦X⟧) ^ m) =
      if 5 ∣ m then (1 - X ^ m) ^ 5 else 1 - X ^ (5 * m) := by
  classical
  have htw (i : ℕ) : rescale (z ^ i) (1 - (X : ℂ⟦X⟧) ^ m) =
      1 - (C (z ^ m)) ^ i * X ^ m := by
    rw [map_sub, map_one, map_pow, rescale_X, mul_pow, ← C.map_pow, ← C.map_pow, ← pow_mul,
      ← pow_mul]
    rw [Nat.mul_comm i m]
  simp only [normFive, htw]
  split_ifs with h
  · simp [(hz.pow_eq_one_iff_dvd m).mpr h]
  · have hcop := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h
    have hr := (hz.pow_of_coprime m hcop.symm).map_of_injective (C_injective (R := ℂ))
    have he := X_pow_sub_C_eq_prod hr (by decide) (rfl : (X ^ m : ℂ⟦X⟧) ^ 5 = _)
    simpa [Polynomial.eval_prod, ← pow_mul, Nat.mul_comm m 5] using
      (congrArg (Polynomial.eval 1) he).symm

private theorem norm_euler (z : ℂ) (hz : IsPrimitiveRoot z 5) (d : ℕ) (hd : d ≠ 0)
    (hc : ¬ 5 ∣ d) :
    normFive z (E d hd (pentagonalSeries ℂ)) *
        E (25 * d) (by positivity) (pentagonalSeries ℂ) =
      E (5 * d) (by positivity) (pentagonalSeries ℂ) ^ 6 := by
  have hn : HasProd (fun n : ℕ => normFive z (1 - (X : ℂ⟦X⟧) ^ (d * (n + 1))))
      (normFive z (E d hd (pentagonalSeries ℂ))) :=
    hasProd_prod fun i _ => (euler_prod d hd).map (rescale (z ^ i)) (continuous_twist _)
  have hl := hn.mul (sparse_prod (5 * d) (by positivity))
  have hr := (euler_prod (5 * d) (by positivity)).mul ((sparse_prod d hd).pow 5)
  simp only [show 5 * (5 * d) = 25 * d by omega] at hl
  rw [show (6 : ℕ) = 1 + 5 by decide, pow_add, pow_one]
  apply hl.unique (hr.congr_fun ?_)
  intro n
  simp only [norm_factor z hz, (by decide : Nat.Prime 5).dvd_mul, or_iff_right hc]
  by_cases h : 5 ∣ n + 1 <;> simp [h, mul_assoc, mul_comm, mul_left_comm]

private noncomputable abbrev V := E 5 (by decide)
private noncomputable abbrev castSeries := PowerSeries.map (Int.castRingHom ℂ)
private noncomputable abbrev signed := castSeries.comp (rescale (-1 : ℤ))

private theorem map_pentagonal : castSeries (pentagonalSeries ℤ) = pentagonalSeries ℂ := by
  ext n
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp [castSeries]
  · simp [castSeries, coeff_pentagonalSeries_eq_zero _ hn]

private theorem norm_mul (z : ℂ) (f g : ℂ⟦X⟧) :
    normFive z (f * g) = normFive z f * normFive z g := by
  simp [normFive, prod_mul_distrib]

private theorem norm_theta (z : ℂ) (hz : IsPrimitiveRoot z 5) (t : ℂ⟦X⟧)
    (ht : t * E 2 (by decide) (pentagonalSeries ℂ) = pentagonalSeries ℂ ^ 2) :
    normFive z t * V (V t) = V t ^ 6 := by
  let p := pentagonalSeries ℂ
  let d := E 2 (by decide) p
  have h : t * d = p ^ 2 := ht
  have hn₁ : normFive z p * V (V p) = V p ^ 6 := by
    simpa [V, E, ← expand_mul, p] using norm_euler z hz 1 (by decide) (by decide)
  have hn₂ : normFive z d * V (V d) = V d ^ 6 := by
    simpa [V, E, ← expand_mul, p, d] using norm_euler z hz 2 (by decide) (by decide)
  have hnorm : normFive z t * normFive z d = normFive z p ^ 2 := by
    simpa only [pow_two, norm_mul] using congrArg (normFive z) h
  have h₁ : V t * V d = V p ^ 2 := by simpa using congrArg V h
  have h₂ : V (V t) * V (V d) = V (V p) ^ 2 := by simpa using congrArg V h₁
  have hd : V d ≠ 0 := by
    intro hzero
    have hc := congrArg constantCoeff hzero
    have h0 := coeff_pentagonalSeries_pentagonal (R := ℂ) 0
    simp [pentagonal_def, coeff_zero_eq_constantCoeff_apply] at h0
    simp [V, E, d, p, h0] at hc
  apply mul_right_cancel₀ (pow_ne_zero 6 hd)
  calc
    _ = (normFive z t * normFive z d) * (V (V t) * V (V d)) := by rw [← hn₂]; ring
    _ = (normFive z p * V (V p)) ^ 2 := by rw [hnorm, h₂]; ring
    _ = (V t * V d) ^ 6 := by rw [hn₁, h₁]; ring
    _ = _ := mul_pow _ _ _

private theorem theta_coeff (n : ℕ) :
    (ramanujanThetaPow 1 1).coeff n = (Nat.card {x : ℤ // x.natAbs ^ 2 = n} : ℤ) := by
  rw [ramanujanThetaPow, coeff_mk]
  push_cast
  have hex (x : ℤ) : x * (x + 1) / 2 + x * (x - 1) / 2 = x ^ 2 := by
    have he : 2 ∣ x * (x - 1) := by
      rcases Int.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (x - 1), by rw [hk]; ring⟩
      · exact ⟨x * k, by rw [hk]; ring⟩
    obtain ⟨k, hk⟩ := he
    have h : x * (x + 1) = 2 * (k + x) := by linarith only [hk]
    have h' : x ^ 2 = 2 * k + x := by linarith only [hk]
    omega
  simp only [one_mul, hex]
  apply congrArg Nat.cast
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [Finset.mem_filter, Finset.mem_Icc]
  have hsq : (x.natAbs ^ 2 : ℕ) = n ↔ x ^ 2 = (n : ℤ) := by
    rw [← Int.natAbs_sq x]
    norm_cast
  rw [hsq, and_iff_right_iff_imp]
  intro hx
  constructor <;> nlinarith [Int.le_self_sq x, Int.le_self_sq (-x)]

private def allButOne {R : Type*} [CommRing R] (f : ℕ → R) : R :=
  ∑ i ∈ range 5, ∏ j ∈ (range 5).erase i, f j

private theorem conjugate_sums {R : Type*} [CommRing R] (a b c w : R)
    (hw : 1 + w + w ^ 2 + w ^ 3 + w ^ 4 = 0)
    (f : ℕ → R) (hf : ∀ i < 5, f i = a + w ^ i * b + w ^ ((4 * i) % 5) * c) :
    (∑ i ∈ range 5, f i) = 5 * a ∧
    (∑ i ∈ range 5, (f i) ^ 3) = 5 * (a ^ 3 + 6 * a * (b * c)) ∧
    allButOne f = 5 * (a ^ 4 - 3 * a ^ 2 * (b * c) + (b * c) ^ 2) := by
  have he : allButOne f =
      f 1 * f 2 * f 3 * f 4 + f 0 * f 2 * f 3 * f 4 + f 0 * f 1 * f 3 * f 4 +
        f 0 * f 1 * f 2 * f 4 + f 0 * f 1 * f 2 * f 3 := by
    have hr : range 5 = {0, 1, 2, 3, 4} := by decide
    norm_num [allButOne, hr, Finset.erase_insert_of_ne, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc]
  rw [he]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num [hf]
  constructor
  · grobner
  constructor <;> grobner

private noncomputable def extract (f : ℂ⟦X⟧) : ℂ⟦X⟧ := mk fun n => f.coeff (5 * n)

private theorem trace_eq (z : ℂ) (hz : IsPrimitiveRoot z 5) (f : ℂ⟦X⟧) :
    ∑ i ∈ range 5, rescale (z ^ i) f = 5 * V (extract f) := by
  ext n
  simp only [map_sum, coeff_rescale, ← sum_mul, coeff_ofNat_mul, V, E, coeff_expand]
  have hs : ∑ i ∈ range 5, (z ^ i) ^ n = ∑ i ∈ range 5, (z ^ n) ^ i := by
    simp only [← pow_mul, Nat.mul_comm _ n]
  rw [hs]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    simp [pow_mul, hz.pow_eq_one, extract]
  · rw [(hz.pow_of_coprime n ((Nat.Prime.coprime_iff_not_dvd
      (by decide : Nat.Prime 5)).mpr h).symm).geom_sum_eq_zero (by decide)]
    simp

private theorem twist_expand (z : ℂ) (hz : z ^ 5 = 1) (f : ℂ⟦X⟧) :
    rescale z (V f) = V f := by
  ext n
  rw [coeff_rescale]
  by_cases h : 5 ∣ n
  · obtain ⟨k, rfl⟩ := h
    simp [pow_mul, hz]
  · simp [V, E, coeff_expand_of_not_dvd _ _ _ h]

private theorem signed_expand (f : ℤ⟦X⟧) (d : ℕ) (hd : d ≠ 0) (hodd : Odd d) :
    signed (expand d hd f) = E d hd (signed f) := by
  ext n
  by_cases h : d ∣ n
  · obtain ⟨k, rfl⟩ := h
    simp [signed, castSeries, E, coeff_rescale, coeff_map, pow_mul, hodd.neg_one_pow]
  · simp [signed, castSeries, E, coeff_rescale, coeff_map, coeff_expand_of_not_dvd _ _ _ h]

private theorem twist_component (z : ℂ) (hz : z ^ 5 = 1) (r i : ℕ) (b : ℤ⟦X⟧)
    (hb : ∀ n, b.coeff n ≠ 0 → n % 5 = r) :
    rescale (z ^ i) (signed b) = C z ^ ((r * i) % 5) * signed b := by
  ext n
  rw [← C.map_pow, coeff_C_mul, coeff_rescale]
  by_cases h : b.coeff n = 0
  · simp [signed, castSeries, coeff_map, coeff_rescale, h]
  · have hi : (z ^ i) ^ 5 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
    rw [pow_eq_pow_mod n hi, hb n h, ← pow_mul, Nat.mul_comm i r, ← pow_eq_pow_mod _ hz]

private theorem theta_twists (z : ℂ) (hz : IsPrimitiveRoot z 5) :
    let t := signed (ramanujanThetaPow 1 1)
    ∃ b c : ℂ⟦X⟧, V (V t) ^ 2 + b * c = V t ^ 2 ∧
      ∀ i < 5, rescale (z ^ i) t = V (V t) + C z ^ i * b + C z ^ ((4 * i) % 5) * c := by
  dsimp only
  obtain ⟨b, c, h, hs, hb, hc⟩ := theta_five_components _ theta_coeff
  have he (f : ℤ⟦X⟧) : signed (expand 25 (by decide) f) = V (V (signed f)) := by
    rw [signed_expand _ _ _ (by decide)]
    exact expand_mul 5 (by decide) 5 (by decide) _
  refine ⟨signed b, signed c, ?_, ?_⟩
  · simpa only [map_add, map_mul, map_pow, he, signed_expand _ 5 _ (by decide)] using
      congrArg signed hs
  · intro i hi
    have hdecomp := congrArg signed h
    simp only [map_add, he] at hdecomp
    have ht : (z ^ i) ^ 5 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    calc
      _ = rescale (z ^ i) (V (V (signed (ramanujanThetaPow 1 1))) + signed b + signed c) :=
        congrArg _ hdecomp
      _ = _ := by
        rw [map_add, map_add, twist_expand _ ht, twist_component z hz.pow_eq_one 1 i b hb,
          twist_component z hz.pow_eq_one 4 i c hc, one_mul, Nat.mod_eq_of_lt hi]

private theorem signed_gauss :
    signed (ramanujanThetaPow 1 1) * E 2 (by decide) (pentagonalSeries ℂ) =
      pentagonalSeries ℂ ^ 2 := by
  simpa only [signed, RingHom.comp_apply, map_mul, map_pow, castSeries, map_expand, E,
    map_pentagonal] using congrArg castSeries (theta_euler_product _ theta_coeff)

private theorem expand_injective : Function.Injective V := by
  intro f g h
  ext n
  simpa [V, E] using congrArg (coeff (5 * n)) h

private theorem trace_quotient (z : ℂ) (hz : IsPrimitiveRoot z 5) (t f : ℂ⟦X⟧)
    (hs : V t ≠ 0) (hf : f * t = V t ^ 5) (hn : normFive z t * V (V t) = V t ^ 6) :
    V t * (5 * V (extract f)) = V (V t) * allButOne (fun i => rescale (z ^ i) t) := by
  let s := V t
  let a := V s
  have hquot (i : ℕ) : rescale (z ^ i) f * rescale (z ^ i) t = s ^ 5 := by
    have hi : (z ^ i) ^ 5 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    simpa only [map_mul, map_pow, twist_expand _ hi] using congrArg (rescale (z ^ i)) hf
  have hprod : normFive z t * (∑ i ∈ range 5, rescale (z ^ i) f) =
      s ^ 5 * allButOne (fun i => rescale (z ^ i) t) := by
    rw [allButOne, mul_sum, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [normFive, ← prod_erase_mul (range 5) (fun j => rescale (z ^ j) t) hi, ← hquot i]
    ring
  rw [← trace_eq z hz]
  apply mul_left_cancel₀ (pow_ne_zero 5 hs)
  change s ^ 5 * (s * _) = s ^ 5 * (a * _)
  calc
    _ = (normFive z t * a) * (∑ i ∈ range 5, rescale (z ^ i) f) := by rw [hn]; ring
    _ = a * (s ^ 5 * allButOne (fun i => rescale (z ^ i) t)) := by rw [← hprod]; ring
    _ = _ := by ring

-- On the two theta monomials H = t s³ and J = s t³ the extraction operator sends
-- H to J and J to 6J - 5H. The quotient differs from an eigenvector by their span.
private theorem extract_recurrence (z : ℂ) (hz : IsPrimitiveRoot z 5) (t f b c : ℂ⟦X⟧)
    (hs : V t ≠ 0) (hf : f * t = V t ^ 5) (hn : normFive z t * V (V t) = V t ^ 6)
    (hbc : V (V t) ^ 2 + b * c = V t ^ 2)
    (ht : ∀ i < 5, rescale (z ^ i) t =
      V (V t) + C z ^ i * b + C z ^ ((4 * i) % 5) * c) :
    extract (extract f) = 6 * extract f - 5 * f := by
  let s := V t
  let a := V s
  let H := t * s ^ 3
  let J := s * t ^ 3
  have hw : 1 + C z + C z ^ 2 + C z ^ 3 + C z ^ 4 = (0 : ℂ⟦X⟧) := by
    simpa [sum_range_succ] using congrArg (C (R := ℂ)) (hz.geom_sum_eq_zero (by decide : 1 < 5))
  obtain ⟨h₁, h₃, h₄⟩ := conjugate_sums a b c (C z) hw _ ht
  have hsub : b * c = s ^ 2 - a ^ 2 := by linear_combination hbc
  have h5 : (5 : ℂ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    norm_num [map_ofNat] at this
  have hV : V f * s = a ^ 5 := by simpa [s, a] using congrArg V hf
  have hF : extract f = 5 * f - 5 * H + J := by
    apply expand_injective
    apply mul_left_cancel₀ h5
    apply mul_left_cancel₀ hs
    rw [trace_quotient z hz t f hs hf hn, h₄, hsub]
    simp only [H, J, map_add, map_sub, map_ofNat, map_mul, map_pow]
    change a * _ = s * (5 * (5 * V f - 5 * (s * a ^ 3) + a * s ^ 3))
    linear_combination -25 * hV
  have htws (i : ℕ) : rescale (z ^ i) s = s := by
    apply twist_expand
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hH : extract H = J := by
    apply expand_injective
    apply mul_left_cancel₀ h5
    rw [← trace_eq z hz]
    simp only [H, J, map_mul, map_pow, htws, ← sum_mul, h₁]
    change 5 * a * s ^ 3 = 5 * (a * s ^ 3)
    ring
  have hJ : extract J = 6 * J - 5 * H := by
    apply expand_injective
    apply mul_left_cancel₀ h5
    rw [← trace_eq z hz]
    simp only [J, H, map_mul, map_pow, htws, ← mul_sum, h₃, hsub, map_sub, map_ofNat]
    change s * (5 * (a ^ 3 + 6 * a * (s ^ 2 - a ^ 2))) =
      5 * (6 * (a * s ^ 3) - 5 * (s * a ^ 3))
    ring
  have hlin : extract (5 * f - 5 * H + J) = 5 * extract f - 5 * extract H + extract J := by
    ext n
    simp [extract]
  calc
    _ = 5 * extract f - 5 * extract H + extract J := (congrArg extract hF).trans hlin
    _ = _ := by rw [hH, hJ]; linear_combination -hF

private theorem base_recurrence (n : ℕ) :
    phiFiveCoreAnalog (25 * n) = 6 * phiFiveCoreAnalog (5 * n) - 5 * phiFiveCoreAnalog n := by
  let t := signed (ramanujanThetaPow 1 1)
  let f := castSeries (mk phiFiveCoreAnalog)
  have hf : f * t = V t ^ 5 := by
    simpa only [f, t, signed, RingHom.comp_apply, castSeries, map_mul, map_pow, map_expand, V, E]
      using congrArg castSeries mk_phiFiveCoreAnalog_mul
  have hs : V t ≠ 0 := by
    intro h
    have hh := congrArg (coeff 0) h
    simp [V, E, coeff_expand, t, castSeries, coeff_map, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_ramanujanThetaPow] at hh
  have hz := Complex.isPrimitiveRoot_exp 5 (by decide)
  obtain ⟨b, c, hbc, ht⟩ := theta_twists _ hz
  have h := extract_recurrence _ hz t f b c hs hf (norm_theta _ hz _ signed_gauss) hbc ht
  have hc := congrArg (coeff n) h
  apply Int.cast_injective (α := ℂ)
  push_cast
  simpa [extract, f, castSeries, coeff_map, ← mul_assoc] using hc

end phiFiveCoreAnalog_five_pow_mul

/-- **Recurrence for the $\varphi$-analog of the 5-core counts along powers of 5.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and let $\bar a_5(n)$ be the coefficient of $q^n$
in $\varphi(-q^5)^5 / \varphi(-q)$. For every natural number $k \ge 2$ and every natural number
$n$, $\bar a_5(5^k n) = \frac{5^k - 1}{4}\, \bar a_5(5n) - \frac{5^k - 5}{4}\, \bar a_5(n)$.
Both quotients are integers.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 2 (`jis-2024-24.4.5-thm-2`). -/
public theorem phiFiveCoreAnalog_five_pow_mul {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    phiFiveCoreAnalog (5 ^ k * n) =
      ((5 ^ k - 1) / 4 : ℤ) * phiFiveCoreAnalog (5 * n) -
        ((5 ^ k - 5) / 4 : ℤ) * phiFiveCoreAnalog n := by
  induction k, hk using Nat.le_induction generalizing n with
  | base => simpa using phiFiveCoreAnalog_five_pow_mul.base_recurrence n
  | succ k _ ih =>
    obtain ⟨m, hm⟩ : (4 : ℤ) ∣ 5 ^ k - 1 := sub_one_dvd_pow_sub_one (5 : ℤ) k
    rw [pow_succ, Nat.mul_assoc, ih, ← Nat.mul_assoc, show (5 : ℕ) * 5 = 25 by decide,
      phiFiveCoreAnalog_five_pow_mul.base_recurrence, pow_succ]
    rw [show ((5 : ℤ) ^ k - 1) / 4 = m by omega,
      show ((5 : ℤ) ^ k - 5) / 4 = m - 1 by omega,
      show ((5 : ℤ) ^ k * 5 - 1) / 4 = 5 * m + 1 by omega,
      show ((5 : ℤ) ^ k * 5 - 5) / 4 = 5 * m by omega]
    ring

end MetaMathlibExt
