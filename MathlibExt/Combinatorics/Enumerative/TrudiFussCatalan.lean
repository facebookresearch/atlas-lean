/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
public import MathlibExt.NumberTheory.GeneralizedFussCatalanNumbersFMNK
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Catalan
import MathlibExt.RingTheory.PowerSeries.LagrangeBurmannCoefficient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Trudi multi-sums of Fuss–Catalan numbers

The theorem `trudiPartitionSum_fussCatalan` evaluates five partition sums by extracting
coefficients from the reciprocals of Catalan and Fuss–Catalan generating functions. The module
also records the Catalan equation over `ℚ` and the coefficients of the square of that series.

## References

* Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan
  Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, pp. 1–23, Corollary 9 (the
  partition sums) and the proof of Theorem 6 (the Catalan equation and coefficient shift).
* Mathlib's `PowerSeries.catalanSeries_sq_mul_X_add_one` supplies the Catalan equation over `ℕ`.
-/

namespace MetaMathlibExt

open PowerSeries

/-- Over `ℚ`, the Catalan generating function `C` satisfies `C = 1 + X * C ^ 2`. -/
public lemma catalanSeries_rat_eq_one_add_X_mul_sq :
    let c : PowerSeries ℚ := mk fun n => (catalan n : ℚ)
    c = 1 + X * c ^ 2 := by
  have hmap : map (Nat.castRingHom ℚ) catalanSeries = mk (fun n => (catalan n : ℚ)) := by
    ext n
    simp
  simpa only [map_add, map_mul, map_pow, map_one, map_X, hmap, add_comm, mul_comm] using
    congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one.symm

/-- The coefficient of degree `n` in the square of the rational Catalan generating function
is the Catalan number of index `n + 1`. -/
public lemma coeff_catalanSeries_rat_sq (n : ℕ) :
    coeff n (mk (fun k => (catalan k : ℚ)) ^ 2) = (catalan (n + 1) : ℚ) := by
  have h := congrArg (coeff (n + 1)) catalanSeries_rat_eq_one_add_X_mul_sq
  simpa [coeff_one, coeff_succ_X_mul] using h.symm

namespace trudiPartitionSum_fussCatalan

open scoped PowerSeries

-- Revert x(1+x)⁻ᵖ to obtain the unique solution of w = x(1+w)ᵖ.
private noncomputable def root (p : ℕ) : ℚ⟦X⟧ :=
  (X * binomialSeries ℚ (-(p : ℤ))).substInvOfIsUnit (by
    rw [show 1 = 0 + 1 by rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    simp)

private lemma root_zero (p : ℕ) : constantCoeff (root p) = 0 :=
  constantCoeff_substInvOfIsUnit _ _

private lemma root_subst (p : ℕ) : HasSubst (root p) :=
  HasSubst.of_constantCoeff_zero' (root_zero p)

-- Integer exponents include both the Fuss–Catalan series and their reciprocals.
private noncomputable def raney (p : ℕ) (r : ℤ) : ℚ⟦X⟧ :=
  subst (root p) (binomialSeries ℚ r)

private lemma raney_zero (p : ℕ) : raney p 0 = 1 := by
  simp [raney, ← coe_substAlgHom (root_subst p)]

private lemma raney_add (p : ℕ) (r s : ℤ) :
    raney p (r + s) = raney p r * raney p s := by
  simp [raney, subst_mul (root_subst p)]

private lemma raney_nat (p r : ℕ) : raney p r = (1 + root p) ^ r := by
  simp [raney, ← coe_substAlgHom (root_subst p), substAlgHom_X]

private lemma root_fix (p : ℕ) : root p = X * raney p p := by
  let P : ℚ⟦X⟧ := X * binomialSeries ℚ (-(p : ℤ))
  have hP : constantCoeff P = 0 := by simp [P]
  have h : subst (root p) P = X := subst_substInvOfIsUnit_right P hP _
  change subst (root p) (X * _) = X at h
  rw [subst_mul (root_subst p), subst_X (root_subst p)] at h
  change root p * raney p (-p) = X at h
  rw [← h, mul_assoc, ← raney_add, neg_add_cancel, raney_zero, mul_one]

private lemma derivative_binomial (r : ℤ) :
    derivative (binomialSeries ℚ r) = C (r : ℚ) * binomialSeries ℚ (r - 1) := by
  ext k
  rw [coeff_derivative, coeff_C_mul]
  simp only [binomialSeries_coeff, zsmul_eq_mul, mul_one]
  have h := Ring.choose_smul_choose r (n := k + 1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_one, Ring.choose_one_right,
    Nat.add_sub_cancel] at h
  rw [mul_comm]
  exact_mod_cast h

private lemma coeff_raney (p : ℕ) (r : ℤ) (n : ℕ) (hn : 0 < n) :
    coeff n (raney p r) = (r : ℚ) / n * (Ring.choose ((p : ℤ) * n + r - 1 : ℤ) (n - 1) : ℤ) := by
  have h := fps_lagrange_burmann_coeff' (root p) (binomialSeries ℚ (p : ℤ))
    (binomialSeries ℚ r) (root_fix p) n hn
  change (n : ℚ) * coeff n (raney p r) = _ at h
  have hpow : (binomialSeries ℚ (p : ℤ)) ^ n = binomialSeries ℚ ((p * n : ℕ) : ℤ) := by
    rw [binomialSeries_nat, binomialSeries_nat, pow_mul]
  rw [derivative_binomial, hpow, mul_assoc, ← binomialSeries_add,
    coeff_C_mul, binomialSeries_coeff, zsmul_eq_mul, mul_one] at h
  push_cast at h
  rw [show (p : ℤ) * n + r - 1 = r - 1 + p * n by ring]
  have hn' : (n : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination h

private lemma coeff_raney_nat (p r n : ℕ) (hn : 0 < n) :
    coeff n (raney p r) = generalizedFussCatalanNumber p n r := by
  rw [coeff_raney p r n hn, generalizedFussCatalanNumber_cast_eq_div_mul_choose]
  by_cases hr : r = 0
  · simp [hr]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show p * n + r ≠ 0 by omega)
  have hz : (p : ℤ) * n + r - 1 = m := by
    have h : (p : ℤ) * n + r = m + 1 := by exact_mod_cast hm
    omega
  rw [hz, Ring.choose_natCast, hm]
  have hq : (p : ℚ) * n + r = m + 1 := by exact_mod_cast hm
  rw [hq]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_sub_one, Int.cast_natCast]
  have hchoose := Nat.add_one_mul_choose_eq m k
  have hc : ((m : ℚ) + 1) * m.choose k = (k + 1 : ℚ) * (m + 1).choose (k + 1) := by
    exact_mod_cast (hchoose.trans (mul_comm _ _))
  push_cast
  field_simp
  linear_combination hc

-- Split a nonempty composition at its first part.
private def prepend (n : ℕ) (x : Σ i : Fin (n + 1), Composition (n - i.val)) :
    Composition (n + 1) where
  blocks := (x.1.val + 1) :: x.2.blocks
  blocks_pos h := by
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · exact x.2.blocks_pos h
  blocks_sum := by
    rw [List.sum_cons, x.2.blocks_sum]
    have := x.1.isLt
    omega

private lemma prepend_bijective (n : ℕ) : Function.Bijective (prepend n) := by
  constructor
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    have hblocks := congrArg Composition.blocks h
    change (i.val + 1) :: c.blocks = (j.val + 1) :: d.blocks at hblocks
    obtain ⟨hij, hcd⟩ := List.cons.inj hblocks
    have : i = j := Fin.ext (by omega)
    subst j
    rw [Composition.ext hcd]
  · rintro ⟨l, hpos, hsum⟩
    obtain _ | ⟨b, l⟩ := l
    · simp at hsum
    cases b with
    | zero => simp at hpos
    | succ i =>
      simp only [List.sum_cons] at hsum
      let hc : Composition (n - i) :=
        ⟨l, fun h => hpos (List.mem_cons_of_mem _ h), by omega⟩
      exact ⟨⟨⟨i, by omega⟩, hc⟩, rfl⟩

private lemma trudi_succ (s : ℚ) (a : ℕ → ℚ) (n : ℕ) :
    trudiPartitionSum s a (n + 1) =
      ∑ i ∈ Finset.range (n + 1), s * a (i + 1) * trudiPartitionSum s a (n - i) := by
  classical
  simp only [trudiPartitionSum_eq_sum_compositions]
  let e := Equiv.ofBijective (prepend n) (prepend_bijective n)
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change s ^ (c.length + 1) * (∏ j : Fin (c.length + 1),
    a (((i.val + 1) :: c.blocks).get j)) = _
  rw [pow_succ, Fin.prod_univ_succ]
  change s ^ c.length * s * (a (i.val + 1) * ∏ j, a (c.blocksFun j)) = _
  ring

-- The weighted compositions are the coefficients of the reciprocal of D.
private lemma trudi_eq_coeff (s : ℚ) (a : ℕ → ℚ) (D F : ℚ⟦X⟧)
    (hDF : D * F = 1) (h0 : coeff 0 D = 1)
    (hD : ∀ i, coeff (i + 1) D = -(s * a (i + 1))) (n : ℕ) :
    trudiPartitionSum s a n = coeff n F := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      have h := congrArg (coeff 0) hDF
      simp only [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, h0, one_mul,
        coeff_one] at h
      rw [h]
      simp [trudiPartitionSum]
    | succ n =>
      have h := congrArg (coeff (n + 1)) hDF
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i D * coeff j F), Finset.sum_range_succ'] at h
      simp only [hD, neg_mul, Finset.sum_neg_distrib, h0, one_mul, Nat.sub_zero,
        Nat.add_sub_add_right, coeff_one, Nat.succ_ne_zero, ite_false] at h
      rw [trudi_succ]
      calc
        _ = ∑ i ∈ Finset.range (n + 1), s * a (i + 1) * coeff (n - i) F := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ih _ (by omega)]
        _ = _ := by linarith

private lemma coeff_zero_raney (p : ℕ) (r : ℤ) : coeff 0 (raney p r) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  change MvPowerSeries.constantCoeff (subst (root p) (binomialSeries ℚ r)) = 1
  rw [constantCoeff_subst_of_constantCoeff_zero (root_zero p)]
  simp

private lemma trudi_raney (p r n : ℕ) (hn : 0 < n) :
    -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber p i r : ℚ)) n =
      (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ) := by
  rw [trudi_eq_coeff _ _ (raney p r) (raney p (-r)), coeff_raney _ _ _ hn]
  · have h (z : ℤ) (k : ℕ) : (Ring.choose z k : ℤ) = (Ring.choose (z : ℚ) k : ℚ) :=
      Ring.map_choose (Int.castRingHom ℚ) z k
    rw [h]
    push_cast
    simp only [sub_eq_add_neg]
    ring
  · rw [← raney_add, add_neg_cancel, raney_zero]
  · exact coeff_zero_raney _ _
  · intro i
    simp [coeff_raney_nat _ _ _ (Nat.succ_pos i)]

-- Multiplication by 1/(1-X) takes partial sums of the coefficients.
private noncomputable def cat : ℚ⟦X⟧ := mk fun n => (catalan n : ℚ)

private lemma coeff_cat (i : ℕ) : coeff i cat = catalan i := by
  simp [cat]

private lemma cat_zero : constantCoeff cat = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_cat, catalan_zero, Nat.cast_one]

private noncomputable def geom : ℚ⟦X⟧ := mk 1

private lemma geom_mul : geom * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℚ

private lemma coeff_cat_geom (n : ℕ) :
    coeff n (cat * geom) = ∑ i ∈ Finset.range (n + 1), (catalan i : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    coeff i cat * coeff j geom)]
  simp [geom, coeff_cat]

private lemma trudi_catalan_diff (n : ℕ) (hn : 1 ≤ n) :
    -trudiPartitionSum (-1) (fun i => (catalan i : ℚ) - catalan (i - 1)) n =
      ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ) := by
  let D := (1 - X) * cat
  let F := geom - X * (cat * geom)
  have hinv : D * F = 1 := by
    have hcat : cat = 1 + X * cat ^ 2 := catalanSeries_rat_eq_one_add_X_mul_sq
    have hc : cat * (1 - X * cat) = 1 := by linear_combination hcat
    calc
      D * F = geom * (1 - X) * (cat * (1 - X * cat)) := by dsimp [D, F]; ring
      _ = 1 := by rw [hc, geom_mul, one_mul]
  rw [trudi_eq_coeff _ _ D F hinv]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp only [F, map_sub, coeff_succ_X_mul, coeff_cat_geom,
      Nat.succ_sub_one]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega)]
    simp [geom]
  · simp [D, cat_zero]
  · intro i
    simp [D, sub_mul, coeff_succ_X_mul, coeff_cat]

private lemma trudi_catalan_shift (n : ℕ) (hn : 1 ≤ n) :
    -trudiPartitionSum (-1) (fun i => (catalan (i + 1) : ℚ) - catalan i) n =
      ∑ i ∈ Finset.range n, (catalan i : ℚ) := by
  let D := 1 + cat ^ 2 - cat
  let F := 1 - X * (cat * geom)
  have hD : D * (1 - X - X * cat) = 1 - X := by
    have hcat : cat = 1 + X * cat ^ 2 := catalanSeries_rat_eq_one_add_X_mul_sq
    dsimp [D]
    linear_combination cat * hcat
  have hF : F = geom * (1 - X - X * cat) := by
    dsimp [F]
    linear_combination -geom_mul
  have hinv : D * F = 1 := by
    rw [hF, mul_left_comm, hD, geom_mul]
  rw [trudi_eq_coeff _ _ D F hinv]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [F, coeff_one, coeff_succ_X_mul, coeff_cat_geom]
  · simp [D, cat_zero]
  · intro i
    have hsq : coeff (i + 1) (cat ^ 2) = (catalan (i + 2) : ℚ) :=
      coeff_catalanSeries_rat_sq (i + 1)
    simp [D, hsq, coeff_one, coeff_cat]

-- H = 1 + X H³, and the series with coefficients J is H².
private lemma ternary_eq : raney 3 1 = 1 + X * raney 3 3 := by
  conv_lhs => rw [show (1 : ℤ) = (1 : ℕ) by rfl, raney_nat, pow_one]
  exact congrArg (1 + ·) (root_fix 3)

private lemma trudi_ternary_shift (n : ℕ) (hn : 2 ≤ n) :
    -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
      2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ) := by
  have hshift (i : ℕ) :
      coeff i (raney 3 3) = (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ) := by
    have h := congrArg (coeff (i + 1)) ternary_eq
    calc
      _ = coeff (i + 1) (raney 3 1) := by simpa [coeff_one, coeff_succ_X_mul] using h.symm
      _ = _ := coeff_raney_nat 3 1 _ (Nat.succ_pos i)
  rw [trudi_eq_coeff _ _ (raney 3 3) (raney 3 (-3))]
  · have h := congrArg (fun f => f * raney 3 (-3)) ternary_eq
    simp only [add_mul, one_mul, mul_assoc, ← raney_add] at h
    norm_num [raney_zero] at h
    have hc := congrArg (coeff n) h
    simp only [map_add, coeff_X, ite_eq_right (by omega : n ≠ 1), add_zero] at hc
    rw [← hc, coeff_raney _ _ _ (by omega)]
    have hi : (3 : ℤ) * n + -2 - 1 = ((3 * n - 3 : ℕ) : ℤ) := by omega
    norm_num only [Nat.cast_ofNat]
    rw [hi, Ring.choose_natCast]
    push_cast
    ring
  · rw [← raney_add]
    exact raney_zero _
  · exact coeff_zero_raney _ _
  · intro i
    simp [hshift]

private lemma trudi_ternary (n : ℕ) (hn : 1 ≤ n) :
    trudiPartitionSum 1 (fun i => (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
      (generalizedFussCatalanNumber 3 n 1 : ℚ) := by
  have hinv : (1 - X * raney 3 2) * raney 3 1 = 1 := by
    rw [sub_mul, one_mul, mul_assoc, ← raney_add]
    norm_num
    linear_combination ternary_eq
  rw [trudi_eq_coeff _ _ _ _ hinv]
  · exact coeff_raney_nat 3 1 n hn
  · simp
  · intro i
    simp only [map_sub, coeff_one, Nat.succ_ne_zero, ite_false, coeff_succ_X_mul,
      zero_sub, Nat.add_sub_cancel, one_mul]
    cases i with
    | zero => rw [coeff_zero_raney]; decide
    | succ i => exact congrArg Neg.neg (coeff_raney_nat 3 2 _ (Nat.succ_pos i))

end trudiPartitionSum_fussCatalan

open trudiPartitionSum_fussCatalan

/-- **Trudi multi-sums of Fuss–Catalan numbers.** For $s \in \mathbb{Q}$ and rational numbers
$a_1, \dots, a_n$ let $T_s(a_1, \dots, a_n)$ be the sum of
$s^{|\alpha|} \binom{|\alpha|}{\alpha_1, \dots, \alpha_n} a_1^{\alpha_1} \cdots a_n^{\alpha_n}$
over all $(\alpha_1, \dots, \alpha_n) \in \mathbb{N}^n$ with
$\alpha_1 + 2 \alpha_2 + \dots + n \alpha_n = n$, where $|\alpha| = \alpha_1 + \dots + \alpha_n$.
Let $A_n(p, r) = \frac{r}{pn + r} \binom{pn + r}{n}$ be the generalized Fuss–Catalan number,
taken to be $0$ when $pn + r = 0$; let $C_n$ be the $n$-th Catalan number,
$K_m = C_{m+2} - C_{m+1}$ for $m \ge -1$ (so $K_{-1} = 0$), $H_n = A_n(3, 1)$ and
$J_n = A_n(3, 2)$. Then the following hold.
(1) For all natural numbers $p, r$ and every $n \ge 1$,
$-T_{-1}(A_1(p, r), \dots, A_n(p, r)) = \frac{r}{n} \binom{pn - r - 1}{n - 1}$, where the
binomial coefficient has an integer, possibly negative, upper index:
$\binom{x}{k} = x (x - 1) \cdots (x - k + 1)/k!$.
(2) For every $n \ge 1$, $-T_{-1}(K_{-1}, K_0, \dots, K_{n-2}) = \sum_{i=1}^{n-1} C_i$.
(3) For every $n \ge 1$, $-T_{-1}(K_0, K_1, \dots, K_{n-1}) = \sum_{i=0}^{n-1} C_i$.
(4) For every $n \ge 2$, $-T_{-1}(H_2, H_3, \dots, H_{n+1}) = \frac{2}{n} \binom{3n - 3}{n - 1}$.
(5) For every $n \ge 1$, $T_1(J_0, J_1, \dots, J_{n-1}) = H_n$.

Identity (1) includes $p = r = 0$, which the paper's standing assumption excludes; there both
sides are $0$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Corollary 9
(`jis-2026-26.1.2-cor-9`). -/
public theorem trudiPartitionSum_fussCatalan :
    (∀ p r n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber p i r : ℚ)) n =
        (r : ℚ) / n * (Ring.choose ((p * n : ℤ) - r - 1) (n - 1) : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (catalan i : ℚ) - catalan (i - 1)) n =
        ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      -trudiPartitionSum (-1) (fun i => (catalan (i + 1) : ℚ) - catalan i) n =
        ∑ i ∈ Finset.range n, (catalan i : ℚ)) ∧
    (∀ n : ℕ, 2 ≤ n →
      -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) n =
        2 / (n : ℚ) * ((3 * n - 3).choose (n - 1) : ℚ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      trudiPartitionSum 1 (fun i => (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) n =
        (generalizedFussCatalanNumber 3 n 1 : ℚ) :=
  ⟨trudi_raney, trudi_catalan_diff, trudi_catalan_shift, trudi_ternary_shift, trudi_ternary⟩

end MetaMathlibExt
