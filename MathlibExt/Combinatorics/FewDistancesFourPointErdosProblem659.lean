/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Real.Irrational

/-!
# Few distinct distances with every four points spanning three (Erdős Problem 659)

We prove that, for each sufficiently large `n`, the plane has an `n`-point set
with few distinct distances and at least three distances among any four of its points.

Erdős Problem 659: is there a set of `n` points in `ℝ²` such that every subset of `4` points
determines at least `3` distances, yet the total number of distinct distances is `≪ n / √(log n)`?

Source: T. F. Bloom, Erdős Problems, Problem #659, https://www.erdosproblems.com/659 (status PROVED
(LEAN)). UnsolvedMath record UM-30006973 (`EP-659`), dataset ulamai/UnsolvedMath v1.8.0.

Points lie in `EuclideanSpace ℝ (Fin 2)` (Euclidean distance). The number of distinct distances is
MathlibExt's `distinctDistances` (`MathlibExt/Geometry/Metric.lean`): the number of values `dist x
y` over pairs `x ≠ y`. "A set of `n` points with `≪ n / √(log n)` distances" is read as: one
constant `C` and, for every sufficiently large `n`, an `n`-point set with at most `C n / √(log n)`
distinct distances satisfying the four-point condition. Compared with the formal-conjectures
statement `ErdosProblems/659.lean` (equivalent; no code imported).
-/

namespace MathlibExt.Combinatorics.FewDistancesFourPointErdosProblem659Wanted

/-! ## The four-point condition for the rectangular lattice -/

private def qdist (a b : ℤ × ℤ) : ℤ :=
  (a.1 - b.1) ^ 2 + 2 * (a.2 - b.2) ^ 2

private lemma qdist_pos {a b : ℤ × ℤ} (hab : a ≠ b) : 0 < qdist a b := by
  have h : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    by_contra! h
    exact hab (Prod.ext h.1 h.2)
  unfold qdist
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (by positivity)
  · exact add_pos_of_nonneg_of_pos (by positivity)
      (mul_pos (by decide) (sq_pos_of_ne_zero (sub_ne_zero.mpr h)))

@[simp] private lemma qdist_self (a : ℤ × ℤ) : qdist a a = 0 := by simp [qdist]

private def parity (a : ℤ × ℤ) : ZMod 2 := a.1

private lemma cast_qdist (a b : ℤ × ℤ) :
    (qdist a b : ZMod 2) = parity a - parity b := by
  simp only [qdist, parity, Int.cast_add, Int.cast_pow, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat]
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul, add_zero]
  generalize (a.1 : ZMod 2) = x, (b.1 : ZMod 2) = y
  decide +revert

private lemma qdist_parity_eq {a b c d : ℤ × ℤ}
    (h : (parity a = parity b) ↔ (parity c = parity d)) :
    (qdist a b : ZMod 2) = (qdist c d : ZMod 2) := by
  rw [cast_qdist, cast_qdist]
  revert h
  generalize parity a = x, parity b = y, parity c = z, parity d = w
  decide +revert

private def halve (a : ℤ × ℤ) : ℤ × ℤ := (a.2, a.1 / 2)

/-- In one parity class, swapping coordinates and halving the even differences scales
squared distances by two. -/
private lemma qdist_halve {a b : ℤ × ℤ} (h : parity a = parity b) :
    qdist a b = 2 * qdist (halve a) (halve b) := by
  have he : (2 : ℤ) ∣ a.1 - b.1 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa [parity] using sub_eq_zero.mpr h)
  have hd : a.1 - b.1 = 2 * (a.1 / 2 - b.1 / 2) := by omega
  simp only [qdist, halve, hd]
  ring

private lemma no_equal_triangle (a b c : ℤ × ℤ) (hab : a ≠ b)
    (h₁ : qdist a b = qdist a c) (h₂ : qdist a b = qdist b c) : False := by
  generalize hn : (qdist a b).toNat = n
  induction n using Nat.strong_induction_on generalizing a b c with
  | ind n ih =>
    have hcast₁ := congrArg (Int.cast (R := ZMod 2)) h₁
    have hcast₂ := congrArg (Int.cast (R := ZMod 2)) h₂
    simp only [cast_qdist] at hcast₁ hcast₂
    have hpar : parity a = parity b ∧ parity a = parity c := by
      revert hcast₁ hcast₂
      generalize parity a = x, parity b = y, parity c = z
      decide +revert
    have e₁ := qdist_halve hpar.1
    have e₂ := qdist_halve hpar.2
    have e₃ := qdist_halve (hpar.1.symm.trans hpar.2)
    have hp := qdist_pos hab
    apply ih (qdist (halve a) (halve b)).toNat (by omega) (a := halve a)
      (b := halve b) (c := halve c)
    · intro he
      rw [he] at e₁
      simp only [qdist_self, mul_zero] at e₁
      omega
    · omega
    · omega
    · rfl

private lemma no_orthogonal_equal (x y u v : ℤ) (hpos : 0 < x ^ 2 + 2 * y ^ 2)
    (hlen : x ^ 2 + 2 * y ^ 2 = u ^ 2 + 2 * v ^ 2) (hdot : x * u + 2 * y * v = 0) :
    False := by
  have hsq : (x ^ 2 + 2 * y ^ 2) ^ 2 = 2 * (x * v - y * u) ^ 2 := by
    calc (x ^ 2 + 2 * y ^ 2) ^ 2 = (x ^ 2 + 2 * y ^ 2) * (u ^ 2 + 2 * v ^ 2) := by
          rw [← hlen, pow_two]
      _ = (x * u + 2 * y * v) ^ 2 + 2 * (x * v - y * u) ^ 2 := by ring
      _ = _ := by rw [hdot]; ring
  obtain ⟨t, ht⟩ : IsSquare (2 : ℚ) := by
    have hdet : x * v - y * u ≠ 0 := by
      intro e
      rw [e] at hsq
      nlinarith
    let t : ℚ := (↑(x ^ 2 + 2 * y ^ 2 : ℤ) : ℚ) / ↑(x * v - y * u)
    refine ⟨t, ?_⟩
    have hh : (↑(x ^ 2 + 2 * y ^ 2 : ℤ) : ℚ) ^ 2 = 2 * (↑(x * v - y * u : ℤ) : ℚ) ^ 2 := by
      exact_mod_cast hsq
    dsimp [t]
    field_simp
    nlinarith
  exact (Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp (show IsSquare ((2 : ℕ) : ℚ) from
    ⟨t, ht⟩)))

private lemma no_equal_cross (a b c d : ℤ × ℤ) (hab : a ≠ b)
    (hdiag : qdist a b = qdist c d)
    (h₁ : qdist a c = qdist a d) (h₂ : qdist a c = qdist b c)
    (h₃ : qdist a c = qdist b d) : False := by
  apply no_orthogonal_equal (a.1 - b.1) (a.2 - b.2) (c.1 - d.1) (c.2 - d.2)
    (qdist_pos hab) hdiag
  unfold qdist at h₁ h₂ h₃
  have hz : 2 * ((a.1 - b.1) * (c.1 - d.1) + 2 * (a.2 - b.2) * (c.2 - d.2)) = 0 := by
    linear_combination h₃ - h₁ - h₂
  omega

/-- Two squared distances on four points would force a monochromatic triangle or two
perpendicular diagonals of equal length after descent through the parity classes. -/
private lemma four_qdist (p : Fin 4 → ℤ × ℤ) (hp : Function.Injective p)
    (r s : ℤ) (h : ∀ i j, i ≠ j → qdist (p i) (p j) = r ∨ qdist (p i) (p j) = s) :
    False := by
  generalize hn : (qdist (p 0) (p 1)).toNat = n
  induction n using Nat.strong_induction_on generalizing p r s with
  | ind n ih =>
    by_cases hall : ∀ i, parity (p i) = parity (p 0)
    · have hhalf (i j : Fin 4) := qdist_halve ((hall i).trans (hall j).symm)
      have h01 := hhalf 0 1
      have hpos := qdist_pos (hp.ne (by decide : (0 : Fin 4) ≠ 1))
      refine ih (qdist (halve (p 0)) (halve (p 1))).toNat (by omega)
        (halve ∘ p) ?_ (r / 2) (s / 2) ?_ rfl
      · intro i j hij
        apply hp
        have e := hhalf i j
        change halve (p i) = halve (p j) at hij
        rw [hij] at e
        by_contra hne
        have := qdist_pos hne
        simp only [qdist_self, mul_zero] at e
        omega
      · intro i j hij
        have e := hhalf i j
        change qdist (halve (p i)) (halve (p j)) = r / 2 ∨
          qdist (halve (p i)) (halve (p j)) = s / 2
        rcases h i j hij with hr | hs
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      have hk0 : k ≠ 0 := by
        intro he
        simp [he] at hk
      have hdiff : (qdist (p k) (p 0) : ZMod 2) ≠ 0 := by rwa [cast_qdist, ne_eq, sub_eq_zero]
      obtain ⟨i, j, hij, heq⟩ : ∃ i j : Fin 4, i ≠ j ∧ parity (p i) = parity (p j) := by
        by_cases h01 : parity (p 0) = parity (p 1)
        · exact ⟨0, 1, by decide, h01⟩
        by_cases h02 : parity (p 0) = parity (p 2)
        · exact ⟨0, 2, by decide, h02⟩
        refine ⟨1, 2, by decide, ?_⟩
        revert h01 h02
        generalize parity (p 0) = x, parity (p 1) = y, parity (p 2) = z
        decide +revert
      have hsame : (qdist (p i) (p j) : ZMod 2) = 0 := by simp [cast_qdist, heq]
      have hrne : (r : ZMod 2) ≠ (s : ZMod 2) := by
        intro e
        apply hdiff
        rcases h i j hij with h₁ | h₁ <;> rcases h k 0 hk0 with h₂ | h₂ <;>
          simp_all
      have eq_of_parity (i₁ j₁ i₂ j₂ : Fin 4) (hne₁ : i₁ ≠ j₁) (hne₂ : i₂ ≠ j₂)
          (he : (parity (p i₁) = parity (p j₁)) ↔ (parity (p i₂) = parity (p j₂))) :
          qdist (p i₁) (p j₁) = qdist (p i₂) (p j₂) := by
        have e := qdist_parity_eq he
        rcases h i₁ j₁ hne₁ with h₁ | h₁ <;> rcases h i₂ j₂ hne₂ with h₂ | h₂ <;>
          simp_all [Ne.symm hrne]
      have triple (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
          (h₁ : parity (p i) = parity (p j)) (h₂ : parity (p i) = parity (p k)) : False :=
        no_equal_triangle (p i) (p j) (p k) (hp.ne hij)
          (eq_of_parity i j i k hij hik (iff_of_true h₁ h₂))
          (eq_of_parity i j j k hij hjk (iff_of_true h₁ (h₁.symm.trans h₂)))
      have pairs (i j k l : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
          (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
          (h₁ : parity (p i) = parity (p j)) (h₂ : parity (p k) = parity (p l))
          (h₃ : parity (p i) ≠ parity (p k)) : False :=
        no_equal_cross (p i) (p j) (p k) (p l) (hp.ne hij)
          (eq_of_parity i j k l hij hkl (by simp [h₁, h₂]))
          (eq_of_parity i k i l hik hil (by simp [← h₂]))
          (eq_of_parity i k j k hik hjk (by simp [← h₁]))
          (eq_of_parity i k j l hik hjl (by simp [← h₁, ← h₂]))
      have classify : ∀ a b c d : ZMod 2,
          (a = b ∧ a = c) ∨ (a = b ∧ a = d) ∨ (a = c ∧ a = d) ∨ (b = c ∧ b = d) ∨
          (a = b ∧ c = d ∧ a ≠ c) ∨ (a = c ∧ b = d ∧ a ≠ b) ∨ (a = d ∧ b = c ∧ a ≠ b) :=
        by decide
      rcases classify (parity (p 0)) (parity (p 1)) (parity (p 2)) (parity (p 3)) with
        ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
        ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
      · exact triple 0 1 2 (by decide) (by decide) (by decide) ha hb
      · exact triple 0 1 3 (by decide) (by decide) (by decide) ha hb
      · exact triple 0 2 3 (by decide) (by decide) (by decide) ha hb
      · exact triple 1 2 3 (by decide) (by decide) (by decide) ha hb
      · exact pairs 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) ha hb hc
      · exact pairs 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) ha hb hc
      · exact pairs 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) ha hb hc

private noncomputable def latticePoint (a : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(a.1 : ℝ), (a.2 : ℝ) * Real.sqrt 2]

private lemma latticePoint_dist_sq (a b : ℤ × ℤ) :
    dist (latticePoint a) (latticePoint b) ^ 2 = (qdist a b : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [latticePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.dist_eq, sq_abs, qdist, Int.cast_add, Int.cast_pow, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat]
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    _ = ((a.1 : ℝ) - (b.1 : ℝ)) ^ 2 + ((a.2 : ℝ) - (b.2 : ℝ)) ^ 2 * (Real.sqrt 2) ^ 2 := by
      ring
    _ = _ := by rw [hsq]; ring

private lemma latticePoint_injective : Function.Injective latticePoint := by
  intro a b he
  by_contra hne
  have hpos := qdist_pos hne
  have hsq := latticePoint_dist_sq a b
  rw [he, dist_self, zero_pow (by decide : 2 ≠ 0)] at hsq
  exact (ne_of_gt (Int.cast_pos.mpr hpos : 0 < (qdist a b : ℝ))) hsq.symm

private lemma dist_mem_distanceSet {X : Type*} [MetricSpace X] {S : Finset X} {a b : X}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : dist a b ∈ distanceSet S := by
  classical
  exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩

private lemma lattice_four_point {S : Finset (EuclideanSpace ℝ (Fin 2))} (hcard : S.card = 4)
    (hS : ∀ x ∈ S, ∃ a, latticePoint a = x) : 3 ≤ distinctDistances S := by
  classical
  let e := (S.equivFinOfCardEq hcard).symm
  choose p hp using fun i : Fin 4 => hS (e i) (e i).property
  have hinj : Function.Injective p := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    rw [← hp i, ← hp j, hij]
  have hdist (i j : Fin 4) (hij : i ≠ j) :
      dist (latticePoint (p i)) (latticePoint (p j)) ∈ distanceSet S := by
    rw [hp, hp]
    exact dist_mem_distanceSet (e i).property (e j).property
      (fun h => hij (e.injective (Subtype.ext h)))
  by_contra! hSmall
  change (distanceSet S).card < 3 at hSmall
  have hpos : 0 < (distanceSet S).card := Finset.card_pos.mpr
    ⟨_, hdist 0 1 (by decide)⟩
  obtain ⟨r, s, hcover⟩ : ∃ r s : ℝ, ∀ d ∈ distanceSet S, d = r ∨ d = s := by
    rcases (show (distanceSet S).card = 1 ∨ (distanceSet S).card = 2 by omega) with h | h
    · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
      exact ⟨r, r, by simp [hr]⟩
    · obtain ⟨r, s, _, hrs⟩ := Finset.card_eq_two.mp h
      exact ⟨r, s, by simp [hrs]⟩
  apply four_qdist p hinj ⌊r ^ 2⌋ ⌊s ^ 2⌋
  intro i j hij
  have hsquare := congrArg Int.floor (latticePoint_dist_sq (p i) (p j))
  simp only [Int.floor_intCast] at hsquare
  rcases hcover _ (hdist i j hij) with h | h
  · exact Or.inl (by simpa [h] using hsquare.symm)
  · exact Or.inr (by simpa [h] using hsquare.symm)

/-! ## Counting positive values of the quadratic form -/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.zeta

private def chi (n : ℕ) : ℤ := ZMod.χ₈' (n : ZMod 8)

private def good (p : ℕ) : Prop := chi p = 1

attribute [local instance] Classical.propDecidable

/-- The indicator of positive integers all of whose prime factors split. -/
private noncomputable def splitIndicator : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, good p then 1 else 0, by simp⟩

private lemma splitIndicator_nonneg (n : ℕ) : 0 ≤ splitIndicator n := by
  change 0 ≤ ite _ (1 : ℝ) 0
  split <;> norm_num

private lemma splitIndicator_le_one (n : ℕ) : splitIndicator n ≤ 1 := by
  change ite _ (1 : ℝ) 0 ≤ 1
  split <;> norm_num

private lemma splitIndicator_mul (m n : ℕ) :
    splitIndicator (m * n) = splitIndicator m * splitIndicator n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [splitIndicator, ArithmeticFunction.coe_mk, ne_eq, hm, hn, mul_eq_zero,
    or_self, not_false_eq_true, true_and, Nat.primeFactors_mul hm hn, Finset.mem_union,
    or_imp, forall_and]
  split <;> split <;> split <;> simp_all

private lemma splitIndicator_multiplicative : splitIndicator.IsMultiplicative :=
  ⟨by simp [splitIndicator, Nat.not_prime_one], fun {m n} _ => splitIndicator_mul m n⟩

private lemma splitIndicator_prime {p : ℕ} (hp : p.Prime) :
    splitIndicator p = if good p then 1 else 0 := by
  simp only [splitIndicator, ArithmeticFunction.coe_mk, hp.ne_zero, ne_eq, not_false_eq_true,
    true_and, hp.primeFactors, Finset.mem_singleton, forall_eq]

private lemma splitIndicator_pow (p k : ℕ) :
    splitIndicator (p ^ k) = splitIndicator p ^ k := by
  induction k with
  | zero => simp [splitIndicator_multiplicative.map_one]
  | succ k ih => rw [pow_succ, splitIndicator_mul, ih, pow_succ]

private lemma chi_zero : chi 0 = 0 := by decide

private lemma chi_one : chi 1 = 1 := by decide

private lemma chi_mul (a b : ℕ) : chi (a * b) = chi a * chi b := by
  simp [chi, map_mul]

private lemma chi_pow (a k : ℕ) : chi (a ^ k) = chi a ^ k := by
  simp [chi, map_pow]

private lemma chi_values (a : ℕ) : chi a = 0 ∨ chi a = 1 ∨ chi a = -1 := by
  unfold chi
  generalize (a : ZMod 8) = d
  decide +revert

private lemma chi_add_eight (a : ℕ) : chi (a + 8) = chi a := by
  simp [chi, Nat.cast_add, show (8 : ZMod 8) = 0 by decide]

private lemma chi_partial (N : ℕ) : ∑ i ∈ range N, chi (i + 1) ≤ 2 := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N < 8
    · interval_cases N <;> decide
    · obtain ⟨M, rfl⟩ : ∃ M, N = 8 + M := ⟨N - 8, by omega⟩
      rw [Finset.sum_range_add]
      have h8 : ∑ i ∈ range 8, chi (i + 1) = 0 := by decide
      rw [h8, zero_add]
      simpa only [show ∀ j : ℕ, 8 + j + 1 = (j + 1) + 8 by omega, chi_add_eight] using
        ih M (by omega)

-- Partial summation uses the upper bound 2 for the unweighted character sums.
private lemma chi_reciprocal_bound (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (chi n : ℝ) / (n : ℝ) ≤ 2 := by
  have aux (M : ℕ) : (∑ i ∈ range M, (chi (i + 1) : ℝ) / ((i : ℝ) + 1)) ≤
      2 - (2 - ∑ i ∈ range M, (chi (i + 1) : ℝ)) / ((M : ℝ) + 1) := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      push_cast
      simp only [Finset.sum_range_succ]
      have h : 0 ≤ 2 - ((∑ i ∈ range M, (chi (i + 1) : ℝ)) + (chi (M + 1) : ℝ)) := by
        have hM := chi_partial (M + 1)
        rw [Finset.sum_range_succ] at hM
        exact sub_nonneg.mpr (by exact_mod_cast hM)
      have hden : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      have hstep := div_le_div_of_nonneg_left h hden
        (show (M : ℝ) + 1 ≤ (M : ℝ) + 1 + 1 by linarith)
      simp only [sub_add_eq_sub_sub, sub_div] at hstep ih ⊢
      linarith
  have hchange : ∑ i ∈ Ioc 0 N, (chi i : ℝ) / (i : ℝ) =
      ∑ i ∈ range N, (chi (i + 1) : ℝ) / ((i : ℝ) + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_range_succ, ih, Nat.cast_succ]
  have hsum : 0 ≤ 2 - ∑ i ∈ range N, (chi (i + 1) : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast chi_partial N)
  exact hchange ▸ (aux N).trans (sub_le_self _ (div_nonneg hsum (by positivity)))

private noncomputable def chiArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => (chi n : ℝ), by simp [chi_zero]⟩

private lemma chiArithmetic_multiplicative : chiArithmetic.IsMultiplicative :=
  ⟨by simp [chiArithmetic, chi_one], fun {m n} _ => by simp [chiArithmetic, chi_mul]⟩

private noncomputable def divisorCharacter : ArithmeticFunction ℝ :=
  chiArithmetic * (ζ : ArithmeticFunction ℝ)

private lemma divisorCharacter_multiplicative : divisorCharacter.IsMultiplicative :=
  chiArithmetic_multiplicative.mul isMultiplicative_zeta.natCast

private lemma divisorCharacter_prime_pow {p k : ℕ} (hp : p.Prime) :
    divisorCharacter (p ^ k) = ∑ i ∈ range (k + 1), (chi p : ℝ) ^ i := by
  rw [divisorCharacter, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  simp [chiArithmetic, chi_pow]

private lemma split_conv_le (n : ℕ) : (splitIndicator * splitIndicator) n ≤ divisorCharacter n := by
  have hnonneg (m : ℕ) : 0 ≤ (splitIndicator * splitIndicator) m := by
    rw [ArithmeticFunction.mul_apply]
    exact Finset.sum_nonneg fun _ _ =>
      mul_nonneg (splitIndicator_nonneg _) (splitIndicator_nonneg _)
  apply Nat.recOnPrimeCoprime (motive := fun n =>
    (splitIndicator * splitIndicator) n ≤ divisorCharacter n) ?_ ?_ ?_ n
  · simp
  · intro p k hp
    have heq : (splitIndicator * splitIndicator) (p ^ k) =
        ∑ i ∈ (p ^ k).divisorsAntidiagonal, splitIndicator (p ^ k) := by
      rw [ArithmeticFunction.mul_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← splitIndicator_mul, (Nat.mem_divisorsAntidiagonal.mp hi).1]
    rw [heq, Nat.sum_divisorsAntidiagonal (fun _ _ => splitIndicator (p ^ k)),
      Nat.sum_divisors_prime_pow hp, divisorCharacter_prime_pow hp,
      splitIndicator_pow, splitIndicator_prime hp]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    by_cases hg : good p
    · simp [hg, show chi p = 1 from hg]
    · cases k with
      | zero => simp
      | succ k =>
        simp only [hg, ite_false, zero_pow (Nat.succ_ne_zero _), mul_zero]
        rcases chi_values p with h | h | h
        · simp [h, Finset.sum_range_succ']
        · exact (hg h).elim
        · rw [h]
          push_cast
          have hsum (j : ℕ) : (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i) = if Even j then 1 else 0 := by
            induction j with
            | zero => simp
            | succ j ih =>
              rw [Finset.sum_range_succ']
              simp_rw [pow_succ]
              rw [← Finset.sum_mul, ih]
              have he : Even (j + 1) ↔ ¬ Even j := by
                simp only [Nat.even_iff]
                omega
              by_cases hj : Even j <;> simp [he, hj]
          rw [hsum]
          split <;> norm_num
  · intro a b _ _ hc ha hb
    rw [(splitIndicator_multiplicative.mul splitIndicator_multiplicative).map_mul_of_coprime hc,
      divisorCharacter_multiplicative.map_mul_of_coprime hc]
    exact mul_le_mul ha hb (hnonneg _) ((hnonneg _).trans ha)

private noncomputable def reciprocal (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / (n : ℝ), by simp⟩

private lemma reciprocal_mul (f g : ArithmeticFunction ℝ) :
    reciprocal (f * g) = reciprocal f * reciprocal g := by
  ext n
  change (f * g) n / (n : ℝ) = _
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  change f x.1 * g x.2 / (n : ℝ) = (f x.1 / (x.1 : ℝ)) * (g x.2 / (x.2 : ℝ))
  have h := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rw [← h, Nat.cast_mul]
  ring

private lemma reciprocal_zeta_apply {n : ℕ} (hn : n ≠ 0) :
    reciprocal (ζ : ArithmeticFunction ℝ) n = (n : ℝ)⁻¹ := by
  simp [reciprocal, hn]

private lemma harmonic_zeta_upper (N : ℕ) :
    ∑ n ∈ Ioc 0 N, reciprocal divisorCharacter n ≤ 2 * (1 + Real.log (N : ℝ)) := by
  rw [divisorCharacter, mul_comm, reciprocal_mul, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ * 2 := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [reciprocal_zeta_apply (Finset.mem_Ioc.mp hn).1.ne']
      exact mul_le_mul_of_nonneg_left (chi_reciprocal_bound _) (by positivity)
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.sum_mul, mul_comm 2, harmonic_eq_sum_Icc]
      push_cast
      congr 2
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by norm_num)

-- Products of two integers at most N lie below N², where the divisor-character sum
-- bounds the squared reciprocal sum.
private lemma harmonic_split_upper (N : ℕ) :
    ∑ n ∈ Ioc 0 N, reciprocal splitIndicator n ≤ Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ))) := by
  have hnonneg (m : ℕ) : 0 ≤ reciprocal splitIndicator m :=
    div_nonneg (splitIndicator_nonneg m) (Nat.cast_nonneg m)
  have hsubset : Ioc 0 N ×ˢ Ioc 0 N ⊆
      (Ioc 0 (N ^ 2) ×ˢ Ioc 0 (N ^ 2)).filter (fun x => x.1 * x.2 ≤ N ^ 2) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc] at hx ⊢
    have hN2 : N ≤ N ^ 2 := by simpa [pow_two] using Nat.le_mul_self N
    exact ⟨⟨⟨hx.1.1, hx.1.2.trans hN2⟩, ⟨hx.2.1, hx.2.2.trans hN2⟩⟩,
      by simpa [pow_two] using Nat.mul_le_mul hx.1.2 hx.2.2⟩
  have hprod : (∑ n ∈ Ioc 0 N, reciprocal splitIndicator n) ^ 2 ≤
      ∑ n ∈ Ioc 0 (N ^ 2), reciprocal (splitIndicator * splitIndicator) n := by
    rw [pow_two, reciprocal_mul, ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter,
      Finset.sum_mul_sum, ← Finset.sum_product']
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun x _ _ =>
      mul_nonneg (hnonneg x.1) (hnonneg x.2)
  have hle : ∑ n ∈ Ioc 0 (N ^ 2), reciprocal (splitIndicator * splitIndicator) n ≤
      ∑ n ∈ Ioc 0 (N ^ 2), reciprocal divisorCharacter n :=
    Finset.sum_le_sum fun n _ => div_le_div_of_nonneg_right (split_conv_le n) (Nat.cast_nonneg _)
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ ∑ n ∈ Ioc 0 (N ^ 2), reciprocal divisorCharacter n := hprod.trans hle
    _ ≤ _ := by
      have h := harmonic_zeta_upper (N ^ 2)
      rw [show ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ (2 : ℕ) by norm_cast, Real.log_pow] at h
      exact h

private noncomputable def splitMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => ArithmeticFunction.vonMangoldt n * splitIndicator n, by simp⟩

-- The von Mangoldt identity converts the reciprocal estimate into a counting bound.
private lemma split_log_eq (n : ℕ) :
    splitIndicator n * Real.log n = (splitIndicator * splitMangoldt) n := by
  rw [ArithmeticFunction.mul_apply]
  have hterm : ∀ x ∈ n.divisorsAntidiagonal,
      splitIndicator x.1 * splitMangoldt x.2 =
        splitIndicator n * ArithmeticFunction.vonMangoldt x.2 := by
    intro x hx
    change splitIndicator x.1 * (ArithmeticFunction.vonMangoldt x.2 * splitIndicator x.2) = _
    rw [mul_comm (ArithmeticFunction.vonMangoldt x.2), ← mul_assoc, ← splitIndicator_mul,
      (Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Nat.sum_divisorsAntidiagonal' (fun _ d => ArithmeticFunction.vonMangoldt d),
    ArithmeticFunction.vonMangoldt_sum]

private lemma split_log_upper {K N : ℕ} (hKN : K ≤ N) :
    ∑ n ∈ Ioc 0 K, splitIndicator n * Real.log n ≤
      (Real.log 4 + 4) * K * Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ))) := by
  simp_rw [split_log_eq]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  calc
    _ ≤ ∑ n ∈ Ioc 0 K, splitIndicator n * ((Real.log 4 + 4) * (K / n : ℕ)) := by
      refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (splitIndicator_nonneg _)
      have hle : ∑ m ∈ Ioc 0 (K / n), splitMangoldt m ≤
          ∑ m ∈ Ioc 0 (K / n), ArithmeticFunction.vonMangoldt m := by
        refine Finset.sum_le_sum fun m _ => ?_
        change ArithmeticFunction.vonMangoldt m * splitIndicator m ≤
          ArithmeticFunction.vonMangoldt m
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (splitIndicator_le_one m) (ArithmeticFunction.vonMangoldt_nonneg)
      refine hle.trans ?_
      have hpsi (k : ℕ) : Chebyshev.psi k = ∑ m ∈ Ioc 0 k, ArithmeticFunction.vonMangoldt m := by
        rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Finset.Icc_eq_cons_Ioc (Nat.zero_le k),
          Finset.sum_cons]
        simp
      rw [← hpsi]
      exact Chebyshev.psi_le_const_mul_self (by positivity)
    _ ≤ ∑ n ∈ Ioc 0 K, (Real.log 4 + 4) * K * reciprocal splitIndicator n := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
      have hbound : ((K / n : ℕ) : ℝ) ≤ (K : ℝ) / (n : ℝ) := by
        apply (le_div_iff₀ hn0).mpr
        exact_mod_cast Nat.div_mul_le_self K n
      calc
        _ ≤ splitIndicator n * ((Real.log 4 + 4) * ((K : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by positivity))
            (splitIndicator_nonneg _)
        _ = _ := by change _ = _ * (splitIndicator n / (n : ℝ)); ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ioc_subset_Ioc_right hKN) (fun n _ _ =>
          div_nonneg (splitIndicator_nonneg n) (Nat.cast_nonneg _))).trans
        (harmonic_split_upper N)) (by positivity)

private lemma prime_dvd_coordinates {p x y : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (hb : ¬ good p) (hd : p ∣ x ^ 2 + 2 * y ^ 2) : p ∣ x ∧ p ∣ y := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hzero : (x : ZMod p) ^ 2 + 2 * (y : ZMod p) ^ 2 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (x ^ 2 + 2 * y ^ 2) p).mpr hd
  have hy : (y : ZMod p) = 0 := by
    by_contra hy
    apply hb
    have hsq : IsSquare (-2 : ZMod p) := by
      refine ⟨(x : ZMod p) / y, ?_⟩
      rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero _ hy)]
      linear_combination -hzero
    have hmod := (ZMod.exists_sq_eq_neg_two_iff hp₂).mp hsq
    have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp₂
    unfold good chi
    rw [ZMod.χ₈'_nat_eq_if_mod_eight]
    simp [hmod, hodd]
  have hx : (x : ZMod p) = 0 := by
    simpa [hy] using hzero
  exact ⟨(ZMod.natCast_eq_zero_iff x p).mp hx, (ZMod.natCast_eq_zero_iff y p).mp hy⟩

/-- Every positive value of the form is a split integer times a square or twice a square. -/
private lemma norm_factor (m : ℕ) (hm : 0 < m) (hq : ∃ x y : ℕ, m = x ^ 2 + 2 * y ^ 2) :
    ∃ d u : ℕ, 0 < d ∧ splitIndicator u = 1 ∧ (m = d ^ 2 * u ∨ m = 2 * d ^ 2 * u) := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hall : ∀ p ∈ m.primeFactors, good p
    · refine ⟨1, m, by decide, ?_, Or.inl (by simp)⟩
      change (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, good p then (1 : ℝ) else 0) = 1
      exact ite_eq_left ⟨hm.ne', hall⟩
    · push Not at hall
      obtain ⟨p, hp, hb⟩ := hall
      have hprime := Nat.prime_of_mem_primeFactors hp
      obtain ⟨x, y, hxy⟩ := hq
      have hd := Nat.dvd_of_mem_primeFactors hp
      rw [hxy] at hd
      have reduce (hx : p ∣ x) (hy : p ∣ y) :
          ∃ d u : ℕ, 0 < d ∧ splitIndicator u = 1 ∧ (m = d ^ 2 * u ∨ m = 2 * d ^ 2 * u) := by
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        let m' := x' ^ 2 + 2 * y' ^ 2
        have he : m = p ^ 2 * m' := by rw [hxy]; dsimp [m']; ring
        have hm' : 0 < m' := by
          by_contra! h
          have hzero : m' = 0 := by omega
          simp [hzero] at he
          omega
        have hp' : 1 < p ^ 2 := one_lt_pow₀ hprime.one_lt (by decide)
        have hlt : m' < m := by
          rw [he]
          simpa using Nat.mul_lt_mul_of_pos_right hp' hm'
        obtain ⟨d, u, hdp, hu, h | h⟩ := ih m' hlt hm' ⟨x', y', rfl⟩
        · exact ⟨p * d, u, Nat.mul_pos hprime.pos hdp, hu, Or.inl (by rw [he, h]; ring)⟩
        · exact ⟨p * d, u, Nat.mul_pos hprime.pos hdp, hu, Or.inr (by rw [he, h]; ring)⟩
      by_cases hp₂ : p = 2
      · subst p
        have hx : 2 ∣ x := by
          have hpow : 2 ∣ x ^ 2 := by
            exact (Nat.dvd_add_iff_left (dvd_mul_right 2 (y ^ 2))).mpr hd
          exact Nat.prime_two.dvd_of_dvd_pow hpow
        by_cases hy : 2 ∣ y
        · exact reduce hx hy
        obtain ⟨x', hx'⟩ := hx
        let m' : ℕ := y ^ 2 + 2 * x' ^ 2
        have hdouble : m = 2 * m' := by rw [hxy, hx']; dsimp [m']; ring
        have hm' : 0 < m' := by omega
        obtain ⟨d, u, hd, hu, h | h⟩ := ih m' (by omega) hm' ⟨y, x', rfl⟩
        · exact ⟨d, u, hd, hu, Or.inr (by rw [hdouble, h]; ring)⟩
        · have hpow : 2 ∣ y ^ 2 := by
            exact (Nat.dvd_add_iff_left (dvd_mul_right 2 (x' ^ 2))).mpr
              (show 2 ∣ m' from ⟨d ^ 2 * u, by rw [h]; ring⟩)
          exact (hy (Nat.prime_two.dvd_of_dvd_pow hpow)).elim
      · obtain ⟨hx, hy⟩ := prime_dvd_coordinates hprime hp₂ hb hd
        exact reduce hx hy

private def squareScale (n : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ (n = d ^ 2 ∨ n = 2 * d ^ 2)

private noncomputable def squareIndicator : ArithmeticFunction ℝ :=
  ⟨fun n => if squareScale n then 1 else 0, by
    apply ite_eq_right
    rintro ⟨d, hd, h | h⟩ <;> have : 0 < d ^ 2 := pow_pos hd _ <;> omega⟩

private lemma squareIndicator_nonneg (n : ℕ) : 0 ≤ squareIndicator n := by
  change 0 ≤ ite _ (1 : ℝ) 0
  split <;> norm_num

private lemma squareIndicator_sum_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, squareIndicator n * F n ≤
      ∑ d ∈ Ioc 0 N, (F (d ^ 2) + F (2 * d ^ 2)) := by
  let A := (Ioc 0 N).image fun d => d ^ 2
  let B := (Ioc 0 N).image fun d => 2 * d ^ 2
  have hsubset : (Ioc 0 N).filter squareScale ⊆ A ∪ B := by
    intro n hn
    obtain ⟨hn, d, hd, hr⟩ := Finset.mem_filter.mp hn
    have hN : n ≤ N := (Finset.mem_Ioc.mp hn).2
    have hle : d ≤ d ^ 2 := by simpa [pow_two] using Nat.le_mul_self d
    rcases hr with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d,
        Finset.mem_Ioc.mpr ⟨hd, hle.trans (h ▸ hN)⟩, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, Finset.mem_Ioc.mpr
        ⟨hd, hle.trans (by omega)⟩, h.symm⟩)
  have hsum : ∑ n ∈ Ioc 0 N, squareIndicator n * F n =
      ∑ n ∈ (Ioc 0 N).filter squareScale, F n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    change (if squareScale n then (1 : ℝ) else 0) * F n = _
    split <;> simp
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ A ∪ B, F n := Finset.sum_le_sum_of_subset_of_nonneg hsubset fun n _ _ => hF n
    _ ≤ (∑ n ∈ A, F n) + ∑ n ∈ B, F n := by
      have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := F)
      have hi : 0 ≤ ∑ n ∈ A ∩ B, F n := Finset.sum_nonneg fun n _ => hF n
      linarith
    _ = _ := by
      dsimp only [A, B]
      rw [Finset.sum_image (Nat.pow_left_injective (by decide : 2 ≠ 0)).injOn,
        Finset.sum_image, Finset.sum_add_distrib]
      intro a _ b _ hab
      change 2 * a ^ 2 = 2 * b ^ 2 at hab
      have he : a ^ 2 = b ^ 2 := by omega
      exact Nat.pow_left_injective (by decide : 2 ≠ 0) he

-- Squares and twice squares have bounded reciprocal and logarithmic reciprocal sums.
private lemma squareIndicator_harmonic_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      (∑ n ∈ Ioc 0 N, squareIndicator n / (n : ℝ)) ≤ B ∧
      (∑ n ∈ Ioc 0 N, squareIndicator n * Real.log n / (n : ℝ)) ≤ B := by
  let F (n : ℕ) : ℝ := (1 + Real.log n) / (n : ℝ)
  have hlog (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  have hF (n : ℕ) : 0 ≤ F n := div_nonneg (by linarith [hlog n]) (by positivity)
  have hpow (a d : ℕ) (ha : 1 ≤ a) (hd : 0 < d) :
      F (a * d ^ 2) ≤ 5 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hd₁ : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have ha₁ : 1 ≤ (a : ℝ) := by exact_mod_cast ha
    let x := (a : ℝ) * (d : ℝ) ^ 2
    have hx₁ : 1 ≤ x := by dsimp [x]; exact one_le_mul_of_one_le_of_one_le ha₁ (one_le_pow₀ hd₁)
    have hx : 0 < x := zero_lt_one.trans_le hx₁
    have hle : (d : ℝ) ^ (2 : ℕ) ≤ x := by
      dsimp [x]
      exact le_mul_of_one_le_left (by positivity) ha₁
    have hquarter : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx₁ (by norm_num)
    have hlogx := Real.log_le_self (show 0 ≤ x ^ (1 / 4 : ℝ) by positivity)
    rw [Real.log_rpow hx] at hlogx
    have hFle : F (a * d ^ 2) ≤ 5 * x ^ (1 / 4 : ℝ) / x := by
      change (1 + Real.log ((a * d ^ 2 : ℕ) : ℝ)) / ((a * d ^ 2 : ℕ) : ℝ) ≤ _
      push_cast
      change (1 + Real.log x) / x ≤ _
      exact div_le_div_of_nonneg_right (by linarith) hx.le
    refine hFle.trans ?_
    rw [mul_div_assoc, ← Real.rpow_sub_one hx.ne', show (1 / 4 : ℝ) - 1 = -(3 / 4) by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ((d : ℝ) ^ (2 : ℕ)) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ d)]
        norm_num
  let f (d : ℕ) : ℝ := (d : ℝ) ^ (-(3 / 2 : ℝ))
  have hf : Summable f := Real.summable_nat_rpow.mpr (by norm_num)
  let B := 10 * ∑' d : ℕ, f d
  refine ⟨B, mul_nonneg (by norm_num) (tsum_nonneg fun d => by positivity), fun N => ?_⟩
  have hb : ∑ n ∈ Ioc 0 N, squareIndicator n * F n ≤ B := by
    refine (squareIndicator_sum_le F hF N).trans ?_
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, 10 * f d := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hpos := (Finset.mem_Ioc.mp hd).1
        have h₁ := hpow 1 d (by decide) hpos
        rw [one_mul] at h₁
        change F (d ^ 2) ≤ 5 * f d at h₁
        have h₂ := hpow 2 d (by decide) hpos
        change F (2 * d ^ 2) ≤ 5 * f d at h₂
        linarith
      _ ≤ B := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hf.sum_le_tsum _ (fun d _ => by positivity)) (by norm_num)
  constructor
  · refine (Finset.sum_le_sum fun n _ => ?_).trans hb
    dsimp only [F]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (show 1 ≤ 1 + Real.log (n : ℝ) by linarith [hlog n])
        (squareIndicator_nonneg n)
  · refine (Finset.sum_le_sum fun n _ => ?_).trans hb
    dsimp only [F]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (squareIndicator_nonneg n)

private noncomputable def logWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log n, by simp⟩

private lemma logWeight_mul (f g : ArithmeticFunction ℝ) :
    logWeight (f * g) = f * logWeight g + logWeight f * g := by
  ext n
  change (f * g) n * Real.log n = (f * logWeight g) n + (logWeight f * g) n
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hx₁ : x.1 ≠ 0 := left_ne_zero_of_mul (hprod ▸ hn)
  have hx₂ : x.2 ≠ 0 := right_ne_zero_of_mul (hprod ▸ hn)
  change _ = f x.1 * (g x.2 * Real.log x.2) + (f x.1 * Real.log x.1) * g x.2
  rw [← hprod, Nat.cast_mul, Real.log_mul (by exact_mod_cast hx₁) (by exact_mod_cast hx₂)]
  ring

private lemma square_split_log_upper :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ Real.log (N : ℝ) →
      ∑ n ∈ Ioc 0 N, logWeight (squareIndicator * splitIndicator) n ≤
        D * N * Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := squareIndicator_harmonic_bound
  let D := B * ((Real.log 4 + 4) * Real.sqrt 6 + 1)
  refine ⟨D, by dsimp [D]; positivity, fun N hN => ?_⟩
  have hlog (n : ℕ) (hn : n ∈ Ioc 0 N) : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_Ioc.mp hn).1)
  have hfirst : ∑ n ∈ Ioc 0 N, (squareIndicator * logWeight splitIndicator) n ≤
      (Real.log 4 + 4) * N * Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ))) * B := by
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, ((Real.log 4 + 4) * N *
          Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ)))) * (squareIndicator n / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hs := split_log_upper (Nat.div_le_self N n)
        calc
          _ ≤ squareIndicator n * ((Real.log 4 + 4) * (N / n : ℕ) *
              Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ)))) :=
            mul_le_mul_of_nonneg_left hs (squareIndicator_nonneg n)
          _ ≤ squareIndicator n * ((Real.log 4 + 4) * ((N : ℝ) / n) *
              Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (squareIndicator_nonneg n)
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
          _ = _ := by ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hb N).1 (by positivity)
  have hsecond : ∑ n ∈ Ioc 0 N, (logWeight squareIndicator * splitIndicator) n ≤ (N : ℝ) * B := by
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, (N : ℝ) * (squareIndicator n * Real.log n / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hsum : ∑ m ∈ Ioc 0 (N / n), splitIndicator m ≤ ((N / n : ℕ) : ℝ) := by
          simpa using Finset.sum_le_sum (s := Ioc 0 (N / n)) (fun m _ => splitIndicator_le_one m)
        have hnon : 0 ≤ logWeight squareIndicator n :=
          mul_nonneg (squareIndicator_nonneg _) (hlog n hn)
        calc
          _ ≤ logWeight squareIndicator n * ((N : ℝ) / n) :=
            mul_le_mul_of_nonneg_left (hsum.trans Nat.cast_div_le) hnon
          _ = _ := by change (squareIndicator n * Real.log n) * _ = _; ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hb N).2 (by positivity)
  have hroot : Real.sqrt (2 * (1 + 2 * Real.log (N : ℝ))) ≤
      Real.sqrt 6 * Real.sqrt (Real.log (N : ℝ)) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hroot₁ : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hN
  rw [logWeight_mul]
  change (∑ n ∈ Ioc 0 N, ((squareIndicator * logWeight splitIndicator) n +
    (logWeight squareIndicator * splitIndicator) n)) ≤ _
  rw [Finset.sum_add_distrib]
  refine (add_le_add hfirst hsecond).trans ?_
  calc
    _ ≤ (Real.log 4 + 4) * N * (Real.sqrt 6 * Real.sqrt (Real.log (N : ℝ))) * B +
        (N : ℝ) * Real.sqrt (Real.log (N : ℝ)) * B := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hroot₁ (Nat.cast_nonneg N)
    _ = _ := by dsimp [D]; ring

private noncomputable def normValues (N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => ∃ x y : ℕ, n = x ^ 2 + 2 * y ^ 2

private lemma square_split_nonneg (n : ℕ) : 0 ≤ (squareIndicator * splitIndicator) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun d _ => mul_nonneg (squareIndicator_nonneg _) (splitIndicator_nonneg _)

private lemma one_le_square_split {N n : ℕ} (hn : n ∈ normValues N) :
    1 ≤ (squareIndicator * splitIndicator) n := by
  obtain ⟨hn, hrep⟩ := Finset.mem_filter.mp hn
  have hn0 := (Finset.mem_Ioc.mp hn).1
  obtain ⟨d, u, hd, hu, h⟩ := norm_factor n hn0 hrep
  obtain ⟨a, ha, hm⟩ : ∃ a, squareScale a ∧ a * u = n := by
    rcases h with h | h
    · exact ⟨d ^ 2, ⟨d, hd, Or.inl rfl⟩, h.symm⟩
    · exact ⟨2 * d ^ 2, ⟨d, hd, Or.inr rfl⟩, h.symm⟩
  have hterm : (a, u) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hm, hn0.ne'⟩
  rw [ArithmeticFunction.mul_apply]
  have ha1 : squareIndicator a = 1 := by
    change (if squareScale a then (1 : ℝ) else 0) = 1
    exact ite_eq_left ha
  simpa only [hu, ha1, mul_one] using
    Finset.single_le_sum (s := n.divisorsAntidiagonal)
      (f := fun d : ℕ × ℕ => squareIndicator d.1 * splitIndicator d.2)
      (fun d _ => mul_nonneg (squareIndicator_nonneg _) (splitIndicator_nonneg _)) hterm

private lemma normValues_card_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ Real.log (N : ℝ) →
      ((normValues N).card : ℝ) ≤ C * N / Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := square_split_log_upper
  refine ⟨1 + 2 * D, by positivity, fun N hN => ?_⟩
  have hlog (n : ℕ) (hn : n ∈ Ioc 0 N) : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_Ioc.mp hn).1)
  have hsub : normValues N ⊆ Ioc 0 N := Finset.filter_subset _ _
  let large := (normValues N).filter (N.sqrt < ·)
  have hlarge : ∑ n ∈ large, Real.log n ≤ D * N * Real.sqrt (Real.log (N : ℝ)) := by
    refine (Finset.sum_le_sum fun n hn => ?_).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.filter_subset _ _).trans hsub) (fun n hn _ =>
          mul_nonneg (square_split_nonneg _) (hlog n hn))).trans (hbound N hN))
    have hn' := (Finset.mem_filter.mp hn).1
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (one_le_square_split hn') (hlog n (hsub hn'))
  have hlarge_card : (large.card : ℝ) * (Real.log (N : ℝ) / 2) ≤
      D * N * Real.sqrt (Real.log (N : ℝ)) := by
    refine (le_trans ?_ hlarge)
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    have hlt : N < n ^ 2 := Nat.sqrt_lt'.mp (Finset.mem_filter.mp hn).2
    have hNpos : 0 < (N : ℝ) := by
      by_contra! h
      have hz : N = 0 := by exact_mod_cast (le_antisymm h (Nat.cast_nonneg N))
      norm_num [hz] at hN
    have hh := Real.log_le_log hNpos (by exact_mod_cast hlt.le : (N : ℝ) ≤ (n : ℝ) ^ (2 : ℕ))
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hsmall_card : ((normValues N).filter (fun n => ¬N.sqrt < n)).card ≤ N.sqrt := by
    calc
      _ ≤ (Ioc 0 N.sqrt).card := by
        apply Finset.card_le_card
        intro n hn
        obtain ⟨hn, hsmall⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp (hsub hn)).1, le_of_not_gt hsmall⟩
      _ = _ := by simp
  have hcard : ((normValues N).card : ℝ) ≤ (large.card : ℝ) + (N.sqrt : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (s := normValues N) (p := (N.sqrt < ·))
    exact_mod_cast h.symm.trans_le (Nat.add_le_add_left hsmall_card _)
  have hroot : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos_of_pos (by linarith)
  have hroot_sq : Real.sqrt (Real.log (N : ℝ)) ^ 2 = Real.log (N : ℝ) :=
    Real.sq_sqrt (by linarith)
  have hl : (large.card : ℝ) ≤ 2 * D * N / Real.sqrt (Real.log (N : ℝ)) := by
    apply (le_div_iff₀ hroot).mpr
    apply le_of_mul_le_mul_right _ hroot
    nlinarith [hroot_sq, hlarge_card]
  have hsqrtN : (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
  have hs : (N.sqrt : ℝ) ≤ (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
    apply (le_div_iff₀ hroot).mpr
    calc
      _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
        mul_le_mul hsqrtN (Real.sqrt_le_sqrt (Real.log_le_self (by positivity))) hroot.le
          (by positivity)
      _ = _ := Real.mul_self_sqrt (by positivity)
  calc
    _ ≤ _ := hcard
    _ ≤ _ := add_le_add hl hs
    _ = _ := by ring

/-! ## Finite lattice boxes -/

private noncomputable def natLatticeEmbedding : ℕ × ℕ ↪ EuclideanSpace ℝ (Fin 2) where
  toFun a := latticePoint (a.1, a.2)
  inj' := by
    intro a b h
    have h' := latticePoint_injective h
    exact Prod.ext (Int.ofNat_inj.mp (congrArg Prod.fst h'))
      (Int.ofNat_inj.mp (congrArg Prod.snd h'))

private noncomputable def latticeBox (m : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (Finset.range m ×ˢ Finset.range m).map natLatticeEmbedding

private lemma latticeBox_card (m : ℕ) : (latticeBox m).card = m ^ 2 := by
  simp [latticeBox, pow_two]

private lemma latticeBox_repr {m : ℕ} {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ latticeBox m) :
    ∃ a : ℕ × ℕ, a.1 < m ∧ a.2 < m ∧ latticePoint (a.1, a.2) = z := by
  obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hz
  exact ⟨a, Finset.mem_range.mp (Finset.mem_product.mp ha).1,
    Finset.mem_range.mp (Finset.mem_product.mp ha).2, he⟩

private lemma box_dist_as_norm {n : ℕ} {P : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP : P ⊆ latticeBox (n.sqrt + 1)) :
    distanceSet P ⊆ (normValues (3 * n)).image (fun q : ℕ => Real.sqrt (q : ℝ)) := by
  classical
  intro d hd
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
  obtain ⟨u, hu₁, hu₂, rfl⟩ := latticeBox_repr (hP ha)
  obtain ⟨v, hv₁, hv₂, rfl⟩ := latticeBox_repr (hP hb)
  let x := ((u.1 : ℤ) - (v.1 : ℤ)).natAbs
  let y := ((u.2 : ℤ) - (v.2 : ℤ)).natAbs
  let q := x ^ 2 + 2 * y ^ 2
  have he : (q : ℤ) = qdist (u.1, u.2) (v.1, v.2) := by
    simp [q, qdist, x, y, sq_abs]
  have hsq := latticePoint_dist_sq (u.1, u.2) (v.1, v.2)
  rw [← he, Int.cast_natCast] at hsq
  have hq : 0 < q := by
    have hqd := qdist_pos (fun h => hne (congrArg latticePoint h))
    rw [← he] at hqd
    exact_mod_cast hqd
  have hx : x ≤ n.sqrt := Nat.le_of_lt_succ (Int.natAbs_coe_sub_coe_lt_of_lt hu₁ hv₁)
  have hy : y ≤ n.sqrt := Nat.le_of_lt_succ (Int.natAbs_coe_sub_coe_lt_of_lt hu₂ hv₂)
  have hq_bound : q ≤ 3 * n := by
    have hxx := (Nat.pow_le_pow_left hx 2).trans (Nat.sqrt_le' n)
    have hyy := (Nat.pow_le_pow_left hy 2).trans (Nat.sqrt_le' n)
    dsimp only [q]
    omega
  exact Finset.mem_image.mpr ⟨q,
    Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq, hq_bound⟩, x, y, rfl⟩,
    (congrArg Real.sqrt hsq).symm.trans (Real.sqrt_sq dist_nonneg)⟩

@[expose] public section

/-- **Statement of Erdős Problem 659.** This is the statement that there is a real constant $C$
such that for every sufficiently large natural number $n$ there is a set $P$ of $n$ points of the
Euclidean plane $\mathbb{R}^2$ such that every $4$-element subset of $P$ determines at least $3$
distinct distances and $P$ determines at most $C n / \sqrt{\log n}$ distinct distances. -/
def fewDistancesWithFourPointCondition : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧
    (∀ S ⊆ P, S.card = 4 → 3 ≤ distinctDistances S) ∧
    (distinctDistances P : ℝ) ≤ C * n / Real.sqrt (Real.log n)

/--
**Erdős Problem 659: few distances with every four points spanning three.** There is a real
constant $C$ such that for every sufficiently large natural number $n$ there is a set $P$ of $n$
points of the Euclidean plane $\mathbb{R}^2$ such that every $4$-element subset of $P$ determines
at least $3$ distinct distances and $P$ determines at most $C n / \sqrt{\log n}$ distinct
distances.

A suitable truncation of the lattice $\{(a, b\sqrt{2}) : a, b \in \mathbb{Z}\}$ has
$O(n / \sqrt{\log n})$ distinct distances (Moree and Osburn) and contains none of the six
four-point configurations that determine only two distances: five of them contain a square or an
equilateral triangle (Erdős–Fishburn, Lund–Sheffer), and the pentagon configuration is excluded by
Grayzel.

Source: T. F. Bloom, Erdős Problems, Problem #659, https://www.erdosproblems.com/659 (status PROVED
(LEAN)); resolution: B. Grayzel, Solution to a Problem of Erdős Concerning Distances and Points,
arXiv:2601.09102 (2026); P. Moree and R. Osburn, Two-dimensional lattices with few distances,
Enseign. Math. (2) 52 (2006), 361-380, abstract of arXiv:2601.09102: n-point sets taken from an m ×
m box of the lattice {(x, √2 y)} determine O(n / √(log n)) distinct distances (Bernays' theorem for
u² + 2v²) and every 4 of their points determine at least 3 distances (Perucca's classification of
the six two-distance 4-point configurations); erdosproblems.com/659 records the construction
(Moree-Osburn, Lund-Sheffer) and the remaining pentagon case ruled out by Grayzel (using Gemini),
'thus giving a complete solution', https://arxiv.org/abs/2601.09102.
-/
theorem fewDistancesWithFourPointCondition_holds :
    fewDistancesWithFourPointCondition := by
  classical
  obtain ⟨C, hC, hnorm⟩ := normValues_card_upper
  refine ⟨3 * C, (Filter.eventually_ge_atTop ⌈Real.exp (1 : ℝ)⌉₊).mono ?_⟩
  intro n hn
  have hlogn : 1 ≤ Real.log (n : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (Nat.le_of_ceil_le hn)
  have hn0 : 0 < (n : ℝ) := (Real.exp_pos 1).trans_le (Nat.le_of_ceil_le hn)
  have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast (show n ≤ 3 * n by omega))
  have hcap : n ≤ (latticeBox (n.sqrt + 1)).card := by
    rw [latticeBox_card]
    exact (Nat.lt_succ_sqrt' n).le
  obtain ⟨P, hP, hcard⟩ := Finset.exists_subset_card_eq hcap
  refine ⟨P, hcard, ?_, ?_⟩
  · intro S hSP hS
    exact lattice_four_point hS fun a ha => by
      obtain ⟨u, _, _, hu⟩ := latticeBox_repr (hP (hSP ha))
      exact ⟨(u.1, u.2), hu⟩
  · have hdist : distinctDistances P ≤ (normValues (3 * n)).card :=
      (Finset.card_le_card (box_dist_as_norm hP)).trans Finset.card_image_le
    calc
      _ ≤ ((normValues (3 * n)).card : ℝ) := by exact_mod_cast hdist
      _ ≤ C * ((3 * n : ℕ) : ℝ) / Real.sqrt (Real.log ((3 * n : ℕ) : ℝ)) :=
        hnorm (3 * n) (hlogn.trans hlog_mono)
      _ ≤ C * ((3 * n : ℕ) : ℝ) / Real.sqrt (Real.log (n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos_of_pos (by linarith))
          (Real.sqrt_le_sqrt hlog_mono)
      _ = _ := by push_cast; ring

end

end MathlibExt.Combinatorics.FewDistancesFourPointErdosProblem659Wanted
