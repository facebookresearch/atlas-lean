/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.CoveringSystem.ExactCover
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
open scoped BigOperators

private theorem fraenkelAux_sum_residue (a n t m : ℕ) (hn : 0 < n) (ha : a < n) :
    (∑ k ∈ (Finset.range (n * t)).filter (fun k => k ≡ a [MOD n]), (k : ℚ) ^ m) =
    ∑ j ∈ Finset.range t, ((a : ℚ) + (j : ℚ) * (n : ℚ)) ^ m := by
  symm
  apply Finset.sum_bij (fun j _ => a + j * n)
  · intro j hj
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      rw [Finset.mem_range] at hj
      calc a + j * n < n + j * n := by
            apply Nat.add_lt_add_right ha
        _ = (j + 1) * n := by ring
        _ ≤ t * n := by
            apply Nat.mul_le_mul_right
            exact hj
        _ = n * t := by ring
    · exact (Nat.add_mul_modulus_modEq_iff.mpr (Nat.ModEq.refl a))
  · intro j₁ hj₁ j₂ hj₂ h
    have h2 : j₁ * n = j₂ * n := Nat.add_left_cancel h
    exact Nat.mul_right_cancel hn h2
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hklt, hkmod⟩ := hk
    have hmod_eq : k % n = a % n := hkmod
    have ha_mod : a % n = a := Nat.mod_eq_of_lt ha
    have hk_mod : k % n = a := by rw [hmod_eq, ha_mod]
    refine ⟨k / n, Finset.mem_range.mpr ?_, ?_⟩
    · have hlt : k / n < t := by
        rw [Nat.div_lt_iff_lt_mul hn]
        calc k < n * t := hklt
          _ = t * n := by ring
      exact hlt
    · conv_rhs => rw [← Nat.div_add_mod k n, hk_mod]
      ring
  · intro j hj
    push_cast
    ring

private theorem fraenkelAux_expand (a n T m : ℕ) :
    (∑ j ∈ Finset.range T, (((a : ℚ)) + ((j : ℚ)) * ((n : ℚ))) ^ m) =
    ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a : ℚ)) ^ (m - r) * ((n : ℚ)) ^ r *
      (∑ j ∈ Finset.range T, ((j : ℚ)) ^ r) := by
  have h_each : ∀ j ∈ Finset.range T, (((a : ℚ)) + ((j : ℚ)) * ((n : ℚ))) ^ m =
      ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a : ℚ)) ^ (m - r) * ((n : ℚ)) ^ r *
          ((j : ℚ)) ^ r := by
    intro j _
    have hpow : (((a : ℚ)) + ((j : ℚ)) * ((n : ℚ))) = (((j : ℚ)) * ((n : ℚ)) + ((a : ℚ))) := by ring
    rw [hpow, add_pow]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_pow]
    ring
  calc (∑ j ∈ Finset.range T, (((a : ℚ)) + ((j : ℚ)) * ((n : ℚ))) ^ m)
      = ∑ j ∈ Finset.range T, ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a : ℚ)) ^
          (m - r) * ((n : ℚ)) ^ r * ((j : ℚ)) ^ r :=
        Finset.sum_congr rfl h_each
    _ = ∑ r ∈ Finset.range (m + 1), ∑ j ∈ Finset.range T, ((Nat.choose m r : ℚ)) * ((a : ℚ)) ^
        (m - r) * ((n : ℚ)) ^ r * ((j : ℚ)) ^ r :=
        Finset.sum_comm
    _ = ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a : ℚ)) ^ (m - r) * ((n : ℚ)) ^ r *
          (∑ j ∈ Finset.range T, ((j : ℚ)) ^ r) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]

private theorem fraenkelAux_faulhaber (N p : ℕ) :
    (∑ k ∈ Finset.range N, ((k : ℚ)) ^ p) =
    Polynomial.eval ((N : ℚ))
      (∑ s ∈ Finset.range (p + 1), Polynomial.C
          (bernoulli s * ((Nat.choose (p+1) s : ℚ)) / (((p : ℚ)) + 1)) * Polynomial.X ^
              (p + 1 - s)) := by
  have h := sum_range_pow N p
  rw [h]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  ring

private theorem fraenkelAux_coeff_pick (m : ℕ) (f : ℕ → ℚ) :
    (∑ s ∈ Finset.range (m + 1), Polynomial.C (f s) * Polynomial.X ^ (m + 1 - s)).coeff 1 = f
        m := by
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · have h1 : m + 1 - m = 1 := by omega
    rw [h1]
    rw [Polynomial.coeff_C_mul_X_pow]
    simp
  · intro s hs hne
    rw [Finset.mem_range] at hs
    rw [Polynomial.coeff_C_mul_X_pow]
    have h : (1 : ℕ) ≠ m + 1 - s := by omega
    simp [h]
  · intro hcon
    have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    exact False.elim (hcon hmem)

private theorem fraenkelAux_keycount (q M m : ℕ) (a n : Fin q → ℕ)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, a i < n i)
    (hcover : ∀ k : ℤ, Int.indexedCoverMultiplicity n (fun i => ((a i : ℤ))) k = M)
    (t : ℕ) :
    (M : ℚ) * ∑ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t), ((k : ℚ)) ^ m =
    ∑ i : Fin q, ∑ j ∈ Finset.range (((Finset.univ.prod fun i => n i) / n i) * t),
        (((a i : ℚ)) + ((j : ℚ)) * ((n i : ℚ))) ^ m := by
  have hdvd : ∀ i : Fin q, n i ∣ Finset.univ.prod fun i => n i := fun i =>
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hcover' : ∀ k : ℤ, ((Finset.univ.filter fun i => k ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]).card) =
      M := by
    intro k
    have h := hcover k
    unfold Int.indexedCoverMultiplicity at h
    exact h
  have hdc : (M : ℚ) * ∑ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t), ((k : ℚ)) ^ m =
      ∑ i : Fin q, ∑ k ∈ (Finset.range ((Finset.univ.prod fun i => n i) * t)).filter
        (fun k : ℕ => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]), ((k : ℚ)) ^ m := by
    have h1 : ∀ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t), (M : ℚ) * ((k : ℚ)) ^ m =
        ∑ i ∈ Finset.univ.filter (fun i => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]), ((k : ℚ)) ^
            m := by
      intro k _
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.univ.filter fun i => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]).card :
          ℚ) = (M : ℚ) := by
        rw [hcover']
      rw [hcard]
    calc (M : ℚ) * ∑ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t), ((k : ℚ)) ^ m
        = ∑ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t), (M : ℚ) * ((k : ℚ)) ^
            m := by rw [Finset.mul_sum]
      _ = ∑ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t), ∑ i ∈ Finset.univ.filter
          (fun i => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]), ((k : ℚ)) ^ m :=
          Finset.sum_congr rfl h1
      _ = ∑ i ∈ Finset.univ, ∑ k ∈ (Finset.range ((Finset.univ.prod fun i => n i) * t)).filter
          (fun k : ℕ => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]), ((k : ℚ)) ^ m := by
          have hif : ∀ k ∈ Finset.range ((Finset.univ.prod fun i => n i) * t),
              (∑ i ∈ Finset.univ.filter (fun i => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]),
                  ((k : ℚ)) ^ m) =
              ∑ i ∈ Finset.univ, (if ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))] then ((k : ℚ)) ^ m
                  else 0) := by
            intro k _
            rw [Finset.sum_filter]
          rw [Finset.sum_congr rfl hif]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_filter]
  rw [hdc]
  apply Finset.sum_congr rfl
  intro i _
  have hpos : 0 < n i := hn i
  have hai : a i < n i := ha i
  obtain ⟨ci, hci⟩ := hdvd i
  have hc_eq : (Finset.univ.prod fun i => n i) / n i = ci := by
    rw [hci, Nat.mul_div_cancel_left _ hpos]
  have hN : (Finset.univ.prod fun i => n i) * t = n i * (ci * t) := by
    rw [hci]
    ring
  have hfilter_eq : (Finset.range ((Finset.univ.prod fun i => n i) * t)).filter
        (fun k : ℕ => ((k : ℤ)) ≡ ((a i : ℤ)) [ZMOD ((n i : ℤ))]) =
      (Finset.range ((Finset.univ.prod fun i => n i) * t)).filter (fun k => k ≡ a i [MOD n i]) :=
    Finset.filter_congr (fun k _ => Int.natCast_modEq_iff)
  rw [hfilter_eq, hc_eq, hN]
  exact fraenkelAux_sum_residue (a i) (n i) (ci * t) m hpos hai

/-- **Fraenkel's Bernoulli recurrence for exact covers by any number of classes.** Let $q$, $M$
and $m \ge 1$ be natural numbers, and for $i = 1, \dots, q$ let $n_i$ be a positive integer and
$a_i$ an integer with $0 \le a_i < n_i$. Suppose the residue classes $a_i \bmod n_i$, counted
with repetition, form an exact $M$-cover of $\mathbb{Z}$: every integer $k$ satisfies
$k \equiv a_i \pmod{n_i}$ for exactly $M$ indices $i$. Then
$$
B_m \Big(M - \sum_{i=1}^{q} n_i^{m-1}\Big) =
\sum_{i=1}^{q} n_i^{m-1} \sum_{s=0}^{m-1} \binom{m}{s} B_s \Big(\frac{a_i}{n_i}\Big)^{m-s},
$$
where $B_s$ is the $s$-th Bernoulli number, with the convention $B_1 = -\frac{1}{2}$.

The source assumes $q \ge 2$; the identity holds without that assumption. -/
theorem fraenkel_exact_M_cover_bernoulli_recurrence_general
    (q M m : ℕ) (a n : Fin q → ℕ) (hm : 1 ≤ m)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, a i < n i)
    (hcover : ∀ k : ℤ, Int.indexedCoverMultiplicity n (fun i => ((a i : ℤ))) k = M) :
    bernoulli m * ((M : ℚ) - ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1)) =
      ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1) *
        (∑ s ∈ Finset.range m, bernoulli s * (Nat.choose m s : ℚ) *
          (((a i : ℚ)) / ((n i : ℚ))) ^ (m - s)) := by
  set L : ℕ := Finset.univ.prod fun i => n i with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Finset.prod_pos
    intro i _
    exact hn i
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hLneQ : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hLne
  have hnneQ : ∀ i : Fin q, ((n i : ℚ)) ≠ 0 := by
    intro i
    exact Nat.cast_ne_zero.mpr (ne_of_gt (hn i))
  have hdvd : ∀ i : Fin q, n i ∣ L := by
    intro i
    rw [hLdef]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hLmulQ : ∀ i : Fin q, (L : ℚ) = ((n i : ℚ)) * ((((L / n i : ℕ))) : ℚ) := by
    intro i
    obtain ⟨ci, hci⟩ := hdvd i
    have hpos : 0 < n i := hn i
    have hc : L / n i = ci := by
      rw [hci]
      exact Nat.mul_div_cancel_left ci hpos
    rw [hc]
    have hcc := congrArg (fun x : ℕ => (x : ℚ)) hci
    simpa [Nat.cast_mul] using hcc
  have hcount : ∀ t : ℕ, (M : ℚ) * ∑ k ∈ Finset.range (L * t), ((k : ℚ)) ^ m =
      ∑ i : Fin q, ∑ j ∈ Finset.range ((L / n i) * t), (((a i : ℚ)) + ((j : ℚ)) * ((n i : ℚ))) ^
          m := by
    intro t
    have h := fraenkelAux_keycount q M m a n hn ha hcover t
    rwa [← hLdef] at h
  set P : Polynomial ℚ := ∑ s ∈ Finset.range (m + 1),
    Polynomial.C ((M : ℚ) * bernoulli s * ((Nat.choose (m + 1) s : ℚ)) * ((L : ℚ)) ^ (m + 1 - s) /
        (((m : ℚ)) + 1)) *
    Polynomial.X ^ (m + 1 - s) with hPdef
  set Q : Polynomial ℚ := ∑ i ∈ Finset.univ, ∑ r ∈ Finset.range (m + 1), ∑ s ∈ Finset.range (r + 1),
    Polynomial.C (((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r *
      bernoulli s * ((Nat.choose (r + 1) s : ℚ)) * ((((L / n i : ℕ))) : ℚ) ^ (r + 1 - s) /
          (((r : ℚ)) + 1)) *
    Polynomial.X ^ (r + 1 - s) with hQdef
  have hevalP : ∀ t : ℕ, Polynomial.eval ((t : ℚ)) P =
      (M : ℚ) * ∑ k ∈ Finset.range (L * t), ((k : ℚ)) ^ m := by
    intro t
    have hF := fraenkelAux_faulhaber (L * t) m
    rw [hPdef, Polynomial.eval_finsetSum, hF, Polynomial.eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    rw [mul_pow]
    ring
  have hevalQ : ∀ t : ℕ, Polynomial.eval ((t : ℚ)) Q =
      ∑ i : Fin q, ∑ j ∈ Finset.range ((L / n i) * t), (((a i : ℚ)) + ((j : ℚ)) * ((n i : ℚ))) ^
          m := by
    intro t
    rw [hQdef, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    have hE := fraenkelAux_expand (a i) (n i) ((L / n i) * t) m
    rw [hE, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro r _
    have hFr := fraenkelAux_faulhaber ((L / n i) * t) r
    rw [Polynomial.eval_finsetSum, hFr, Polynomial.eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    rw [mul_pow]
    ring
  have heval : ∀ t : ℕ, Polynomial.eval ((t : ℚ)) P = Polynomial.eval ((t : ℚ)) Q := by
    intro t
    rw [hevalP, hevalQ]
    exact hcount t
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : Set.range (Nat.cast : ℕ → ℚ) ⊆ {x | Polynomial.eval x P = Polynomial.eval x Q} := by
      intro x hx
      obtain ⟨t, rfl⟩ := hx
      exact heval t
    exact Set.Infinite.mono hsub (Set.infinite_range_of_injective Nat.cast_injective)
  have hcoeff : P.coeff 1 = Q.coeff 1 := by rw [hPQ]
  have hcoeffP : P.coeff 1 = (M : ℚ) * bernoulli m * ((L : ℚ)) := by
    rw [hPdef, fraenkelAux_coeff_pick]
    show (M : ℚ) * bernoulli m * ((Nat.choose (m + 1) m : ℚ)) * ((L : ℚ)) ^ (m + 1 - m) /
        (((m : ℚ)) + 1) = _
    have hC : Nat.choose (m + 1) m = m + 1 := Nat.choose_succ_self_right m
    have hCq : ((Nat.choose (m + 1) m : ℕ) : ℚ) = ((m : ℚ)) + 1 := by
      rw [hC]
      push_cast
      ring
    have hm1 : m + 1 - m = 1 := by omega
    rw [hCq, hm1, pow_one]
    have hmp1 : ((m : ℚ)) + 1 ≠ 0 := by
      have hnn : (0 : ℚ) ≤ ((m : ℚ)) := Nat.cast_nonneg m
      linarith
    field_simp
  have hcoeffQ : Q.coeff 1 =
      ∑ i : Fin q, ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
          ((n i : ℚ)) ^ r *
        bernoulli r * ((((L / n i : ℕ))) : ℚ) := by
    rw [hQdef, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro r _
    rw [fraenkelAux_coeff_pick]
    show ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r *
        bernoulli r * ((Nat.choose (r + 1) r : ℚ)) * ((((L / n i : ℕ))) : ℚ) ^ (r + 1 - r) /
            (((r : ℚ)) + 1) = _
    have hCr : Nat.choose (r + 1) r = r + 1 := Nat.choose_succ_self_right r
    have hCrq : ((Nat.choose (r + 1) r : ℕ) : ℚ) = ((r : ℚ)) + 1 := by
      rw [hCr]
      push_cast
      ring
    have hre : r + 1 - r = 1 := by omega
    rw [hCrq, hre, pow_one]
    have hrp1 : ((r : ℚ)) + 1 ≠ 0 := by
      have hnn : (0 : ℚ) ≤ ((r : ℚ)) := Nat.cast_nonneg r
      linarith
    field_simp
  have hBeq : (M : ℚ) * bernoulli m * ((L : ℚ)) =
      ∑ i : Fin q, ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
          ((n i : ℚ)) ^ r *
        bernoulli r * ((((L / n i : ℕ))) : ℚ) := by
    rw [← hcoeffP, hcoeff, hcoeffQ]
  have hdiv : ∀ i : Fin q, ∀ x : ℚ, x * ((((L / n i : ℕ))) : ℚ) = (x / ((n i : ℚ))) *
      ((L : ℚ)) := by
    intro i x
    have hn0 := hnneQ i
    rw [hLmulQ i]
    field_simp
  have hMBeq : (M : ℚ) * bernoulli m =
      ∑ i : Fin q, (∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
          ((n i : ℚ)) ^ r *
        bernoulli r / ((n i : ℚ))) := by
    have hfac : (∑ i : Fin q, ∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^
        (m - r) * ((n i : ℚ)) ^ r *
        bernoulli r * ((((L / n i : ℕ))) : ℚ)) =
        (∑ i : Fin q, (∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
            ((n i : ℚ)) ^ r *
          bernoulli r / ((n i : ℚ)))) * ((L : ℚ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      exact hdiv i _
    rw [hfac] at hBeq
    exact mul_right_cancel₀ hLneQ hBeq
  have h0m : 0 < m := by omega
  have hsplit : ∀ i : Fin q, (∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^
      (m - r) * ((n i : ℚ)) ^ r *
      bernoulli r / ((n i : ℚ))) =
      (∑ r ∈ Finset.range m, ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r *
        bernoulli r / ((n i : ℚ))) + bernoulli m * (((n i : ℚ)) ^ (m - 1)) := by
    intro i
    rw [Finset.sum_range_succ]
    congr 1
    have hCself : ((Nat.choose m m : ℕ) : ℚ) = 1 := by
      rw [Nat.choose_self]
      simp
    have hsub : m - m = 0 := Nat.sub_self m
    have hn0 := hnneQ i
    have hpow : ((n i : ℚ)) ^ m / ((n i : ℚ)) = ((n i : ℚ)) ^ (m - 1) := by
      have hm1 : m - 1 + 1 = m := by omega
      calc ((n i : ℚ)) ^ m / ((n i : ℚ)) = ((n i : ℚ)) ^ (m - 1 + 1) / ((n i : ℚ)) := by rw [hm1]
        _ = (((n i : ℚ)) ^ (m - 1) * ((n i : ℚ))) / ((n i : ℚ)) := by rw [pow_succ]
        _ = ((n i : ℚ)) ^ (m - 1) := by field_simp
    calc ((Nat.choose m m : ℚ)) * ((a i : ℚ)) ^ (m - m) * ((n i : ℚ)) ^ m * bernoulli m /
        ((n i : ℚ))
        = bernoulli m * (((n i : ℚ)) ^ m / ((n i : ℚ))) := by
          rw [hCself, hsub]
          ring
      _ = bernoulli m * (((n i : ℚ)) ^ (m - 1)) := by rw [hpow]
  have hterm : ∀ i : Fin q, ∀ r ∈ Finset.range m,
      ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r * bernoulli r / ((n i : ℚ)) =
      ((n i : ℚ)) ^ (m - 1) * (bernoulli r * ((Nat.choose m r : ℚ)) * ((((a i : ℚ)) / ((n i : ℚ))))
          ^ (m - r)) := by
    intro i r hr
    have hn0 := hnneQ i
    have hrm : r ≤ m := by
      have hlt := Finset.mem_range.mp hr
      omega
    have e1 : ((n i : ℚ)) ^ (m - 1) * ((n i : ℚ)) = ((n i : ℚ)) ^ m := by
      have hm1 : m - 1 + 1 = m := by omega
      calc ((n i : ℚ)) ^ (m - 1) * ((n i : ℚ)) = ((n i : ℚ)) ^ ((m - 1) + 1) := by rw [pow_succ]
        _ = ((n i : ℚ)) ^ m := by rw [hm1]
    have e2 : ((n i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r = ((n i : ℚ)) ^ m := by
      rw [← pow_add]
      congr 1
      omega
    have hpow_ne : ((n i : ℚ)) ^ (m - r) ≠ 0 := pow_ne_zero _ hn0
    have hkey : ((n i : ℚ)) ^ (m - 1) / ((n i : ℚ)) ^ (m - r) = ((n i : ℚ)) ^ r / ((n i : ℚ)) := by
      rw [div_eq_div_iff hpow_ne hn0]
      have hkk : ((n i : ℚ)) ^ (m - 1) * ((n i : ℚ)) = ((n i : ℚ)) ^ r * ((n i : ℚ)) ^ (m - r) := by
        calc ((n i : ℚ)) ^ (m - 1) * ((n i : ℚ)) = ((n i : ℚ)) ^ m := e1
          _ = ((n i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r := e2.symm
          _ = ((n i : ℚ)) ^ r * ((n i : ℚ)) ^ (m - r) := by ring
      exact hkk
    have hmain : ((n i : ℚ)) ^ r / ((n i : ℚ)) = ((n i : ℚ)) ^ (m - 1) / ((n i : ℚ)) ^ (m - r) :=
        hkey.symm
    rw [div_pow]
    calc ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) * ((n i : ℚ)) ^ r * bernoulli r /
        ((n i : ℚ))
        = ((Nat.choose m r : ℚ)) * bernoulli r * ((a i : ℚ)) ^ (m - r) *
            (((n i : ℚ)) ^ r / ((n i : ℚ))) := by ring
      _ = ((Nat.choose m r : ℚ)) * bernoulli r * ((a i : ℚ)) ^ (m - r) *
          (((n i : ℚ)) ^ (m - 1) / ((n i : ℚ)) ^ (m - r)) := by rw [hmain]
      _ = ((n i : ℚ)) ^ (m - 1) * (bernoulli r * ((Nat.choose m r : ℚ)) *
          (((a i : ℚ)) ^ (m - r) / ((n i : ℚ)) ^ (m - r))) := by ring
  have hsum : (∑ i : Fin q, (∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^
      (m - r) * ((n i : ℚ)) ^ r *
      bernoulli r / ((n i : ℚ)))) =
      (∑ i : Fin q, (∑ r ∈ Finset.range m, ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
          ((n i : ℚ)) ^ r *
        bernoulli r / ((n i : ℚ)))) + bernoulli m * ∑ i : Fin q, (((n i : ℚ)) ^ (m - 1)) := by
    calc (∑ i : Fin q, (∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
        ((n i : ℚ)) ^ r *
          bernoulli r / ((n i : ℚ))))
        = ∑ i : Fin q, ((∑ r ∈ Finset.range m, ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
            ((n i : ℚ)) ^ r *
            bernoulli r / ((n i : ℚ))) + bernoulli m * (((n i : ℚ)) ^ (m - 1))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hsplit i
      _ = (∑ i : Fin q, (∑ r ∈ Finset.range m, ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
          ((n i : ℚ)) ^ r *
            bernoulli r / ((n i : ℚ)))) + (∑ i : Fin q, bernoulli m * (((n i : ℚ)) ^ (m - 1))) :=
                Finset.sum_add_distrib
      _ = (∑ i : Fin q, (∑ r ∈ Finset.range m, ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
          ((n i : ℚ)) ^ r *
            bernoulli r / ((n i : ℚ)))) + bernoulli m * ∑ i : Fin q,
                (((n i : ℚ)) ^ (m - 1)) := by rw [← Finset.mul_sum]
  have hinner : ∀ i : Fin q, (∑ r ∈ Finset.range m, ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^ (m - r) *
      ((n i : ℚ)) ^ r *
      bernoulli r / ((n i : ℚ))) =
      ((n i : ℚ)) ^ (m - 1) * (∑ s ∈ Finset.range m, bernoulli s * ((Nat.choose m s : ℚ)) *
        ((((a i : ℚ)) / ((n i : ℚ)))) ^ (m - s)) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hterm i r hr]
  have hXeq : (∑ i : Fin q, (∑ r ∈ Finset.range (m + 1), ((Nat.choose m r : ℚ)) * ((a i : ℚ)) ^
      (m - r) * ((n i : ℚ)) ^ r *
      bernoulli r / ((n i : ℚ)))) =
      (∑ i : Fin q, ((n i : ℚ)) ^ (m - 1) *
          (∑ s ∈ Finset.range m, bernoulli s * ((Nat.choose m s : ℚ)) *
        ((((a i : ℚ)) / ((n i : ℚ)))) ^ (m - s))) + bernoulli m * ∑ i : Fin q,
            (((n i : ℚ)) ^ (m - 1)) := by
    rw [hsum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact hinner i
  have hfin : (M : ℚ) * bernoulli m =
      (∑ i : Fin q, ((n i : ℚ)) ^ (m - 1) *
          (∑ s ∈ Finset.range m, bernoulli s * ((Nat.choose m s : ℚ)) *
        ((((a i : ℚ)) / ((n i : ℚ)))) ^ (m - s))) + bernoulli m * ∑ i : Fin q,
            (((n i : ℚ)) ^ (m - 1)) := by
    rw [hMBeq, hXeq]
  linear_combination hfin


set_option linter.unusedVariables false in
/-- **Fraenkel's Bernoulli recurrence for exact covers.** Let $q \ge 2$, $m \ge 1$ and $M$ be
natural numbers, and for $i = 1, \dots, q$ let $n_i$ be a positive integer and $a_i$ an integer
with $0 \le a_i < n_i$. Suppose the residue classes $a_i \bmod n_i$, counted with repetition,
form an exact $M$-cover of $\mathbb{Z}$: every integer $k$ satisfies $k \equiv a_i \pmod{n_i}$
for exactly $M$ indices $i$. Then
$$
B_m \Big(M - \sum_{i=1}^{q} n_i^{m-1}\Big) =
\sum_{i=1}^{q} n_i^{m-1} \sum_{s=0}^{m-1} \binom{m}{s} B_s \Big(\frac{a_i}{n_i}\Big)^{m-s},
$$
where $B_s$ is the $s$-th Bernoulli number, with the convention $B_1 = -\frac{1}{2}$.

Only this direction of the source's equation (23) is stated; the converse, Beebee's variant with
a parameter $x$, and Porubsky's weighted variant are not.

Proves `Wanted` entry `fraenkel_exact_M_cover_bernoulli_recurrence`.

Source: Yevgenya Movshovich, "Raabe's Identity and Covering Systems,"
Journal of Integer Sequences 23 (2020), Article 20.2.8,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Movshovich/movsho5.tex>.
Equation (23); exact source span: lines 228–241; full live TeX source-file SHA-256
`24b31e07198371d27b492f46b2d747aa49e9a49323696d6b4a9c18deab8ff593`;
exact newline-terminated equation/context span SHA-256
`1c95008be9bbbc150a494df7eef936abd3ee277ab9bd32ff1f67b0b0f4b76526`.
-/
theorem fraenkel_exact_M_cover_bernoulli_recurrence
    (q M m : ℕ) (a n : Fin q → ℕ)
    (hq : 2 ≤ q) (hm : 1 ≤ m)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, a i < n i)
    (hcover : ∀ k : ℤ, Int.indexedCoverMultiplicity n (fun i => ((a i : ℤ))) k = M) :
    bernoulli m * ((M : ℚ) - ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1)) =
      ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1) *
        (∑ s ∈ Finset.range m, bernoulli s * (Nat.choose m s : ℚ) *
          (((a i : ℚ)) / ((n i : ℚ))) ^ (m - s)) :=
  fraenkel_exact_M_cover_bernoulli_recurrence_general q M m a n hm hn ha hcover

end

end MetaMathlibExt
