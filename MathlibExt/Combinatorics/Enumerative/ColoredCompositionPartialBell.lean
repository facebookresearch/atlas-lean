/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Field.Rat
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The Hoggatt–Lind formula for colored compositions

We prove `coloredCompositionCount_eq_partialBell`: for a coloring sequence `γ`, the number
$c_{n,k}(\gamma)$ of colored compositions of $n$ with $k$ parts satisfies
$c_{n,k}(\gamma) = \frac{k!}{n!} B_{n,k}(1!\,\gamma_1, 2!\,\gamma_2, \dots)$, where $B_{n,k}$ is
the partial Bell polynomial. Gil, Hoover, and Shearer recall it, citing Hoggatt and Lind, as
Proposition 1.1 of *Bijections between colored compositions, Dyck paths, and polygon partitions*
(arXiv:2403.04575v1), published in the Journal of Integer Sequences 27 (2024), Article 24.5.2.

## Proof

Both sides are the coefficient of $X^n$ in $C^k$, where $C = \sum_{j \ge 1} \gamma_j X^j$.
Splitting off the first part of a composition gives the recurrence that the coefficients of
$C^{k+1} = C \cdot C^k$ satisfy. The multinomial theorem expands $C^k$ over the multiplicity
vectors $(m_1, m_2, \dots)$ with $\sum_j m_j = k$. Those with $\sum_j j\, m_j = n$ contribute
$\binom{k}{m_1, m_2, \dots} \prod_j \gamma_j^{m_j}$, which is $\frac{k!}{n!}$ times the matching
term of $B_{n,k}(1!\,\gamma_1, 2!\,\gamma_2, \dots)$.
-/

namespace MetaMathlibExt

open Finset PowerSeries

namespace coloredCompositionCount_eq_partialBell

section Compositions

variable {M : Type*} [AddCommMonoid M]

/-- A sum over the compositions of `0` is the value at the empty composition. -/
private theorem sum_zero (f : List ℕ → M) : ∑ c : Composition 0, f c.blocks = f [] := by
  simp [(Composition.blocks_eq_nil _).mpr rfl, composition_card]

/-- Remove the first part `a + 1` of a composition. -/
private def tailComp {m k : ℕ} (a : ℕ) (c : Composition m) (ha : c.blocks.headI = a + 1)
    (h : a + 1 + k = m) : Composition k where
  blocks := c.blocks.tail
  blocks_pos hi := c.blocks_pos (List.mem_of_mem_tail hi)
  blocks_sum := by
    have hs := c.blocks_sum
    cases hc : c.blocks with
    | nil => rw [hc] at ha; simp at ha
    | cons b t =>
      rw [hc] at ha hs
      simp only [List.headI_cons] at ha
      simp only [List.sum_cons] at hs
      simp only [List.tail_cons]
      omega

/-- Prepend the part `a + 1` to a composition. -/
private def consComp {m k : ℕ} (a : ℕ) (c : Composition m) (h : a + 1 + m = k) :
    Composition k where
  blocks := (a + 1) :: c.blocks
  blocks_pos hi := by
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Nat.succ_pos a
    · exact c.blocks_pos hi
  blocks_sum := by
    rw [List.sum_cons, c.blocks_sum, h]

/-- A composition of `n + 1` has a first part. -/
private theorem exists_blocks_eq_cons {n : ℕ} (c : Composition (n + 1)) :
    ∃ a t, c.blocks = (a + 1) :: t ∧ a + 1 + t.sum = n + 1 := by
  have hs := c.blocks_sum
  rcases hc : c.blocks with _ | ⟨b, t⟩
  · rw [hc] at hs; simp at hs
  · have hb : 0 < b := c.blocks_pos (by rw [hc]; exact List.mem_cons_self)
    refine ⟨b - 1, t, by rw [Nat.sub_add_cancel hb], ?_⟩
    rw [hc, List.sum_cons] at hs
    omega

/-- A sum over the compositions of `n + 1`, split according to the first part `a + 1`. -/
private theorem sum_succ (n : ℕ) (f : List ℕ → M) :
    ∑ c : Composition (n + 1), f c.blocks =
      ∑ p ∈ antidiagonal n, ∑ c : Composition p.2, f ((p.1 + 1) :: c.blocks) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun c : Composition (n + 1) => (c.blocks.headI - 1, n + 1 - c.blocks.headI))
    (t := antidiagonal n) (fun c _ => by
      obtain ⟨a, t, hc, hs⟩ := exists_blocks_eq_cons c
      simp only [mem_antidiagonal, hc, List.headI_cons]
      omega)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = n := mem_antidiagonal.mp hp
  refine Finset.sum_bij'
    (fun c hc => tailComp p.1 c (by
        obtain ⟨a, t, hct, hs⟩ := exists_blocks_eq_cons c
        simp only [mem_filter, mem_univ, true_and, hct, List.headI_cons, Prod.ext_iff] at hc ⊢
        omega) (by omega))
    (fun c _ => consComp p.1 c (by omega)) ?_ ?_ ?_ ?_ ?_
  · intro c _
    exact mem_univ _
  · intro c _
    simp only [mem_filter, mem_univ, true_and, consComp, List.headI_cons, Prod.ext_iff]
    omega
  · intro c hc
    obtain ⟨a, t, hct, hs⟩ := exists_blocks_eq_cons c
    simp only [mem_filter, mem_univ, true_and, hct, List.headI_cons, Prod.ext_iff] at hc
    ext1
    simp only [consComp, tailComp, hct, List.tail_cons]
    congr 1
    omega
  · intro c _
    ext1
    simp [consComp, tailComp]
  · intro c hc
    obtain ⟨a, t, hct, hs⟩ := exists_blocks_eq_cons c
    simp only [mem_filter, mem_univ, true_and, hct, List.headI_cons, Prod.ext_iff] at hc
    simp only [tailComp, hct, List.tail_cons]
    congr 2
    omega

end Compositions

/-- The colored weight of a list of parts, counted only when the list has `k` parts. -/
private def weight (γ : ℕ → ℕ) (k : ℕ) (l : List ℕ) : ℕ :=
  if l.length = k then (l.map γ).prod else 0

private theorem count_eq_sum (γ : ℕ → ℕ) (n k : ℕ) :
    coloredCompositionCount γ n k = ∑ c : Composition n, weight γ k c.blocks := by
  rw [coloredCompositionCount, sum_filter]
  rfl

private theorem count_zero_left (γ : ℕ → ℕ) (k : ℕ) :
    coloredCompositionCount γ 0 k = if k = 0 then 1 else 0 := by
  rw [count_eq_sum, sum_zero]
  rcases k with _ | k <;> simp [weight]

private theorem count_succ_zero (γ : ℕ → ℕ) (n : ℕ) :
    coloredCompositionCount γ (n + 1) 0 = 0 := by
  rw [count_eq_sum, sum_succ]
  simp [weight]

/-- Splitting off the first part: $c_{n+1,k+1} = \sum_{a + b = n} \gamma_{a+1}\, c_{b,k}$. -/
private theorem count_succ_succ (γ : ℕ → ℕ) (n k : ℕ) :
    coloredCompositionCount γ (n + 1) (k + 1) =
      ∑ p ∈ antidiagonal n, γ (p.1 + 1) * coloredCompositionCount γ p.2 k := by
  rw [count_eq_sum, sum_succ]
  refine sum_congr rfl fun p _ => ?_
  rw [count_eq_sum, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  simp only [weight, List.length_cons, Nat.add_right_cancel_iff, List.map_cons, List.prod_cons,
    mul_ite, mul_zero]

/-- The power series $C = \sum_{j \ge 1} \gamma_j X^j$. -/
private noncomputable def series (γ : ℕ → ℕ) : ℚ⟦X⟧ :=
  mk fun j => if j = 0 then 0 else (γ j : ℚ)

/-- The coefficient of $X^n$ in $C^k$ is $c_{n,k}(\gamma)$. -/
private theorem coeff_series_pow (γ : ℕ → ℕ) (n k : ℕ) :
    coeff n (series γ ^ k) = coloredCompositionCount γ n k := by
  induction k generalizing n with
  | zero =>
    rcases n with _ | n
    · simp [count_zero_left]
    · simp [count_succ_zero, coeff_one]
  | succ k ih =>
    rcases n with _ | n
    · rw [pow_succ', coeff_mul, count_zero_left]
      simp [series]
    · rw [pow_succ', coeff_mul, Nat.sum_antidiagonal_succ, count_succ_succ]
      simp only [ih]
      simp [series]

/-- The multiplicity vectors `m` (with `m i` parts of size `i + 1`) of `k` parts summing to `n`,
as they index the partial Bell polynomial `B_{n,k}`. -/
private theorem piAntidiag_filter_eq (n k : ℕ) :
    (univ.piAntidiag k).filter (fun m : Fin (n + 1) → ℕ => n = ∑ i, m i * (i.val + 1)) =
      (Fintype.piFinset fun _ : Fin (n + 1) => range (n + 1)).filter
        (fun m => (∑ i, (i.val + 1) * m i = n) ∧ ∑ i, m i = k) := by
  ext m
  simp only [mem_filter, mem_piAntidiag, Fintype.mem_piFinset, mem_range, mem_univ,
    implies_true, and_true]
  have hcomm : ∑ i, m i * (i.val + 1) = ∑ i, (i.val + 1) * m i :=
    sum_congr rfl fun i _ => Nat.mul_comm _ _
  rw [hcomm]
  constructor
  · rintro ⟨hk, hn⟩
    refine ⟨fun i => ?_, hn.symm, hk⟩
    have hle : (i.val + 1) * m i ≤ ∑ j, (j.val + 1) * m j :=
      single_le_sum (f := fun j : Fin (n + 1) => (j.val + 1) * m j)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
    have : m i ≤ (i.val + 1) * m i := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  · rintro ⟨_, hn, hk⟩
    exact ⟨hk, hn.symm⟩

/-- The multinomial expansion of the coefficient of $X^n$ in $C^k$. -/
private theorem coeff_series_pow_eq_sum (γ : ℕ → ℕ) (n k : ℕ) :
    coeff n (series γ ^ k) =
      ∑ m ∈ (Fintype.piFinset fun _ : Fin (n + 1) => range (n + 1)).filter
          (fun m => (∑ i, (i.val + 1) * m i = n) ∧ ∑ i, m i = k),
        (Nat.multinomial univ m : ℚ) * ∏ i, (γ (i.val + 1) : ℚ) ^ m i := by
  -- Only the terms of degree at most `n` of `C` matter.
  have hA : coeff n (series γ ^ k) =
      coeff n ((∑ i : Fin (n + 1), monomial (i.val + 1) (γ (i.val + 1) : ℚ)) ^ k) := by
    rw [coeff_pow, coeff_pow]
    refine sum_congr rfl fun l hl => prod_congr rfl fun i hi => ?_
    have hle : l i ≤ n := by
      rw [mem_finsuppAntidiag] at hl
      rw [← hl.1]
      exact single_le_sum (fun _ _ => Nat.zero_le _) hi
    rw [series, coeff_mk, map_sum]
    simp_rw [coeff_monomial]
    rw [Fin.sum_univ_eq_sum_range (fun j => if l i = j + 1 then (γ (j + 1) : ℚ) else 0) (n + 1)]
    rcases Nat.eq_zero_or_pos (l i) with h0 | hpos
    · rw [h0]
      simp
    · rw [sum_eq_single (l i - 1)]
      · rw [Nat.sub_add_cancel hpos]
        simp [hpos.ne']
      · intro j _ hj
        rw [ite_eq_right (by omega)]
      · intro hmem
        exact absurd (mem_range.mpr (by omega)) hmem
  -- The multinomial theorem.
  have hB : coeff n ((∑ i : Fin (n + 1), monomial (i.val + 1) (γ (i.val + 1) : ℚ)) ^ k) =
      ∑ m ∈ (univ : Finset (Fin (n + 1))).piAntidiag k, (Nat.multinomial univ m : ℚ) *
        (if n = ∑ i, m i * (i.val + 1) then ∏ i, (γ (i.val + 1) : ℚ) ^ m i else 0) := by
    rw [sum_pow_eq_sum_piAntidiag, map_sum]
    refine sum_congr rfl fun m _ => ?_
    have hp : ∏ i : Fin (n + 1), (monomial (i.val + 1) (γ (i.val + 1) : ℚ)) ^ m i =
        monomial (∑ i, m i * (i.val + 1)) (∏ i : Fin (n + 1), (γ (i.val + 1) : ℚ) ^ m i) := by
      simp_rw [monomial_pow]
      rw [prod_monomial]
    rw [hp, ← nsmul_eq_mul, map_nsmul, coeff_monomial, nsmul_eq_mul]
  rw [hA, hB]
  simp_rw [mul_ite, mul_zero]
  rw [← sum_filter, piAntidiag_filter_eq]

/-- The multinomial coefficient in each term of `partialBellPolynomial` is an exact quotient. -/
private theorem prod_factorial_dvd {n : ℕ} (m : Fin (n + 1) → ℕ)
    (hm : ∑ i, (i.val + 1) * m i = n) :
    ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i ∣ n.factorial := by
  calc ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i
      ∣ ∏ i, ((i.val + 1) * m i).factorial := prod_dvd_prod_of_dvd _ _ fun i _ =>
        Dvd.intro_left (Nat.uniformBell (m i) (i.val + 1)) (by
          rw [mul_comm (i.val + 1), ← Nat.uniformBell_mul_eq (m i) (Nat.succ_ne_zero i.val)]
          ring)
    _ ∣ (∑ i, (i.val + 1) * m i).factorial := Nat.prod_factorial_dvd_factorial_sum _ _
    _ = n.factorial := by rw [hm]

/-- The normalized partial Bell polynomial `k! / n! * B_{n,k}(1! γ₁, 2! γ₂, ...)` as a sum of
multinomial coefficients. -/
private theorem partialBell_eq_sum (γ : ℕ → ℕ) (n k : ℕ) :
    (k.factorial : ℚ) / n.factorial *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j) =
      ∑ m ∈ (Fintype.piFinset fun _ : Fin (n + 1) => range (n + 1)).filter
          (fun m => (∑ i, (i.val + 1) * m i = n) ∧ ∑ i, m i = k),
        (Nat.multinomial univ m : ℚ) * ∏ i, (γ (i.val + 1) : ℚ) ^ m i := by
  rw [partialBellPolynomial, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨hn, hk⟩ := (mem_filter.mp hm).2
  have hdvd := prod_factorial_dvd m hn
  have hD : ((∏ i, (m i).factorial * (i.val + 1).factorial ^ m i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hdvd n.factorial_pos).ne'
  have hspec : (∏ i, ((m i).factorial : ℚ)) * Nat.multinomial univ m = k.factorial := by
    rw [← hk]
    exact_mod_cast Nat.multinomial_spec univ m
  have hn' : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [Nat.cast_div hdvd hD, ← hspec]
  push_cast at hD ⊢
  rw [prod_mul_distrib] at hD ⊢
  simp only [mul_pow, prod_mul_distrib]
  obtain ⟨hA, hF⟩ := mul_ne_zero_iff.mp hD
  field_simp

end coloredCompositionCount_eq_partialBell

-- The source assumes `n ≥ 1`, although the formula also holds for `n = 0`.
set_option linter.unusedVariables false in
open coloredCompositionCount_eq_partialBell in
/-- **Hoggatt–Lind formula for colored compositions.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$
be a sequence of natural numbers and let $c_{n,k}(\gamma)$ be the number of compositions of $n$
with $k$ parts in which each part $j$ carries one of $\gamma_j$ colors. For every natural number
$n \ge 1$ and every natural number $k$, as rational numbers,
$$c_{n,k}(\gamma) = \frac{k!}{n!} B_{n,k}(1! \, \gamma_1, 2! \, \gamma_2, \dots),$$
where $B_{n,k}$ is the partial Bell polynomial.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 1 (`jis-2024-24.5.2-prop-1`), citing Hoggatt and Lind. -/
public theorem coloredCompositionCount_eq_partialBell (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    (coloredCompositionCount γ n k : ℚ) =
      (k.factorial : ℚ) / n.factorial *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j) := by
  rw [← coeff_series_pow, coeff_series_pow_eq_sum, partialBell_eq_sum]

end MetaMathlibExt
