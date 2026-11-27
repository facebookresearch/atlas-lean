/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/--
**Dobinski's formula.** Let $B_n$ denote the $n$-th Bell number, the number of partitions of
an $n$-element set. For every natural number $n$, the real series $\sum_{k=0}^{\infty} k^n / k!$
is summable with sum $e \cdot B_n$, so $B_n = \frac{1}{e} \sum_{k=0}^{\infty} \frac{k^n}{k!}$.
At $n = 0$ the term $k = 0$ is $0^0 / 0! = 1$, matching the exponential series.

Proves `Wanted` entry `dobinski_formula_hasSum`.

Concept ID: `jis_dep_b5aac440aefd6e0d2de97890`.
Grounded record ID: `jis_grounded_f1b5718dcb195df798f06188`.
Source: `https://cs.uwaterloo.ca/journals/JIS/VOL14/Mezo/mezo9.tex`, lines 283-293.
Source file SHA-256: `dbddfbb43d2055fbdcfac511e341bda8ef2def13cb9d80ddd429b75ed1b02927`.
Source-text SHA-256: `f0df8e7588fe5cb6ca545ee2ce6973ea9dd1ffd15da7e303c1dadc9bc7d28a38`.
Corrected classical accounting: 2 mentions / 2 papers / 0 proof uses (2/2/0).
Only the classical Bell-number identity is stated here; the r-Bell generalizations are excluded.
-/
theorem dobinski_formula_hasSum (n : Nat) :
    HasSum (fun k : Nat => (k : Real) ^ n / (k.factorial : Real))
      (Real.exp 1 * (Nat.bell n : Real)) := by
  have e12 : Real.exp 1 * Real.exp (-1) = 1 := by
    calc Real.exp 1 * Real.exp (-1) = Real.exp ((1 : ℝ) + (-1)) :=
          (Real.exp_add 1 (-1)).symm
      _ = 1 := by
          have h01 : (1 : ℝ) + (-1) = 0 := by ring
          rw [h01, Real.exp_zero]
  have key : ∀ (N : ℕ) (m : ℕ), m ≤ N →
      HasSum (fun k : Nat => (k : Real) ^ m / (k.factorial : Real))
        (Real.exp 1 * (Nat.bell m : Real)) := by
    intro N
    induction N with
    | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0
      rw [Nat.bell_zero, Nat.cast_one, mul_one]
      have h2 : HasSum (fun k : ℕ => Real.exp (-1) / (k.factorial : ℝ)) 1 := by
        have h := ProbabilityTheory.hasSum_one_poissonMeasure (1 : NNReal)
        simpa using h
      have h3 := HasSum.mul_left (Real.exp 1) h2
      rw [mul_one] at h3
      refine HasSum.congr_fun h3 (fun k => ?_)
      simp only [pow_zero]
      rw [← mul_div_assoc, e12]
    | succ N ihN =>
      intro m hm
      by_cases hle : m ≤ N
      · exact ihN m hle
      · have hmeq : m = N + 1 := by omega
        subst hmeq
        set F : ℕ → ℝ := fun k : ℕ => (k : ℝ) ^ (N + 1) / (k.factorial : ℝ) with hFdef
        have bell_eq : ((Nat.bell (N + 1) : ℕ) : ℝ) =
            ∑ i ∈ Finset.range (N + 1), ((N.choose i : ℕ) : ℝ) * ((Nat.bell i : ℕ) : ℝ) := by
          have h := Nat.bell_succ N
          have hIic : Finset.Iic N = Finset.range (N + 1) := by
            ext i
            simp only [Finset.mem_Iic, Finset.mem_range]
            omega
          have hR : ((Nat.bell (N + 1) : ℕ) : ℝ) =
              ∑ i ∈ Finset.Iic N, ((N.choose i : ℕ) : ℝ) * ((Nat.bell (N - i) : ℕ) : ℝ) := by
            exact_mod_cast h
          rw [hIic] at hR
          rw [hR]
          have e1 : ∀ j : ℕ, N + 1 - 1 - j = N - j := fun j => by omega
          have step1 : (∑ i ∈ Finset.range (N + 1),
                ((N.choose i : ℕ) : ℝ) * ((Nat.bell (N - i) : ℕ) : ℝ))
              = ∑ j ∈ Finset.range (N + 1),
                (fun j : ℕ => ((N.choose (N - j) : ℕ) : ℝ) *
                  ((Nat.bell (N - (N - j)) : ℕ) : ℝ)) (N + 1 - 1 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjN : j ≤ N := by
              rw [Finset.mem_range] at hj
              omega
            have e2 : N - (N - j) = j := by omega
            change ((N.choose j : ℕ) : ℝ) * ((Nat.bell (N - j) : ℕ) : ℝ) =
              ((N.choose (N - (N + 1 - 1 - j)) : ℕ) : ℝ) *
                ((Nat.bell (N - (N - (N + 1 - 1 - j))) : ℕ) : ℝ)
            rw [e1 j, e2]
          rw [step1]
          have hrefl := Finset.sum_range_reflect
            (fun j : ℕ => ((N.choose (N - j) : ℕ) : ℝ) *
              ((Nat.bell (N - (N - j)) : ℕ) : ℝ)) (N + 1)
          rw [hrefl]
          apply Finset.sum_congr rfl
          intro j hj
          have hjN : j ≤ N := by
            rw [Finset.mem_range] at hj
            omega
          have e2 : N - (N - j) = j := by omega
          change ((N.choose (N - j) : ℕ) : ℝ) * ((Nat.bell (N - (N - j)) : ℕ) : ℝ) = _
          rw [e2, Nat.choose_symm hjN]
        have hEach : ∀ i ∈ Finset.range (N + 1),
            HasSum (fun j : ℕ => ((N.choose i : ℕ) : ℝ) * ((j : ℝ) ^ i / (j.factorial : ℝ)))
              (((N.choose i : ℕ) : ℝ) * (Real.exp 1 * ((Nat.bell i : ℕ) : ℝ))) := by
          intro i hi
          have hiN : i ≤ N := by
            rw [Finset.mem_range] at hi
            omega
          exact HasSum.mul_left _ (ihN i hiN)
        have hSum : ∀ (s : Finset ℕ), s ⊆ Finset.range (N + 1) → HasSum
            (fun j : ℕ => ∑ i ∈ s, ((N.choose i : ℕ) : ℝ) * ((j : ℝ) ^ i / (j.factorial : ℝ)))
            (∑ i ∈ s, ((N.choose i : ℕ) : ℝ) * (Real.exp 1 * ((Nat.bell i : ℕ) : ℝ))) := by
          intro s
          refine Finset.induction_on s ?_ ?_
          · intro _
            simp only [Finset.sum_empty]
            exact hasSum_zero
          · intro a t hat ihsub hsub
            have ha : a ∈ Finset.range (N + 1) := hsub (Finset.mem_insert_self a t)
            have hsub' : t ⊆ Finset.range (N + 1) :=
              fun x hx => hsub (Finset.mem_insert_of_mem hx)
            have h1 := hEach a ha
            have h2 := ihsub hsub'
            simp only [Finset.sum_insert hat]
            exact h1.add h2
        have hSum' := hSum (Finset.range (N + 1)) (Finset.Subset.refl _)
        have hmix : ∀ j : ℕ, ((j : ℝ) + 1) ^ N / (j.factorial : ℝ)
            = ∑ i ∈ Finset.range (N + 1),
              ((N.choose i : ℕ) : ℝ) * ((j : ℝ) ^ i / (j.factorial : ℝ)) := by
          intro j
          have hpow := add_pow (j : ℝ) 1 N
          rw [hpow, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          simp only [one_pow, mul_one]
          ring
        have hmixS : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ N / (j.factorial : ℝ)) :=
          Summable.congr hSum'.summable (fun j => (hmix j).symm)
        have hts : (∑' j : ℕ, ∑ i ∈ Finset.range (N + 1),
              ((N.choose i : ℕ) : ℝ) * ((j : ℝ) ^ i / (j.factorial : ℝ)))
            = ∑ i ∈ Finset.range (N + 1),
              ((N.choose i : ℕ) : ℝ) * (Real.exp 1 * ((Nat.bell i : ℕ) : ℝ)) :=
          hSum'.tsum_eq
        have hmixT : (∑' j : ℕ, ((j : ℝ) + 1) ^ N / (j.factorial : ℝ))
            = ∑ i ∈ Finset.range (N + 1),
              ((N.choose i : ℕ) : ℝ) * (Real.exp 1 * ((Nat.bell i : ℕ) : ℝ)) := by
          rw [← hts]
          exact tsum_congr (fun j => hmix j)
        have hV : (∑ i ∈ Finset.range (N + 1),
              ((N.choose i : ℕ) : ℝ) * (Real.exp 1 * ((Nat.bell i : ℕ) : ℝ)))
            = Real.exp 1 * ((Nat.bell (N + 1) : ℕ) : ℝ) := by
          calc (∑ i ∈ Finset.range (N + 1),
                ((N.choose i : ℕ) : ℝ) * (Real.exp 1 * ((Nat.bell i : ℕ) : ℝ)))
              = Real.exp 1 * (∑ i ∈ Finset.range (N + 1),
                ((N.choose i : ℕ) : ℝ) * ((Nat.bell i : ℕ) : ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
            _ = Real.exp 1 * ((Nat.bell (N + 1) : ℕ) : ℝ) := by rw [bell_eq]
        have hgHas : HasSum (fun j : ℕ => ((j : ℝ) + 1) ^ N / (j.factorial : ℝ))
            (Real.exp 1 * ((Nat.bell (N + 1) : ℕ) : ℝ)) := by
          rw [← hV, ← hmixT]
          exact hmixS.hasSum
        have hcomp : ∀ j : ℕ, F (j + 1) = ((j : ℝ) + 1) ^ N / (j.factorial : ℝ) := by
          intro j
          have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
          have hjF : ((j.factorial : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero j
          have hN1 : N + 1 ≠ 0 := by omega
          simp only [hFdef]
          rw [Nat.factorial_succ]
          push_cast
          rw [pow_succ]
          field_simp
        have h1 : Summable (fun j : ℕ => F (j + 1)) :=
          Summable.congr hmixS (fun j => (hcomp j).symm)
        have hfSumm : Summable F := (summable_nat_add_iff 1).mp h1
        have hF0 : F 0 = 0 := by
          have hN1 : N + 1 ≠ 0 := by omega
          simp only [hFdef]
          rw [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one,
            zero_pow hN1, zero_div]
        have htsum : (∑' k : ℕ, F k) = Real.exp 1 * ((Nat.bell (N + 1) : ℕ) : ℝ) := by
          have h0 := hfSumm.tsum_eq_zero_add
          rw [hF0, zero_add] at h0
          have hts2 : (∑' b : ℕ, F (b + 1))
              = ∑' j : ℕ, ((j : ℝ) + 1) ^ N / (j.factorial : ℝ) :=
            tsum_congr (fun b => hcomp b)
          rw [hts2, hgHas.tsum_eq] at h0
          exact h0
        rw [← htsum]
        exact hfSumm.hasSum
  exact key n n le_rfl

end MetaMathlibExt
