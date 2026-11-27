/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.AcceleratedZeckendorfGame
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Weight
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination
import all MathlibExt.Combinatorics.AcceleratedZeckendorfGame
import all MathlibExt.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound

/-!
# Termination and the length bound for the Accelerated Zeckendorf Game

Starting with `n` copies of `F₁`, there is no infinite play. Every complete game ends at the
Zeckendorf decomposition of `n`, and its number of moves satisfies the upper bound of Theorem 1.3.
This includes `n = 0`, for which the empty state is terminal and the bound is zero.

## References

* Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin,
  *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1, pp. 3–14,
  Theorem 1.3.
* Paul Baird-Smith, Alyssa Epstein, Kristen Flint, and Steven J. Miller, *The Zeckendorf Game*,
  in *Combinatorial and Additive Number Theory III*, Springer Proceedings in Mathematics &
  Statistics 297 (2020), pp. 25–38, §1 (termination of the ordinary game).
* Anna Cusenza, Aidan Dunkelberg, Kate Huffman, Dianhui Ke, Micah McClatchey, Steven J. Miller,
  Clayton Mizgerd, Vashisth Tiwari, Jingkai Ye, and Xiaoyan Zheng, *Bounds on Zeckendorf Games*,
  The Fibonacci Quarterly 60 (2022), no. 1, pp. 57–71, Theorem 1.3 and §3, equations (3.15)–(3.20)
  (the length potential and its real-valued upper estimate).
* Édouard Zeckendorf, *Représentation des nombres naturels par une somme de nombres de Fibonacci
  ou de nombres de Lucas*, Bulletin de la Société Royale des Sciences de Liège 41 (1972),
  pp. 179–182 (uniqueness of the decomposition, used via Mathlib's `Nat.zeckendorf_sum_fib`).
* The Lean proof uses `accelZeckRank_lt` from `MathlibExt.Combinatorics.AcceleratedZeckendorfGame`
  and `accelZeckGame_invariant`, `accelZeckTerminal_counts` and `accelZeckTerminal_adjacent` from
  `MathlibExt.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound`. The move-by-move
  potential calculation uses the subtraction argument of `accelZeckRank_lt` and
  `accelZeckRank_remove`.
-/

namespace MetaMathlibExt

open scoped BigOperators goldenRatio

private theorem accelZeckTerminal_sorted_support {s : ℕ →₀ ℕ} {n : ℕ}
    (ht : ∀ t, ¬ AccelZeckMove s t) (hzero : s 0 = 0)
    (hsum : ∑ i ∈ s.support, Nat.fib (i + 1) = n) :
    (Nat.zeckendorf n).map (· - 1) = s.support.sort (· ≥ ·) := by
  let l := s.support.sort (· ≥ ·)
  have hmem {i : ℕ} (hi : i ∈ l) : s i ≠ 0 :=
    Finsupp.mem_support_iff.mp ((Finset.mem_sort (· ≥ ·)).mp hi)
  have hrep : (l.map (· + 1)).IsZeckendorfRep := by
    let : IsTrans ℕ (fun a b => b + 2 ≤ a) := ⟨fun _ _ _ hab hbc => by omega⟩
    rw [List.IsZeckendorfRep, List.isChain_iff_pairwise, List.pairwise_append]
    refine ⟨List.pairwise_map.mpr ?_, by simp, ?_⟩
    · refine (s.support.sortedGT_sort.pairwise).imp_of_mem (fun {a b} ha hb hab => ?_)
      by_contra! h
      have hnext : s (b + 1) ≠ 0 := by
        rw [show b + 1 = a by omega]
        exact hmem ha
      exact hmem hb (accelZeckTerminal_adjacent s ht hzero b hnext)
    · intro a ha b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      have hb' : b = 0 := by simpa using hb
      have hi' : i ≠ 0 := fun h => hmem hi (h ▸ hzero)
      omega
  have hsum' : ((l.map (· + 1)).map Nat.fib).sum = n := by
    rw [← hsum, List.map_map, Finset.sum_eq_multiset_sum, ← s.support.sort_eq (· ≥ ·)]
    rfl
  have heq := Nat.zeckendorf_sum_fib hrep
  rw [hsum'] at heq
  rw [heq, List.map_map]
  simp [Function.comp_def, l]

-- The length potential of a token at the paper's index i is F_(i+2) - i - 2.
private noncomputable def accelZeckLengthWeight (i : ℕ) : ℝ :=
  (Nat.fib (i + 3) : ℝ) - i - 2

private noncomputable abbrev accelZeckLengthPotential : (ℕ →₀ ℕ) →+ ℝ :=
  Finsupp.weight accelZeckLengthWeight

private theorem accelZeckLengthPotential_step {s t : ℕ →₀ ℕ} (h : AccelZeckMove s t) :
    accelZeckLengthPotential s + 1 ≤ accelZeckLengthPotential t := by
  have remove (u : ℕ →₀ ℕ) (i m : ℕ) (hm : m ≤ u i) :
      accelZeckLengthPotential (u - Finsupp.single i m) =
        accelZeckLengthPotential u - m * accelZeckLengthWeight i := by
    apply eq_sub_of_add_eq
    rw [← nsmul_eq_mul, ← Finsupp.weight_single, ← map_add,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hm)]
  rcases h with ⟨m, hm, ⟨i, hi, h₁, h₂, rfl⟩ | ⟨h₁, rfl⟩ | ⟨h₂, rfl⟩ | ⟨i, hi, hᵢ, rfl⟩⟩
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hi' : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
    have h₂' : m ≤ (s - Finsupp.single (i - 1) m) i := by
      simpa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (by omega : i ≠ i - 1)] using h₂
    have hf : Nat.fib (i + 1 + 3) = Nat.fib (i - 1 + 3) + Nat.fib (i + 3) := by
      rw [show i + 1 + 3 = (i + 2) + 2 by omega, show i - 1 + 3 = i + 2 by omega,
        Nat.fib_add_two]
    have hcost : accelZeckLengthWeight (i + 1) - accelZeckLengthWeight (i - 1) -
        accelZeckLengthWeight i = i := by
      rw [accelZeckLengthWeight, accelZeckLengthWeight, accelZeckLengthWeight, hf]
      push_cast [Nat.cast_sub (by omega : 1 ≤ i)]
      ring
    calc
      _ ≤ accelZeckLengthPotential s + (m : ℝ) * i :=
        add_le_add_right (one_le_mul_of_one_le_of_one_le hm' hi') _
      _ = _ := by
        simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, remove _ _ _ h₂', remove _ _ _ h₁]
        linear_combination -(m : ℝ) * hcost
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, remove _ _ _ h₁]
    norm_num [accelZeckLengthWeight, Nat.cast_mul]
    linarith
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, remove _ _ _ h₂]
    norm_num [accelZeckLengthWeight, Nat.cast_mul]
    linarith
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hf : Nat.fib (i - 2 + 3) + Nat.fib (i + 1 + 3) = 2 * Nat.fib (i + 3) := by
      have h₁ : Nat.fib (i + 3) = Nat.fib (i + 1) + Nat.fib (i + 2) := @Nat.fib_add_two (i + 1)
      have h₂ : Nat.fib (i + 4) = Nat.fib (i + 2) + Nat.fib (i + 3) := @Nat.fib_add_two (i + 2)
      rw [show i - 2 + 3 = i + 1 by omega, show i + 1 + 3 = i + 4 by omega]
      omega
    have hcost : accelZeckLengthWeight (i - 2) + accelZeckLengthWeight (i + 1) -
        2 * accelZeckLengthWeight i = 1 := by
      have hf' : (Nat.fib (i - 2 + 3) : ℝ) + Nat.fib (i + 1 + 3) = 2 * Nat.fib (i + 3) := by
        exact_mod_cast hf
      simp only [accelZeckLengthWeight, Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ i),
        Nat.cast_ofNat, Nat.cast_one]
      linarith only [hf']
    calc
      _ ≤ accelZeckLengthPotential s + (m : ℝ) := add_le_add_right hm' _
      _ = _ := by
        simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, remove _ _ _ hᵢ, Nat.cast_mul,
          Nat.cast_ofNat]
        linear_combination -(m : ℝ) * hcost

private theorem accelZeckLengthWeight_le {i : ℕ} (hi : 1 ≤ i) :
    accelZeckLengthWeight i ≤ (φ + 1) * (Nat.fib (i + 1) : ℝ) - i - φ := by
  have hpow : ψ ^ (i + 1) ≤ ψ ^ 2 := calc
    _ ≤ |ψ ^ (i + 1)| := le_abs_self _
    _ = |ψ| ^ (i + 1) := abs_pow ..
    _ ≤ |ψ| ^ 2 := pow_le_pow_of_le_one (abs_nonneg _) (abs_le.mpr
      ⟨Real.neg_one_lt_goldenConj.le, Real.goldenConj_neg.le.trans zero_le_one⟩) (by omega)
    _ = ψ ^ 2 := sq_abs _
  have hf := Real.fib_succ_sub_goldenRatio_mul_fib (i + 1)
  have hstep : (Nat.fib (i + 3) : ℝ) = Nat.fib (i + 1) + Nat.fib (i + 2) := by
    exact_mod_cast (@Nat.fib_add_two (i + 1))
  unfold accelZeckLengthWeight
  linarith only [hf, hstep, hpow, Real.goldenConj_sq, Real.goldenRatio_add_goldenConj]

@[expose] public section

/-- **The Accelerated Zeckendorf Game terminates at the Zeckendorf decomposition.** Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n$ be a natural
number, let $Z(n)$ be the number of terms of the Zeckendorf decomposition of $n$, and let $IZ(n)$
be the sum of the indices $k$ of its terms $F_k$. Then there is no infinite sequence of moves
starting from $n$ copies of $F_1$. Moreover, every complete Accelerated Zeckendorf Game on $n$
(a sequence of moves from $n$ copies of $F_1$ to a state from which no move is possible) ends at
the state with one copy of each term of the Zeckendorf decomposition of $n$, and its number $L$
of moves satisfies

$$L \le \frac{3 + \sqrt 5}{2} n - IZ(n) - \frac{1 + \sqrt 5}{2} Z(n).$$

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.3. -/
public theorem accelZeckGame_terminates_at_zeckendorf (n : ℕ) :
    (¬ ∃ g : ℕ → ℕ →₀ ℕ,
        g 0 = Finsupp.single 1 n ∧ ∀ j, AccelZeckMove (g j) (g (j + 1))) ∧
      ∀ L g, IsAccelZeckGame n L g →
        g L = zeckendorfState n ∧
          (L : ℝ) ≤ (Real.sqrt 5 + 3) / 2 * n - (((Nat.zeckendorf n).map (· - 1)).sum : ℕ) -
            (1 + Real.sqrt 5) / 2 * (Nat.zeckendorf n).length := by
  constructor
  · rintro ⟨g, _, hmove⟩
    obtain ⟨j, hj⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
      (fun j => accelZeckRank (g j))
    exact hj (accelZeckRank_lt (hmove j))
  intro L g hg
  let s := g L
  have hinv := accelZeckGame_invariant n L g hg L le_rfl
  have hzero : s 0 = 0 := hinv.2 0 (Or.inl rfl)
  have hpos {i : ℕ} (hi : i ∈ s.support) : 1 ≤ i := by
    by_contra! h
    exact Finsupp.mem_support_iff.mp hi (by rwa [show i = 0 by omega])
  have hcount {i : ℕ} (hi : i ∈ s.support) : s i = 1 := by
    have hne := Finsupp.mem_support_iff.mp hi
    have hle := accelZeckTerminal_counts s hg.2.2 i (hpos hi)
    omega
  have hsum : ∑ i ∈ s.support, Nat.fib (i + 1) = n := by
    rw [← hinv.1]
    change _ = ∑ i ∈ s.support, s i * Nat.fib (i + 1)
    exact Finset.sum_congr rfl fun i hi => by rw [hcount hi, one_mul]
  have hlist : (Nat.zeckendorf n).map (· - 1) = s.support.sort (· ≥ ·) :=
    accelZeckTerminal_sorted_support hg.2.2 hzero hsum
  refine ⟨?_, ?_⟩
  · change s = (↑((Nat.zeckendorf n).map (· - 1)) : Multiset ℕ).toFinsupp
    rw [hlist, Finset.sort_eq]
    ext i
    rw [Multiset.toFinsupp_apply, Multiset.count_eq_of_nodup s.support.nodup]
    by_cases hi : i ∈ s.support
    · simp [hi, hcount hi]
    · simp [hi, Finsupp.notMem_support_iff.mp hi]
  have hsteps (j : ℕ) (hj : j ≤ L) : (j : ℝ) ≤ accelZeckLengthPotential (g j) := by
    induction j with
    | zero =>
      rw [hg.1, Finsupp.weight_single]
      norm_num [accelZeckLengthWeight, nsmul_eq_mul]
    | succ j ih =>
      rw [Nat.cast_succ]
      exact (add_le_add_left (ih (by omega)) 1).trans
        (accelZeckLengthPotential_step (hg.2.1 j (by omega)))
  have hvalue : (∑ i ∈ s.support, (Nat.fib (i + 1) : ℝ)) = n := by exact_mod_cast hsum
  have hindices : (∑ i ∈ s.support, (i : ℝ)) =
      (((Nat.zeckendorf n).map (· - 1)).sum : ℕ) := by
    norm_cast
    rw [hlist, Finset.sum_eq_multiset_sum, ← s.support.sort_eq (· ≥ ·)]
    rfl
  have hlength : s.support.card = (Nat.zeckendorf n).length := by
    rw [← List.length_map (f := fun i : ℕ => i - 1), hlist, Finset.length_sort]
  calc
    (L : ℝ) ≤ accelZeckLengthPotential s := hsteps L le_rfl
    _ = ∑ i ∈ s.support, accelZeckLengthWeight i := by
      rw [Finsupp.weight_apply]
      exact Finset.sum_congr rfl fun i hi => by simp only [hcount hi, one_smul]
    _ ≤ ∑ i ∈ s.support, ((φ + 1) * (Nat.fib (i + 1) : ℝ) - (i : ℝ) - φ) :=
      Finset.sum_le_sum fun _ hi => accelZeckLengthWeight_le (hpos hi)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hvalue, hindices,
        Finset.sum_const, nsmul_eq_mul, hlength]
      unfold Real.goldenRatio
      ring

end

end MetaMathlibExt
