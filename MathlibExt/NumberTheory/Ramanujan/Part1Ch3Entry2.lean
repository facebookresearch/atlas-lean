/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry2Rightsummable

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 2

∑ x^(j+1)/((z+j) j!) is eˣ times an alternating rising-product series; in particular the
left-hand series is summable.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry2

private lemma key_identity (z : ℂ) (hz : ∀ r : ℕ, (z + (r : ℂ)) ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))) =
    1 / ((z + (n : ℂ)) * (Nat.factorial n : ℂ)) := by
  have hP : ∀ j : ℕ, (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))) ≠ 0 := by
    intro j
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact hz k
  have hfact : ∀ m : ℕ, ((Nat.factorial m : ℂ)) ≠ 0 := by
    intro m
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  set Q : ℕ → ℂ := fun j => if j = 0 then 1 else ∏ k ∈ Finset.range j, (z + (k : ℂ)) with hQdef
  have hQ0 : Q 0 = 1 := by simp [hQdef]
  have hQne : ∀ j, Q j ≠ 0 := by
    intro j
    by_cases hj : j = 0
    · simp [hQdef, hj]
    · simp only [hQdef, hj, ite_false]
      rw [Finset.prod_ne_zero_iff]
      intro k _
      exact hz k
  have hPQ : ∀ j, (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))) = Q j * (z + (j : ℂ)) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [hQdef]
    · have h1 : Q j = ∏ k ∈ Finset.range j, (z + (k : ℂ)) := by simp [hQdef, hj]
      rw [h1, Finset.prod_range_succ]
  have hQsucc : ∀ i, Q (i + 1) = ∏ k ∈ Finset.range (i + 1), (z + (k : ℂ)) := by
    intro i
    simp [hQdef]
  suffices h : (z + (n : ℂ)) * (∑ j ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))))) =
      1 / (Nat.factorial n : ℂ) by
    have hzne : (z + (n : ℂ)) ≠ 0 := hz n
    have hfn : ((Nat.factorial n : ℂ)) ≠ 0 := hfact n
    rw [eq_div_iff (mul_ne_zero hzne hfn)]
    have hring : (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))))) *
        ((z + (n : ℂ)) * (Nat.factorial n : ℂ)) =
        ((z + (n : ℂ)) * (∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))))) *
        (Nat.factorial n : ℂ) := by ring
    rw [hring, h]
    field_simp
  set F : ℕ → ℂ := fun j => (-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * Q j) with hFdef
  set G : ℕ → ℂ := fun j => if j = n then 0 else (-1 : ℂ) ^ j / ((Nat.factorial (n - j - 1) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))) with hGdef
  have hGn : G n = 0 := by simp [hGdef]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (z + (n : ℂ)) * ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))) = F j + G j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := Nat.le_of_lt_succ hj
    have hsub : ((((n - j : ℕ))) : ℂ) = ((n : ℂ)) - ((j : ℂ)) := Nat.cast_sub hjn
    have hcast : ((n : ℂ)) = ((j : ℂ)) + ((((n - j : ℕ))) : ℂ) := by rw [hsub]; ring
    have hsplit : (z + (n : ℂ)) = (z + (j : ℂ)) + ((((n - j : ℕ))) : ℂ) := by rw [hcast]; ring
    have hzj : (z + (j : ℂ)) ≠ 0 := hz j
    have hQj : Q j ≠ 0 := hQne j
    have hfj : ((Nat.factorial (n - j) : ℂ)) ≠ 0 := hfact _
    have hPj : (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))) ≠ 0 := hP j
    have e1 : (z + (j : ℂ)) * ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))) = F j := by
      simp only [hFdef]
      rw [hPQ j, ← mul_div_assoc,
        div_eq_div_iff (mul_ne_zero hfj (mul_ne_zero hQj hzj)) (mul_ne_zero hfj hQj)]
      ring
    have e2 : ((((n - j : ℕ))) : ℂ) * ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))) = G j := by
      by_cases hjn2 : j = n
      · subst hjn2
        simp [hGdef]
      · simp only [hGdef, hjn2, ite_false]
        have hlt : j < n := Nat.lt_of_le_of_ne hjn hjn2
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - j ≠ 0)
        have hk2 : n - j - 1 = k := by omega
        have hfacteq : Nat.factorial (n - j) = (n - j) * Nat.factorial (n - j - 1) := by
          rw [hk2, hk, Nat.factorial_succ]
        have hne1 : ((((n - j : ℕ))) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hD1 : ((Nat.factorial (n - j - 1) : ℂ)) ≠ 0 := hfact _
        have hfactcast : ((Nat.factorial (n - j) : ℂ)) = ((((n - j : ℕ))) : ℂ) * ((Nat.factorial (n - j - 1) : ℂ)) := by
          rw [hfacteq]; push_cast; ring
        rw [hfactcast, ← mul_div_assoc,
          div_eq_div_iff (mul_ne_zero (mul_ne_zero hne1 hD1) hPj) (mul_ne_zero hD1 hPj)]
        ring
    rw [hsplit, add_mul, e1, e2]
  rw [Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.range (n + 1), ((z + (n : ℂ)) * ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))))) =
      ∑ j ∈ Finset.range (n + 1), F j + ∑ j ∈ Finset.range (n + 1), G j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j hj
  rw [hsum]
  have hFsplit : ∑ j ∈ Finset.range (n + 1), F j = (∑ i ∈ Finset.range n, F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F n
  have hGsplit : ∑ j ∈ Finset.range (n + 1), G j = ∑ i ∈ Finset.range n, G i := by
    rw [Finset.sum_range_succ, hGn, add_zero]
  rw [hFsplit, hGsplit]
  have hcancel : ∀ i ∈ Finset.range n, F (i + 1) + G i = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hilt : i < n := hi
    have hQeq : Q (i + 1) = ∏ k ∈ Finset.range (i + 1), (z + (k : ℂ)) := hQsucc i
    have hine : i ≠ n := Nat.ne_of_lt hilt
    simp only [hFdef, hGdef, hine, ite_false]
    have hsub : n - (i + 1) = n - i - 1 := by omega
    rw [hsub, ← hQeq]
    have hD : ((Nat.factorial (n - i - 1) : ℂ) * Q (i + 1)) ≠ 0 :=
      mul_ne_zero (hfact _) (hQne _)
    field_simp
    have hpow : (-1 : ℂ) ^ (i + 1) = -(-1 : ℂ) ^ i := by ring
    rw [hpow]
    ring
  have hzero : (∑ i ∈ Finset.range n, F (i + 1)) + (∑ i ∈ Finset.range n, G i) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    exact hcancel i hi
  have hF0 : F 0 = 1 / (Nat.factorial n : ℂ) := by
    simp [hFdef, hQ0]
  calc (∑ i ∈ Finset.range n, F (i + 1)) + F 0 + ∑ i ∈ Finset.range n, G i
      = ((∑ i ∈ Finset.range n, F (i + 1)) + ∑ i ∈ Finset.range n, G i) + F 0 := by ring
    _ = 0 + F 0 := by rw [hzero]
    _ = 1 / (Nat.factorial n : ℂ) := by rw [zero_add, hF0]

/-- **Ramanujan's exponential transformation of a factorial series (Chapter 3, Entry 2).** For all
complex numbers $x$ and $z$ such that $z + r \ne 0$ for every natural number $r$, the series
$\sum_{j \ge 0} \frac{x^{j+1}}{(z+j)\, j!}$ converges absolutely, and its sum is
$e^x \sum_{j \ge 0} \frac{(-1)^j x^{j+1}}{z(z+1)\cdots(z+j)}$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 2, formula (2.1), printed
    p. 46 / PDF p. 56.
Proves `Wanted` entry `ramanujan_part1_ch3_entry2`.
-/
theorem ramanujan_part1_ch3_entry2 (x z : ℂ) (hz : ∀ r : ℕ, (z + (r : ℂ)) ≠ 0) :
    HasSum (fun j : ℕ => x ^ (j + 1) / ((z + (j : ℂ)) * (Nat.factorial j : ℂ)))
      (Complex.exp x * ∑' (j : ℕ),
          ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))) := by
  have hfExp : HasSum (fun m : ℕ => x ^ m / (Nat.factorial m : ℂ)) (Complex.exp x) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) x
    rwa [← Complex.exp_eq_exp_ℂ] at h
  have hEnorm : Summable fun m : ℕ => ‖x ^ m / (Nat.factorial m : ℂ)‖ := by
    have hEq : (fun m : ℕ => ‖x ^ m / (Nat.factorial m : ℂ)‖) =
        (fun m : ℕ => ‖x‖ ^ m / (Nat.factorial m : ℝ)) := by
      funext m
      rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [hEq]
    exact Real.summable_pow_div_factorial _
  have hBnorm := (Entry2Rightsummable.ramanujan_part1_ch3_entry2_rightsummable x z hz).norm
  have hcauchy := hasSum_sum_range_mul_of_summable_norm hEnorm hBnorm
  have hrefl : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (x ^ k / (Nat.factorial k : ℂ)) *
        ((-1 : ℂ) ^ (n - k) * x ^ ((n - k) + 1) / ∏ kk ∈ Finset.range ((n - k) + 1), (z + (kk : ℂ))))
      = ∑ j ∈ Finset.range (n + 1), (x ^ (n - j) / (Nat.factorial (n - j) : ℂ)) *
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ))) := by
    intro n
    have h := Finset.sum_range_reflect
      (fun j => (x ^ (n - j) / (Nat.factorial (n - j) : ℂ)) *
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ)))) (n + 1)
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := Nat.le_of_lt_succ hj
    have e : n + 1 - 1 - j = n - j := by omega
    show (x ^ j / (Nat.factorial j : ℂ)) *
        ((-1 : ℂ) ^ (n - j) * x ^ ((n - j) + 1) / ∏ kk ∈ Finset.range ((n - j) + 1), (z + (kk : ℂ)))
      = (x ^ (n - (n + 1 - 1 - j)) / (Nat.factorial (n - (n + 1 - 1 - j)) : ℂ)) *
        ((-1 : ℂ) ^ (n + 1 - 1 - j) * x ^ ((n + 1 - 1 - j) + 1) / ∏ kk ∈ Finset.range ((n + 1 - 1 - j) + 1), (z + (kk : ℂ)))
    rw [e, Nat.sub_sub_self hjn]
  have hterm : ∀ n : ℕ, ∀ j ∈ Finset.range (n + 1),
      (x ^ (n - j) / (Nat.factorial (n - j) : ℂ)) *
        ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ)))
      = x ^ (n + 1) * ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ)))) := by
    intro n j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := Nat.le_of_lt_succ hj
    have hpow : x ^ (n - j) * x ^ (j + 1) = x ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    calc (x ^ (n - j) / (Nat.factorial (n - j) : ℂ)) *
          ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ)))
        = ((-1 : ℂ) ^ j * (x ^ (n - j) * x ^ (j + 1))) /
          ((Nat.factorial (n - j) : ℂ) * ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ))) := by ring
      _ = x ^ (n + 1) * ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ)))) := by
          rw [hpow]; ring
  have hconv : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (x ^ k / (Nat.factorial k : ℂ)) *
        ((-1 : ℂ) ^ (n - k) * x ^ ((n - k) + 1) / ∏ kk ∈ Finset.range ((n - k) + 1), (z + (kk : ℂ))))
      = x ^ (n + 1) / ((z + (n : ℂ)) * (Nat.factorial n : ℂ)) := by
    intro n
    have e1 := hrefl n
    have e2 : (∑ j ∈ Finset.range (n + 1), (x ^ (n - j) / (Nat.factorial (n - j) : ℂ)) *
          ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ))))
        = x ^ (n + 1) * (∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j / ((Nat.factorial (n - j) : ℂ) * ∏ kk ∈ Finset.range (j + 1), (z + (kk : ℂ))))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm n j hj)
    rw [e1, e2, key_identity z hz n, mul_one_div]
  have hexp : (∑' m : ℕ, x ^ m / (Nat.factorial m : ℂ)) = Complex.exp x := hfExp.tsum_eq
  have hfin := hcauchy.congr_fun (fun n => (hconv n).symm)
  rw [hexp] at hfin
  exact hfin

end Entry2

namespace Entry2Leftsummable

/-- **Convergence of the left side of Ramanujan's Chapter 3, Entry 2.** For all complex numbers
$x$ and $z$ such that $z + r \ne 0$ for every natural number $r$, the series
$\sum_{j \ge 0} \frac{x^{j+1}}{(z+j)\, j!}$ converges absolutely.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 2, formula (2.1), printed
    p. 46 / PDF p. 56.
Proves `Wanted` entry `ramanujan_part1_ch3_entry2_leftsummable`.
-/
theorem ramanujan_part1_ch3_entry2_leftsummable (x z : ℂ) (hz : ∀ r : ℕ, z + (r : ℂ) ≠ 0) :
    Summable (fun j : ℕ => x ^ (j + 1) / ((z + (j : ℂ)) * (Nat.factorial j : ℂ))) :=
  (Entry2.ramanujan_part1_ch3_entry2 x z hz).summable

end Entry2Leftsummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
