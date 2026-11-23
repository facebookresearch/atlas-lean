/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7 Example 1 (boundary)

∑ arctan(2/((√5-1)/2+k+1)²) = π/2.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example1Boundary

private lemma c_pos : 0 < (Real.sqrt 5 - 1) / 2 := by
  have h1 : (1 : ℝ) < Real.sqrt 5 := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt 5 := by
          apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private lemma c_mul : ((Real.sqrt 5 - 1) / 2) * (((Real.sqrt 5 - 1) / 2) + 1) = 1 := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hring : ((Real.sqrt 5 - 1) / 2) * (((Real.sqrt 5 - 1) / 2) + 1)
      = ((Real.sqrt 5) ^ 2 - 1) / 4 := by ring
  rw [hring, h5]
  norm_num

private lemma term_eq (k : ℕ) :
    Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2))
      = Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (k : ℝ)))
        - Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (k : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < (Real.sqrt 5 - 1) / 2 + (k : ℝ) := by
    have hc := c_pos
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 : (0 : ℝ) < (Real.sqrt 5 - 1) / 2 + (k : ℝ) + 2 := by linarith
  have eM : ((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1))
      = (((Real.sqrt 5 - 1) / 2 + (k : ℝ)) + 1) := by ring
  rw [eM]
  generalize (Real.sqrt 5 - 1) / 2 + (k : ℝ) = u at h1 h2 ⊢
  have n1 : u ≠ 0 := ne_of_gt h1
  have n2 : u + 2 ≠ 0 := ne_of_gt h2
  have ha : (0 : ℝ) < 1 / u := one_div_pos.mpr h1
  have hb : (0 : ℝ) < 1 / (u + 2) := one_div_pos.mpr h2
  have hab : (1 / u) * (-(1 / (u + 2))) < 1 := by
    have hpos : 0 < (1 / u) * (1 / (u + 2)) := mul_pos ha hb
    have heq : (1 / u) * (-(1 / (u + 2)))
        = -((1 / u) * (1 / (u + 2))) := by ring
    linarith
  have hadd := Real.arctan_add hab
  rw [Real.arctan_neg] at hadd
  have hN : (1 / u + -(1 / (u + 2))) = 2 / (u * (u + 2)) := by
    field_simp
    ring
  have hD : (1 - (1 / u) * (-(1 / (u + 2)))) = (u + 1) ^ 2 / (u * (u + 2)) := by
    field_simp
    ring
  have hfrac : ((1 / u + -(1 / (u + 2))) / (1 - (1 / u) * (-(1 / (u + 2)))))
      = 2 / ((u + 1) ^ 2) := by
    rw [hN, hD]
    have hne : u * (u + 2) ≠ 0 := mul_ne_zero n1 n2
    field_simp
  rw [hfrac] at hadd
  linarith

/-- **Arctangent series at the exceptional point (Entry 7, Example 1).** Let
$c = (\sqrt{5} - 1)/2$. The series
$$\sum_{k=0}^{\infty} \arctan \frac{2}{(c + k + 1)^2}$$
converges absolutely and its sum is $\pi/2$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2,
    boundary consequence of Entry 7, Example 1, formula (7.4), printed p. 36 / PDF p. 46.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example1_boundary`.
-/
theorem ramanujan_part1_ch2_entry7_example1_boundary :
    HasSum (fun k : ℕ => Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2)))
        (Real.pi / 2) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2)) := by
    intro k
    apply le_of_lt
    rw [Real.arctan_pos]
    have hm : (0 : ℝ) < (Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1) := by
      have hc := c_pos
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_pos (by norm_num) (pow_pos hm 2)
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr ?_
  have hstep : ∀ k : ℕ, Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2))
      = (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (k : ℝ)))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (k : ℝ) + 1)))
        - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((((k + 1 : ℕ))) : ℝ)))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((((k + 1 : ℕ))) : ℝ) + 1))) := by
    intro k
    rw [term_eq k]
    push_cast
    ring_nf
  have hpoint : ∀ N : ℕ, (∑ k ∈ Finset.range N, Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2)))
      = (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ)))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ) + 1)))
        - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ))))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ)) + 1))) := by
    intro N
    have hsub := Finset.sum_range_sub' (fun n : ℕ => Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((n : ℝ))))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((n : ℝ)) + 1))) N
    have hsub' : (∑ x ∈ Finset.range N, ((Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((x : ℝ))))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((x : ℝ)) + 1)))
        - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((((x + 1 : ℕ))) : ℝ)))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((((x + 1 : ℕ))) : ℝ) + 1)))))
        = (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ)))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ) + 1)))
        - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ))))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ)) + 1))) := hsub
    calc (∑ k ∈ Finset.range N, Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2)))
        = (∑ x ∈ Finset.range N, ((Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((x : ℝ))))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((x : ℝ)) + 1)))
        - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((((x + 1 : ℕ))) : ℝ)))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((((x + 1 : ℕ))) : ℝ) + 1))))) :=
          Finset.sum_congr rfl (fun k _ => hstep k)
      _ = _ := hsub'
  have hg0 : (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ)))
      + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ) + 1))) = Real.pi / 2 := by
    simp only [Nat.cast_zero, add_zero]
    have e0 : (1 : ℝ) / ((Real.sqrt 5 - 1) / 2) = (Real.sqrt 5 - 1) / 2 + 1 := by
      have hne : ((Real.sqrt 5 - 1) / 2) ≠ 0 := ne_of_gt c_pos
      rw [div_eq_iff hne, mul_comm]
      exact c_mul.symm
    have e1 : (1 : ℝ) / ((Real.sqrt 5 - 1) / 2 + 1) = (Real.sqrt 5 - 1) / 2 := by
      have hne : ((Real.sqrt 5 - 1) / 2 + 1) ≠ 0 := ne_of_gt (by linarith [c_pos])
      rw [div_eq_iff hne]
      exact c_mul.symm
    rw [e0, e1]
    have h := Real.arctan_inv_of_pos c_pos
    have ec : ((Real.sqrt 5 - 1) / 2)⁻¹ = (Real.sqrt 5 - 1) / 2 + 1 :=
      inv_eq_of_mul_eq_one_right c_mul
    rw [ec] at h
    linarith
  have hg : Filter.Tendsto (fun N : ℕ => Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ))))
      + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ)) + 1))) Filter.atTop (nhds 0) := by
    have base1 : Filter.Tendsto (fun n : ℕ => (Real.sqrt 5 - 1) / 2 + (n : ℝ)) Filter.atTop Filter.atTop := by
      have h := Filter.tendsto_atTop_add_const_right Filter.atTop ((Real.sqrt 5 - 1) / 2)
        tendsto_natCast_atTop_atTop
      have heq : (fun n : ℕ => (Real.sqrt 5 - 1) / 2 + (n : ℝ))
          = (fun n : ℕ => (n : ℝ) + ((Real.sqrt 5 - 1) / 2)) := by
        funext n; ring
      rw [heq]; exact h
    have base2 : Filter.Tendsto (fun n : ℕ => (Real.sqrt 5 - 1) / 2 + (n : ℝ) + 1) Filter.atTop Filter.atTop := by
      have h := Filter.tendsto_atTop_add_const_right Filter.atTop (((Real.sqrt 5 - 1) / 2) + 1)
        tendsto_natCast_atTop_atTop
      have heq : (fun n : ℕ => (Real.sqrt 5 - 1) / 2 + (n : ℝ) + 1)
          = (fun n : ℕ => (n : ℝ) + (((Real.sqrt 5 - 1) / 2) + 1)) := by
        funext n; ring
      rw [heq]; exact h
    have t1 : Filter.Tendsto (fun n : ℕ => ((Real.sqrt 5 - 1) / 2 + (n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp base1
    have t2 : Filter.Tendsto (fun n : ℕ => ((Real.sqrt 5 - 1) / 2 + (n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp base2
    have a1 : Filter.Tendsto (fun n : ℕ => Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (n : ℝ)))) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun n : ℕ => Real.arctan (((Real.sqrt 5 - 1) / 2 + (n : ℝ))⁻¹)) Filter.atTop
          (nhds (Real.arctan 0)) :=
        (Real.continuous_arctan.tendsto 0).comp t1
      simpa [Real.arctan_zero] using h
    have a2 : Filter.Tendsto (fun n : ℕ => Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun n : ℕ => Real.arctan (((Real.sqrt 5 - 1) / 2 + (n : ℝ) + 1)⁻¹)) Filter.atTop
          (nhds (Real.arctan 0)) :=
        (Real.continuous_arctan.tendsto 0).comp t2
      simpa [Real.arctan_zero] using h
    have h := a1.add a2
    simpa using h
  have hlim : Filter.Tendsto (fun N : ℕ => (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ)))
      + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ) + 1)))
      - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ))))
      + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ)) + 1)))) Filter.atTop (nhds (Real.pi / 2)) := by
    rw [hg0]
    have h : Filter.Tendsto (fun N : ℕ => (Real.pi / 2 : ℝ)
        - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ))))
        + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ)) + 1)))) Filter.atTop
        (nhds ((Real.pi / 2 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hg
    simpa using h
  have hfun : (fun N : ℕ => ∑ k ∈ Finset.range N, Real.arctan ((2 : ℝ) / (((Real.sqrt 5 - 1) / 2 + ((k : ℝ) + 1)) ^ 2)))
      = (fun N : ℕ => (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ)))
      + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + (((0 : ℕ)) : ℝ) + 1)))
      - (Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ))))
      + Real.arctan (1 / ((Real.sqrt 5 - 1) / 2 + ((N : ℝ)) + 1)))) := funext hpoint
  rw [hfun]
  exact hlim

end Entry7Example1Boundary

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
