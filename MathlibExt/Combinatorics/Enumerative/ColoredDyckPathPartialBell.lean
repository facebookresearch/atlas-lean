/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredCompositionPartialBell
import all MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons
import Mathlib.Tactic.FieldSimp

/-!
# The Mansour–Sun formula for colored Dyck paths

`coloredDyckPathCount_eq_partialBell` evaluates the count of colored Dyck paths with a given
number of peaks. In the cycle count of rise and fall runs, the fall lengths form a colored
composition. Substituting the partial Bell formula for its count gives the result.
-/

namespace MetaMathlibExt

namespace coloredDyckPathCount_eq_partialBell

open Finset choose_mul_coloredDyckPathCount_eq

/-- The positive fall lengths in the cycle count are precisely the parts of a composition. -/
private theorem sum_parts (γ : ℕ → ℕ) {n k : ℕ} (hk : k ≤ n) :
    ∑ b ∈ parts 1 k (n - k), (b.map γ).prod = coloredCompositionCount γ n k := by
  symm
  refine sum_bij' (fun c _ => c.blocks) (fun b hb =>
    ⟨b, fun hi => (mem_parts.mp hb).2.2 _ hi, by
      simpa [Nat.sub_add_cancel hk] using (mem_parts.mp hb).2.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact mem_parts.mpr ⟨(mem_filter.mp hc).2, by simp [Nat.sub_add_cancel hk],
      fun _ hi => c.blocks_pos hi⟩
  · intro b hb
    exact mem_filter.mpr ⟨mem_univ _, (mem_parts.mp hb).1⟩
  · intro c _
    rfl
  · intro b _
    rfl
  · intro c _
    rfl

/-- Marking one of the peaks counts all rotations of a valid word of rise and fall runs. -/
private theorem marked_count (γ : ℕ → ℕ) {n t : ℕ} (h : t + 1 ≤ n) :
    (t + 1) * coloredDyckPathCount γ n (t + 1) =
      n.choose t * coloredCompositionCount γ n (t + 1) := by
  have hc := cycle_weight γ (m := 1) (k := t + 1) (x := n + 1 - (t + 1)) (y := n - (t + 1))
    (by omega)
  rwa [← dyck_count γ (by omega) h, words_weight, card_parts, sum_parts γ h,
    show n + 1 - (t + 1) + t = n by omega] at hc

/-- The descents of a nonempty Dyck path give a composition of its semilength. -/
private theorem exists_descent_composition {n : ℕ} (hn : 1 ≤ n)
    (p : {p : DyckWord // p.semilength = n}) :
    ∃ c : Composition n, c.blocks = dyckPeakDescents p.1.toList := by
  obtain ⟨w, hp, hw⟩ := word_from_path hn p
  rw [encoded_peaks hw hp]
  refine ⟨⟨_, ?_, ?_⟩, rfl⟩
  · intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hi)
    exact (hp e he).2
  · have hd := (steps_count w).2
    have hn' : p.val.toList.count DyckStep.U = n := p.property
    simpa [hw, falls, ← p.val.count_U_eq_count_D, hn'] using hd.symm

end coloredDyckPathCount_eq_partialBell

open coloredDyckPathCount_eq_partialBell in
/-- **Mansour–Sun formula for colored Dyck paths.** Let $\gamma = (\gamma_1, \gamma_2, \dots)$ be
a sequence of natural numbers and let $d_{n,k}(\gamma)$ be the number of Dyck paths of semilength
$n$ with $k$ peaks in which each block $UD^j$, formed by a peak and the maximal run of $D$ steps
starting at its $D$, carries one of $\gamma_j$ colors. For every natural number $n \ge 1$ and
every natural number $k$, as rational numbers,
$$d_{n,k}(\gamma) = \frac{1}{(n+1-k)!} B_{n,k}(1! \, \gamma_1, 2! \, \gamma_2, \dots),$$
where $B_{n,k}$ is the partial Bell polynomial and $n + 1 - k$ is truncated subtraction, which is
$0$ when $k > n + 1$.

For $k \le n + 1$ the factor is $1/(n-k+1)!$; for every $k > n$ both sides vanish because
$B_{n,k} = 0$.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 2 (`jis-2024-24.5.2-prop-2`), citing Mansour and Sun. -/
public theorem coloredDyckPathCount_eq_partialBell (γ : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    (coloredDyckPathCount γ n k : ℚ) =
      1 / ((n + 1 - k).factorial : ℚ) *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j) := by
  have hcomp := coloredCompositionCount_eq_partialBell γ hn k
  by_cases hk : 1 ≤ k ∧ k ≤ n
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hcount : ((t + 1 : ℕ) : ℚ) * coloredDyckPathCount γ n (t + 1) =
        (n.choose t : ℚ) * coloredCompositionCount γ n (t + 1) := by
      exact_mod_cast marked_count γ hk.2
    have ht : t ≤ n := by omega
    have hc : (n.choose t : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht).ne'
    apply mul_left_cancel₀ (show ((t + 1 : ℕ) : ℚ) ≠ 0 by positivity)
    rw [hcount, hcomp, Nat.factorial_succ, ← Nat.choose_mul_factorial_mul_factorial ht,
      show n + 1 - (t + 1) = n - t by omega]
    push_cast
    field_simp
  · have hlen (c : Composition n) : c.length ≠ k := fun he =>
      hk (he ▸ ⟨c.length_pos_of_pos hn, c.length_le⟩)
    have hc : coloredCompositionCount γ n k = 0 := by simp [coloredCompositionCount, hlen]
    have hd : coloredDyckPathCount γ n k = 0 := by
      have hpeak (p : {p : DyckWord // p.semilength = n}) :
          (dyckPeakDescents p.1.toList).length ≠ k := by
        obtain ⟨c, he⟩ := exists_descent_composition hn p
        rw [← he]
        exact hlen c
      simp [coloredDyckPathCount, hpeak]
    rw [hc, Nat.cast_zero, eq_comm, mul_eq_zero] at hcomp
    rw [hd, hcomp.resolve_left (by simp [Nat.factorial_ne_zero]), mul_zero, Nat.cast_zero]

end MetaMathlibExt
