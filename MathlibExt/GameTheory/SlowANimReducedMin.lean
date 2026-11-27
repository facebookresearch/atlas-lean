/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.GameTheory.SlowANim
import Mathlib.Algebra.BigOperators.Ring.Finset
import all MathlibExt.GameTheory.SlowANimGeneralReduction

/-!
# Truncating reduced positions in Slow A-Nim

Capping every stack of a reduced position at the same height leaves it reduced.
The proof uses the token-count bounds from `MathlibExt.GameTheory.SlowANimGeneralReduction`.

## References

* Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
  Slow A-Nim*, INTEGERS 26 (2026), Article G3, pp. 1–25. Theorem 4 (Section 3.2) gives the
  reduced-position criterion, and Lemma 2 (Section 3.4) proves that chopping preserves reduction.
-/

namespace MetaMathlibExt

-- Scaling by the old maximum makes capping a termwise inequality.
private theorem scaled_le_sum_min {n M m : ℕ} (p : Fin n → ℕ) (hm : m ≤ M)
    (hp : ∀ i, p i ≤ M) : m * (∑ i, p i) ≤ M * ∑ i, min (p i) m := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rcases le_total (p i) m with hi | hi
  · rw [min_eq_left hi]
    exact Nat.mul_le_mul_right _ hm
  · rw [min_eq_right hi]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left m (hp i)

/-- **Chopping a reduced position keeps it reduced.** Let $A \subseteq \{1, \dots, n\}$ and let
$p$ be a reduced position of Slow $A$-Nim on $n$ stacks. Then for every $m \in \mathbb{N}$ the
position $\mathrm{ctt}(p, m)$ with stack heights $\mathrm{ctt}(p, m)_i = \min(p_i, m)$ is
reduced.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 2. -/
public theorem slowANimReduced_min (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (p : Fin n → ℕ) (hp : SlowANimReduced A p) (m : ℕ) :
    SlowANimReduced A fun i => min (p i) m := by
  let M := Finset.univ.sup p
  have hle (i : Fin n) : p i ≤ M := Finset.le_sup (Finset.mem_univ i)
  by_cases hm : M ≤ m
  · have hsame : (fun i => min (p i) m) = p :=
      funext fun i => min_eq_left ((hle i).trans hm)
    rwa [hsame]
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · have hzero (i : Fin n) : p i = 0 := by
      obtain ⟨t, hpt, -, hti⟩ := hp i
      cases hpt with
      | refl => exact hti
      | tail _ hmove => simp [slowANimMoves] at hmove
    simpa only [hzero, zero_min] using (slowANimReduced_zero (n := n) ∅)
  let a := A.min' hAne
  have ha : a ∈ A := Finset.min'_mem _ _
  have ha_pos : 0 < a := (Finset.mem_Icc.mp (hA ha)).1
  have hM : 0 < M := (Nat.zero_le m).trans_lt (Nat.lt_of_not_ge hm)
  have hbefore : a * M ≤ ∑ i, p i := by
    rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with he | hne
    · simp [M, he] at hM
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne p
    obtain ⟨t, hpt, -, hti⟩ := hp i
    change a * Finset.univ.sup p ≤ _
    rw [hi]
    exact slowANim_generalReduction.tokens_needed_to_empty hAne i hpt hti
  have htotal : a * m ≤ ∑ i, min (p i) m := by
    apply Nat.le_of_mul_le_mul_left _ hM
    calc
      M * (a * m) = m * (a * M) := by ac_rfl
      _ ≤ m * ∑ i, p i := Nat.mul_le_mul_left _ hbefore
      _ ≤ M * ∑ i, min (p i) m := scaled_le_sum_min p (Nat.le_of_lt (Nat.lt_of_not_ge hm)) hle
  have hcap : (Finset.univ.sup fun i => min (p i) m) ≤ m :=
    Finset.sup_le fun i _ => min_le_right (p i) m
  exact slowANim_generalReduction.reduced_of_total ha ha_pos
    ((Nat.mul_le_mul_left a hcap).trans htotal)

end MetaMathlibExt
