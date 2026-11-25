/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NicomacheanTranslations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nicomachean sequences with a large gap at the top

For any prescribed gap, there is a list of positive integers with zero Nicomachean defect
whose unique maximum exceeds its second-largest entry by more than that gap.
-/

namespace MetaMathlibExt

/-- **Nicomachean sequences with a large gap at the top.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every natural number $G$ there is a finite sequence $\sigma$ of
positive integers with $\nu(\sigma) = 0$ and entries $a < b$ of $\sigma$ such that $b$ is the
largest entry of $\sigma$ and occurs exactly once, every entry other than $b$ is at most $a$, and
$b - a > G$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 6
(`jis-2024-24.6.3-prop-6`). -/
public theorem exists_nicomachean_large_top_gap (G : ℕ) :
    ∃ σ : List ℤ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ a ∈ σ, ∃ b ∈ σ,
      σ.count b = 1 ∧ (∀ x ∈ σ, x ≤ b) ∧ a < b ∧ (∀ x ∈ σ, x ≠ b → x ≤ a) ∧ (G : ℤ) < b - a := by
  -- For a top entry (2 * m)^2, choose the counts of ones and twos so that
  -- the sum is (2 * m)^3 + 1 and the sum of cubes is its square.
  let m : ℕ := 3 * G + 1
  let b : ℤ := 4 * (m : ℤ) ^ 2
  let twoCount : ℕ := 2 * m ^ 2 * (2 * G + 1)
  let oneCount : ℕ := 16 * G * m ^ 2 + 1
  let rest := List.replicate twoCount (2 : ℤ) ++ List.replicate oneCount 1
  have hgap : (G : ℤ) < b - 2 := by
    dsimp [b, m]
    nlinarith [Int.natCast_nonneg G, sq_nonneg (G : ℤ)]
  have htop : 2 < b := by omega
  have htwoCount : twoCount ≠ 0 := by
    dsimp [twoCount, m]
    exact Nat.ne_of_gt (by positivity)
  have htwo : (2 : ℤ) ∈ rest :=
    List.mem_append_left _ (List.mem_replicate.mpr ⟨htwoCount, rfl⟩)
  have hrest {x : ℤ} (hx : x ∈ rest) : 0 < x ∧ x ≤ 2 := by
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      decide
    · rw [List.eq_of_mem_replicate hx]
      decide
  refine ⟨b :: rest, ?_, ?_, 2, List.mem_cons_of_mem _ htwo, b, List.mem_cons_self,
    ?_, ?_, htop, ?_, hgap⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (by decide : (0 : ℤ) < 2).trans htop
    · exact (hrest hx).1
  · simp only [rest, nicomacheanNu, List.map_cons, List.map_append, List.map_replicate,
      List.sum_cons, List.sum_append, List.sum_replicate, nsmul_eq_mul]
    dsimp [b, twoCount, oneCount, m]
    ring
  · rw [List.count_cons_self, List.count_eq_zero.mpr (fun hb => htop.not_ge (hrest hb).2)]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact (hrest hx).2.trans htop.le
  · intro x hx hxb
    exact (hrest ((List.mem_cons.mp hx).resolve_left hxb)).2

end MetaMathlibExt
