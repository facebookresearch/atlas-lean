/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma betweenness_ratio {P Q R : EuclideanSpace ℝ (Fin 2)}
    (h : dist P Q + dist Q R = dist P R)
    (h1 : 0 < dist P Q) (h2 : 0 < dist Q R) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ Q - P = s • (R - P) ∧
      dist P Q = s * dist P R ∧ dist Q R = (1 - s) * dist P R := by
  have hPR : 0 < dist P R := by linarith
  have hPRne : dist P R ≠ 0 := ne_of_gt hPR
  have hQRne : dist Q R ≠ 0 := ne_of_gt h2
  refine ⟨dist P Q / dist P R, div_pos h1 hPR, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one hPR]
    linarith
  · have huv : (Q - P) + (R - Q) = R - P := by abel
    have hnu : ‖Q - P‖ = dist P Q := by
      rw [dist_eq_norm, norm_sub_rev]
    have hnv : ‖R - Q‖ = dist Q R := by
      rw [dist_eq_norm, norm_sub_rev]
    have hnw : ‖(Q - P) + (R - Q)‖ = dist P R := by
      rw [huv, dist_eq_norm, norm_sub_rev]
    have hnorm : ‖Q - P‖ + ‖R - Q‖ = ‖(Q - P) + (R - Q)‖ := by
      rw [hnu, hnv, hnw]; exact h
    have hexpand := norm_add_sq_real (Q - P) (R - Q)
    have hsq : (‖Q - P‖ + ‖R - Q‖) ^ 2 = ‖(Q - P) + (R - Q)‖ ^ 2 := by rw [hnorm]
    have hpow : (‖Q - P‖ + ‖R - Q‖) ^ 2
        = ‖Q - P‖ ^ 2 + 2 * (‖Q - P‖ * ‖R - Q‖) + ‖R - Q‖ ^ 2 := by ring
    have hinn : inner ℝ (Q - P) (R - Q) = ‖Q - P‖ * ‖R - Q‖ := by
      rw [hsq, hexpand] at hpow
      linarith
    have hcs := inner_eq_norm_mul_iff_real.mp hinn
    have hau : (0:ℝ) < ‖Q - P‖ := by rw [hnu]; exact h1
    have hav : (0:ℝ) < ‖R - Q‖ := by rw [hnv]; exact h2
    have hbne : (‖R - Q‖ : ℝ) ≠ 0 := ne_of_gt hav
    have hu_eq : Q - P = (dist P Q / dist Q R) • (R - Q) := by
      have e1 : Q - P = ((‖R - Q‖⁻¹ * ‖Q - P‖ : ℝ)) • (R - Q) := by
        have e2 : ((‖R - Q‖⁻¹ * ‖R - Q‖ : ℝ)) • (Q - P) = Q - P := by
          rw [inv_mul_cancel₀ hbne, one_smul]
        have e3 : ((‖R - Q‖⁻¹ * ‖R - Q‖ : ℝ)) • (Q - P)
            = ((‖R - Q‖⁻¹ * ‖Q - P‖ : ℝ)) • (R - Q) := by
          rw [mul_smul, mul_smul, hcs]
        rw [e2] at e3
        exact e3
      have e4 : (dist P Q / dist Q R : ℝ) = (‖R - Q‖⁻¹ * ‖Q - P‖ : ℝ) := by
        rw [← hnu, ← hnv, div_eq_mul_inv, mul_comm]
      rw [e4]
      exact e1
    have hc1 : (dist P Q / dist Q R + 1 : ℝ) = dist P R / dist Q R := by
      have e : dist P Q / dist Q R + 1 = (dist P Q + dist Q R) / dist Q R := by
        rw [add_div, div_self hQRne]
      rw [e, h]
    have hsc : (dist P Q / dist P R) * (dist P Q / dist Q R + 1)
        = dist P Q / dist Q R := by
      rw [hc1]
      exact div_mul_div_cancel₀ hPRne
    have hR : R - P = ((dist P Q / dist Q R + 1 : ℝ)) • (R - Q) := by
      rw [← huv, hu_eq, add_smul, one_smul]
    have e : (dist P Q / dist P R) • (R - P)
        = (dist P Q / dist Q R) • (R - Q) := by
      rw [hR, ← mul_smul, hsc]
    rw [e]
    exact hu_eq
  · rw [div_mul_cancel₀ _ hPRne]
  · have hADs : dist P Q = (dist P Q / dist P R) * dist P R := by
      rw [div_mul_cancel₀ _ hPRne]
    have hmid : (1 - dist P Q / dist P R) * dist P R = dist P R - dist P Q := by
      linear_combination hADs
    rw [hmid]
    linarith

/-- **Intercept theorem.** Let $A, B, C, D, E$ be points of the Euclidean plane $\mathbb{R}^2$,
and write $XY$ for the distance between points $X$ and $Y$. Suppose that $C - A$ is not a real
multiple of $B - A$; that $AD + DB = AB$ with $AD > 0$ and $DB > 0$, so $D$ lies strictly
between $A$ and $B$; that $AE + EC = AC$ with $AE > 0$ and $EC > 0$, so $E$ lies strictly
between $A$ and $C$; and that $E - D = r(C - B)$ for some real $r \ne 0$, so $DE$ is parallel
to $BC$. Then $AD / DB = AE / EC$.

Proves `Wanted` entry `intercept_theorem`.

Source: https://en.wikipedia.org/wiki/Intercept_theorem (statement intercept-s1).
-/
theorem intercept_theorem : ∀ (A B C D E : EuclideanSpace ℝ (Fin 2)),
  dist A D + dist D B = dist A B →
  0 < dist A D →
  0 < dist D B →
  dist A E + dist E C = dist A C →
  0 < dist A E →
  0 < dist E C →
  (¬ ∃ t : ℝ, C - A = t • (B - A)) →
  (∃ r : ℝ, r ≠ 0 ∧ E - D = r • (C - B)) →
  dist A D / dist D B = dist A E / dist E C := by
  intro A B C D E hD hAD hDB hE hAE hEC hnoncoll hpar_ex
  obtain ⟨s, hs0, hs1, hDs, hADs, hDBs⟩ := betweenness_ratio hD hAD hDB
  obtain ⟨t, ht0, ht1, hEt, hAEs, hECs⟩ := betweenness_ratio hE hAE hEC
  obtain ⟨r, hr0, hpar⟩ := hpar_ex
  have hABpos : 0 < dist A B := by linarith
  have hABne : dist A B ≠ 0 := ne_of_gt hABpos
  have hACpos : 0 < dist A C := by linarith
  have hACne : dist A C ≠ 0 := ne_of_gt hACpos
  have hBA : B - A ≠ 0 := by
    intro hcon
    apply hABne
    have h1 : dist A B = ‖A - B‖ := dist_eq_norm _ _
    have h2 : A - B = -(B - A) := by abel
    rw [h1, h2, hcon, neg_zero, norm_zero]
  have hED : E - D = t • (C - A) - s • (B - A) := by
    have e : (E - A) - (D - A) = E - D := by abel
    rw [← e, hEt, hDs]
  have hCB : C - B = (C - A) - (B - A) := by abel
  rw [hED, hCB] at hpar
  -- hpar : t • (C - A) - s • (B - A) = r • ((C - A) - (B - A))
  have key : (t - r) • (C - A) + (r - s) • (B - A) = 0 := by
    have e : (t - r) • (C - A) + (r - s) • (B - A)
        = (t • (C - A) - s • (B - A)) - r • ((C - A) - (B - A)) := by
      module
    rw [e, hpar, sub_self]
  have htr : t = r := by
    by_contra hne
    apply hnoncoll
    have hne' : (t - r : ℝ) ≠ 0 := sub_ne_zero.mpr hne
    have h2 : (t - r) • (C - A) = -((r - s) • (B - A)) :=
      eq_neg_of_add_eq_zero_left key
    refine ⟨-((r - s) / (t - r)), ?_⟩
    have h1 : C - A = (t - r)⁻¹ • ((t - r) • (C - A)) := by
      rw [← mul_smul, inv_mul_cancel₀ hne', one_smul]
    rw [h1, h2, smul_neg, ← mul_smul, div_eq_mul_inv]
    module
  have hrs : r - s = 0 := by
    rw [htr] at key
    simp only [sub_self, zero_smul, zero_add] at key
    rcases smul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hBA
  have hst : s = t := by linarith
  have h1s : (1 : ℝ) - s ≠ 0 := by
    have : (0 : ℝ) < 1 - s := by linarith
    exact ne_of_gt this
  rw [hADs, hDBs, hAEs, hECs, hst]
  rw [mul_div_mul_right _ _ hABne, mul_div_mul_right _ _ hACne]

end MetaMathlibExt
