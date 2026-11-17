/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

@[expose] public section

section
open scoped InnerProductSpace ComplexOrder

universe u

namespace MathlibExt.Analysis.CStarAlgebra.LandmarkWanted

-- Helper predicates allowed; no forbidden constructs.

/--
**Russo–Dye theorem.** In a unital C*-algebra $A$, the norm closure of the convex hull of the
unitary elements of $A$ equals the closed unit ball $\{a \in A : \|a\| \le 1\}$.

Proves `Wanted` entry `cStarAlgebra_russoDye`.

Source: Russo–Dye theorem, B. Russo–H. Dye, Duke Math. J. 33 (1966); see
Takesaki I; Lean is norm-closure of convex hull of unitaries equals closed unit ball.
-/
theorem cStarAlgebra_russoDye
    (A : Type u) [CStarAlgebra A] :
    closure (convexHull ℝ (unitary A : Set A)) = Metric.closedBall (0 : A) 1 := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  apply le_antisymm
  · -- (⊆) unitaries have norm ≤ 1; the closed ball is convex and closed
    refine closure_minimal ?_ Metric.isClosed_closedBall
    refine convexHull_min ?_ (convex_closedBall 0 1)
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hnt : Nontrivial A
    · have := hnt
      rw [CStarRing.norm_of_mem_unitary hu]
    · rw [not_nontrivial_iff_subsingleton] at hnt
      have := hnt
      have hu0 : u = 0 := Subsingleton.elim u 0
      rw [hu0, norm_zero]
      exact zero_le_one
  · -- (⊇)
    by_cases hnt : Nontrivial A
    · have := hnt
      have h1norm : ‖(1 : A)‖ = 1 :=
        CStarRing.norm_of_mem_unitary (one_mem _)
      -- Step 1: if ‖y‖ < 1 then 1 + y is a sum of two unitaries
      have step1 : ∀ y : A, ‖y‖ < 1 →
          ∃ w₁ w₂ : A, w₁ ∈ unitary A ∧ w₂ ∈ unitary A ∧ (1 : A) + y = w₁ + w₂ := by
        intro y hy
        -- (a) z = 1 + y is a unit
        have hz_unit : IsUnit ((1 : A) + y) := by
          have h1 : ‖-y‖ < 1 := by rwa [norm_neg]
          have hu := (Units.oneSub (-y) h1).isUnit
          rw [Units.val_oneSub, sub_neg_eq_add] at hu
          exact hu
        -- (b) p = |z|
        have hp_nonneg : 0 ≤ CFC.abs ((1 : A) + y) := CFC.abs_nonneg _
        have hp_sa : IsSelfAdjoint (CFC.abs ((1 : A) + y)) :=
          IsSelfAdjoint.of_nonneg hp_nonneg
        have hpp : CFC.abs ((1 : A) + y) * CFC.abs ((1 : A) + y)
            = star ((1 : A) + y) * ((1 : A) + y) := CFC.abs_mul_abs _
        have hp_unit : IsUnit (CFC.abs ((1 : A) + y)) := by
          have h1 : IsUnit (star ((1 : A) + y) * ((1 : A) + y)) :=
            hz_unit.star.mul hz_unit
          rw [← hpp, ← pow_two] at h1
          exact (isUnit_pow_iff two_ne_zero).mp h1
        have hp_norm : ‖CFC.abs ((1 : A) + y)‖ < 2 := by
          have h1 : ‖CFC.abs ((1 : A) + y)‖ = ‖(1 : A) + y‖ := CFC.norm_abs
          have h2 := norm_add_le (1 : A) y
          rw [h1norm] at h2
          linarith
        -- (c) v = z * p⁻¹
        have hpinv_sa : star (Ring.inverse (CFC.abs ((1 : A) + y)))
            = Ring.inverse (CFC.abs ((1 : A) + y)) := by
          rw [← Ring.inverse_star, hp_sa.star_eq]
        have hvv : star ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
            * ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y))) = 1 := by
          have hpp' : star ((1 : A) + y) * ((1 : A) + y)
              = CFC.abs ((1 : A) + y) * CFC.abs ((1 : A) + y) :=
            (CFC.abs_mul_abs _).symm
          calc star ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
                * ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              = Ring.inverse (CFC.abs ((1 : A) + y))
                * (star ((1 : A) + y)
                  * ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))) := by
                rw [star_mul, hpinv_sa, mul_assoc]
            _ = Ring.inverse (CFC.abs ((1 : A) + y))
                * ((CFC.abs ((1 : A) + y) * CFC.abs ((1 : A) + y))
                  * Ring.inverse (CFC.abs ((1 : A) + y))) := by
                rw [← mul_assoc (star ((1 : A) + y)) ((1 : A) + y) _, hpp']
            _ = Ring.inverse (CFC.abs ((1 : A) + y))
                * (CFC.abs ((1 : A) + y)
                  * (CFC.abs ((1 : A) + y)
                    * Ring.inverse (CFC.abs ((1 : A) + y)))) := by
                rw [mul_assoc (CFC.abs ((1 : A) + y)) (CFC.abs ((1 : A) + y)) _]
            _ = 1 := by
                rw [Ring.mul_inverse_cancel _ hp_unit, mul_one,
                  Ring.inverse_mul_cancel _ hp_unit]
        have hv_unit : IsUnit ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y))) :=
          hz_unit.mul (IsUnit.ringInverse hp_unit)
        have hvv2 : (1 + y) * Ring.inverse (CFC.abs ((1 : A) + y))
            * star ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y))) = 1 := by
          obtain ⟨vu, hvu⟩ := hv_unit
          have h1 : star ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              * (vu : A) = 1 := by
            rw [hvu]
            exact hvv
          have hstar : star ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              = ((vu⁻¹ : Aˣ) : A) :=
            (Units.inv_eq_of_mul_eq_one_left h1).symm
          calc (1 + y) * Ring.inverse (CFC.abs ((1 : A) + y))
                * star ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              = (vu : A) * ((vu⁻¹ : Aˣ) : A) := by
                rw [hstar, ← hvu]
            _ = 1 := Units.mul_inv vu
        have hv_mem : (1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)) ∈ unitary A :=
          Unitary.mem_iff.mpr ⟨hvv, hvv2⟩
        -- (d) h = (1/2) p, w = h + I sqrt(1 - h^2)
        have hh_sa : IsSelfAdjoint ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) := by
          change star ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) = _
          rw [star_smul, star_trivial, hp_sa.star_eq]
        have hh_norm : ‖(1 / 2 : ℝ) • CFC.abs ((1 : A) + y)‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          linarith
        have hw_mem : (1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
            CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2) ∈ unitary A :=
          IsSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ hh_sa hh_norm
        have hstar_w : star ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
            CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2))
            = (1 / 2 : ℝ) • CFC.abs ((1 : A) + y) - Complex.I •
            CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2) := by
          have ha_norm : ‖(⟨_, hh_sa⟩ : selfAdjoint A)‖ ≤ 1 := hh_norm
          exact selfAdjoint.star_coe_unitarySelfAddISMul (⟨_, hh_sa⟩ : selfAdjoint A)
            ha_norm
        have hww : ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
            CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2))
            + star ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
            CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2))
            = CFC.abs ((1 : A) + y) := by
          rw [hstar_w]
          have e1 : (1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
              CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2)
              + ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) - Complex.I •
              CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2))
              = (1 / 2 : ℝ) • CFC.abs ((1 : A) + y)
              + (1 / 2 : ℝ) • CFC.abs ((1 : A) + y) := by
            abel
          rw [e1, ← add_smul]
          have e2 : ((1 / 2 : ℝ) + 1 / 2) = 1 := by norm_num
          rw [e2, one_smul]
        -- (e) assemble
        have hzp : (1 : A) + y
            = ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              * ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
              CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2))
            + ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              * star ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
              CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2)) := by
          have e1 : (1 : A) + y = ((1 + y)
              * Ring.inverse (CFC.abs ((1 : A) + y))) * CFC.abs ((1 : A) + y) := by
            rw [mul_assoc _ _ _, Ring.inverse_mul_cancel _ hp_unit, mul_one]
          have e2 : ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              * CFC.abs ((1 : A) + y)
              = ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              * ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
              CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2))
            + ((1 + y) * Ring.inverse (CFC.abs ((1 : A) + y)))
              * star ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y) + Complex.I •
              CFC.sqrt (1 - ((1 / 2 : ℝ) • CFC.abs ((1 : A) + y)) ^ 2)) := by
            rw [← mul_add, hww]
          exact e1.trans e2
        exact ⟨_, _, mul_mem hv_mem hw_mem,
          mul_mem hv_mem (Unitary.star_mem hw_mem), hzp⟩
      -- Step 2: shift by a unitary
      have step2 : ∀ u y : A, u ∈ unitary A → ‖y‖ < 1 →
          ∃ v₁ v₂ : A, v₁ ∈ unitary A ∧ v₂ ∈ unitary A ∧ u + y = v₁ + v₂ := by
        intro u y hu hy
        have h1 : ‖star u * y‖ < 1 := by
          rw [CStarRing.norm_mem_unitary_mul y (Unitary.star_mem hu)]
          exact hy
        obtain ⟨w₁, w₂, hw₁, hw₂, h12⟩ := step1 (star u * y) h1
        refine ⟨u * w₁, u * w₂, mul_mem hu hw₁, mul_mem hu hw₂, ?_⟩
        have e : u + y = u * (1 + star u * y) := by
          rw [mul_add, mul_one]
          congr 1
          rw [← mul_assoc, Unitary.mul_star_self_of_mem hu, one_mul]
        rw [e, h12, mul_add]
      -- Step 3: induction
      have step3 : ∀ y : A, ‖y‖ < 1 → ∀ k : ℕ, ∀ u : A, u ∈ unitary A →
          ∃ f : Fin (k + 1) → A, (∀ i, f i ∈ unitary A)
            ∧ ∑ i, f i = u + (k : ℝ) • y := by
        intro y hy k
        induction k with
        | zero =>
          intro u hu
          refine ⟨fun _ => u, fun _ => hu, ?_⟩
          change ∑ _ : Fin 1, u = u + ((0 : ℕ) : ℝ) • y
          rw [Fin.sum_univ_one]
          simp
        | succ k ih =>
          intro u hu
          obtain ⟨v₁, v₂, hv₁, hv₂, h12⟩ := step2 u y hu hy
          obtain ⟨g, hg, hgsum⟩ := ih v₂ hv₂
          refine ⟨Fin.cons v₁ g, ?_, ?_⟩
          · intro i
            exact Fin.cases (by simpa using hv₁) (fun j => by simpa using hg j) i
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hgsum]
            have e : u + ((k + 1 : ℕ) : ℝ) • y = (u + y) + (k : ℝ) • y := by
              push_cast
              rw [add_smul, one_smul]
              abel
            rw [e, h12]
            abel
      -- it suffices to show the open ball lies in the convex hull
      rw [← closure_ball (0 : A) (one_ne_zero : (1 : ℝ) ≠ 0)]
      apply closure_mono
      intro x hx
      rw [Metric.mem_ball, dist_zero_right] at hx
      -- Step 4: convex combination via the Archimedean property
      have hδ : (0 : ℝ) < 1 - ‖x‖ := by linarith
      obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 / (1 - ‖x‖))
      set m : ℕ := n₀ + 1 with hm_def
      have hm1 : 1 ≤ m := by
        rw [hm_def]
        omega
      have hm_pos : (0 : ℝ) < (m : ℝ) := by
        have h0 : (0 : ℕ) < m := by omega
        exact_mod_cast h0
      have hn_pos' : (0 : ℝ) < ((((m + 1 : ℕ))) : ℝ) := by
        push_cast
        linarith [hm_pos]
      have h2n : 2 / ((((m + 1 : ℕ))) : ℝ) < 1 - ‖x‖ := by
        rw [div_lt_iff₀ hn_pos']
        have hbase : (2 : ℝ) < (n₀ : ℝ) * (1 - ‖x‖) := (div_lt_iff₀ hδ).mp hn₀
        have hle : (n₀ : ℝ) ≤ ((((m + 1 : ℕ))) : ℝ) := by
          rw [hm_def]
          push_cast
          linarith
        have hmono : (n₀ : ℝ) * (1 - ‖x‖)
            ≤ ((((m + 1 : ℕ))) : ℝ) * (1 - ‖x‖) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hδ)
        linarith
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      have hne : ((((m + 1 : ℕ))) : ℝ) ≠ 0 := ne_of_gt hn_pos'
      have hny : ‖((m : ℝ))⁻¹ • (((((m + 1 : ℕ))) : ℝ) • x - 1)‖ < 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm_pos),
          inv_mul_lt_iff₀ hm_pos, mul_one]
        have hle1 : ‖((((m + 1 : ℕ))) : ℝ) • x - 1‖
            ≤ ((((m + 1 : ℕ))) : ℝ) * ‖x‖ + 1 := by
          have h := norm_sub_le (((((m + 1 : ℕ))) : ℝ) • x) (1 : A)
          rw [h1norm] at h
          have e : ‖((((m + 1 : ℕ))) : ℝ) • x‖
              = ((((m + 1 : ℕ))) : ℝ) * ‖x‖ := by
            have hnn : (0 : ℝ) ≤ ((((m + 1 : ℕ))) : ℝ) := le_of_lt hn_pos'
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
          rw [e] at h
          exact h
        have hlt : ((((m + 1 : ℕ))) : ℝ) * ‖x‖ + 1 < (m : ℝ) := by
          have h2a : (2 : ℝ) < (1 - ‖x‖) * ((((m + 1 : ℕ))) : ℝ) := by
            have h := (div_lt_iff₀ hn_pos').mp h2n
            linarith
          push_cast at h2a ⊢
          linarith
        exact lt_of_le_of_lt hle1 hlt
      have h1ky : (1 : A) + (m : ℝ)
          • (((m : ℝ))⁻¹ • (((((m + 1 : ℕ))) : ℝ) • x - 1))
          = ((((m + 1 : ℕ))) : ℝ) • x := by
        rw [← mul_smul, mul_inv_cancel₀ hm_ne, one_smul]
        exact add_sub_cancel _ _
      obtain ⟨f, hf, hfsum⟩ := step3 _ hny m 1 (one_mem _)
      have hfsum2 : ∑ i, f i = ((((m + 1 : ℕ))) : ℝ) • x := by
        rw [hfsum, h1ky]
      have hnx : x
          = ∑ i : Fin (m + 1), ((((m + 1 : ℕ))) : ℝ)⁻¹ • f i := by
        have e : ((((m + 1 : ℕ))) : ℝ)⁻¹ • (((((m + 1 : ℕ))) : ℝ) • x) = x := by
          rw [← mul_smul, inv_mul_cancel₀ hne, one_smul]
        rw [← hfsum2, Finset.smul_sum] at e
        exact e.symm
      have hx_mem : x ∈ convexHull ℝ (unitary A : Set A) := by
        have hmem : (∑ i : Fin (m + 1), ((((m + 1 : ℕ))) : ℝ)⁻¹ • f i)
            ∈ convexHull ℝ (unitary A : Set A) := by
          apply Convex.sum_mem (convex_convexHull ℝ _)
          · intro i _
            exact le_of_lt (inv_pos.mpr hn_pos')
          · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            exact mul_inv_cancel₀ hne
          · intro i _
            exact subset_convexHull ℝ _ (hf i)
        rwa [← hnx] at hmem
      exact hx_mem
    · -- subsingleton case: everything is 0, and 1 = 0 is unitary
      rw [not_nontrivial_iff_subsingleton] at hnt
      have := hnt
      intro x _
      have hx0 : x = 0 := Subsingleton.elim x 0
      rw [hx0]
      have h10 : (1 : A) = 0 := Subsingleton.elim 1 0
      have h0mem : (0 : A) ∈ unitary A := by
        rw [← h10]
        exact one_mem _
      exact subset_closure (subset_convexHull ℝ _ h0mem)

end MathlibExt.Analysis.CStarAlgebra.LandmarkWanted
end
