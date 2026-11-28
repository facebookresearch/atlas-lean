/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.NeumannSeries

/-! # The rendering equation as a fixed-point equation -/

open scoped ENNReal

namespace ContinuousLinearMap

@[expose] public section

/-- **The rendering equation as a fixed-point equation.** On a real Banach space, if the
continuous linear transport operator $T$ satisfies $\|T\| \le c < 1$, then the solution of
$I = E + TI$ for emission $E$ is unique and is the convergent series $\sum_{k \ge 0} T^k E$.
Keeping the terms from $0$ to $K$ gives error at most $c^{K+1}\|E\|/(1-c)$.

Pointwise strict loss does not suffice. On bounded real sequences indexed from zero, the
operator with diagonal entries $1-1/(n+1)$ has norm $1$. With constant unit emission the
coordinate equations force $I_n=n+1$, so there is no bounded solution.

Sources: James T. Kajiya, *The Rendering Equation*, SIGGRAPH 1986, and Eric Veach,
*Robust Monte Carlo Methods for Light Transport Simulation*, 1997, Section 4.4, for the
Neumann-series representation. The uniform norm bound gives the stated truncation estimate. -/
theorem rendering_equation_fixed_point_and_counterexample :
    (∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (T : X →L[ℝ] X) (c : ℝ), ‖T‖ ≤ c → c < 1 → ∀ E : X,
      let I := ∑' k : ℕ, (T ^ k) E
      HasSum (fun k : ℕ => (T ^ k) E) I ∧
        (∀ J : X, J = E + T J ↔ J = I) ∧
        ∀ K : ℕ, ‖I - ∑ k ∈ Finset.range (K + 1), (T ^ k) E‖ ≤
          c ^ (K + 1) * ‖E‖ / (1 - c)) ∧
    (∃ (T : lp (fun _ : ℕ => ℝ) ⊤ →L[ℝ] lp (fun _ : ℕ => ℝ) ⊤)
       (E : lp (fun _ : ℕ => ℝ) ⊤),
      (∀ x n, (T x : ℕ → ℝ) n = (1 - 1 / (n + 1 : ℝ)) * (x : ℕ → ℝ) n) ∧
        (∀ n, (E : ℕ → ℝ) n = 1) ∧ ‖T‖ = 1 ∧ ¬ ∃ I, I = E + T I) := by
  constructor
  · intro X _ _ _ T c hT hc E
    have hsum : Summable (fun k : ℕ => T ^ k) :=
      (summable_geometric_of_lt_one (norm_nonneg T) (hT.trans_lt hc))
        |>.of_norm_bounded_eventually_nat (eventually_norm_pow_le T)
    have hseries : neumannSeries T E = ∑' k : ℕ, (T ^ k) E := tsum_apply hsum E
    have hpoint := neumannSeries_apply_eq_add T c hT hc E
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · rw [← hseries]
      exact hasSum_apply hsum.hasSum E
    · intro J
      rw [← hseries]
      refine ⟨eq_neumannSeries_apply T c hT hc, ?_⟩
      rintro rfl
      exact hpoint
    · intro K
      rw [← hseries]
      exact norm_neumannSeries_apply_sub_sum_le T c hT ((norm_nonneg T).trans hT) hc E K
  · let e : lp (fun _ : ℕ => ℝ) ⊤ := ⟨fun _ => 1, memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact (norm_one : ‖(1 : ℝ)‖ = 1).le⟩⟩
    have he (n : ℕ) : (e : ℕ → ℝ) n = 1 := rfl
    refine ⟨lpDiag, e, lpDiag_apply_apply, he, lpDiag_norm, ?_⟩
    rintro ⟨I, hI⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ‖I‖
    have hpos : 0 < (n + 1 : ℝ) := by positivity
    have hcoord : (I : ℕ → ℝ) n = (↑(e + lpDiag I) : ℕ → ℝ) n :=
      congrArg (fun x : lp (fun _ : ℕ => ℝ) ⊤ => (x : ℕ → ℝ) n) hI
    simp only [lp.coeFn_add, Pi.add_apply, he, lpDiag_apply_apply] at hcoord
    let a : ℝ := (I : ℕ → ℝ) n
    change a = 1 + (1 - 1 / (n + 1 : ℝ)) * a at hcoord
    have hquot : a / (n + 1 : ℝ) = 1 := by
      have hmul : (1 - 1 / (n + 1 : ℝ)) * a = a - a / (n + 1 : ℝ) := by ring
      linarith only [hcoord, hmul]
    have hval : (I : ℕ → ℝ) n = (n + 1 : ℝ) := by
      simpa only [one_mul] using (div_eq_iff hpos.ne').mp hquot
    have hle := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) I n
    rw [hval, Real.norm_of_nonneg hpos.le] at hle
    linarith only [hle, hn]

end

end ContinuousLinearMap
