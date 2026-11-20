/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.FiniteCurrentParityLift

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def conditionalCurrentTerm (beta : ℝ) (k : ℕ) : ℝ :=
  beta ^ k / k.factorial

noncomputable def parityEdgeKernel (beta : ℝ) (odd : Bool) (k : ℕ) : ℝ :=
  if odd then
    if Odd k then conditionalCurrentTerm beta k / Real.sinh beta else 0
  else
    if Even k then conditionalCurrentTerm beta k / Real.cosh beta else 0

noncomputable def parityCurrentKernel (beta : ℝ)
    (H : Finset (Sym2 V)) (m : EdgeCurrent G) : ℝ :=
  ∏ e : G.edgeFinset, parityEdgeKernel beta (e.1 ∈ H) (m e)

private theorem summable_conditionalCurrentTerm (beta : ℝ) :
    Summable (conditionalCurrentTerm beta) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) beta
  exact h.congr (fun k => by
    simp [conditionalCurrentTerm, div_eq_inv_mul, mul_comm])

private theorem summable_conditionalCurrentTerm_filter
    (beta : ℝ) (Q : ℕ → Prop) [DecidablePred Q] :
    Summable (fun k => if Q k then conditionalCurrentTerm beta k else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_conditionalCurrentTerm beta).norm
  split <;> simp

private theorem tsum_conditionalCurrentTerm_even (beta : ℝ) :
    (∑' k : ℕ, if Even k then conditionalCurrentTerm beta k else 0) =
      Real.cosh beta := by
  simpa [conditionalCurrentTerm] using
    (tsum_parityCurrentTerm_even beta)

private theorem tsum_conditionalCurrentTerm_odd (beta : ℝ) :
    (∑' k : ℕ, if Odd k then conditionalCurrentTerm beta k else 0) =
      Real.sinh beta := by
  simpa [conditionalCurrentTerm] using
    (tsum_parityCurrentTerm_odd beta)

theorem summable_parityEdgeKernel (beta : ℝ) (odd : Bool) :
    Summable (parityEdgeKernel beta odd) := by
  cases odd
  · refine ((summable_conditionalCurrentTerm_filter beta Even).div_const
      (Real.cosh beta)).congr
      (fun k => ?_)
    by_cases hk : Even k <;> simp [parityEdgeKernel, hk]
  · refine ((summable_conditionalCurrentTerm_filter beta Odd).div_const
      (Real.sinh beta)).congr
      (fun k => ?_)
    by_cases hk : Odd k <;> simp [parityEdgeKernel, hk]

theorem parityEdgeKernel_nonneg (beta : ℝ) (hbeta : 0 < beta)
    (odd : Bool) (k : ℕ) : 0 ≤ parityEdgeKernel beta odd k := by
  have hb : 0 ≤ beta := hbeta.le
  cases odd <;> simp only [parityEdgeKernel, Bool.false_eq_true, if_false, if_true]
  · split
    · exact div_nonneg
        (div_nonneg (pow_nonneg hb _) (Nat.cast_nonneg _))
        (Real.cosh_pos beta).le
    · exact le_rfl
  · split
    · exact div_nonneg
        (div_nonneg (pow_nonneg hb _) (Nat.cast_nonneg _))
        (Real.sinh_pos_iff.2 hbeta).le
    · exact le_rfl

theorem tsum_parityEdgeKernel (beta : ℝ) (hbeta : 0 < beta)
    (odd : Bool) : ∑' k : ℕ, parityEdgeKernel beta odd k = 1 := by
  cases odd
  · rw [show (∑' k : ℕ, parityEdgeKernel beta false k) =
        ∑' k : ℕ,
          (if Even k then conditionalCurrentTerm beta k else 0) /
            Real.cosh beta by
      apply tsum_congr
      intro k
      by_cases hk : Even k <;> simp [parityEdgeKernel, hk]]
    rw [tsum_div_const, tsum_conditionalCurrentTerm_even]
    exact div_self (ne_of_gt (Real.cosh_pos beta))
  · rw [show (∑' k : ℕ, parityEdgeKernel beta true k) =
        ∑' k : ℕ,
          (if Odd k then conditionalCurrentTerm beta k else 0) /
            Real.sinh beta by
      apply tsum_congr
      intro k
      by_cases hk : Odd k <;> simp [parityEdgeKernel, hk]]
    rw [tsum_div_const, tsum_conditionalCurrentTerm_odd]
    exact div_self (ne_of_gt (Real.sinh_pos_iff.2 hbeta))

theorem tsum_parityCurrentKernel (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G, parityCurrentKernel G beta H m = 1 := by
  let g : Sym2 V → ℕ → ℝ := fun e k =>
    parityEdgeKernel beta (e ∈ H) k
  have hg : ∀ e, Summable (g e) := fun e =>
    summable_parityEdgeKernel beta (e ∈ H)
  have hgnn : ∀ e k, 0 ≤ g e k := fun e k =>
    parityEdgeKernel_nonneg beta hbeta (e ∈ H) k
  have hf := prod_tsum_fubini g hg hgnn G.edgeFinset
  calc
    (∑' m : EdgeCurrent G, parityCurrentKernel G beta H m) =
        ∏ e ∈ G.edgeFinset, ∑' k : ℕ, g e k := by
      rw [hf.2]
      rfl
    _ = 1 := by
      apply Finset.prod_eq_one
      intro e he
      exact tsum_parityEdgeKernel beta hbeta (e ∈ H)

noncomputable def parityFiberMass (G : SimpleGraph V) [DecidableRel G.Adj] (beta : ℝ)
    (H : Finset (Sym2 V)) : ℝ :=
  ∏ e : G.edgeFinset,
    if e.1 ∈ H then Real.sinh beta else Real.cosh beta

theorem parityFiberMass_closed (beta : ℝ) (hbeta : 0 ≤ beta)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    parityFiberMass G beta H =
      Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card := by
  have hopen := fixedParity_weight_tsum G beta hbeta H hH
  have hclosed := fixedParity_weight_tsum_closed G beta hbeta H hH
  rw [hopen] at hclosed
  unfold parityFiberMass
  change (∏ e ∈ (Finset.univ : Finset G.edgeFinset),
      if e.1 ∈ H then Real.sinh beta else Real.cosh beta) = _
  rw [show (Finset.univ : Finset G.edgeFinset) = G.edgeFinset.attach by
    ext e
    simp]
  exact (Finset.prod_attach G.edgeFinset
    (fun e => if e ∈ H then Real.sinh beta else Real.cosh beta)).trans hclosed

theorem weight_eq_parityFiberMass_mul_kernel
    (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m = H) :
    weight G beta (fun _ => 1) (ofEdgeFun G m) =
      parityFiberMass G beta H * parityCurrentKernel G beta H m := by
  have hall := (currentParitySupport_eq_iff G H hH m).mp hm
  unfold parityFiberMass parityCurrentKernel
  symm
  calc
    (∏ e : G.edgeFinset,
        if e.1 ∈ H then Real.sinh beta else Real.cosh beta) *
          ∏ e : G.edgeFinset,
            parityEdgeKernel beta (e.1 ∈ H) (m e) =
        ∏ e : G.edgeFinset,
          (if e.1 ∈ H then Real.sinh beta else Real.cosh beta) *
            parityEdgeKernel beta (e.1 ∈ H) (m e) := by
      exact (Finset.prod_mul_distrib (s := Finset.univ)).symm
    _ = ∏ e : G.edgeFinset,
          (beta * (fun _ => (1 : ℝ)) e.1) ^ m e / (m e).factorial := by
      apply Fintype.prod_congr
      intro e
      by_cases heH : e.1 ∈ H
      · have ho : Odd (m e) := by simpa [heH] using hall e
        have hsinh : Real.sinh beta ≠ 0 :=
          ne_of_gt (Real.sinh_pos_iff.2 hbeta)
        simp [parityEdgeKernel, heH, ho, conditionalCurrentTerm]
        field_simp [hsinh]
      · have hev : Even (m e) := by simpa [heH] using hall e
        have hcosh : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
        simp [parityEdgeKernel, heH, hev, conditionalCurrentTerm]
        field_simp [hcosh]
    _ = weight G beta (fun _ => 1) (ofEdgeFun G m) :=
      (weight_ofEdgeFun G beta (fun _ => 1) m).symm

end StatMech.FrontierB
