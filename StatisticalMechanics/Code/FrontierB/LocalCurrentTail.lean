/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.BoxCurrentLaws
import Code.Ising.KWSelfDuality

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in

theorem spinProd_le_one (A : Finset V) (s : ConfigSpace V) : spinProd A s ≤ 1 := by
  classical
  have hpm : spinProd A s = 1 ∨ spinProd A s = -1 := by
    induction A using Finset.induction with
    | empty => simp [spinProd]
    | @insert a A ha ih =>
      rw [spinProd, Finset.prod_insert ha]
      change spin s a * spinProd A s = 1 ∨ spin s a * spinProd A s = -1
      rcases spin_eq_pm s a with hs | hs <;>
        rcases ih with hA | hA <;> simp [hs, hA]
  rcases hpm with h | h
  · rw [h]
  · rw [h]
    norm_num


theorem expectationJ_le_one (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G beta J A ≤ 1 := by
  unfold expectationJ
  apply (div_le_one (partitionJ_pos G beta J)).2
  unfold partitionJ
  apply Finset.sum_le_sum
  intro s hs
  exact mul_le_of_le_one_left (boltzmannJ_pos G beta J s).le (spinProd_le_one A s)



theorem currentSum_le_empty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    currentSum G beta J A ≤ currentSum G beta J ∅ := by
  rw [Ising.acr_eq15_insertion']
  exact mul_le_of_le_one_left
    (Ising.acr_currentSum_nonneg G beta J hbeta hJ ∅)
    (expectationJ_le_one G beta J A)


def doubledEdgeCoupling (J : Sym2 V → ℝ) (e : Sym2 V) : Sym2 V → ℝ :=
  fun f => if f = e then 2 * J f else J f


theorem weight_doubledEdgeCoupling (beta : ℝ) (J : Sym2 V → ℝ)
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) =
      (2 : ℝ) ^ (m e) * weight G beta J (ofEdgeFun G m) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  calc
    (∏ i : G.edgeFinset,
        (beta * doubledEdgeCoupling J e.1 i.1) ^ m i / (m i).factorial) =
        ∏ i : G.edgeFinset,
          (if e = i then (2 : ℝ) ^ m i else 1) *
            ((beta * J i.1) ^ m i / (m i).factorial) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hei : e = i
      · subst i
        simp [doubledEdgeCoupling]
        ring
      · have hval : i.1 ≠ e.1 := fun h => hei (Subtype.ext h.symm)
        simp [doubledEdgeCoupling, hei, hval]
    _ = (∏ i : G.edgeFinset, if e = i then (2 : ℝ) ^ m i else 1) *
        ∏ i : G.edgeFinset, ((beta * J i.1) ^ m i / (m i).factorial) :=
      Finset.prod_mul_distrib
    _ = (2 : ℝ) ^ m e *
        ∏ i : G.edgeFinset, ((beta * J i.1) ^ m i / (m i).factorial) := by
      rw [Fintype.prod_ite_eq]

omit [Fintype V] in

theorem doubledEdgeCoupling_nonneg (J : Sym2 V → ℝ) (hJ : ∀ f, 0 ≤ J f)
    (e f : Sym2 V) : 0 ≤ doubledEdgeCoupling J e f := by
  simp only [doubledEdgeCoupling]
  split
  · exact mul_nonneg (by norm_num) (hJ f)
  · exact hJ f


theorem boltzmannJ_doubledEdgeCoupling_le (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (e : G.edgeFinset)
    (s : ConfigSpace V) :
    boltzmannJ G beta (doubledEdgeCoupling J e.1) s ≤
      Real.exp (beta * J e.1) * boltzmannJ G beta J s := by
  have hsum :
      (∑ f ∈ G.edgeFinset, doubledEdgeCoupling J e.1 f * bond s f) =
        J e.1 * bond s e.1 + ∑ f ∈ G.edgeFinset, J f * bond s f := by
    calc
      (∑ f ∈ G.edgeFinset, doubledEdgeCoupling J e.1 f * bond s f) =
          ∑ f ∈ G.edgeFinset,
            ((if f = e.1 then J f * bond s f else 0) + J f * bond s f) := by
        apply Finset.sum_congr rfl
        intro f hf
        by_cases hfe : f = e.1
        · simp [doubledEdgeCoupling, hfe]
          ring
        · simp [doubledEdgeCoupling, hfe]
      _ = (∑ f ∈ G.edgeFinset, if f = e.1 then J f * bond s f else 0) +
          ∑ f ∈ G.edgeFinset, J f * bond s f := by
        rw [Finset.sum_add_distrib]
      _ = J e.1 * bond s e.1 + ∑ f ∈ G.edgeFinset, J f * bond s f := by
        simp [e.2]
  have hb : bond s e.1 ≤ 1 := by
    rcases bond_eq_one_or_neg_one s e.1 with h | h
    · rw [h]
    · rw [h]
      norm_num
  unfold boltzmannJ
  rw [hsum, mul_add, Real.exp_add]
  gcongr
  simpa using mul_le_mul_of_nonneg_left hb (hJ e.1)



theorem partitionJ_doubledEdgeCoupling_le (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (e : G.edgeFinset) :
    partitionJ G beta (doubledEdgeCoupling J e.1) ≤
      Real.exp (beta * J e.1) * partitionJ G beta J := by
  unfold partitionJ
  calc
    (∑ s : ConfigSpace V, boltzmannJ G beta (doubledEdgeCoupling J e.1) s) ≤
        ∑ s : ConfigSpace V, Real.exp (beta * J e.1) * boltzmannJ G beta J s := by
      exact Finset.sum_le_sum fun s _ =>
        boltzmannJ_doubledEdgeCoupling_le G beta J hbeta hJ e s
    _ = Real.exp (beta * J e.1) * ∑ s : ConfigSpace V, boltzmannJ G beta J s := by
      rw [Finset.mul_sum]


theorem currentSum_doubledEdgeCoupling_le (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (e : G.edgeFinset) :
    currentSum G beta (doubledEdgeCoupling J e.1) ∅ ≤
      Real.exp (beta * J e.1) * currentSum G beta J ∅ := by
  have hp := partitionJ_doubledEdgeCoupling_le G beta J hbeta hJ e
  rw [partitionJ_eq_currentSum, partitionJ_eq_currentSum] at hp
  have hpow : (0 : ℝ) < 2 ^ Fintype.card V := by positivity
  nlinarith


theorem currentWeight_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (m : EdgeCurrent G) :
    0 ≤ weight G beta J (ofEdgeFun G m) := by
  unfold weight
  exact Finset.prod_nonneg fun f _ =>
    div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)



theorem sourceless_current_tail_doubling_le (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (e : G.edgeFinset)
    (K : ℕ) :
    (∑' m : EdgeCurrent G,
        if sources G (ofEdgeFun G m) = ∅ ∧ K ≤ m e then
          weight G beta J (ofEdgeFun G m) else 0) ≤
      ((2 : ℝ) ^ K)⁻¹ *
        currentSum G beta (doubledEdgeCoupling J e.1) ∅ := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if sources G (ofEdgeFun G m) = ∅ ∧ K ≤ m e then
      weight G beta J (ofEdgeFun G m) else 0
  let major : EdgeCurrent G → ℝ := fun m =>
    ((2 : ℝ) ^ K)⁻¹ *
      (if sources G (ofEdgeFun G m) = ∅ then
        weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) else 0)
  have hJ' : ∀ f, 0 ≤ doubledEdgeCoupling J e.1 f :=
    doubledEdgeCoupling_nonneg J hJ e.1
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split
    · exact currentWeight_nonneg G beta J hbeta hJ _
    · exact le_rfl
  have hmajor : Summable major := by
    exact ((summable_norm_currentSum_summand G beta
      (doubledEdgeCoupling J e.1) ∅).of_norm).mul_left (((2 : ℝ) ^ K)⁻¹)
  have hpoint : ∀ m, tail m ≤ major m := by
    intro m
    simp only [tail, major]
    by_cases hsrc : sources G (ofEdgeFun G m) = ∅
    · by_cases hm : K ≤ m e
      · simp only [hsrc, hm, and_self, if_true]
        rw [weight_doubledEdgeCoupling G beta J e m]
        have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ m e :=
          pow_le_pow_right₀ (by norm_num) hm
        have hpos : 0 < (2 : ℝ) ^ K := by positivity
        rw [inv_mul_eq_div]
        apply (le_div_iff₀ hpos).2
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hpow
          (currentWeight_nonneg G beta J hbeta hJ _)
      · simp [hsrc, hm,
          currentWeight_nonneg G beta (doubledEdgeCoupling J e.1) hbeta hJ']
    · simp [hsrc]
  calc
    (∑' m : EdgeCurrent G,
        if sources G (ofEdgeFun G m) = ∅ ∧ K ≤ m e then
          weight G beta J (ofEdgeFun G m) else 0) = ∑' m, tail m := rfl
    _ ≤ ∑' m, major m :=
      (Summable.of_nonneg_of_le htail_nonneg hpoint hmajor).tsum_le_tsum hpoint hmajor
    _ = ((2 : ℝ) ^ K)⁻¹ *
        currentSum G beta (doubledEdgeCoupling J e.1) ∅ := by
      rw [show (∑' m, major m) = ((2 : ℝ) ^ K)⁻¹ *
          ∑' m : EdgeCurrent G,
            if sources G (ofEdgeFun G m) = ∅ then
              weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) else 0 by
        exact tsum_mul_left]
      rfl



theorem sourcelessCurrentMeasure_edge_exponential_tail_le
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (e : G.edgeFinset)
    (K : ℕ) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if sources G (ofEdgeFun G m) = ∅ ∧ K ≤ m e then
      weight G beta J (ofEdgeFun G m) else 0
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split
    · exact currentWeight_nonneg G beta J hbeta hJ _
    · exact le_rfl
  have htailSummable : Summable tail := by
    refine Summable.of_nonneg_of_le htail_nonneg (fun m => ?_)
      (summable_norm_weight_ofEdgeFun G beta J).of_norm
    simp only [tail]
    split
    · exact le_rfl
    · exact currentWeight_nonneg G beta J hbeta hJ m
  have hZ : 0 < currentSum G beta J ∅ :=
    Ising.acr_currentSum_empty_pos G beta J
  change (sourcelessCurrentPMF G beta J hbeta hJ).toMeasure {m | K ≤ m e} ≤ _
  rw [PMF.toMeasure_apply_eq_tsum]
  have hsum :
      (∑' m : EdgeCurrent G,
        {m : EdgeCurrent G | K ≤ m e}.indicator
          (sourcelessCurrentPMF G beta J hbeta hJ) m) =
        ENNReal.ofReal (∑' m, tail m) /
          ENNReal.ofReal (currentSum G beta J ∅) := by
    calc
      (∑' m : EdgeCurrent G,
          {m : EdgeCurrent G | K ≤ m e}.indicator
            (sourcelessCurrentPMF G beta J hbeta hJ) m) =
          ∑' m : EdgeCurrent G,
            ENNReal.ofReal (tail m) *
              (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        apply tsum_congr
        intro m
        by_cases hm : K ≤ m e
        · rw [Set.indicator_of_mem
            (show m ∈ {m : EdgeCurrent G | K ≤ m e} from hm)]
          rw [sourcelessCurrentPMF, currentPMF_apply]
          by_cases hsrc : sources G (ofEdgeFun G m) = ∅
          · simp [currentRawMass, tail, hsrc, hm]
          · simp [currentRawMass, tail, hsrc]
        · rw [Set.indicator_of_notMem
            (show m ∉ {m : EdgeCurrent G | K ≤ m e} from hm)]
          simp [tail, hm]
      _ = (∑' m : EdgeCurrent G, ENNReal.ofReal (tail m)) *
          (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' m, tail m) *
          (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ := by
        rw [ENNReal.ofReal_tsum_of_nonneg htail_nonneg htailSummable]
      _ = ENNReal.ofReal (∑' m, tail m) /
          ENNReal.ofReal (currentSum G beta J ∅) := rfl
  rw [hsum]
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top]
  have hcoef : 0 ≤ Real.exp (beta * J e.1) / (2 : ℝ) ^ K :=
    div_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _)
  rw [← ENNReal.ofReal_mul hcoef]
  apply ENNReal.ofReal_le_ofReal
  have htail := sourceless_current_tail_doubling_le G beta J hbeta hJ e K
  have hZ' := currentSum_doubledEdgeCoupling_le G beta J hbeta hJ e
  calc
    (∑' m, tail m) ≤ ((2 : ℝ) ^ K)⁻¹ *
        currentSum G beta (doubledEdgeCoupling J e.1) ∅ := htail
    _ ≤ ((2 : ℝ) ^ K)⁻¹ *
        (Real.exp (beta * J e.1) * currentSum G beta J ∅) :=
      mul_le_mul_of_nonneg_left hZ' (inv_nonneg.2 (pow_nonneg (by norm_num) _))
    _ = (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) *
        currentSum G beta J ∅ := by field_simp



theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simpa [mul_two] using Nat.add_le_add ih (Nat.one_le_two_pow (n := n))


theorem sourcelessCurrentMeasure_edge_inverse_tail_le
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f) (e : G.edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal (Real.exp (beta * J e.1) / K) := by
  calc
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
        ENNReal.ofReal (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) :=
      sourcelessCurrentMeasure_edge_exponential_tail_le G beta J hbeta hJ e K
    _ ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / K) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (Nat.cast_pos.2 hK)
      exact_mod_cast nat_le_two_pow K

end StatMech.FrontierB
