/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeElitzur
import Code.Ising.GKS2










open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unnecessarySeqFocus false

namespace StatMech.FrontierA

noncomputable section

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem gaugeEdgeSpin_xnor
    (sigma q : GaugeConfig E) (e : E) :
    gaugeEdgeSpin (StatMech.Ising.xnor sigma q) e =
      gaugeEdgeSpin sigma e * gaugeEdgeSpin q e := by
  exact StatMech.Ising.spin_xnor sigma q e

omit [Fintype P] [DecidableEq P] in
theorem plaquetteSpin_xnor
    (incidence : P -> Finset E) (sigma q : GaugeConfig E) (p : P) :
    plaquetteSpin incidence (StatMech.Ising.xnor sigma q) p =
      plaquetteSpin incidence sigma p * plaquetteSpin incidence q p := by
  unfold plaquetteSpin
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun e _ => gaugeEdgeSpin_xnor sigma q e)

omit [Fintype P] [DecidableEq P] in
theorem wilsonSpin_xnor (L : Finset E) (sigma q : GaugeConfig E) :
    wilsonSpin L (StatMech.Ising.xnor sigma q) =
      wilsonSpin L sigma * wilsonSpin L q := by
  unfold wilsonSpin
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun e _ => gaugeEdgeSpin_xnor sigma q e)

omit [Fintype P] [DecidableEq P] in
theorem wilsonSpin_mul_self (A B : Finset E) (sigma : GaugeConfig E) :
    wilsonSpin A sigma * wilsonSpin B sigma = wilsonSpin (A ∆ B) sigma := by
  simpa only [wilsonSpin, gaugeEdgeSpin] using
    StatMech.Ising.spinProd_mul_self A B sigma

omit [Fintype P] [DecidableEq P] in
theorem isSpinMonomial_plaquetteSpin (incidence : P -> Finset E) (p : P) :
    StatMech.Ising.IsSpinMonomial (fun sigma => plaquetteSpin incidence sigma p) := by
  simpa only [plaquetteSpin, gaugeEdgeSpin, StatMech.Ising.spinProd] using
    StatMech.Ising.isSpinMonomial_spinProd (incidence p)

omit [Fintype P] [DecidableEq P] in
theorem isSpinMonomial_wilsonSpin (L : Finset E) :
    StatMech.Ising.IsSpinMonomial (wilsonSpin L : GaugeConfig E -> Real) := by
  simpa only [wilsonSpin, gaugeEdgeSpin, StatMech.Ising.spinProd] using
    StatMech.Ising.isSpinMonomial_spinProd L

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem one_add_plaquetteSpin_nonneg
    (incidence : P -> Finset E) (q : GaugeConfig E) (p : P) :
    0 <= 1 + plaquetteSpin incidence q p := by
  rcases plaquetteSpin_eq_one_or_neg_one incidence q p with h | h <;>
    rw [h] <;> norm_num

omit [Fintype P] [DecidableEq P] in
theorem one_sub_wilsonSpin_nonneg (L : Finset E) (q : GaugeConfig E) :
    0 <= 1 - wilsonSpin L q := by
  simpa only [wilsonSpin, gaugeEdgeSpin, StatMech.Ising.spinProd] using
    StatMech.Ising.one_sub_spinProd_nonneg L q




theorem gaugeWeight_mul_xnor
    (incidence : P -> Finset E) (K : P -> Real)
    (sigma q : GaugeConfig E) :
    gaugeWeight incidence K sigma *
        gaugeWeight incidence K (StatMech.Ising.xnor sigma q) =
      gaugeWeight incidence
        (fun p => K p * (1 + plaquetteSpin incidence q p)) sigma := by
  unfold gaugeWeight gaugeAction
  rw [← Real.exp_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquetteSpin_xnor]
  ring


theorem gauge_monomial_weight_sum_nonneg
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p)
    (obs : GaugeConfig E -> Real)
    (hobs : StatMech.Ising.IsSpinMonomial obs) :
    0 <= ∑ sigma : GaugeConfig E, obs sigma * gaugeWeight incidence K sigma := by
  have hkernel : 0 <= ∑ sigma : GaugeConfig E,
      obs sigma * ∏ p : P,
        (1 + Real.tanh (K p) * plaquetteSpin incidence sigma p) := by
    have h := StatMech.Ising.gks_kernel (Finset.univ : Finset P)
      (fun _ => (1 : Real)) (fun p => Real.tanh (K p))
      (fun _ _ => by norm_num)
      (fun p _ => by
        change 0 <= Real.tanh (K p)
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr (hK p)) (Real.cosh_pos _).le)
      (fun p sigma => plaquetteSpin incidence sigma p)
      (fun p _ => isSpinMonomial_plaquetteSpin incidence p) obs hobs
    simpa only [Finset.mem_univ, Finset.prod_const, Nat.card_eq_fintype_card,
      one_pow, mul_comm] using h
  have hcosh : 0 <= ∏ p : P, Real.cosh (K p) :=
    Finset.prod_nonneg (fun p _ => (Real.cosh_pos (K p)).le)
  simp_rw [gaugeWeight_eq_highTempFactors incidence K]
  calc
    0 <= (∏ p : P, Real.cosh (K p)) *
        ∑ sigma : GaugeConfig E, obs sigma *
          ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence sigma p) :=
      mul_nonneg hcosh hkernel
    _ = ∑ sigma : GaugeConfig E, obs sigma *
        ((∏ p : P, Real.cosh (K p)) *
          ∏ p : P, (1 + Real.tanh (K p) * plaquetteSpin incidence sigma p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma _
      ring


theorem gauge_inner_q_nonneg
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p) (A B : Finset E) (q : GaugeConfig E) :
    0 <= ∑ sigma : GaugeConfig E,
      (wilsonSpin (A ∆ B) sigma * gaugeWeight incidence K sigma *
          gaugeWeight incidence K (StatMech.Ising.xnor sigma q) -
        wilsonSpin A sigma * gaugeWeight incidence K sigma *
          (wilsonSpin B (StatMech.Ising.xnor sigma q) *
            gaugeWeight incidence K (StatMech.Ising.xnor sigma q))) := by
  have key : forall sigma : GaugeConfig E,
      (wilsonSpin (A ∆ B) sigma * gaugeWeight incidence K sigma *
          gaugeWeight incidence K (StatMech.Ising.xnor sigma q) -
        wilsonSpin A sigma * gaugeWeight incidence K sigma *
          (wilsonSpin B (StatMech.Ising.xnor sigma q) *
            gaugeWeight incidence K (StatMech.Ising.xnor sigma q))) =
      (1 - wilsonSpin B q) *
        ((wilsonSpin A sigma * wilsonSpin B sigma) *
          gaugeWeight incidence
            (fun p => K p * (1 + plaquetteSpin incidence q p)) sigma) := by
    intro sigma
    rw [← gaugeWeight_mul_xnor incidence K sigma q,
      wilsonSpin_xnor, ← wilsonSpin_mul_self]
    ring
  rw [Finset.sum_congr rfl (fun sigma _ => key sigma), ← Finset.mul_sum]
  apply mul_nonneg (one_sub_wilsonSpin_nonneg B q)
  apply gauge_monomial_weight_sum_nonneg
  · intro p
    exact mul_nonneg (hK p) (one_add_plaquetteSpin_nonneg incidence q p)
  · exact (isSpinMonomial_wilsonSpin A).mul (isSpinMonomial_wilsonSpin B)


theorem gaugeWilsonNumerator_mul_le
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p) (A B : Finset E) :
    gaugeWilsonNumerator incidence K A * gaugeWilsonNumerator incidence K B <=
      gaugeWilsonNumerator incidence K (A ∆ B) * gaugePartition incidence K := by
  unfold gaugeWilsonNumerator gaugePartition
  rw [← sub_nonneg, Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Finset.sum_sub_distrib]
  rw [StatMech.Ising.sum_dbl_reindex (fun pair =>
    wilsonSpin (A ∆ B) pair.1 * gaugeWeight incidence K pair.1 *
        gaugeWeight incidence K pair.2 -
      wilsonSpin A pair.1 * gaugeWeight incidence K pair.1 *
        (wilsonSpin B pair.2 * gaugeWeight incidence K pair.2))]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_nonneg (fun q _ => gauge_inner_q_nonneg incidence K hK A B q)



theorem gaugeWilsonExpectation_mul_le_symmDiff
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall p, 0 <= K p) (A B : Finset E) :
    gaugeWilsonExpectation incidence K A * gaugeWilsonExpectation incidence K B <=
      gaugeWilsonExpectation incidence K (A ∆ B) := by
  unfold gaugeWilsonExpectation
  have hZ : 0 < gaugePartition incidence K := gaugePartition_pos incidence K
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hZ]
  calc
    gaugeWilsonNumerator incidence K A * gaugeWilsonNumerator incidence K B *
        gaugePartition incidence K <=
      (gaugeWilsonNumerator incidence K (A ∆ B) *
          gaugePartition incidence K) * gaugePartition incidence K :=
        mul_le_mul_of_nonneg_right
          (gaugeWilsonNumerator_mul_le incidence K hK A B) hZ.le
    _ = gaugeWilsonNumerator incidence K (A ∆ B) *
        (gaugePartition incidence K * gaugePartition incidence K) := by ring


def addGaugePlaquetteCoupling (K : P -> Real) (p : P) (delta : Real) : P -> Real :=
  fun q => if q = p then K q + delta else K q

theorem gaugeAction_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real)
    (sigma : GaugeConfig E) :
    gaugeAction incidence (addGaugePlaquetteCoupling K p delta) sigma =
      gaugeAction incidence K sigma + delta * plaquetteSpin incidence sigma p := by
  unfold gaugeAction addGaugePlaquetteCoupling
  calc
    (∑ q : P, (if q = p then K q + delta else K q) *
        plaquetteSpin incidence sigma q) =
      ∑ q : P, (K q * plaquetteSpin incidence sigma q +
        if q = p then delta * plaquetteSpin incidence sigma q else 0) := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hqp : q = p <;> simp [hqp] <;> ring
    _ = (∑ q : P, K q * plaquetteSpin incidence sigma q) +
        ∑ q : P, if q = p then delta * plaquetteSpin incidence sigma q else 0 := by
      rw [Finset.sum_add_distrib]
    _ = _ := by simp

theorem gaugeWeight_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real)
    (sigma : GaugeConfig E) :
    gaugeWeight incidence (addGaugePlaquetteCoupling K p delta) sigma =
      gaugeWeight incidence K sigma *
        (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta) := by
  unfold gaugeWeight
  rw [gaugeAction_addPlaquetteCoupling, Real.exp_add,
    StatMech.Ising.exp_mul_pm delta (plaquetteSpin incidence sigma p)
      (plaquetteSpin_eq_one_or_neg_one incidence sigma p)]


theorem gaugeWilsonNumerator_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real)
    (L : Finset E) :
    gaugeWilsonNumerator incidence (addGaugePlaquetteCoupling K p delta) L =
      Real.cosh delta * gaugeWilsonNumerator incidence K L +
        Real.sinh delta * gaugeWilsonNumerator incidence K (L ∆ incidence p) := by
  unfold gaugeWilsonNumerator
  simp_rw [gaugeWeight_addPlaquetteCoupling]
  calc
    (∑ sigma : GaugeConfig E, wilsonSpin L sigma *
        (gaugeWeight incidence K sigma *
          (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta))) =
      ∑ sigma : GaugeConfig E,
        (Real.cosh delta * (wilsonSpin L sigma * gaugeWeight incidence K sigma) +
          Real.sinh delta *
            (wilsonSpin (L ∆ incidence p) sigma * gaugeWeight incidence K sigma)) := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [← wilsonSpin_mul_self L (incidence p) sigma]
        rw [show plaquetteSpin incidence sigma p =
          wilsonSpin (incidence p) sigma by rfl]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]


theorem gaugePartition_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real) (p : P) (delta : Real) :
    gaugePartition incidence (addGaugePlaquetteCoupling K p delta) =
      Real.cosh delta * gaugePartition incidence K +
        Real.sinh delta * gaugeWilsonNumerator incidence K (incidence p) := by
  unfold gaugePartition gaugeWilsonNumerator
  simp_rw [gaugeWeight_addPlaquetteCoupling]
  calc
    (∑ sigma : GaugeConfig E, gaugeWeight incidence K sigma *
        (Real.cosh delta + plaquetteSpin incidence sigma p * Real.sinh delta)) =
      ∑ sigma : GaugeConfig E,
        (Real.cosh delta * gaugeWeight incidence K sigma +
          Real.sinh delta *
            (wilsonSpin (incidence p) sigma * gaugeWeight incidence K sigma)) := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [show plaquetteSpin incidence sigma p =
          wilsonSpin (incidence p) sigma by rfl]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]




theorem gaugeWilsonExpectation_le_addPlaquetteCoupling
    (incidence : P -> Finset E) (K : P -> Real)
    (hK : forall q, 0 <= K q) (p : P) {delta : Real} (hdelta : 0 <= delta)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L <=
      gaugeWilsonExpectation incidence (addGaugePlaquetteCoupling K p delta) L := by
  let Z := gaugePartition incidence K
  let N := gaugeWilsonNumerator incidence K L
  let Pn := gaugeWilsonNumerator incidence K (incidence p)
  let NP := gaugeWilsonNumerator incidence K (L ∆ incidence p)
  have hZ : 0 < Z := gaugePartition_pos incidence K
  have hZ' : 0 < gaugePartition incidence (addGaugePlaquetteCoupling K p delta) :=
    gaugePartition_pos incidence (addGaugePlaquetteCoupling K p delta)
  have hgks : N * Pn <= NP * Z :=
    gaugeWilsonNumerator_mul_le incidence K hK L (incidence p)
  have hsinh : 0 <= Real.sinh delta := Real.sinh_nonneg_iff.mpr hdelta
  unfold gaugeWilsonExpectation
  rw [gaugeWilsonNumerator_addPlaquetteCoupling,
    gaugePartition_addPlaquetteCoupling]
  change N / Z <=
    (Real.cosh delta * N + Real.sinh delta * NP) /
      (Real.cosh delta * Z + Real.sinh delta * Pn)
  have hden : 0 < Real.cosh delta * Z + Real.sinh delta * Pn := by
    rw [← gaugePartition_addPlaquetteCoupling incidence K p delta]
    exact hZ'
  rw [div_le_div_iff₀ hZ hden]
  nlinarith [mul_le_mul_of_nonneg_left hgks hsinh]



theorem gaugeWilsonExpectation_mono_coupling
    (incidence : P -> Finset E) (K K' : P -> Real)
    (hK : forall p, 0 <= K p) (hKK' : forall p, K p <= K' p)
    (L : Finset E) :
    gaugeWilsonExpectation incidence K L <=
      gaugeWilsonExpectation incidence K' L := by
  let replaceOn (S : Finset P) : P -> Real :=
    fun p => if p ∈ S then K' p else K p
  have hstep : forall S : Finset P,
      gaugeWilsonExpectation incidence K L <=
        gaugeWilsonExpectation incidence (replaceOn S) L := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [replaceOn]
    | @insert p S hp ih =>
        have hcurrent : forall q, 0 <= replaceOn S q := by
          intro q
          by_cases hq : q ∈ S
          · simpa [replaceOn, hq] using le_trans (hK q) (hKK' q)
          · simpa [replaceOn, hq] using hK q
        have hdelta : 0 <= K' p - K p := sub_nonneg.mpr (hKK' p)
        have hreplace : replaceOn (insert p S) =
            addGaugePlaquetteCoupling (replaceOn S) p (K' p - K p) := by
          funext q
          by_cases hqp : q = p
          · subst q
            simp [replaceOn, addGaugePlaquetteCoupling, hp]
          · simp [replaceOn, addGaugePlaquetteCoupling, hqp]
        rw [hreplace]
        exact ih.trans (gaugeWilsonExpectation_le_addPlaquetteCoupling
          incidence (replaceOn S) hcurrent p hdelta L)
  simpa [replaceOn] using hstep (Finset.univ : Finset P)

end

end StatMech.FrontierA
