/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.GHSInhomogeneous

open Finset Filter
open scoped BigOperators

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def replicaBridgeInteraction (sites : I -> V)
    (a b : ConfigSpace V) : Real :=
  ∑ i : I, spin a (sites i) * spin b (sites i)


def replicaAgreementSpin (sites : I -> V) (q : ConfigSpace V) : Real :=
  ∑ i : I, spin q (sites i)


def replicaBridgeMonomial (sites : I -> V) (S : Finset I)
    (s : ConfigSpace V) : Real :=
  ∏ i ∈ S, spin s (sites i)

theorem replicaBridgeInteraction_mate
    (sites : I -> V) (q a : ConfigSpace V) :
    replicaBridgeInteraction sites a (ghsLMate q a) =
      replicaAgreementSpin sites q := by
  unfold replicaBridgeInteraction replicaAgreementSpin
  apply Finset.sum_congr rfl
  intro i hi
  unfold ghsLMate spin
  by_cases hq : q (sites i) <;>
    by_cases ha : a (sites i) <;> simp [hq, ha]


def replicaBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b =>
    Real.exp (r * replicaBridgeInteraction sites a b))


def replicaBridgeMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b =>
      replicaBridgeInteraction sites a b *
        Real.exp (r * replicaBridgeInteraction sites a b)) /
    replicaBridgeMoment G J hf sites r



def replicaBridgeVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiExp2 G J hf (fun a b =>
      replicaBridgeInteraction sites a b ^ 2 *
        Real.exp (r * replicaBridgeInteraction sites a b)) /
      replicaBridgeMoment G J hf sites r -
    replicaBridgeMean G J hf sites r ^ 2


def replicaBridgeFreeEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  Real.log (replicaBridgeMoment G J hf sites r) -
    Real.log (replicaBridgeMoment G J hf sites (-r))

theorem replicaBridgeMoment_pos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    0 < replicaBridgeMoment G J hf sites r := by
  unfold replicaBridgeMoment ghsiExp2
  apply div_pos
  · apply Finset.sum_pos
    · intro a _
      apply Finset.sum_pos
      · intro b _
        exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
          (Real.exp_pos _)
      · exact Finset.univ_nonempty
    · exact Finset.univ_nonempty
  · exact sq_pos_of_pos (ZJ_pos _ _ _)



theorem replicaBridgeMoment_eq_agreementTilt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMoment G J hf sites r =
      ∑ q : ConfigSpace V, ghsiAgreementProb G J hf q *
        Real.exp (r * replicaAgreementSpin sites q) := by
  unfold replicaBridgeMoment ghsiExp2 ghsiAgreementProb
  rw [ghsL_sum_pair_xnor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  unfold ghsiFibreMass ghsiFibreWeight
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  apply congrArg (fun z => z / ZJ G.edgeFinset J hf ^ 2)
  apply Finset.sum_congr rfl
  intro a ha
  change wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf (ghsLMate q a) *
      Real.exp (r * replicaBridgeInteraction sites a (ghsLMate q a)) = _
  rw [replicaBridgeInteraction_mate]



theorem ghsiExp2_replicaBridgeFunction_eq_agreement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (F : Real -> Real) :
    ghsiExp2 G J hf (fun a b => F (replicaBridgeInteraction sites a b)) =
      ∑ q : ConfigSpace V, ghsiAgreementProb G J hf q *
        F (replicaAgreementSpin sites q) := by
  unfold ghsiExp2 ghsiAgreementProb
  rw [ghsL_sum_pair_xnor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  unfold ghsiFibreMass ghsiFibreWeight
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  apply congrArg (fun z => z / ZJ G.edgeFinset J hf ^ 2)
  apply Finset.sum_congr rfl
  intro a ha
  change wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf (ghsLMate q a) *
      F (replicaBridgeInteraction sites a (ghsLMate q a)) = _
  rw [replicaBridgeInteraction_mate]


def replicaAgreementTiltProb
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) (q : ConfigSpace V) : Real :=
  ghsiAgreementProb G J hf q *
      Real.exp (r * replicaAgreementSpin sites q) /
    replicaBridgeMoment G J hf sites r


def replicaAgreementTiltVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  (∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q *
      replicaAgreementSpin sites q ^ 2) -
    (∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q *
      replicaAgreementSpin sites q) ^ 2

theorem replicaAgreementTiltProb_sum_eq_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    ∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q = 1 := by
  unfold replicaAgreementTiltProb
  rw [← Finset.sum_div, div_eq_one_iff_eq
    (replicaBridgeMoment_pos G J hf sites r).ne']
  exact (replicaBridgeMoment_eq_agreementTilt G J hf sites r).symm

theorem replicaBridgeMean_eq_agreementTiltMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMean G J hf sites r =
      ∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q *
        replicaAgreementSpin sites q := by
  unfold replicaBridgeMean replicaAgreementTiltProb
  rw [ghsiExp2_replicaBridgeFunction_eq_agreement G J hf sites
    (fun x => x * Real.exp (r * x))]
  rw [Finset.sum_div]
  congr 1
  funext q
  ring

theorem replicaBridgeVariance_eq_agreementTiltVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeVariance G J hf sites r =
      replicaAgreementTiltVariance G J hf sites r := by
  unfold replicaBridgeVariance replicaAgreementTiltVariance
  rw [replicaBridgeMean_eq_agreementTiltMean]
  rw [ghsiExp2_replicaBridgeFunction_eq_agreement G J hf sites
    (fun x => x ^ 2 * Real.exp (r * x))]
  unfold replicaAgreementTiltProb
  rw [Finset.sum_div]
  congr 2
  funext q
  ring

theorem ghsiExp2_finset_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {A : Type*} (S : Finset A)
    (F : A -> ConfigSpace V -> ConfigSpace V -> Real) :
    ghsiExp2 G J hf (fun a b => ∑ i ∈ S, F i a b) =
      ∑ i ∈ S, ghsiExp2 G J hf (F i) := by
  classical
  induction S using Finset.induction with
  | empty => simp [ghsiExp2]
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi, ghsiExp2_add, ih]



theorem replicaBridgeMoment_highTemp
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMoment G J hf sites r =
      ∑ S ∈ (Finset.univ : Finset I).powerset,
        Real.sinh r ^ S.card *
          Real.cosh r ^ (Fintype.card I - S.card) *
          (expJ G.edgeFinset J hf (replicaBridgeMonomial sites S)) ^ 2 := by
  have hexpand :
      (fun a b : ConfigSpace V =>
        Real.exp (r * replicaBridgeInteraction sites a b)) =
      (fun a b =>
        ∑ S ∈ (Finset.univ : Finset I).powerset,
          Real.sinh r ^ S.card *
            Real.cosh r ^ (Fintype.card I - S.card) *
            (replicaBridgeMonomial sites S a *
              replicaBridgeMonomial sites S b)) := by
    funext a b
    rw [replicaBridgeInteraction, Finset.mul_sum, Real.exp_sum]
    have hfac (i : I) :
        Real.exp (r * (spin a (sites i) * spin b (sites i))) =
          spin a (sites i) * spin b (sites i) * Real.sinh r +
            Real.cosh r := by
      rw [exp_mul_pm r _ (by
        rcases spin_eq_pm a (sites i) with ha | ha <;>
          rcases spin_eq_pm b (sites i) with hb | hb <;> simp [ha, hb])]
      ring
    simp_rw [hfac]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro S hS
    have hsub : S ⊆ (Finset.univ : Finset I) := Finset.mem_powerset.mp hS
    rw [show (∏ i ∈ S,
        spin a (sites i) * spin b (sites i) * Real.sinh r) =
      Real.sinh r ^ S.card *
        (replicaBridgeMonomial sites S a *
          replicaBridgeMonomial sites S b) by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      unfold replicaBridgeMonomial
      rw [Finset.prod_mul_distrib]
      ring,
      show (∏ _i ∈ (Finset.univ : Finset I) \ S, Real.cosh r) =
        Real.cosh r ^ (Fintype.card I - S.card) by
      rw [Finset.prod_const]
      congr 1
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
        Finset.card_univ]]
    ring
  unfold replicaBridgeMoment
  rw [hexpand, ghsiExp2_finset_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [ghsiExp2_const_mul, ghsiExp2_factor]
  ring

theorem hasDerivAt_replicaBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    HasDerivAt (replicaBridgeMoment G J hf sites)
      (ghsiExp2 G J hf (fun a b =>
        replicaBridgeInteraction sites a b *
          Real.exp (r * replicaBridgeInteraction sites a b))) r := by
  unfold replicaBridgeMoment ghsiExp2
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro a ha
  apply HasDerivAt.fun_sum
  intro b hb
  have hexp : HasDerivAt
      (fun t : Real => Real.exp
        (t * replicaBridgeInteraction sites a b))
      (Real.exp (r * replicaBridgeInteraction sites a b) *
        replicaBridgeInteraction sites a b) r := by
    simpa using (Real.hasDerivAt_exp
      (r * replicaBridgeInteraction sites a b)).comp r
        ((hasDerivAt_id r).mul_const
          (replicaBridgeInteraction sites a b))
  convert hexp.const_mul
    (wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b) using 1 <;> ring

theorem hasDerivAt_replicaBridgeWeightedMeanNumerator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    HasDerivAt (fun t => ghsiExp2 G J hf (fun a b =>
      replicaBridgeInteraction sites a b *
        Real.exp (t * replicaBridgeInteraction sites a b)))
      (ghsiExp2 G J hf (fun a b =>
        replicaBridgeInteraction sites a b ^ 2 *
          Real.exp (r * replicaBridgeInteraction sites a b))) r := by
  unfold ghsiExp2
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro a ha
  apply HasDerivAt.fun_sum
  intro b hb
  have hexp : HasDerivAt
      (fun t : Real => Real.exp
        (t * replicaBridgeInteraction sites a b))
      (Real.exp (r * replicaBridgeInteraction sites a b) *
        replicaBridgeInteraction sites a b) r := by
    simpa using (Real.hasDerivAt_exp
      (r * replicaBridgeInteraction sites a b)).comp r
        ((hasDerivAt_id r).mul_const
          (replicaBridgeInteraction sites a b))
  convert (hexp.const_mul (replicaBridgeInteraction sites a b)).const_mul
    (wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b) using 1 <;> ring



theorem hasDerivAt_replicaBridgeMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    HasDerivAt (replicaBridgeMean G J hf sites)
      (replicaBridgeVariance G J hf sites r) r := by
  let N : Real -> Real := fun t => ghsiExp2 G J hf (fun a b =>
    replicaBridgeInteraction sites a b *
      Real.exp (t * replicaBridgeInteraction sites a b))
  let N2 : Real := ghsiExp2 G J hf (fun a b =>
    replicaBridgeInteraction sites a b ^ 2 *
      Real.exp (r * replicaBridgeInteraction sites a b))
  let Zr := replicaBridgeMoment G J hf sites r
  have hN : HasDerivAt N N2 r := by
    simpa only [N, N2] using
      hasDerivAt_replicaBridgeWeightedMeanNumerator G J hf sites r
  have hZ := hasDerivAt_replicaBridgeMoment G J hf sites r
  have hZne : Zr ≠ 0 := by
    exact (replicaBridgeMoment_pos G J hf sites r).ne'
  have hquot := hN.div hZ hZne
  change HasDerivAt (N / replicaBridgeMoment G J hf sites)
    (replicaBridgeVariance G J hf sites r) r
  convert hquot using 1
  unfold replicaBridgeVariance replicaBridgeMean
  dsimp only [N, N2, Zr]
  field_simp [(replicaBridgeMoment_pos G J hf sites r).ne']
  have hsecond :
      ghsiExp2 G J hf (fun a b =>
        replicaBridgeInteraction sites a b ^ 2 *
          Real.exp (replicaBridgeInteraction sites a b * r)) =
        ghsiExp2 G J hf (fun a b =>
          replicaBridgeInteraction sites a b ^ 2 *
            Real.exp (r * replicaBridgeInteraction sites a b)) := by
    congr 1
    funext a b
    rw [mul_comm (replicaBridgeInteraction sites a b) r]
  rw [hsecond]
  ring


theorem hasDerivAt_replicaBridgeSymmetricMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    HasDerivAt (fun t =>
      replicaBridgeMean G J hf sites t +
        replicaBridgeMean G J hf sites (-t))
      (replicaBridgeVariance G J hf sites r -
        replicaBridgeVariance G J hf sites (-r)) r := by
  have hp := hasDerivAt_replicaBridgeMean G J hf sites r
  have hm := (hasDerivAt_replicaBridgeMean G J hf sites (-r)).comp r
    (hasDerivAt_id r).neg
  convert hp.add hm using 1 <;> ring

theorem hasDerivAt_log_replicaBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    HasDerivAt (fun t => Real.log (replicaBridgeMoment G J hf sites t))
      (replicaBridgeMean G J hf sites r) r := by
  exact (hasDerivAt_replicaBridgeMoment G J hf sites r).log
    (replicaBridgeMoment_pos G J hf sites r).ne'


theorem hasDerivAt_replicaBridgeFreeEnergy
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    HasDerivAt (replicaBridgeFreeEnergy G J hf sites)
      (replicaBridgeMean G J hf sites r +
        replicaBridgeMean G J hf sites (-r)) r := by
  unfold replicaBridgeFreeEnergy
  have hp := hasDerivAt_log_replicaBridgeMoment G J hf sites r
  have hm := (hasDerivAt_log_replicaBridgeMoment G J hf sites (-r)).comp r
    (hasDerivAt_id r).neg
  convert hp.sub hm using 1 <;> ring



theorem replicaBridgeMean_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V) :
    replicaBridgeMean G J hf sites 0 =
      ∑ i : I,
        (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
  have hmoment : replicaBridgeMoment G J hf sites 0 = 1 := by
    unfold replicaBridgeMoment
    simp only [zero_mul, Real.exp_zero]
    have h := ghsiExp2_factor G J hf
      (fun _ => (1 : Real)) (fun _ => (1 : Real))
    simpa [expJ_one G J hf] using h
  unfold replicaBridgeMean
  rw [hmoment, div_one]
  simp only [zero_mul, Real.exp_zero, mul_one]
  have hsum :
      (fun a b : ConfigSpace V => replicaBridgeInteraction sites a b) =
      (fun a b => ∑ i : I, spin a (sites i) * spin b (sites i)) := rfl
  rw [hsum]
  unfold ghsiExp2
  have hZ : ZJ G.edgeFinset J hf ≠ 0 := (ZJ_pos _ _ _).ne'
  have hreorder :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
          ∑ i : I, spin a (sites i) * spin b (sites i)) =
      ∑ i : I,
        (∑ a : ConfigSpace V,
          spin a (sites i) * wJ G.edgeFinset J hf a) ^ 2 := by
    calc
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
          wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
            ∑ i : I, spin a (sites i) * spin b (sites i)) =
          ∑ a : ConfigSpace V, ∑ b : ConfigSpace V, ∑ i : I,
            wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
              (spin a (sites i) * spin b (sites i)) := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.mul_sum]
      _ = ∑ a : ConfigSpace V, ∑ i : I, ∑ b : ConfigSpace V,
            wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
              (spin a (sites i) * spin b (sites i)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_comm]
      _ = ∑ i : I, ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
            wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
              (spin a (sites i) * spin b (sites i)) := by
            rw [Finset.sum_comm]
      _ = ∑ i : I,
          (∑ a : ConfigSpace V,
            spin a (sites i) * wJ G.edgeFinset J hf a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [pow_two, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            ring
  rw [hreorder]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  unfold expJ
  field_simp



theorem replicaBridgeFreeEnergy_deriv_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V) :
    deriv (replicaBridgeFreeEnergy G J hf sites) 0 =
      2 * ∑ i : I,
        (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
  rw [(hasDerivAt_replicaBridgeFreeEnergy G J hf sites 0).deriv]
  rw [neg_zero, replicaBridgeMean_zero]
  ring



theorem replicaBridgeSymmetricMean_le_zero_of_variance_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) (hr : 0 <= r)
    (hvar : forall t, 0 <= t ->
      replicaBridgeVariance G J hf sites t <=
        replicaBridgeVariance G J hf sites (-t)) :
    replicaBridgeMean G J hf sites r +
        replicaBridgeMean G J hf sites (-r) <=
      2 * replicaBridgeMean G J hf sites 0 := by
  let D : Real -> Real := fun t =>
    replicaBridgeMean G J hf sites t +
      replicaBridgeMean G J hf sites (-t)
  have hdiff : Differentiable Real D := by
    intro t
    exact (hasDerivAt_replicaBridgeSymmetricMean G J hf sites t).differentiableAt
  have hanti : AntitoneOn D (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : Real))
    · exact hdiff.continuous.continuousOn
    · intro t ht
      exact DifferentiableAt.differentiableWithinAt
        (hasDerivAt_replicaBridgeSymmetricMean G J hf sites t).differentiableAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hasDerivAt_replicaBridgeSymmetricMean G J hf sites t).deriv]
      exact sub_nonpos.mpr (hvar t ht.le)
  have hle := hanti (by simp) hr hr
  dsimp only [D] at hle
  rw [neg_zero] at hle
  linarith




theorem replicaBridgeFreeEnergy_le_of_symmetric_mean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) (hr : 0 ≤ r)
    (hmean : ∀ t, 0 ≤ t ->
      replicaBridgeMean G J hf sites t +
          replicaBridgeMean G J hf sites (-t) ≤
        2 * replicaBridgeMean G J hf sites 0) :
    replicaBridgeFreeEnergy G J hf sites r ≤
      2 * r * ∑ i : I,
        (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [replicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (replicaBridgeFreeEnergy G J hf sites) := by
    intro t
    exact (hasDerivAt_replicaBridgeFreeEnergy G J hf sites t).differentiableAt
  have hcont : ContinuousOn
      (replicaBridgeFreeEnergy G J hf sites) (Set.Icc 0 r) :=
    hdiffAll.continuous.continuousOn
  have hdiff : DifferentiableOn Real
      (replicaBridgeFreeEnergy G J hf sites) (Set.Ioo 0 r) :=
    hdiffAll.differentiableOn
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (replicaBridgeFreeEnergy G J hf sites) hrpos hcont hdiff
  have hderiv : deriv (replicaBridgeFreeEnergy G J hf sites) c ≤
      2 * replicaBridgeMean G J hf sites 0 := by
    rw [(hasDerivAt_replicaBridgeFreeEnergy G J hf sites c).deriv]
    exact hmean c hc.1.le
  have hzero : replicaBridgeFreeEnergy G J hf sites 0 = 0 := by
    simp [replicaBridgeFreeEnergy]
  have hr0 : 0 < r := hrpos
  have hmul : deriv (replicaBridgeFreeEnergy G J hf sites) c * r ≤
      (2 * replicaBridgeMean G J hf sites 0) * r := by
    exact mul_le_mul_of_nonneg_right hderiv hr0.le
  rw [hslope, hzero] at hmul
  simp only [sub_zero] at hmul
  rw [div_mul_cancel₀ _ hr0.ne'] at hmul
  calc
    replicaBridgeFreeEnergy G J hf sites r ≤
        (2 * replicaBridgeMean G J hf sites 0) * r := hmul
    _ = 2 * r * ∑ i : I,
        (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
      rw [replicaBridgeMean_zero]
      ring



theorem replicaBridgeFreeEnergy_le_of_variance_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) (hr : 0 <= r)
    (hvar : forall t, 0 <= t ->
      replicaBridgeVariance G J hf sites t <=
        replicaBridgeVariance G J hf sites (-t)) :
    replicaBridgeFreeEnergy G J hf sites r <=
      2 * r * ∑ i : I,
        (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
  apply replicaBridgeFreeEnergy_le_of_symmetric_mean G J hf sites r hr
  intro t ht
  exact replicaBridgeSymmetricMean_le_zero_of_variance_order
    G J hf sites t ht hvar

end

end StatMech.Ising
