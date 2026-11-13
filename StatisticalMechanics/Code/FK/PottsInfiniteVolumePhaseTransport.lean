/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FK.PottsInfiniteVolume
import Code.FK.EdwardsSokalWiredCorrelation
import Code.IsingFK.PcUpperAllDimensions
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section


def pottsColorEvent (d q : Nat) (x : Site d) (b : Fin q) :
    Set (PottsConfig d q) :=
  {sigma | sigma x = b}

theorem pottsColorEvent_isClopen (d q : Nat) (x : Site d) (b : Fin q) :
    IsClopen (pottsColorEvent d q x b) := by
  change IsClopen ((fun sigma : PottsConfig d q => sigma x) ⁻¹' {b})
  exact IsClopen.preimage (isClopen_discrete _)
    (continuous_apply x : Continuous
      (fun sigma : PottsConfig d q => sigma x))



theorem wiredPottsFiniteMeasure_real_pottsColorEvent_origin
    (d n q : Nat) [NeZero q] (b : Fin q) (beta J : Real) :
    ((wiredPottsFiniteMeasure d n q b beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) b) =
      pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n)
        q b beta J (boxOrigin d n) := by
  classical
  let E : Set (boxVerts d n -> Fin q) :=
    {sigma | sigma (boxOrigin d n) = b}
  have hpre : ivp_extendSpin d n q ⁻¹'
      pottsColorEvent d q (origin d) b = E := by
    ext sigma
    simp only [Set.mem_preimage, pottsColorEvent, Set.mem_setOf_eq, E]
    unfold ivp_extendSpin
    rw [dif_pos (origin_mem_box_boxVerts d n)]
    rfl
  have hmeas : MeasurableSet (pottsColorEvent d q (origin d) b) :=
    (pottsColorEvent_isClopen d q (origin d) b).2.measurableSet
  change ((Measure.map (ivp_extendSpin d n q)
    (wiredPottsPMF (boxGraph d n) (boxBoundary d n)
      q b beta J).toMeasure) (pottsColorEvent d q (origin d) b)).toReal = _
  rw [Measure.map_apply (ivp_measurable_extendSpin d n q) hmeas, hpre]
  unfold wiredPottsPMF pottsBoundaryProbWired
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun sigma _ => ?_)]
  · apply Finset.sum_congr rfl
    intro sigma _
    by_cases hsigma : sigma (boxOrigin d n) = b
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal
          (pottsProbWired_nonneg (boxGraph d n) (boxBoundary d n)
            q b beta J sigma)]
      simp [hsigma]
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp [hsigma]
  · by_cases hsigma : sigma (boxOrigin d n) = b
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp



theorem wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection
    (d n q : Nat) [NeZero q] (hd : 1 <= d) (hn : 1 <= n)
    (hq : 2 <= q) (b : Fin q) (beta J : Real)
    (hbeta : 0 < beta) (hJ : 0 < J) :
    ((wiredPottsFiniteMeasure d n q b beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real
          (pottsColorEvent d q (origin d) b) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        ((wiredFiniteMeasure d n
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d n) := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hq0 : (0 : Real) < q := by
    exact_mod_cast (show 0 < q by omega)
  obtain ⟨v0, hv0⟩ := boxBoundary_nonempty d n hd hn
  rw [wiredPottsFiniteMeasure_real_pottsColorEvent_origin]
  rw [pottsBoundaryProbWired_sub_inv_eq_conn
    (boxGraph d n) (boxBoundary d n) q b beta J
    (boxOrigin d n) v0 hv0]
  rw [wiredConnToBdryProbQ_eq_wiredFkProb_sum]
  let S : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (boxOrigin d n)}
  have hmass := fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) n hp hp1 hq0 S
      (measurableSet_boxBdryConnEvent d n)
  have hsum :
      (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 (boxVerts d n)) =>
            ConnToBdry (boxGraph d n) (boxBoundary d n) omega
              (boxOrigin d n)),
        wiredFkProb (boxGraph d n) (boxBoundary d n) p (q : Real) omega) =
      ∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
        S.indicator (fun _ => (1 : Real)) omega *
          wiredFkProb (boxGraph d n) (boxBoundary d n) p (q : Real) omega := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : ConnToBdry (boxGraph d n) (boxBoundary d n) omega
        (boxOrigin d n)
    · have hmem : omega ∈ S := homega
      simp [homega, Set.indicator_of_mem hmem]
    · have hmem : omega ∉ S := homega
      simp [homega, Set.indicator_of_notMem hmem]
  rw [hsum, <- hmass]
  rfl



theorem wiredPottsLimit_colorBias_eq_fkTheta
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (b : Fin q) (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat)
    (hphi : StrictMono phi)
    (hmu : Tendsto
      (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
      atTop (nhds mu)) :
    ((mu : Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) b)) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        fkTheta d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
          (q := q) := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hq1 : (1 : Real) <= q := by exact_mod_cast (show 1 <= q by omega)
  have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq1
  let A := pottsColorEvent d q (origin d) b
  have hA : IsClopen A := pottsColorEvent_isClopen d q (origin d) b
  have hcolorNN :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hmu hA
  have hcolor : Tendsto
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A)
      atTop (nhds ((mu : Measure _).real A)) := by
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hcolorNN
  have hconn := (fkgq_boxBdryConnEvent_diag_tendsto
    (d := d) hp hp1 hq1).comp hphi.tendsto_atTop
  have heq : ∀ᶠ n : Nat in atTop,
      ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A -
          1 / (q : Real) =
        ((q : Real) - 1) / q *
          ((wiredFiniteMeasure d (phi n) hp hp1 hq0 :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
              (boxBdryConnEvent d (phi n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [A, p] using
      wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection
        d (phi n) q hd (le_trans hn (hphi.id_le n)) hq b beta J hbeta hJ
  have hleft := hcolor.sub (tendsto_const_nhds :
    Tendsto (fun _ : Nat => 1 / (q : Real)) atTop (nhds (1 / (q : Real))))
  have hright := (tendsto_const_nhds : Tendsto
      (fun _ : Nat => ((q : Real) - 1) / q) atTop
        (nhds (((q : Real) - 1) / q))).mul hconn
  have heq' :
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A -
          1 / (q : Real)) =ᶠ[atTop]
      (fun n => ((q : Real) - 1) / q *
        ((wiredFiniteMeasure d (phi n) hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
            (boxBdryConnEvent d (phi n))) := heq
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.EventuallyEq.symm heq'))





theorem Potts.monoIndicator_relabel
    {V : Type*} {q : Nat} (e : Fin q ≃ Fin q)
    (sigma : V -> Fin q) (edge : Sym2 V) :
    Potts.monoIndicator (fun x => e (sigma x)) edge =
      Potts.monoIndicator sigma edge := by
  induction edge with
  | _ x y => simp [Potts.monoIndicator_mk]


theorem Potts.pottsProb_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : Nat} [NeZero q] (e : Fin q ≃ Fin q)
    (beta J : Real) (sigma : V -> Fin q) :
    Potts.pottsProb G q beta J (fun x => e (sigma x)) =
      Potts.pottsProb G q beta J sigma := by
  have hagreement : Potts.agreement G (fun x => e (sigma x)) =
      Potts.agreement G sigma := by
    unfold Potts.agreement
    apply Finset.sum_congr rfl
    intro edge _
    exact Potts.monoIndicator_relabel e sigma edge
  simp [Potts.pottsProb, Potts.pottsWeight, hagreement]



theorem pottsProbWired_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    {q : Nat} [NeZero q] (b : Fin q) (e : Fin q ≃ Fin q)
    (he : e b = b) (beta J : Real) (sigma : V -> Fin q) :
    pottsProbWired G bdry q b beta J (fun x => e (sigma x)) =
      pottsProbWired G bdry q b beta J sigma := by
  have hboundary : BoundaryFixed bdry b (fun x => e (sigma x)) ↔
      BoundaryFixed bdry b sigma := by
    constructor
    · intro h x hx
      apply e.injective
      calc
        e (sigma x) = b := h x hx
        _ = e b := he.symm
    · intro h x hx
      change e (sigma x) = b
      rw [h x hx, he]
  have hagreement : Potts.agreement G (fun x => e (sigma x)) =
      Potts.agreement G sigma := by
    unfold Potts.agreement
    apply Finset.sum_congr rfl
    intro edge _
    exact Potts.monoIndicator_relabel e sigma edge
  unfold pottsProbWired pottsWeightWired
  rw [if_congr hboundary rfl rfl]
  simp [Potts.pottsWeight, hagreement]


noncomputable def pottsColorProbWired
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (q : Nat) (b a : Fin q) (beta J : Real) (x : V) : Real :=
  ∑ sigma : V -> Fin q, pottsProbWired G bdry q b beta J sigma *
    (if sigma x = a then 1 else 0)

theorem pottsColorProbWired_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (q : Nat) (b : Fin q) (beta J : Real) (x : V) :
    pottsColorProbWired G bdry q b b beta J x =
      pottsBoundaryProbWired G bdry q b beta J x := rfl



theorem pottsColorProbWired_eq_of_ne_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (q : Nat) [NeZero q] (b a c : Fin q) (beta J : Real) (x : V)
    (ha : a ≠ b) (hc : c ≠ b) :
    pottsColorProbWired G bdry q b a beta J x =
      pottsColorProbWired G bdry q b c beta J x := by
  classical
  let e : Fin q ≃ Fin q := Equiv.swap a c
  have heb : e b = b := by
    exact Equiv.swap_apply_of_ne_of_ne ha.symm hc.symm
  let E : (V -> Fin q) ≃ (V -> Fin q) :=
    Equiv.piCongrRight (fun _ => e)
  unfold pottsColorProbWired
  calc
    (∑ sigma : V -> Fin q, pottsProbWired G bdry q b beta J sigma *
        (if sigma x = a then 1 else 0)) =
      ∑ sigma : V -> Fin q,
        pottsProbWired G bdry q b beta J (E sigma) *
          (if (E sigma) x = a then 1 else 0) := by
      symm
      exact E.sum_comp (fun sigma => pottsProbWired G bdry q b beta J sigma *
        (if sigma x = a then 1 else 0))
    _ = ∑ sigma : V -> Fin q, pottsProbWired G bdry q b beta J sigma *
        (if sigma x = c then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro sigma _
      change pottsProbWired G bdry q b beta J (fun y => e (sigma y)) *
          (if e (sigma x) = a then 1 else 0) =
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = c then 1 else 0)
      rw [pottsProbWired_relabel G bdry b e heb]
      have hiff : e (sigma x) = a ↔ sigma x = c := by
        dsimp [e]
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      by_cases hsigma : sigma x = c
      · rw [if_pos hsigma, if_pos (hiff.mpr hsigma)]
      · rw [if_neg hsigma, if_neg (fun h => hsigma (hiff.mp h))]


theorem sum_pottsColorProbWired
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (q : Nat) [NeZero q] (b : Fin q) (beta J : Real) (x : V) :
    ∑ a : Fin q, pottsColorProbWired G bdry q b a beta J x = 1 := by
  classical
  unfold pottsColorProbWired
  calc
    (∑ a : Fin q, ∑ sigma : V -> Fin q,
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = a then 1 else 0)) =
      ∑ sigma : V -> Fin q, ∑ a : Fin q,
        pottsProbWired G bdry q b beta J sigma *
          (if sigma x = a then 1 else 0) := by rw [Finset.sum_comm]
    _ = ∑ sigma : V -> Fin q,
        pottsProbWired G bdry q b beta J sigma := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [← Finset.mul_sum]
      simp
    _ = 1 := pottsProbWired_sum_eq_one G bdry q b beta J



theorem pottsColorProbWired_other_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (q : Nat) [NeZero q] (hq : 2 <= q) (b a : Fin q)
    (ha : a ≠ b) (beta J : Real) (x : V) :
    pottsColorProbWired G bdry q b a beta J x =
      (1 - pottsBoundaryProbWired G bdry q b beta J x) /
        ((q : Real) - 1) := by
  classical
  let P : Fin q -> Real := fun c =>
    pottsColorProbWired G bdry q b c beta J x
  have htotal : ∑ c : Fin q, P c = 1 :=
    sum_pottsColorProbWired G bdry q b beta J x
  have hsplit : ∑ c : Fin q, P c = P b + ∑ c ∈ Finset.univ.erase b, P c := by
    calc
      ∑ c : Fin q, P c = (∑ c ∈ Finset.univ.erase b, P c) + P b :=
        (Finset.sum_erase_add Finset.univ P (Finset.mem_univ b)).symm
      _ = P b + ∑ c ∈ Finset.univ.erase b, P c := add_comm _ _
  have hother : ∑ c ∈ Finset.univ.erase b, P c =
      ((q : Nat) - 1 : Nat) * P a := by
    calc
      ∑ c ∈ Finset.univ.erase b, P c =
          ∑ _c ∈ Finset.univ.erase b, P a := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcb : c ≠ b := Finset.ne_of_mem_erase hc
        exact pottsColorProbWired_eq_of_ne_boundary
          G bdry q b c a beta J x hcb ha
      _ = ((Finset.univ.erase b).card : Nat) * P a := by simp
      _ = ((q : Nat) - 1 : Nat) * P a := by simp
  have hlinear : P b + ((q : Real) - 1) * P a = 1 := by
    rw [hsplit, hother] at htotal
    have hqNat : 1 <= q := by omega
    rw [Nat.cast_sub hqNat] at htotal
    norm_num at htotal ⊢
    exact htotal
  have hden : (q : Real) - 1 ≠ 0 := by
    have : (1 : Real) < q := by exact_mod_cast hq
    linarith
  change P a = (1 - P b) / ((q : Real) - 1)
  rw [eq_div_iff hden]
  linarith



theorem wiredPottsFiniteMeasure_real_pottsColorEvent
    (d n q : Nat) [NeZero q] (b a : Fin q) (beta J : Real) :
    ((wiredPottsFiniteMeasure d n q b beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) a) =
      pottsColorProbWired (boxGraph d n) (boxBoundary d n)
        q b a beta J (boxOrigin d n) := by
  classical
  let E : Set (boxVerts d n -> Fin q) :=
    {sigma | sigma (boxOrigin d n) = a}
  have hpre : ivp_extendSpin d n q ⁻¹'
      pottsColorEvent d q (origin d) a = E := by
    ext sigma
    simp only [Set.mem_preimage, pottsColorEvent, Set.mem_setOf_eq, E]
    unfold ivp_extendSpin
    rw [dif_pos (origin_mem_box_boxVerts d n)]
    rfl
  have hmeas : MeasurableSet (pottsColorEvent d q (origin d) a) :=
    (pottsColorEvent_isClopen d q (origin d) a).2.measurableSet
  change ((Measure.map (ivp_extendSpin d n q)
    (wiredPottsPMF (boxGraph d n) (boxBoundary d n)
      q b beta J).toMeasure) (pottsColorEvent d q (origin d) a)).toReal = _
  rw [Measure.map_apply (ivp_measurable_extendSpin d n q) hmeas, hpre]
  unfold wiredPottsPMF pottsColorProbWired
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun sigma _ => ?_)]
  · apply Finset.sum_congr rfl
    intro sigma _
    by_cases hsigma : sigma (boxOrigin d n) = a
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal
          (pottsProbWired_nonneg (boxGraph d n) (boxBoundary d n)
            q b beta J sigma)]
      simp [hsigma]
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp [hsigma]
  · by_cases hsigma : sigma (boxOrigin d n) = a
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp



theorem wiredPottsLimit_otherColorBias_eq_fkTheta
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (b a : Fin q) (ha : a ≠ b)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat)
    (hphi : StrictMono phi)
    (hmu : Tendsto
      (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
      atTop (nhds mu)) :
    ((mu : Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) a)) - 1 / (q : Real) =
      -(1 / (q : Real)) *
        fkTheta d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
          (q := q) := by
  let A := pottsColorEvent d q (origin d) a
  let B := pottsColorEvent d q (origin d) b
  have hA : IsClopen A := pottsColorEvent_isClopen d q (origin d) a
  have hB : IsClopen B := pottsColorEvent_isClopen d q (origin d) b
  have hA_nn :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hmu hA
  have hB_nn :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hmu hB
  have hA_real : Tendsto
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A)
      atTop (nhds ((mu : Measure _).real A)) := by
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hA_nn
  have hB_real : Tendsto
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real B)
      atTop (nhds ((mu : Measure _).real B)) := by
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hB_nn
  have hfinite :
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A) =
      fun n => (1 - ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real B) /
          ((q : Real) - 1) := by
    funext n
    rw [wiredPottsFiniteMeasure_real_pottsColorEvent,
      wiredPottsFiniteMeasure_real_pottsColorEvent_origin]
    exact pottsColorProbWired_other_eq
      (boxGraph d (phi n)) (boxBoundary d (phi n)) q hq b a ha
        beta J (boxOrigin d (phi n))
  have hrelation : (mu : Measure (PottsConfig d q)).real A =
      (1 - (mu : Measure (PottsConfig d q)).real B) /
        ((q : Real) - 1) := by
    have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hright := (hone.sub hB_real).div_const ((q : Real) - 1)
    rw [hfinite] at hA_real
    exact tendsto_nhds_unique hA_real hright
  have hown := wiredPottsLimit_colorBias_eq_fkTheta
    d q hd hq b beta J hbeta hJ mu phi hphi hmu
  have hq0 : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hqm1 : (q : Real) - 1 ≠ 0 := by
    have hqR : (1 : Real) < q := by exact_mod_cast hq
    linarith
  dsimp [A, B] at hrelation ⊢
  field_simp [hq0, hqm1] at hrelation hown ⊢
  have hmul : ((q : Real) - 1) *
      ((mu : Measure (PottsConfig d q)).real
          (pottsColorEvent d q (origin d) a) * (q : Real) - 1 +
        fkTheta d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
          (q := q)) = 0 := by
    linear_combination (q : Real) * hrelation - hown
  have hzero := (mul_eq_zero.mp hmul).resolve_left hqm1
  linarith


theorem Potts.pottsColorProbability_eq_inv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Nat) [NeZero q] (beta J : Real) (x : V) (b : Fin q) :
    (∑ sigma : V -> Fin q, Potts.pottsProb G q beta J sigma *
        (if sigma x = b then 1 else 0)) = 1 / (q : Real) := by
  classical
  let mass : Fin q -> Real := fun a =>
    ∑ sigma : V -> Fin q, Potts.pottsProb G q beta J sigma *
      (if sigma x = a then 1 else 0)
  have hmass_eq : forall a : Fin q, mass a = mass b := by
    intro a
    let e : Fin q ≃ Fin q := Equiv.swap a b
    let E : (V -> Fin q) ≃ (V -> Fin q) :=
      Equiv.piCongrRight (fun _ => e)
    calc
      mass a = ∑ sigma : V -> Fin q,
          Potts.pottsProb G q beta J (E sigma) *
            (if (E sigma) x = a then 1 else 0) := by
        symm
        exact E.sum_comp (fun sigma => Potts.pottsProb G q beta J sigma *
          (if sigma x = a then 1 else 0))
      _ = mass b := by
        apply Finset.sum_congr rfl
        intro sigma _
        change Potts.pottsProb G q beta J (fun x => e (sigma x)) *
          (if e (sigma x) = a then 1 else 0) =
            Potts.pottsProb G q beta J sigma *
              (if sigma x = b then 1 else 0)
        rw [Potts.pottsProb_relabel G e]
        have hiff : e (sigma x) = a ↔ sigma x = b := by
          dsimp [e]
          rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        by_cases hsigma : sigma x = b
        · rw [if_pos hsigma, if_pos (hiff.mpr hsigma)]
        · rw [if_neg hsigma, if_neg (fun h => hsigma (hiff.mp h))]
  have htotal : ∑ a : Fin q, mass a = 1 := by
    calc
      ∑ a : Fin q, mass a =
          ∑ sigma : V -> Fin q, ∑ a : Fin q,
            Potts.pottsProb G q beta J sigma *
              (if sigma x = a then 1 else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ sigma : V -> Fin q, Potts.pottsProb G q beta J sigma := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [← Finset.mul_sum]
        simp
      _ = 1 := Potts.pottsProb_sum_eq_one G q beta J
  have hq0 : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hb : (q : Real) * mass b = 1 := by
    rw [← htotal]
    simp_rw [hmass_eq]
    simp
  change mass b = 1 / (q : Real)
  rw [eq_div_iff hq0]
  nlinarith


theorem freePottsFiniteMeasure_real_pottsColorEvent_origin
    (d n q : Nat) [NeZero q] (b : Fin q) (beta J : Real) :
    ((freePottsFiniteMeasure d n q beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) b) = 1 / (q : Real) := by
  classical
  let E : Set (boxVerts d n -> Fin q) :=
    {sigma | sigma (boxOrigin d n) = b}
  have hpre : ivp_extendSpin d n q ⁻¹'
      pottsColorEvent d q (origin d) b = E := by
    ext sigma
    simp only [Set.mem_preimage, pottsColorEvent, Set.mem_setOf_eq, E]
    unfold ivp_extendSpin
    rw [dif_pos (origin_mem_box_boxVerts d n)]
    rfl
  have hmeas : MeasurableSet (pottsColorEvent d q (origin d) b) :=
    (pottsColorEvent_isClopen d q (origin d) b).2.measurableSet
  change ((Measure.map (ivp_extendSpin d n q)
    (Potts.pottsPMF (boxGraph d n) q beta J).toMeasure)
      (pottsColorEvent d q (origin d) b)).toReal = _
  rw [Measure.map_apply (ivp_measurable_extendSpin d n q) hmeas, hpre]
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun sigma _ => ?_)]
  · rw [show (∑ sigma : boxVerts d n -> Fin q,
        (E.indicator (Potts.pottsPMF (boxGraph d n) q beta J) sigma).toReal) =
      ∑ sigma : boxVerts d n -> Fin q,
        Potts.pottsProb (boxGraph d n) q beta J sigma *
          (if sigma (boxOrigin d n) = b then 1 else 0) by
      apply Finset.sum_congr rfl
      intro sigma _
      by_cases hsigma : sigma (boxOrigin d n) = b
      · have hmem : sigma ∈ E := hsigma
        rw [Set.indicator_of_mem hmem, Potts.pottsPMF_apply,
          ENNReal.toReal_ofReal
            (Potts.pottsProb_nonneg (boxGraph d n) q beta J sigma)]
        simp [hsigma]
      · have hmem : sigma ∉ E := hsigma
        rw [Set.indicator_of_notMem hmem]
        simp [hsigma]]
    exact Potts.pottsColorProbability_eq_inv
      (boxGraph d n) q beta J (boxOrigin d n) b
  · by_cases hsigma : sigma (boxOrigin d n) = b
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, Potts.pottsPMF_apply]
      exact ENNReal.ofReal_ne_top
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp


theorem freePottsLimit_colorProbability_eq_inv
    (d q : Nat) [NeZero q] (b : Fin q) (beta J : Real)
    (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat)
    (hmu : Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
      atTop (nhds mu)) :
    (mu : Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) b) = 1 / (q : Real) := by
  let A := pottsColorEvent d q (origin d) b
  have hA : IsClopen A := pottsColorEvent_isClopen d q (origin d) b
  have hcolorNN :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hmu hA
  have hcolor : Tendsto
      (fun n => ((freePottsFiniteMeasure d (phi n) q beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A)
      atTop (nhds ((mu : Measure _).real A)) := by
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hcolorNN
  have hconst : Tendsto (fun _ : Nat => 1 / (q : Real)) atTop
      (nhds (1 / (q : Real))) := tendsto_const_nhds
  have heq : (fun n => ((freePottsFiniteMeasure d (phi n) q beta J :
      ProbabilityMeasure (PottsConfig d q)) : Measure _).real A) =
      fun _ => 1 / (q : Real) := by
    funext n
    exact freePottsFiniteMeasure_real_pottsColorEvent_origin
      d (phi n) q b beta J
  rw [heq] at hcolor
  exact tendsto_nhds_unique hcolor hconst



theorem freePottsLimit_ne_wiredPottsLimit_of_fkTheta_pos
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (b : Fin q) (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (muFree muWired : ProbabilityMeasure (PottsConfig d q))
    (phiFree phiWired : Nat -> Nat) (hphiWired : StrictMono phiWired)
    (hmuFree : Tendsto
      (fun n => freePottsFiniteMeasure d (phiFree n) q beta J)
      atTop (nhds muFree))
    (hmuWired : Tendsto
      (fun n => wiredPottsFiniteMeasure d (phiWired n) q b beta J)
      atTop (nhds muWired))
    (htheta : 0 < fkTheta d
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        exact neg_neg_of_pos (mul_pos hbeta hJ))
      (by linarith [Real.exp_pos (-(beta * J))])
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
      (q := q)) :
    muFree ≠ muWired := by
  have hfree := freePottsLimit_colorProbability_eq_inv
    d q b beta J muFree phiFree hmuFree
  have hwired := wiredPottsLimit_colorBias_eq_fkTheta
    d q hd hq b beta J hbeta hJ muWired phiWired hphiWired hmuWired
  have hcoef : 0 < ((q : Real) - 1) / q := by
    have hqR : (1 : Real) < q := by exact_mod_cast hq
    positivity
  intro heq
  subst muWired
  rw [hfree] at hwired
  have hpos := mul_pos hcoef htheta
  linarith



theorem wiredPottsLimits_ne_of_boundary_ne_of_fkTheta_pos
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (b c : Fin q) (hbc : b ≠ c)
    (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (muB muC : ProbabilityMeasure (PottsConfig d q))
    (phiB phiC : Nat -> Nat) (hphiB : StrictMono phiB)
    (hphiC : StrictMono phiC)
    (hmuB : Tendsto
      (fun n => wiredPottsFiniteMeasure d (phiB n) q b beta J)
      atTop (nhds muB))
    (hmuC : Tendsto
      (fun n => wiredPottsFiniteMeasure d (phiC n) q c beta J)
      atTop (nhds muC))
    (htheta : 0 < fkTheta d
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        exact neg_neg_of_pos (mul_pos hbeta hJ))
      (by linarith [Real.exp_pos (-(beta * J))])
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
      (q := q)) :
    muB ≠ muC := by
  have hown := wiredPottsLimit_colorBias_eq_fkTheta
    d q hd hq b beta J hbeta hJ muB phiB hphiB hmuB
  have hother := wiredPottsLimit_otherColorBias_eq_fkTheta
    d q hd hq c b hbc beta J hbeta hJ muC phiC hphiC hmuC
  intro heq
  subst muC
  have hq0 : (q : Real) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp [hq0] at hown hother
  have hqm1 : 0 < (q : Real) - 1 := by
    have : (1 : Real) < q := by exact_mod_cast hq
    linarith
  have hpos := mul_pos hqm1 htheta
  linarith



theorem wiredPottsOrderedInfiniteVolume_exists
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (b : Fin q) (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q))
      (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat),
      StrictMono phi ∧
      Tendsto (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J
          (by
            apply sub_nonneg.mpr
            rw [Real.exp_le_one_iff]
            exact neg_nonpos.mpr (mul_pos hbeta hJ).le))
        atTop (nhds Xi) ∧
      Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
        atTop (nhds mu) ∧
      Xi.map continuous_fst.measurable.aemeasurable = mu ∧
      Xi.map continuous_snd.measurable.aemeasurable =
        wiredInfiniteVolume d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) ∧
      (mu : Measure (PottsConfig d q)).real
          (pottsColorEvent d q (origin d) b) - 1 / (q : Real) =
        ((q : Real) - 1) / q *
          fkTheta d
            (by
              apply sub_pos.mpr
              rw [Real.exp_lt_one_iff]
              exact neg_neg_of_pos (mul_pos hbeta hJ))
            (by linarith [Real.exp_pos (-(beta * J))])
            (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
            (q := q) := by
  obtain ⟨Xi, mu, phi, hphi, hjoint, hspin, hfst, hsnd⟩ :=
    wiredPottsInfiniteVolume_exists d q hd hq b beta J hbeta hJ
  exact ⟨Xi, mu, phi, hphi, hjoint, hspin, hfst, hsnd,
    wiredPottsLimit_colorBias_eq_fkTheta
      d q hd hq b beta J hbeta hJ mu phi hphi hspin⟩

end

end StatMech.FK
