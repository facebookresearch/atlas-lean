/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.OSSS.FKSharpnessWeightedCoherentLimit
import Code.FK.InfiniteFiniteEnergy
import Code.Percolation.GridBoxConnected

open MeasureTheory
open Set

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedPhaseTransport

open Lattice FK Percolation
open FKSharpnessWeightedPeriodic
open FKSharpnessWeightedInfiniteVolume

variable {d : Nat}







def HasBoxFiniteEnergy
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  forall n, mu.map (forceOpenFinset (boxEdges d n)) ≪ mu

theorem HasFiniteEnergyMerge.hasBoxFiniteEnergy
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hfe : HasFiniteEnergyMerge mu) : HasBoxFiniteEnergy mu :=
  fun n => hfe (boxEdges d n)



theorem clusterInfiniteEvent_subset_forceOpen_preimage
    (F : Finset (Sym2 (Site d))) (x y : Site d)
    (hconn : forall omega, Connected d (forceOpenFinset F omega) x y) :
    clusterInfiniteEvent d x <=
      forceOpenFinset F ⁻¹' clusterInfiniteEvent d y := by
  intro omega hx
  change (cluster d (forceOpenFinset F omega) y).Infinite
  have hx' : (cluster d (forceOpenFinset F omega) x).Infinite :=
    hx.mono (cluster_mono (forceOpenFinset_le F omega) x)
  rwa [cluster_eq_of_connected (hconn omega)] at hx'



theorem clusterInfiniteEvent_measure_pos_of_connector
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (F : Finset (Sym2 (Site d))) (x y : Site d)
    (hfe : mu.map (forceOpenFinset F) ≪ mu)
    (hconn : forall omega, Connected d (forceOpenFinset F omega) x y)
    (hx : 0 < mu (clusterInfiniteEvent d x)) :
    0 < mu (clusterInfiniteEvent d y) := by
  by_contra hy
  have hy0 : mu (clusterInfiniteEvent d y) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hy)
  have hmap0 :
      (mu.map (forceOpenFinset F)) (clusterInfiniteEvent d y) = 0 :=
    hfe hy0
  have hpre0 :
      mu (forceOpenFinset F ⁻¹' clusterInfiniteEvent d y) = 0 := by
    rw [← Measure.map_apply (measurable_forceOpenFinset F)
      (measurableSet_clusterInfiniteEvent y)]
    exact hmap0
  have hle : mu (clusterInfiniteEvent d x) <=
      mu (forceOpenFinset F ⁻¹' clusterInfiniteEvent d y) :=
    measure_mono
      (clusterInfiniteEvent_subset_forceOpen_preimage F x y hconn)
  rw [hpre0] at hle
  exact (not_lt_of_ge hle) hx




theorem clusterInfiniteEvent_measure_pos_iff
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hfe : HasBoxFiniteEnergy mu) (x y : Site d) :
    0 < mu (clusterInfiniteEvent d x) <->
      0 < mu (clusterInfiniteEvent d y) := by
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y} : Set (Site d))
    ((Set.finite_singleton y).insert x)
  have hxbox : x ∈ box d n := hn (Set.mem_insert x {y})
  have hybox : y ∈ box d n := hn (Set.mem_insert_of_mem x (Set.mem_singleton y))
  have hxy : forall omega,
      Connected d (forceOpenFinset (boxEdges d n) omega) x y :=
    fun omega => box_allOpen_connected omega hxbox hybox
  constructor
  · exact clusterInfiniteEvent_measure_pos_of_connector mu
      (boxEdges d n) x y (hfe n) hxy
  · exact clusterInfiniteEvent_measure_pos_of_connector mu
      (boxEdges d n) y x (hfe n) (fun omega => (hxy omega).symm)


theorem clusterInfiniteEvent_real_pos_iff
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure mu]
    (hfe : HasBoxFiniteEnergy mu) (x y : Site d) :
    0 < mu.real (clusterInfiniteEvent d x) <->
      0 < mu.real (clusterInfiniteEvent d y) := by
  have hxtop : mu (clusterInfiniteEvent d x) ≠ ⊤ := measure_ne_top mu _
  have hytop : mu (clusterInfiniteEvent d y) ≠ ⊤ := measure_ne_top mu _
  constructor
  · intro hx
    have hx0 : mu (clusterInfiniteEvent d x) ≠ 0 := by
      intro hz
      rw [Measure.real, hz] at hx
      simp at hx
    have hy := (clusterInfiniteEvent_measure_pos_iff mu hfe x y).mp
      (bot_lt_iff_ne_bot.mpr hx0)
    exact ENNReal.toReal_pos hy.ne' hytop
  · intro hy
    have hy0 : mu (clusterInfiniteEvent d y) ≠ 0 := by
      intro hz
      rw [Measure.real, hz] at hy
      simp at hy
    have hx := (clusterInfiniteEvent_measure_pos_iff mu hfe x y).mpr
      (bot_lt_iff_ne_bot.mpr hy0)
    exact ENNReal.toReal_pos hx.ne' hxtop





theorem shift_mem_clusterInfiniteEvent_iff
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    ConfigSpace.shift g omega ∈ clusterInfiniteEvent d (g • x) <->
      omega ∈ clusterInfiniteEvent d x := by
  change (cluster d (ConfigSpace.shift g omega) (g • x)).Infinite <->
    (cluster d omega x).Infinite
  rw [cluster_shift]
  exact Set.infinite_image_iff
    (Set.injOn_of_injective (smul_injective g))


theorem shift_preimage_clusterInfiniteEvent
    (g : Multiplicative (Site d)) (x : Site d) :
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
      ConfigSpace (Sym2 (Site d))) ⁻¹'
        clusterInfiniteEvent d (g • x) =
      clusterInfiniteEvent d x := by
  ext omega
  exact shift_mem_clusterInfiniteEvent_iff g omega x











def CovariantWeightedPhaseCoherentFiniteEnergy
    (d : Nat) {P : Type*}
    (phase : Site d -> P)
    (mu : P -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  (forall x y,
    (mu (phase y) : Measure (ConfigSpace (Sym2 (Site d)))) =
      (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y)) :
          ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d)))) ∧
  (forall a, HasBoxFiniteEnergy
    (mu a : Measure (ConfigSpace (Sym2 (Site d)))))



theorem phasePositivityTransport_of_coherentFiniteEnergy
    {P : Type*} (phase : Site d -> P)
    (hsurj : Function.Surjective phase)
    (mu : P -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hcoh : CovariantWeightedPhaseCoherentFiniteEnergy d phase mu) :
    WeightedPhasePositivityTransport
      (fun a _ => (((mu a : ProbabilityMeasure _) : Measure _).real
        (percolationEvent d))) := by
  intro a b beta
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (x - y)
  have hmeasure :
      (mu (phase y) : Measure (ConfigSpace (Sym2 (Site d)))) =
        (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).map
          (ConfigSpace.shift g) := by
    simpa [g] using hcoh.1 x y
  have hbase := clusterInfiniteEvent_real_pos_iff
    (((mu (phase x) : ProbabilityMeasure _) : Measure _))
    (hcoh.2 (phase x))
    ((g⁻¹ : Multiplicative (Site d)) • origin d) (origin d)
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
        ConfigSpace (Sym2 (Site d))) ⁻¹' percolationEvent d =
      clusterInfiniteEvent d ((g⁻¹ : Multiplicative (Site d)) • origin d) := by
    have hs := shift_preimage_clusterInfiniteEvent
      (d := d) g ((g⁻¹ : Multiplicative (Site d)) • origin d)
    simpa [percolationEvent] using hs
  change 0 < (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).real
      (percolationEvent d) <->
    0 < (mu (phase y) : Measure (ConfigSpace (Sym2 (Site d)))).real
      (percolationEvent d)
  have hmapreal :
      ((mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).map
        (ConfigSpace.shift g)).real (percolationEvent d) =
      (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (clusterInfiniteEvent d ((g⁻¹ : Multiplicative (Site d)) • origin d)) := by
    have hperco : MeasurableSet (percolationEvent d) := by
      simpa [percolationEvent, clusterInfiniteEvent] using
        (measurableSet_clusterInfiniteEvent (d := d) (origin d))
    rw [Measure.real, Measure.real,
      Measure.map_apply (ConfigSpace.measurable_shift g)
        hperco, hpre]
  rw [hmeasure, hmapreal]
  simpa [percolationEvent, clusterInfiniteEvent] using hbase.symm



def CovariantWeightedSelectedPhaseLaws
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (q : Real) (hq : 0 < q) : Prop :=
  forall beta (hbeta : 0 < beta),
    CovariantWeightedPhaseCoherentFiniteEnergy d phase
      (fun a => weightedPhaseInfiniteVolume d phaseJ a (hJ a)
        q beta hq hbeta)


def CovariantWeightedSelectedPhaseTranslation
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (q : Real) (hq : 0 < q) : Prop :=
  forall beta (hbeta : 0 < beta) x y,
    (weightedPhaseInfiniteVolume d phaseJ (phase y) (hJ (phase y))
        q beta hq hbeta : Measure (ConfigSpace (Sym2 (Site d)))) =
      (weightedPhaseInfiniteVolume d phaseJ (phase x) (hJ (phase x))
          q beta hq hbeta : Measure (ConfigSpace (Sym2 (Site d)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y)))





def WeightedSelectedPhaseFiniteEnergy
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q : Real) (hq : 0 < q) : Prop :=
  forall beta (hbeta : 0 < beta) a,
    HasBoxFiniteEnergy
      (weightedPhaseInfiniteVolume d phaseJ a (hJ a)
        q beta hq hbeta : Measure (ConfigSpace (Sym2 (Site d))))

theorem covariantWeightedSelectedPhaseLaws_iff
    {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (q : Real) (hq : 0 < q) :
    CovariantWeightedSelectedPhaseLaws d phaseJ hJ phase q hq <->
      CovariantWeightedSelectedPhaseTranslation d phaseJ hJ phase q hq ∧
        WeightedSelectedPhaseFiniteEnergy d phaseJ hJ q hq := by
  constructor
  · intro h
    exact ⟨fun beta hbeta => (h beta hbeta).1,
      fun beta hbeta => (h beta hbeta).2⟩
  · rintro ⟨htrans, hfe⟩ beta hbeta
    exact ⟨htrans beta hbeta, hfe beta hbeta⟩



theorem covariantWeightedPhasePositivityTransport_of_selectedLaws
    {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (phase : Site d -> P) (hsurj : Function.Surjective phase)
    (q : Real) (hq : 0 < q)
    (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ hJ phase q hq) :
    WeightedPhasePositivityTransport
      (weightedPhaseThetaProfile d phaseJ hJ q hq) := by
  intro a b beta
  unfold weightedPhaseThetaProfile
  split_ifs with hbeta
  · exact phasePositivityTransport_of_coherentFiniteEnergy phase hsurj
      (fun c => weightedPhaseInfiniteVolume d phaseJ c (hJ c)
        q beta hq hbeta)
      (hlaws beta hbeta) a b beta
  · simp



theorem covariantWeightedPhasePositivityTransport_of_selectedLaws'
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q)
    (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) phase q hq) :
    CovariantWeightedPhasePositivityTransport
      d J phase phaseJ hJ hsurj hcov q hq := by
  exact covariantWeightedPhasePositivityTransport_of_selectedLaws
    phaseJ (hcov.phaseCoupling_pos hsurj hJ) phase hsurj q hq hlaws


theorem covariant_weighted_phase_common_critical_of_selectedLaws
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 0 < q)
    (hlaws : CovariantWeightedSelectedPhaseLaws d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) phase q hq)
    (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj hJ) q hq b beta) = 0} =
      sSup {beta | weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj hJ) q hq a beta = 0} := by
  apply covariant_weighted_phase_common_critical
    d J phase phaseJ hJ hsurj hcov q hq
  exact covariantWeightedPhasePositivityTransport_of_selectedLaws'
    J phase phaseJ hJ hsurj hcov q hq hlaws

end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
