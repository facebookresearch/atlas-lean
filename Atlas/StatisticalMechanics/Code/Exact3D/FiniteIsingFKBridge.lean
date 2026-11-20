/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKTwoPointQ2Bridge
import Code.FK.EsCorrelations
import Code.FK.ThetaZeroBelowPc
import Code.IsingFK.Q2
import Code.Ising.TransitionFK










open scoped BigOperators
open Filter
open MeasureTheory

namespace StatMech
namespace Exact3D

open FK



noncomputable def finiteIsingXAxisTwoPointBox (β : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : ConfigSpace (boxVerts 3 n),
    Ising.isingProb (boxGraph 3 n) β 0 σ *
      (Ising.spin σ (ising3DOriginBoxVertex n) *
        Ising.spin σ (ising3DXAxisBoxVertex n))



noncomputable def finiteIsingXAxisTwoPointInBox
    (β : ℝ) (N n : ℕ) (hn : n ≤ N) : ℝ :=
  ∑ σ : ConfigSpace (boxVerts 3 N),
    Ising.isingProb (boxGraph 3 N) β 0 σ *
      (Ising.spin σ (ising3DOriginBoxVertex N) *
        Ising.spin σ (ising3DXAxisBoxVertexInBox N n hn))



noncomputable def finiteIsingXAxisTwoPointInVolume
    (β : ℝ) (N n : ℕ) : ℝ :=
  if hn : n ≤ N then
    finiteIsingXAxisTwoPointInBox β N n hn
  else
    0

theorem finiteIsingXAxisTwoPointInVolume_eq_of_le
    {β : ℝ} {N n : ℕ} (hn : n ≤ N) :
    finiteIsingXAxisTwoPointInVolume β N n =
      finiteIsingXAxisTwoPointInBox β N n hn := by
  simp [finiteIsingXAxisTwoPointInVolume, hn]



theorem finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2
    (d N : ℕ) (β : ℝ)
    (hp : 0 < IsingFK.pOfBeta β) (hp1 : IsingFK.pOfBeta β < 1)
    (x y : boxVerts d N) :
    (∑ σ : ConfigSpace (boxVerts d N),
        Ising.isingProb (boxGraph d N) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y)) =
      (freeFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y) := by
  have hspin : ∀ σ : boxVerts d N → Fin 2,
      Ising.spin (IsingFK.toIsing σ) x * Ising.spin (IsingFK.toIsing σ) y =
        isingSpin (σ x) * isingSpin (σ y) := by
    intro σ
    rw [← Ising.bond_mk]
    rw [IsingFK.bond_eq_two_mul_ite]
    rw [isingSpin_mul]
    by_cases h : σ x = σ y
    · rw [if_pos h, if_pos ((IsingFK.sigma_eq_iff σ x y).mp h)]
    · rw [if_neg h, if_neg (fun ht =>
        h ((IsingFK.sigma_eq_iff σ x y).mpr ht))]
  have hesFirst :
      (∑ σ : boxVerts d N → Fin 2,
          esFirstMarginal (boxGraph d N) 2 (IsingFK.pOfBeta β) σ *
            (isingSpin (σ x) * isingSpin (σ y))) =
        esTwoPoint (boxGraph d N) (IsingFK.pOfBeta β) x y := by
    unfold esFirstMarginal esTwoPoint
    simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
  rw [freeFiniteMeasure_real_boxConnEvent d N hp hp1
    (by norm_num : (0 : ℝ) < 2) x y]
  rw [← (Equiv.ofBijective (IsingFK.toIsing (V := boxVerts d N))
    IsingFK.toIsing_bijective).sum_comp
      (fun σ : ConfigSpace (boxVerts d N) =>
        Ising.isingProb (boxGraph d N) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y))]
  change (∑ σ : boxVerts d N → Fin 2,
      Ising.isingProb (boxGraph d N) β 0 (IsingFK.toIsing σ) *
        (Ising.spin (IsingFK.toIsing σ) x *
          Ising.spin (IsingFK.toIsing σ) y)) =
    twoPointFun (boxGraph d N) (IsingFK.pOfBeta β) 2 x y
  simp_rw [hspin]
  have hprob : ∀ σ : boxVerts d N → Fin 2,
      Ising.isingProb (boxGraph d N) β 0 (IsingFK.toIsing σ) =
        esFirstMarginal (boxGraph d N) 2 (IsingFK.pOfBeta β) σ := by
    intro σ
    rw [IsingFK.isingProb_eq_pottsProb
      (boxGraph d N) β (2 * β) 1 (by ring) σ]
    rw [← esFirstMarginal_eq_pottsProb (boxGraph d N) 2 (2 * β) 1 σ]
    simp [IsingFK.pOfBeta]
  simp_rw [hprob]
  rw [hesFirst, esTwoPoint_eq_connProb]
  simpa [connProb, Connected, connEvent] using
    (twoPointFun_eq_sum_filter
      (boxGraph d N) (IsingFK.pOfBeta β) (2 : ℝ) x y).symm



theorem finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
    (d N : ℕ) {β : ℝ} (hβ : 0 < β) (x y : boxVerts d N) :
    (∑ σ : ConfigSpace (boxVerts d N),
        Ising.isingProb (boxGraph d N) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y)) =
      (freeFiniteMeasure d N (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y) :=
  finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2
    d N β (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) x y



theorem finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2
    {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    finiteIsingXAxisTwoPointBox β n =
      freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n := by
  unfold finiteIsingXAxisTwoPointBox freeFiniteVolumeXAxisConnectionQ2
  exact finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
    3 n hβ (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)



theorem finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
    {β : ℝ} (hβ : 0 < β) (N n : ℕ) :
    finiteIsingXAxisTwoPointInVolume β N n =
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
  by_cases hn : n ≤ N
  · rw [finiteIsingXAxisTwoPointInVolume_eq_of_le hn]
    unfold freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
    rw [dif_pos hn]
    unfold finiteIsingXAxisTwoPointInBox
    exact finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
      3 N hβ (ising3DOriginBoxVertex N)
      (ising3DXAxisBoxVertexInBox N n hn)
  · simp [finiteIsingXAxisTwoPointInVolume,
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume, hn]



def FreeIsingXAxisThermodynamicLimitToFiniteVolumes (β : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    Tendsto (fun N => finiteIsingXAxisTwoPointInVolume β N n)
      atTop (nhds |freeTwoPointOnXAxis β n|)



def FreeFullVolumeQ2ThermodynamicLimitToIsing
    (β : ℝ) (hβ : 0 < β) : Prop :=
  ∀ᶠ n in atTop,
    Tendsto (fun N =>
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n)
      atTop (nhds |freeTwoPointOnXAxis β n|)



theorem freeFullVolumeQ2ThermodynamicLimitToIsing_of_finiteIsing
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
    FreeFullVolumeQ2ThermodynamicLimitToIsing β hβ := by
  filter_upwards [hIsing] with n hIsing_n
  exact Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun N =>
      finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
        hβ N n)
    hIsing_n




theorem freeInfiniteVolumeXAxisConnectionOfBetaQ2_le_freeTwoPoint_of_finiteIsing
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
    ∀ᶠ n in atTop,
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤
        |freeTwoPointOnXAxis β n| := by
  filter_upwards [hIsing] with n hIsing_n
  have hFK :=
    tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ n
  have hFull :
      Tendsto (fun N =>
        freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n)
        atTop (nhds |freeTwoPointOnXAxis β n|) := by
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N =>
        finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
          hβ N n)
      hIsing_n
  exact le_of_tendsto_of_tendsto hFK hFull
    (eventually_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_le_full β hβ n)




def FreeQ2FiniteVolumeBoundaryErrorBound
    (β : ℝ) (hβ : 0 < β) (B : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ N in atTop,
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n ≤ B n



noncomputable def freeQ2BoundaryProfileOfBeta
    (β : ℝ) (hβ : 0 < β) : ℕ → ℝ :=
  fun n =>
    IsingFK.boxBoundaryConnProfile 3
      (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2) n



theorem tendsto_freeQ2BoundaryProfileOfBeta
    (β : ℝ) (hβ : 0 < β) :
    Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop
      (nhds (fkTheta 3 (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2))) := by
  simpa [freeQ2BoundaryProfileOfBeta] using
    (boxBoundaryConnProfile_tendsto (d := 3)
      (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β))



theorem tendsto_freeQ2BoundaryProfileOfBeta_zero_of_fkTheta_eq_zero
    {β : ℝ} (hβ : 0 < β)
    (hθ :
      fkTheta 3 (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2) = 0) :
    Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) := by
  simpa [hθ] using tendsto_freeQ2BoundaryProfileOfBeta β hβ



theorem tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_lt_fkPc
    {β : ℝ} (hβ : 0 < β) (hpc : IsingFK.pOfBeta β < FK.fkPc 3 2) :
    Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) :=
  tendsto_freeQ2BoundaryProfileOfBeta_zero_of_fkTheta_eq_zero hβ
    (FK.tzp_fkTheta_eq_zero_of_lt_pc
      (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) hpc)



theorem tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_le_fkPc_of_pc
    (hθpc : ∀ (hp : 0 < FK.fkPc 3 2) (hp1 : FK.fkPc 3 2 < 1),
      FK.fkTheta 3 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    {β : ℝ} (hβ : 0 < β) (hpc : IsingFK.pOfBeta β ≤ FK.fkPc 3 2) :
    Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) :=
  tendsto_freeQ2BoundaryProfileOfBeta_zero_of_fkTheta_eq_zero hβ
    (FK.tzp_fkTheta_eq_zero_of_le_pc_of_pc hθpc
      (IsingFK.pOfBeta β) (Ising.pOfBeta_pos hβ)
      (Ising.pOfBeta_lt_one β) hpc)





theorem measureReal_boxBdryConnEvent_le_sum_boxConnEvent
    (d n : ℕ) (μ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) :
    μ.real (FK.boxBdryConnEvent d n)
      ≤ ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts d n => FK.boxBoundary d n v),
          μ.real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) := by
  rw [FK.boxBdryConnEvent_eq_iUnion]
  simpa using
    (measureReal_biUnion_finset_le
      (Finset.univ.filter (fun v : FK.boxVerts d n => FK.boxBoundary d n v))
      (fun v => FK.boxConnEvent d n (IsingFK.boxOrigin d n) v)
      (μ := μ))





theorem wiredFiniteMeasure_real_boxBdryConnEvent_le_sum_boxConnEvent
    (d n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxBdryConnEvent d n)
      ≤ ∑ v ∈ Finset.univ.filter
          (fun v : FK.boxVerts d n => FK.boxBoundary d n v),
          ((FK.wiredFiniteMeasure d n hp hp1
              (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
            (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) := by
  rw [FK.boxBdryConnEvent_eq_iUnion]
  simpa using
    (measureReal_biUnion_finset_le
      (Finset.univ.filter (fun v : FK.boxVerts d n => FK.boxBoundary d n v))
      (fun v => FK.boxConnEvent d n (IsingFK.boxOrigin d n) v))



theorem wiredFiniteMeasure_real_boxBdryConnEvent_le_card_mul_of_forall_boundary
    (d n : ℕ) {p B : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpoint : ∀ v : FK.boxVerts d n, FK.boxBoundary d n v →
      ((FK.wiredFiniteMeasure d n hp hp1
          (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) ≤ B) :
    ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxBdryConnEvent d n)
      ≤ ((Finset.univ.filter
          (fun v : FK.boxVerts d n => FK.boxBoundary d n v)).card : ℝ) * B := by
  calc
    ((FK.wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
        (FK.boxBdryConnEvent d n)
        ≤ ∑ v ∈ Finset.univ.filter
            (fun v : FK.boxVerts d n => FK.boxBoundary d n v),
            ((FK.wiredFiniteMeasure d n hp hp1
                (by norm_num : (0 : ℝ) < 2))
              : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
              (FK.boxConnEvent d n (IsingFK.boxOrigin d n) v) :=
      wiredFiniteMeasure_real_boxBdryConnEvent_le_sum_boxConnEvent d n hp hp1
    _ ≤ ∑ _v ∈ Finset.univ.filter
        (fun v : FK.boxVerts d n => FK.boxBoundary d n v), B := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact hpoint v (by simpa using hv)
    _ = ((Finset.univ.filter
        (fun v : FK.boxVerts d n => FK.boxBoundary d n v)).card : ℝ) * B := by
      simp [nsmul_eq_mul]



theorem freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary
    {β B : ℝ} (hβ : 0 < β) (n : ℕ)
    (hpoint : ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
      ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ B) :
    freeQ2BoundaryProfileOfBeta β hβ n
      ≤ ((Finset.univ.filter
          (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * B := by
  rw [freeQ2BoundaryProfileOfBeta]
  rw [FK.boxBoundaryConnProfile_eq_wiredFiniteMeasure_real]
  exact wiredFiniteMeasure_real_boxBdryConnEvent_le_card_mul_of_forall_boundary
    3 n (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) hpoint



theorem eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary
    {β : ℝ} (hβ : 0 < β) {B : ℕ → ℝ}
    (hpoint : ∀ᶠ n in atTop,
      ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
        ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
            (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ B n) :
    ∀ᶠ n in atTop,
      freeQ2BoundaryProfileOfBeta β hβ n
        ≤ ((Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) * B n := by
  filter_upwards [hpoint] with n hn
  exact freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβ n hn

set_option linter.style.longLine false in




theorem eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_exp_of_eventually_boundary
    {β mass : ℝ} (hβ : 0 < β) {A : ℕ → ℝ}
    (hpoint : ∀ᶠ n in atTop,
      ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
        ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
            (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤
          A n * Real.exp (-(mass * (n : ℝ)))) :
    ∀ᶠ n in atTop,
      freeQ2BoundaryProfileOfBeta β hβ n
        ≤ (((Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
              A n) * Real.exp (-(mass * (n : ℝ))) := by
  filter_upwards [hpoint] with n hn
  calc
    freeQ2BoundaryProfileOfBeta β hβ n
        ≤ ((Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
            (A n * Real.exp (-(mass * (n : ℝ)))) :=
      freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβ n hn
    _ = (((Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
              A n) * Real.exp (-(mass * (n : ℝ))) := by
      ring



theorem
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume_le_profile_of_le
    (β : ℝ) (hβ : 0 < β) {N n : ℕ} (hN : n ≤ N) :
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβ N n ≤
      freeQ2BoundaryProfileOfBeta β hβ n := by
  have hFreeLeWired :
      ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxBdryConnEvent 3 n) ≤
        ((wiredFiniteMeasure 3 N (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxBdryConnEvent 3 n) := by
    simpa using
      (freeFiniteMeasure_dominated 3 N
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (1 : ℝ) ≤ 2)
        (boxBdryConnEvent 3 n) (measurableSet_boxBdryConnEvent 3 n)
        (isIncreasing_boxBdryConnEvent 3 n))
  have hWiredLeDiag :
      ((wiredFiniteMeasure 3 N (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxBdryConnEvent 3 n) ≤
        ((wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxBdryConnEvent 3 n) := by
    have hanti :=
      radius_antitone (d := 3) n
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
    have hle := hanti (Nat.zero_le (N - n))
    have hN' : n + (N - n) = N := Nat.add_sub_of_le hN
    simpa [hN'] using hle
  have hProfile :=
    boxBoundaryConnProfile_eq_wiredFiniteMeasure_real 3 n
      (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
  unfold freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
  simpa [freeQ2BoundaryProfileOfBeta, hProfile] using
    hFreeLeWired.trans hWiredLeDiag





theorem freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile
    (β : ℝ) (hβ : 0 < β) :
    FreeQ2FiniteVolumeBoundaryErrorBound β hβ
      (freeQ2BoundaryProfileOfBeta β hβ) := by
  filter_upwards with n
  filter_upwards [eventually_ge_atTop n] with N hN
  exact
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume_le_profile_of_le
      β hβ hN





theorem freeQ2BoundaryErrorProfile_tendsto_zero_of_pOfBeta_lt_fkPc
    {β : ℝ} (hβ : 0 < β)
    (hpc : IsingFK.pOfBeta β < FK.fkPc 3 2) :
    FreeQ2FiniteVolumeBoundaryErrorBound β hβ
        (freeQ2BoundaryProfileOfBeta β hβ) ∧
      Tendsto (freeQ2BoundaryProfileOfBeta β hβ) atTop (nhds 0) :=
  ⟨freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile β hβ,
    tendsto_freeQ2BoundaryProfileOfBeta_zero_of_pOfBeta_lt_fkPc hβ hpc⟩



theorem freeTwoPoint_le_freeInfiniteVolumeXAxisConnectionOfBetaQ2_add_boundary
    {β : ℝ} (hβ : 0 < β) {B : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B) :
    ∀ᶠ n in atTop,
      |freeTwoPointOnXAxis β n| ≤
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n := by
  filter_upwards [hIsing, hBoundary, eventually_ge_atTop 1]
    with n hIsing_n hBoundary_n hnpos
  have hInner :=
    tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ n
  have hFull :
      Tendsto (fun N =>
        freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n)
        atTop (nhds |freeTwoPointOnXAxis β n|) := by
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun N =>
        finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
          hβ N n)
      hIsing_n
  have hBoundEvent :
      ∀ᶠ N in atTop,
        freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n ≤
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n + B n := by
    filter_upwards [eventually_ge_atTop n, hBoundary_n] with N hN hB
    have hDetour :
        freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤ B n :=
      (freeFiniteVolumeXAxisDetourOfBetaQ2InVolume_le_boundary_of_le
        β hβ hnpos hN).trans hB
    have hAdd :
        freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n +
            freeFiniteVolumeXAxisDetourOfBetaQ2InVolume β hβ N n ≤
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n + B n := by
      linarith
    exact
      (freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume_le_inner_add_detour_of_le
        β hβ hN).trans hAdd
  exact le_of_tendsto_of_tendsto hFull
    (hInner.add tendsto_const_nhds) hBoundEvent



theorem
    freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint
    {β : ℝ} (hβ : 0 < β) {B : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B) :
    ∀ᶠ n in atTop,
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤
          |freeTwoPointOnXAxis β n| ∧
        |freeTwoPointOnXAxis β n| ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n := by
  filter_upwards
    [freeInfiniteVolumeXAxisConnectionOfBetaQ2_le_freeTwoPoint_of_finiteIsing
      hβ hIsing,
    freeTwoPoint_le_freeInfiniteVolumeXAxisConnectionOfBetaQ2_add_boundary
      hβ hIsing hBoundary] with n hLower hUpper
  exact ⟨hLower, hUpper⟩



theorem
    freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint_profile
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β) :
    ∀ᶠ n in atTop,
      freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤
          |freeTwoPointOnXAxis β n| ∧
        |freeTwoPointOnXAxis β n| ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n +
            freeQ2BoundaryProfileOfBeta β hβ n :=
  freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint
    hβ hIsing
    (freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile β hβ)



theorem
    freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_additiveCompare
    {β mass : ℝ} (hβ : 0 < β) {B Alo Ahi : ℕ → ℝ}
    (hcompare :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n ≤
            |freeTwoPointOnXAxis β n| ∧
          |freeTwoPointOnXAxis β n| ≤
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
  refine ⟨hlo_pos, hhi_pos, hlo_log, hhi_log, ?_, ?_⟩
  · filter_upwards [hcompare, hlo] with n hcmp hn
    exact hn.trans hcmp.1
  · filter_upwards [hcompare, hhi] with n hcmp hn
    exact hcmp.2.trans hn



theorem
    freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundary
    {β mass : ℝ} (hβ : 0 < β) {B Alo Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass :=
  freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_additiveCompare
    hβ
    (freeInfiniteVolumeXAxisConnectionOfBetaQ2_additive_compare_freeTwoPoint
      hβ hIsing hBoundary)
    hlo_pos hhi_pos hlo_log hhi_log hlo hhi



theorem
    freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryProfile
    {β mass : ℝ} (hβ : 0 < β) {Alo Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n +
            freeQ2BoundaryProfileOfBeta β hβ n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass :=
  freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundary
    hβ hIsing
    (freeQ2FiniteVolumeBoundaryErrorBound_boxBoundaryConnProfile β hβ)
    hlo_pos hhi_pos hlo_log hhi_log hlo hhi




theorem
    freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_profileSeparate
    {β mass : ℝ} (hβ : 0 < β) {Alo AfkHi AprofHi Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hprofileHi :
      ∀ᶠ n in atTop,
        freeQ2BoundaryProfileOfBeta β hβ n ≤
          AprofHi n * Real.exp (-(mass * (n : ℝ))))
    (hcombine :
      ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n) :
    FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass := by
  refine
    freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryProfile
      hβ hIsing hconn.1 hhi_pos hconn.2.2.1 hhi_log hconn.2.2.2.2.1 ?_
  filter_upwards [hconn.2.2.2.2.2, hprofileHi, hcombine]
    with n hfkHi hprofHi hcombine_n
  calc
    freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n +
        freeQ2BoundaryProfileOfBeta β hβ n
        ≤ AfkHi n * Real.exp (-(mass * (n : ℝ))) +
            AprofHi n * Real.exp (-(mass * (n : ℝ))) :=
          add_le_add hfkHi hprofHi
    _ = (AfkHi n + AprofHi n) * Real.exp (-(mass * (n : ℝ))) := by
          ring
    _ ≤ Ahi n * Real.exp (-(mass * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hcombine_n
            (le_of_lt (Real.exp_pos _))

set_option linter.style.longLine false in



theorem
    freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryPointwise
    {β mass : ℝ} (hβ : 0 < β) {Alo AfkHi AbdryHi Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hboundaryPoint :
      ∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤
            AbdryHi n * Real.exp (-(mass * (n : ℝ))))
    (hcombine :
      ∀ᶠ n in atTop,
        AfkHi n +
            ((Finset.univ.filter
              (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
              AbdryHi n ≤
          Ahi n) :
    FreeXAxisTwoSidedSubexponentialBounds β Alo Ahi mass :=
  freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_profileSeparate
    hβ (AprofHi := fun n =>
      ((Finset.univ.filter
        (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
        AbdryHi n)
    hIsing hconn hhi_pos hhi_log
    (eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_exp_of_eventually_boundary
      hβ hboundaryPoint)
    hcombine




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary
    {β mass : ℝ} (hβ : 0 < β) {B Alo Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundary
      hβ hIsing hBoundary hlo_pos hhi_pos hlo_log hhi_log hlo hhi)



theorem free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary
    {β mass : ℝ} (hβ : 0 < β) (hmass : 0 < mass)
    {B Alo Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hBoundary : FreeQ2FiniteVolumeBoundaryErrorBound β hβ B)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n + B n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  HasInverseCorrelationLength.hasCorrelationLength_inv
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundary
      hβ hIsing hBoundary hlo_pos hhi_pos hlo_log hhi_log hlo hhi)
    hmass




theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile
    {β mass : ℝ} (hβ : 0 < β) {Alo Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n +
            freeQ2BoundaryProfileOfBeta β hβ n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryProfile
      hβ hIsing hlo_pos hhi_pos hlo_log hhi_log hlo hhi)



theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile
    {β mass : ℝ} (hβ : 0 < β) (hmass : 0 < mass) {Alo Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hlo_pos : ∀ᶠ n in atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hlo_log :
      Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        atTop (nhds 0))
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hlo :
      ∀ᶠ n in atTop,
        Alo n * Real.exp (-(mass * (n : ℝ))) ≤
          freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)
    (hhi :
      ∀ᶠ n in atTop,
        freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n +
            freeQ2BoundaryProfileOfBeta β hβ n ≤
          Ahi n * Real.exp (-(mass * (n : ℝ)))) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  HasInverseCorrelationLength.hasCorrelationLength_inv
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryProfile
      hβ hIsing hlo_pos hhi_pos hlo_log hhi_log hlo hhi)
    hmass



theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate
    {β mass : ℝ} (hβ : 0 < β) {Alo AfkHi AprofHi Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hprofileHi :
      ∀ᶠ n in atTop,
        freeQ2BoundaryProfileOfBeta β hβ n ≤
          AprofHi n * Real.exp (-(mass * (n : ℝ))))
    (hcombine :
      ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_profileSeparate
      hβ hIsing hconn hhi_pos hhi_log hprofileHi hcombine)



theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate
    {β mass : ℝ} (hβ : 0 < β) (hmass : 0 < mass)
    {Alo AfkHi AprofHi Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hprofileHi :
      ∀ᶠ n in atTop,
        freeQ2BoundaryProfileOfBeta β hβ n ≤
          AprofHi n * Real.exp (-(mass * (n : ℝ))))
    (hcombine :
      ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  HasInverseCorrelationLength.hasCorrelationLength_inv
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_profileSeparate
      hβ hIsing hconn hhi_pos hhi_log hprofileHi hcombine)
    hmass

set_option linter.style.longLine false in



theorem
    free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise
    {β mass : ℝ} (hβ : 0 < β) {Alo AfkHi AbdryHi Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hboundaryPoint :
      ∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤
            AbdryHi n * Real.exp (-(mass * (n : ℝ))))
    (hcombine :
      ∀ᶠ n in atTop,
        AfkHi n +
            ((Finset.univ.filter
              (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
              AbdryHi n ≤
          Ahi n) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass :=
  free_hasInverseCorrelationLength_xAxis_of_twoSidedSubexponentialBounds
    (freeXAxisTwoSidedSubexponentialBounds_of_freeInfiniteVolumeQ2_boundaryPointwise
      hβ hIsing hconn hhi_pos hhi_log hboundaryPoint hcombine)

set_option linter.style.longLine false in



theorem
    free_hasCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise
    {β mass : ℝ} (hβ : 0 < β) (hmass : 0 < mass)
    {Alo AfkHi AbdryHi Ahi : ℕ → ℝ}
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hconn :
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ) Alo AfkHi mass)
    (hhi_pos : ∀ᶠ n in atTop, 0 < Ahi n)
    (hhi_log :
      Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        atTop (nhds 0))
    (hboundaryPoint :
      ∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβ)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤
            AbdryHi n * Real.exp (-(mass * (n : ℝ))))
    (hcombine :
      ∀ᶠ n in atTop,
        AfkHi n +
            ((Finset.univ.filter
              (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
              AbdryHi n ≤
          Ahi n) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay mass⁻¹ :=
  HasInverseCorrelationLength.hasCorrelationLength_inv
    (free_hasInverseCorrelationLength_xAxis_of_freeInfiniteVolumeQ2_boundaryPointwise
      hβ hIsing hconn hhi_pos hhi_log hboundaryPoint hcombine)
    hmass







def FreeFiniteIsingFKXAxisRestrictedCylinderComparison
    (β : ℝ) (hβ : 0 < β) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ N in atTop,
    finiteIsingXAxisTwoPointInVolume β N n =
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ N n





theorem freeXAxisQ2ConnectionAgrees_of_finiteVolume_restrictedCylinderComparison
    {β : ℝ} (hβ : 0 < β)
    (hIsing : FreeIsingXAxisThermodynamicLimitToFiniteVolumes β)
    (hrestricted : FreeFiniteIsingFKXAxisRestrictedCylinderComparison β hβ) :
    FreeXAxisQ2ConnectionAgrees β hβ := by
  unfold FreeXAxisQ2ConnectionAgrees FreeXAxisFKConnectionAgrees
  filter_upwards [hIsing, hrestricted] with n hIsing_n hrestricted_n
  have hFK :=
    tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβ n
  have hIsing_to_fk :
      Tendsto (fun N => finiteIsingXAxisTwoPointInVolume β N n)
        atTop (nhds (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβ n)) := by
    exact Filter.Tendsto.congr' (hrestricted_n.mono fun _ h => h.symm) hFK
  exact tendsto_nhds_unique hIsing_n hIsing_to_fk




theorem fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing
    {β A m : ℝ} (hβ : 0 < β) :
    FKXAxisConnectionExactExponentialDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (finiteIsingXAxisTwoPointBox β) A m :=
  FKXAxisConnectionExactExponentialDecay.congr_eventually_iff <| by
    filter_upwards with n
    exact finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n



theorem fkXAxisConnectionExactExponentialDecay_finiteIsing_iff_freeFiniteVolumeQ2
    {β A m : ℝ} (hβ : 0 < β) :
    FKXAxisConnectionExactExponentialDecay
      (finiteIsingXAxisTwoPointBox β) A m ↔
    FKXAxisConnectionExactExponentialDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m :=
  (fkXAxisConnectionExactExponentialDecay_freeFiniteVolumeQ2_iff_finiteIsing
    hβ).symm




theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (finiteIsingXAxisTwoPointBox β) A m :=
  FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff <| by
    filter_upwards with n
    exact finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n



theorem
    fkXAxisConnectionSubexponentialPrefactorDecay_finiteIsing_iff_freeFiniteVolumeQ2
    {β m : ℝ} {A : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionSubexponentialPrefactorDecay
      (finiteIsingXAxisTwoPointBox β) A m ↔
    FKXAxisConnectionSubexponentialPrefactorDecay
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) A m :=
  (fkXAxisConnectionSubexponentialPrefactorDecay_freeFiniteVolumeQ2_iff_finiteIsing
    hβ).symm




theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (finiteIsingXAxisTwoPointBox β) Alo Ahi m :=
  FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff <| by
    filter_upwards with n
    exact finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2 hβ n



theorem
    fkXAxisConnectionTwoSidedSubexponentialBounds_finiteIsing_iff_freeFiniteVolumeQ2
    {β m : ℝ} {Alo Ahi : ℕ → ℝ} (hβ : 0 < β) :
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (finiteIsingXAxisTwoPointBox β) Alo Ahi m ↔
    FKXAxisConnectionTwoSidedSubexponentialBounds
      (freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)) Alo Ahi m :=
  (fkXAxisConnectionTwoSidedSubexponentialBounds_freeFiniteVolumeQ2_iff_finiteIsing
    hβ).symm

end Exact3D
end StatMech
