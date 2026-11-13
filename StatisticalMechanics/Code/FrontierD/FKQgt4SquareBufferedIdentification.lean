/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierD.FKQgt4OuterLeafDual
import Code.FrontierD.FKQgt4SquarePeriodicBridge
import Code.FK.FKGeneralQConsumer

open Finset Set MeasureTheory Filter Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar

noncomputable section



theorem fkSquarePeriodicConfigEquiv_boxRestrict (n : Nat)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    fkSquarePeriodicConfigEquiv (square.bufferedRadius n)
        (FK.boxRestrict 2 (square.bufferedRadius n) omega) =
      square.bufferedRestrict n omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem fkSquarePeriodicConfigEquiv_monotone (n : Nat) :
    Monotone (fkSquarePeriodicConfigEquiv n) := by
  intro omega eta home e
  exact home _



theorem fkSquarePeriodic_freeBufferedMeasure_eq (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    square.freeBufferedMeasure n hp hp1 hq =
      FK.freeFiniteMeasure 2 (square.bufferedRadius n) hp hp1 hq := by
  exact fkSquarePeriodic_freeFiniteMeasure_eq
    (square.bufferedRadius n) hp hp1 hq




theorem fkSquarePeriodic_bufferedBoundary_iff_orbitBoundary
    (n : Nat) (hr : 0 < square.bufferedRadius n)
    (x : square.BufferedVertex n) :
    square.bufferedBoundary n x ↔
      square.orbitBoundary (square.bufferedRadius n) x := by
  let r := square.bufferedRadius n
  have hr' : 0 < r := hr
  unfold PeriodicGraph.bufferedBoundary PeriodicGraph.orbitBoundary
  rw [fkSquarePeriodic_mem_orbitBox_iff]
  constructor
  · rintro ⟨w, hxw, hw⟩ hxinner
    apply hw
    rw [fkSquarePeriodic_mem_orbitBox_iff]
    change (hypercubicLattice 2).Adj x.1 w at hxw
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxw
    intro i
    fin_cases i
    · have hdiff : (x.1 0 - w 0).natAbs ≤ 1 := by omega
      calc
        (w 0).natAbs = ((w 0 - x.1 0) + x.1 0).natAbs := by ring_nf
        _ ≤ (w 0 - x.1 0).natAbs + (x.1 0).natAbs :=
          Int.natAbs_add_le _ _
        _ = (x.1 0 - w 0).natAbs + (x.1 0).natAbs := by
          rw [← Int.natAbs_neg, neg_sub]
        _ ≤ 1 + (r - 1) := Nat.add_le_add hdiff (hxinner 0)
        _ = r := by omega
    · have hdiff : (x.1 1 - w 1).natAbs ≤ 1 := by omega
      calc
        (w 1).natAbs = ((w 1 - x.1 1) + x.1 1).natAbs := by ring_nf
        _ ≤ (w 1 - x.1 1).natAbs + (x.1 1).natAbs :=
          Int.natAbs_add_le _ _
        _ = (x.1 1 - w 1).natAbs + (x.1 1).natAbs := by
          rw [← Int.natAbs_neg, neg_sub]
        _ ≤ 1 + (r - 1) := Nat.add_le_add hdiff (hxinner 1)
        _ = r := by omega
  · intro hxouter
    have hxbox : x.1 ∈ box 2 r := by
      exact (fkSquarePeriodic_mem_orbitBox_iff r x.1).mp x.2
    simp only [mem_box] at hxbox
    simp only [mem_box] at hxouter
    push Not at hxouter
    obtain ⟨i, hi⟩ := hxouter
    have habs : (x.1 i).natAbs = r := by
      exact le_antisymm (hxbox i) (by omega)
    fin_cases i
    · rcases Int.natAbs_eq_iff.mp habs with hpos | hneg
      · let w : Site 2 := fun j => if j = 0 then (r : Int) + 1 else x.1 j
        have hx0 : x.1 0 = (r : Int) := by simpa using hpos
        refine ⟨w, ?_, ?_⟩
        · change (hypercubicLattice 2).Adj x.1 w
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp [w, hx0]
        · rw [fkSquarePeriodic_mem_orbitBox_iff]
          intro hw
          have hw0 := hw 0
          change (((r : Int) + 1).natAbs ≤ r) at hw0
          have hnat : ((r : Int) + 1).natAbs = r + 1 := by
            rw [Int.natAbs_eq_iff]
            left
            push_cast
            ring
          rw [hnat] at hw0
          omega
      · let w : Site 2 := fun j => if j = 0 then -((r : Int) + 1) else x.1 j
        have hx0 : x.1 0 = -(r : Int) := by simpa using hneg
        refine ⟨w, ?_, ?_⟩
        · change (hypercubicLattice 2).Adj x.1 w
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp [w, hx0]
        · rw [fkSquarePeriodic_mem_orbitBox_iff]
          intro hw
          have hw0 := hw 0
          change ((-((r : Int) + 1)).natAbs ≤ r) at hw0
          have hnat : (-((r : Int) + 1)).natAbs = r + 1 := by
            rw [Int.natAbs_eq_iff]
            right
            push_cast
            ring
          rw [hnat] at hw0
          omega
    · rcases Int.natAbs_eq_iff.mp habs with hpos | hneg
      · let w : Site 2 := fun j => if j = 1 then (r : Int) + 1 else x.1 j
        have hx1 : x.1 1 = (r : Int) := by simpa using hpos
        refine ⟨w, ?_, ?_⟩
        · change (hypercubicLattice 2).Adj x.1 w
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp [w, hx1]
        · rw [fkSquarePeriodic_mem_orbitBox_iff]
          intro hw
          have hw1 := hw 1
          change (((r : Int) + 1).natAbs ≤ r) at hw1
          have hnat : ((r : Int) + 1).natAbs = r + 1 := by
            rw [Int.natAbs_eq_iff]
            left
            push_cast
            ring
          rw [hnat] at hw1
          omega
      · let w : Site 2 := fun j => if j = 1 then -((r : Int) + 1) else x.1 j
        have hx1 : x.1 1 = -(r : Int) := by simpa using hneg
        refine ⟨w, ?_, ?_⟩
        · change (hypercubicLattice 2).Adj x.1 w
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp [w, hx1]
        · rw [fkSquarePeriodic_mem_orbitBox_iff]
          intro hw
          have hw1 := hw 1
          change ((-((r : Int) + 1)).natAbs ≤ r) at hw1
          have hnat : (-((r : Int) + 1)).natAbs = r + 1 := by
            rw [Int.natAbs_eq_iff]
            right
            push_cast
            ring
          rw [hnat] at hw1
          omega


theorem fkSquarePeriodic_wiredBufferedMeasure_eq (n : Nat)
    (hr : 0 < square.bufferedRadius n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    square.wiredBufferedMeasure n hp hp1 hq =
      FK.wiredFiniteMeasure 2 (square.bufferedRadius n) hp hp1 hq := by
  have hpmf : square.wiredBufferedPMF n hp hp1 hq =
      square.wiredFinitePMF (square.bufferedRadius n) hp hp1 hq := by
    apply PMF.ext
    intro omega
    unfold PeriodicGraph.wiredBufferedPMF PeriodicGraph.bufferedGraph
      PeriodicGraph.wiredFinitePMF
    rw [FK.wiredFkPMF, FK.wiredFkPMF, PMF.ofFintype_apply,
      PMF.ofFintype_apply]
    have hprob := FK.fvs_wiredFkProb_reCfgIso
      (square.orbitGraph (square.bufferedRadius n))
      (square.orbitGraph (square.bufferedRadius n))
      (square.bufferedBoundary n)
      (square.orbitBoundary (square.bufferedRadius n))
      (Equiv.refl (square.BufferedVertex n))
      (by simp)
      (fun x => fkSquarePeriodic_bufferedBoundary_iff_orbitBoundary n hr x)
      p q omega
    have hre : FK.reCfgIso (Equiv.refl (square.BufferedVertex n)) omega = omega := by
      funext e
      induction e using Sym2.inductionOn with
      | _ x y => rfl
    rw [hre] at hprob
    exact congrArg ENNReal.ofReal hprob
  rw [← fkSquarePeriodic_wiredFiniteMeasure_eq
    (square.bufferedRadius n) hp hp1 hq]
  apply ProbabilityMeasure.toMeasure_injective
  unfold PeriodicGraph.wiredBufferedMeasure
    PeriodicGraph.wiredFiniteMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [hpmf]



theorem fkSquarePeriodic_bufferedCylinder_eq_boxCylinder (n : Nat)
    (S : Set (ConfigSpace (Sym2 (square.BufferedVertex n)))) :
    square.bufferedCylinder n S =
      FK.boxRestrict 2 (square.bufferedRadius n) ⁻¹'
        ((fkSquarePeriodicConfigEquiv (square.bufferedRadius n)) ⁻¹' S) := by
  ext omega
  simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage]
  rw [fkSquarePeriodicConfigEquiv_boxRestrict]



theorem fkSquarePeriodic_freeBufferedInfiniteVolume_real_cylinder
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) =
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) := by
  let r := square.bufferedRadius N
  let Sbox : Set (ConfigSpace (Sym2 (FK.boxVerts 2 r))) :=
    (fkSquarePeriodicConfigEquiv r) ⁻¹' S
  have hSbox : IsIncreasing Sbox := by
    intro omega eta home homega
    exact hS (fkSquarePeriodicConfigEquiv_monotone r home) homega
  have hbuffered := square.freeBufferedMeasure_tendsto_cylinder
    N hp hp1 hq hS
  rw [fkSquarePeriodic_bufferedCylinder_eq_boxCylinder] at hbuffered ⊢
  change Tendsto
      (fun m => (square.freeBufferedMeasure m hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxRestrict 2 r ⁻¹' Sbox)) atTop _ at hbuffered
  simp_rw [fkSquarePeriodic_freeBufferedMeasure_eq] at hbuffered
  have hcanonical := (FK.fkgq_free_infinite_measure r hp hp1 hq hSbox).comp
    square.bufferedRadius_strictMono.tendsto_atTop
  exact tendsto_nhds_unique hbuffered hcanonical



theorem fkSquarePeriodic_wiredBufferedInfiniteVolume_real_cylinder
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) =
      (FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) := by
  let r := square.bufferedRadius N
  let Sbox : Set (ConfigSpace (Sym2 (FK.boxVerts 2 r))) :=
    (fkSquarePeriodicConfigEquiv r) ⁻¹' S
  have hSbox : IsIncreasing Sbox := by
    intro omega eta home homega
    exact hS (fkSquarePeriodicConfigEquiv_monotone r home) homega
  have hbuffered := square.wiredBufferedMeasure_tendsto_cylinder
    N hp hp1 hq hS
  rw [fkSquarePeriodic_bufferedCylinder_eq_boxCylinder] at hbuffered ⊢
  change Tendsto
      (fun m => (square.wiredBufferedMeasure m hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxRestrict 2 r ⁻¹' Sbox)) atTop _ at hbuffered
  have hshift := hbuffered.comp (tendsto_add_atTop_nat 1)
  change Tendsto
      (fun m => (square.wiredBufferedMeasure (m + 1) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxRestrict 2 r ⁻¹' Sbox)) atTop _ at hshift
  have hpositive : ∀ m : Nat, 0 < square.bufferedRadius (m + 1) := by
    intro m
    have h := square.bufferedRadius_strictMono (Nat.zero_lt_succ m)
    simpa using h
  have hfun :
      (fun m => (square.wiredBufferedMeasure (m + 1) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxRestrict 2 r ⁻¹' Sbox)) =
      (fun m => (FK.wiredFiniteMeasure 2 (square.bufferedRadius (m + 1))
        hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site 2)))).real
            (FK.boxRestrict 2 r ⁻¹' Sbox)) := by
    funext m
    rw [fkSquarePeriodic_wiredBufferedMeasure_eq
      (m + 1) (hpositive m) hp hp1 (zero_lt_one.trans_le hq)]
  rw [hfun] at hshift
  have hradius : Tendsto (fun m => square.bufferedRadius (m + 1))
      atTop atTop :=
    square.bufferedRadius_strictMono.tendsto_atTop.comp
      (tendsto_add_atTop_nat 1)
  have hcanonical :=
    (FK.fkgq_wired_infinite_measure r hp hp1 hq hSbox).comp hradius
  exact tendsto_nhds_unique hshift hcanonical

private theorem probabilityMeasure_bufferedCylinder_real_eq_signedSum
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) (N : Nat)
    (S : Set (ConfigSpace (Sym2 (square.BufferedVertex N))))
    {I : Type*} (t : Finset I) (c : I → Real)
    (A : I → Set (ConfigSpace (Sym2 (square.BufferedVertex N))))
    (hexp : S.indicator
        (1 : ConfigSpace (Sym2 (square.BufferedVertex N)) → Real) =
      ∑ i ∈ t, c i • (A i).indicator 1) :
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (square.bufferedCylinder N S) =
      ∑ i ∈ t, c i *
        (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N (A i)) := by
  have hpoint : (square.bufferedCylinder N S).indicator
        (1 : ConfigSpace (Sym2 (Site 2)) → Real) =
      ∑ i ∈ t, c i •
        (square.bufferedCylinder N (A i)).indicator 1 := by
    funext omega
    have h := congrFun hexp (square.bufferedRestrict N omega)
    simpa only [PeriodicGraph.bufferedCylinder, Set.indicator_apply,
      Set.mem_preimage, Finset.sum_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul] using h
  calc
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
        (square.bufferedCylinder N S) =
        ∫ omega, (square.bufferedCylinder N S).indicator
          (fun _ => (1 : Real)) omega ∂mu := by
            rw [integral_indicator_const (1 : Real)
              (square.bufferedCylinder_measurableSet N S)]
            simp
    _ = ∫ omega, (∑ i ∈ t, c i •
          (square.bufferedCylinder N (A i)).indicator
            (1 : ConfigSpace (Sym2 (Site 2)) → Real)) omega ∂mu := by
          apply integral_congr_ae
          filter_upwards with omega
          simpa using congrFun hpoint omega
    _ = ∑ i ∈ t, c i *
          (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
            (square.bufferedCylinder N (A i)) := by
          simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [integral_const_mul]
            congr 1
            simpa using (integral_indicator_const
              (μ := (mu : Measure _)) (1 : Real)
              (square.bufferedCylinder_measurableSet N (A i)))
          · intro i hi
            exact ((integrable_const (1 : Real)).indicator
              (square.bufferedCylinder_measurableSet N (A i))).const_mul _



theorem fkSquarePeriodic_freeBufferedInfiniteVolume_real_allCylinder
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))) :
    (square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) =
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) := by
  classical
  have hdep : DependsOn
      (S.indicator
        (1 : ConfigSpace (Sym2 (square.BufferedVertex N)) → Real))
      (Finset.univ : Finset (Sym2 (square.BufferedVertex N))) := by
    intro omega eta heq
    congr 1
    funext e
    exact heq e (by simp)
  have hsigned := indicator_signedIncreasingCombo_of_dependsOn
    S Finset.univ hdep
  obtain ⟨I, t, c, A, hA, hexp⟩ :=
    (signedIncreasingCombo_iff
      (S.indicator
        (1 : ConfigSpace (Sym2 (square.BufferedVertex N)) → Real))).mp hsigned
  rw [probabilityMeasure_bufferedCylinder_real_eq_signedSum
      (square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
      N S t c A hexp,
    probabilityMeasure_bufferedCylinder_real_eq_signedSum
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq))
      N S t c A hexp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fkSquarePeriodic_freeBufferedInfiniteVolume_real_cylinder
    N hp hp1 hq (hA i hi)]


theorem fkSquarePeriodic_wiredBufferedInfiniteVolume_real_allCylinder
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))) :
    (square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) =
      (FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) := by
  classical
  have hdep : DependsOn
      (S.indicator
        (1 : ConfigSpace (Sym2 (square.BufferedVertex N)) → Real))
      (Finset.univ : Finset (Sym2 (square.BufferedVertex N))) := by
    intro omega eta heq
    congr 1
    funext e
    exact heq e (by simp)
  have hsigned := indicator_signedIncreasingCombo_of_dependsOn
    S Finset.univ hdep
  obtain ⟨I, t, c, A, hA, hexp⟩ :=
    (signedIncreasingCombo_iff
      (S.indicator
        (1 : ConfigSpace (Sym2 (square.BufferedVertex N)) → Real))).mp hsigned
  rw [probabilityMeasure_bufferedCylinder_real_eq_signedSum
      (square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
      N S t c A hexp,
    probabilityMeasure_bufferedCylinder_real_eq_signedSum
      (FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq))
      N S t c A hexp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fkSquarePeriodic_wiredBufferedInfiniteVolume_real_cylinder
    N hp hp1 hq (hA i hi)]

private theorem squareProbabilityMeasure_eq_of_bufferedCylinder_real_eq
    (mu nu : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2))))
    (h : ∀ (N : Nat)
      (S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))),
      (mu : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S) =
        (nu : Measure (ConfigSpace (Sym2 (Site 2)))).real
          (square.bufferedCylinder N S)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite
    (measurableCylinders (fun _ : Sym2 (Site 2) => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨s, S, hS, rfl⟩ := hC
    obtain ⟨N, hs⟩ := square.exists_bufferedLevel_edges s
    rw [square.fullCylinder_eq_bufferedCylinder N s S hs]
    have hreal := h N
      (square.extendEdge (square.bufferedRadius N) ⁻¹' cylinder s S)
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu : Measure (ConfigSpace (Sym2 (Site 2)))) _)
      (measure_ne_top (nu : Measure (ConfigSpace (Sym2 (Site 2)))) _)).mp hreal
  · rw [measure_univ, measure_univ]



theorem fkSquarePeriodic_freeBufferedInfiniteVolume_eq
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) =
      FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) := by
  apply squareProbabilityMeasure_eq_of_bufferedCylinder_real_eq
  intro N S
  exact fkSquarePeriodic_freeBufferedInfiniteVolume_real_allCylinder
    N hp hp1 hq S


theorem fkSquarePeriodic_wiredBufferedInfiniteVolume_eq
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) =
      FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) := by
  apply squareProbabilityMeasure_eq_of_bufferedCylinder_real_eq
  intro N S
  exact fkSquarePeriodic_wiredBufferedInfiniteVolume_real_allCylinder
    N hp hp1 hq S

end

end StatMech.FrontierD
