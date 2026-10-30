/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKUniquenessDensity
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneInPBoundaryCondition
public import PhyslibExt.StatisticalMechanics.RandomCluster.LogitFreeEnergyComparison
public import PhyslibExt.StatisticalMechanics.RandomCluster.HolleyCoupling
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointInfinite
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeWeakLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.Limits
public import MathlibExt.Probability.StochasticOrder.Strassen

/-!
# Uniqueness of the `q = 2` infinite-volume measure on a box from free-energy data

Restricting the free and wired `q = 2` infinite-volume measures to a box `Λ_N` gives two families
of mass functions, parametrized by `t` with `p = logistic(t)`, that are monotonically coupled; if
their edge densities are the one-sided derivatives of one convex function, they agree on all
increasing events of `Λ_N` for all but countably many `t`.

## i. Overview

The restrictions `fuc_freeMass d N t` and `fuc_wiredMass d N t` of the free and wired measures to
`Λ_N` are probability mass functions with `free ≼ wired`; Strassen's theorem gives a monotone
coupling. The wired edge density is monotone in `t`. Under `fuc_HomogeneousFreeEnergyData` (the
wired and free edge densities are the right and left derivatives of one convex `g`), the abstract
argument of `FKUniquenessDensity` applies.

## ii. Key results

- `fuc_isMonotoneCouplingFun_of_dominated` : stochastic domination of mass functions gives a
  monotone coupling.
- `fuc_dominated` : the free restriction is dominated by the wired one.
- `fuc_fk_uniqueness` : countable-exception uniqueness on increasing box events, given
  `fuc_HomogeneousFreeEnergyData`.

## iii. Table of contents

- A. Mass functions of finite pushforwards
- B. Monotone couplings from stochastic domination
- C. Box restrictions of the infinite-volume measures
- D. Uniqueness from free-energy data

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.63.
- V. Strassen, *The existence of probability measures with given marginals*, Ann. Math. Statist.
  36 (1965).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

/-! ## A. Mass functions of finite pushforwards -/

lemma fuc_real_preimage_eq_indicator_sum {α β : Type*} [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (A : Set β) :
    μ.real (f ⁻¹' A) = ∑ ω : β, A.indicator (fun _ => (1 : ℝ)) ω * μ.real (f ⁻¹' {ω}) := by
  classical
  have hpre : f ⁻¹' A = ⋃ ω ∈ (Finset.univ.filter (· ∈ A)), f ⁻¹' {ω} := by
    ext x; simp [Set.mem_preimage]
  rw [hpre, measureReal_biUnion_finset]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  · intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxa hxb
    exact hab (hxa ▸ hxb)
  · intro ω _; exact hf (measurableSet_singleton ω)

lemma fuc_sum_real_preimage_eq_one {α β : Type*} [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f) :
    ∑ ω : β, μ.real (f ⁻¹' {ω}) = 1 := by
  classical
  have h : (∑ ω : β, μ.real (f ⁻¹' {ω})) = μ.real (f ⁻¹' (univ : Set β)) := by
    have hpre : (f ⁻¹' (univ : Set β)) = ⋃ ω : β, f ⁻¹' {ω} := by ext x; simp
    rw [hpre, measureReal_iUnion_fintype
      (by intro i j hij; apply Set.disjoint_left.mpr; intro x h1 h2; simp_all)
      (fun ω => hf (measurableSet_singleton ω))]
  rw [h]; simp [measureReal_def]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## B. Monotone couplings from stochastic domination -/

lemma fuc_measOfMass_real_singleton {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ)
    (x : ConfigSpace E) : (measOfMass μ).real {x} = μ x := by
  classical
  rw [measOfMass_real μ hμ {x}, Finset.sum_eq_single x]
  · simp
  · intro b _ hb; simp [Set.mem_singleton_iff, hb]
  · intro h; exact absurd (Finset.mem_univ x) h

lemma fuc_isMonotoneCouplingFun_of_monotoneCoupling {μ ν : ConfigSpace E → ℝ}
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    {κ : Measure (ConfigSpace E × ConfigSpace E)} [IsFiniteMeasure κ]
    (hcoup : MonotoneCoupling (measOfMass μ) (measOfMass ν) κ) :
    IsMonotoneCouplingFun (fun z => κ.real {z}) μ ν := by
  classical
  refine ⟨fun z => measureReal_nonneg, ?_, ?_, ?_⟩
  · intro z hz
    have hmem : z ∈ (orderSet E)ᶜ := hz
    have hle : κ {z} ≤ κ (orderSet E)ᶜ :=
      measure_mono (by
        intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hmem)
    rw [hcoup.supported] at hle
    simp only [measureReal_def]
    rw [le_antisymm hle bot_le]; simp
  · intro ω
    have hfib : (∑ ω' : ConfigSpace E, κ.real {(ω, ω')}) = κ.fst.real {ω} := by
      rw [measureReal_def, Measure.fst_apply (measurableSet_singleton ω)]
      have hpre : (Prod.fst ⁻¹' {ω} : Set (ConfigSpace E × ConfigSpace E))
          = ⋃ ω' : ConfigSpace E, {(ω, ω')} := by ext ⟨a, b⟩; simp [Set.mem_preimage, eq_comm]
      rw [hpre, measure_iUnion
        (by intro i j hij; apply Set.disjoint_left.mpr; rintro ⟨a, b⟩ h1 h2; simp_all)
        (fun ω' => measurableSet_singleton _)]
      rw [tsum_fintype, ENNReal.toReal_sum (fun ω' _ => measure_ne_top κ _)]; rfl
    rw [hfib, hcoup.fst_eq, fuc_measOfMass_real_singleton hμ ω]
  · intro ω'
    have hfib : (∑ ω : ConfigSpace E, κ.real {(ω, ω')}) = κ.snd.real {ω'} := by
      rw [measureReal_def, Measure.snd_apply (measurableSet_singleton ω')]
      have hpre : (Prod.snd ⁻¹' {ω'} : Set (ConfigSpace E × ConfigSpace E))
          = ⋃ ω : ConfigSpace E, {(ω, ω')} := by ext ⟨a, b⟩; simp [Set.mem_preimage, eq_comm]
      rw [hpre, measure_iUnion
        (by intro i j hij; apply Set.disjoint_left.mpr; rintro ⟨a, b⟩ h1 h2; simp_all)
        (fun ω => measurableSet_singleton _)]
      rw [tsum_fintype, ENNReal.toReal_sum (fun ω _ => measure_ne_top κ _)]; rfl
    rw [hfib, hcoup.snd_eq, fuc_measOfMass_real_singleton hν ω']

lemma fuc_isMonotoneCouplingFun_of_dominated {μ ν : ConfigSpace E → ℝ}
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hnμ : ∑ ω, μ ω = 1) (hnν : ∑ ω, ν ω = 1)
    (hdom : measOfMass μ ≼ measOfMass ν) :
    ∃ P : ConfigSpace E × ConfigSpace E → ℝ, IsMonotoneCouplingFun P μ ν := by
  have hpμ : IsProbabilityMeasure (measOfMass μ) := measOfMass_isProbabilityMeasure μ hμ hnμ
  have hpν : IsProbabilityMeasure (measOfMass ν) := measOfMass_isProbabilityMeasure ν hν hnν
  obtain ⟨κ, hκfin, hκ⟩ :=
    StatMech.exists_monotoneCoupling_of_stochasticallyDominated _ _ hdom
  exact ⟨fun z => κ.real {z}, fuc_isMonotoneCouplingFun_of_monotoneCoupling hμ hν hκ⟩

variable {d : ℕ}

/-! ## C. Box restrictions of the infinite-volume measures -/

/-- The mass function on configurations of `Λ_N` of the free `q = 2` infinite-volume measure at
`p = logistic(t)`, restricted to `Λ_N`.
-/
noncomputable def fuc_freeMass (d N : ℕ) (t : ℝ) : ConfigSpace (Sym2 (boxVerts d N)) → ℝ :=
  fun ω => (freeInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t)
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d N ⁻¹' {ω})

/-- The mass function on configurations of `Λ_N` of the wired `q = 2` infinite-volume measure at
`p = logistic(t)`, restricted to `Λ_N`.
-/
noncomputable def fuc_wiredMass (d N : ℕ) (t : ℝ) : ConfigSpace (Sym2 (boxVerts d N)) → ℝ :=
  fun ω => (wiredInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t)
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d N ⁻¹' {ω})

lemma fuc_freeMass_nonneg (d N : ℕ) (t : ℝ) : 0 ≤ fuc_freeMass d N t :=
  fun _ => measureReal_nonneg

lemma fuc_wiredMass_nonneg (d N : ℕ) (t : ℝ) : 0 ≤ fuc_wiredMass d N t :=
  fun _ => measureReal_nonneg

lemma fuc_freeMass_sum_one (d N : ℕ) (t : ℝ) : ∑ ω, fuc_freeMass d N t ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

lemma fuc_wiredMass_sum_one (d N : ℕ) (t : ℝ) : ∑ ω, fuc_wiredMass d N t ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

lemma fuc_eventMassProb_free (d N : ℕ) (t : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_freeMass d N t) A
      = (freeInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t)
          (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fuc_freeMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]

lemma fuc_eventMassProb_wired (d N : ℕ) (t : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_wiredMass d N t) A
      = (wiredInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t)
          (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fuc_wiredMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]

lemma fuc_edgeMargProb_eq_eventMassProb {N : ℕ} (μ : ConfigSpace (Sym2 (boxVerts d N)) → ℝ)
    (e' : Sym2 (boxVerts d N)) :
    edgeMargProb μ e' = eventMassProb μ (boxEdgeOpenEvent d N e') := by
  unfold edgeMargProb eventMassProb boxEdgeOpenEvent
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω e' = true
  · simp [Set.indicator, hω]
  · simp only [Bool.not_eq_true] at hω
    simp [Set.indicator, hω]

lemma fuc_edgeMargProb_free (d N : ℕ) (t : ℝ) (e' : Sym2 (boxVerts d N)) :
    edgeMargProb (fuc_freeMass d N t) e'
      = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fuc_eventMassProb_free,
    freeEdgeDensity_q2_eq_real d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

lemma fuc_edgeMargProb_wired (d N : ℕ) (t : ℝ) (e' : Sym2 (boxVerts d N)) :
    edgeMargProb (fuc_wiredMass d N t) e'
      = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fuc_eventMassProb_wired,
    wiredEdgeDensity_q2_eq_real d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

lemma fuc_freeIV_le_wiredIV (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  have htf := fk_free_infinite_measure N hp hp1 hS
  have htw := fk_wired_infinite_measure N hp hp1 hS
  refine le_of_tendsto_of_tendsto htf htw (Filter.Eventually.of_forall (fun m => ?_))
  exact freeFiniteMeasure_dominated d m hp hp1 (by norm_num)
    (boxRestrict d N ⁻¹' S)
    ((continuous_boxRestrict d N).measurable (MeasurableSet.of_discrete))
    (fun a b hab ha => hS (monotone_boxRestrict d N hab) ha)

lemma fuc_dominated (d N : ℕ) (t : ℝ) :
    measOfMass (fuc_freeMass d N t) ≼ measOfMass (fuc_wiredMass d N t) := by
  intro A _ hAinc
  have hfree : (measOfMass (fuc_freeMass d N t)).real A
      = eventMassProb (fuc_freeMass d N t) A := by
    rw [measOfMass_real_eq_indicator_sum _ (fuc_freeMass_nonneg d N t) A]; rfl
  have hwired : (measOfMass (fuc_wiredMass d N t)).real A
      = eventMassProb (fuc_wiredMass d N t) A := by
    rw [measOfMass_real_eq_indicator_sum _ (fuc_wiredMass_nonneg d N t) A]; rfl
  rw [hfree, hwired, fuc_eventMassProb_free, fuc_eventMassProb_wired]
  exact fuc_freeIV_le_wiredIV d N (fsc_logistic_pos t) (fsc_logistic_lt_one t) hAinc

lemma fuc_hcoup (d N : ℕ) :
    ∀ t : ℝ, ∃ P : ConfigSpace (Sym2 (boxVerts d N)) × ConfigSpace (Sym2 (boxVerts d N)) → ℝ,
      IsMonotoneCouplingFun P (fuc_freeMass d N t) (fuc_wiredMass d N t) :=
  fun t => fuc_isMonotoneCouplingFun_of_dominated
    (fuc_freeMass_nonneg d N t) (fuc_wiredMass_nonneg d N t)
    (fuc_freeMass_sum_one d N t) (fuc_wiredMass_sum_one d N t) (fuc_dominated d N t)

lemma fuc_hmono (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    Monotone (fun t => edgeMargProb (fuc_wiredMass d N t) eb) := by
  intro t1 t2 hle
  simp only [fuc_edgeMargProb_wired]
  exact wiredEdgeDensity_q2_monotoneOn d N eb (fsc_logistic_mem_Ioo t1)
    (fsc_logistic_mem_Ioo t2) (fsc_logistic_strictMono.monotone hle)

/-! ## D. Uniqueness from free-energy data -/

/-- There is a convex `g` whose right and left derivatives at `t` are the wired and free `q = 2`
edge
densities at `p = logistic(t)`, for every edge of `Λ_N`.
-/
def fuc_HomogeneousFreeEnergyData (d N : ℕ) : Prop :=
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
    ∧ (∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
        wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t)
    ∧ (∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
        freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t)

/-- Given `fuc_HomogeneousFreeEnergyData`, the free and wired `q = 2` measures agree on every
increasing event of `Λ_N` for all but countably many `t`.
-/
lemma fuc_fk_uniqueness (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fuc_HomogeneousFreeEnergyData d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hg, hwired, hfree⟩ := hdata
  choose P hP using fuc_hcoup d N
  exact fud_countable_phi_ne_of_homogeneous
    (fun t => fuc_freeMass d N t) (fun t => fuc_wiredMass d N t) eb P hP
    (a := pressureLeftDeriv g) (b := pressureRightDeriv g) (g := g)
    (fuc_hmono d N eb)
    hg
    (fun e' t => by rw [fuc_edgeMargProb_free]; exact hfree e' t)
    (fun e' t => by rw [fuc_edgeMargProb_wired]; exact hwired e' t)
    (fun _ => rfl)
    (fun _ => rfl)

lemma fuc_homogeneousData_imp_fsc (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fuc_HomogeneousFreeEnergyData d N) :
    fsc_FreeEnergyData d N eb := by
  obtain ⟨g, hg, hwired, hfree⟩ := hdata
  exact ⟨g, hg, fun t => hwired eb t, fun t => hfree eb t⟩

end FK

end StatMech
