/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.MonotoneAutomatonStep3Bridge

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}



def pairDisjointInfiniteHighAt (x : Site d) : Set (PairSiteConfig d) :=
  {omega | (pairHighCluster omega x).Infinite ∧
    ¬(pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty}

theorem measurableSet_pairDisjointInfiniteHighAt (x : Site d) :
    MeasurableSet (pairDisjointInfiniteHighAt x) := by
  exact (measurableSet_pairHighInfinite x).inter
    (measurableSet_pairHighCluster_meets_lowInfinite x).compl



def pairStep3CoreAt (x : Site d) : Set (PairSiteConfig d) :=
  pairDisjointInfiniteHighAt x ∩
    {omega | (pairNearestHighSet omega x).Infinite}

theorem measurableSet_pairStep3CoreAt (x : Site d) :
    MeasurableSet (pairStep3CoreAt x) := by
  exact (measurableSet_pairDisjointInfiniteHighAt x).inter
    (measurableSet_pairNearestHighSet_finite x).compl



theorem pairDisjointInfiniteHighAt_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) (x : Site d) :
    StatMech.ConfigSpace.shift g omega ∈
        pairDisjointInfiniteHighAt (g • x) ↔
      omega ∈ pairDisjointInfiniteHighAt x := by
  unfold pairDisjointInfiniteHighAt
  simp only [Set.mem_setOf_eq]
  rw [pairHighCluster_shift, pairLowInfiniteVertices_shift]
  simp only [translateSiteSet]
  have hinj : Function.Injective
      (fun z : Site d => Multiplicative.toAdd g + z) :=
    add_right_injective _
  rw [Set.infinite_image_iff (Set.injOn_of_injective hinj),
    ← Set.image_inter hinj, Set.image_nonempty]



theorem pairDisjointInfiniteHighAt_measure_zero_of_origin
    (nu : Measure (PairSiteConfig d)) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
    (hzero : nu (pairDisjointInfiniteHighAt (0 : Site d)) = 0)
    (x : Site d) :
    nu (pairDisjointInfiniteHighAt x) = 0 := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hg0 : g • (0 : Site d) = x := by
    change x + 0 = x
    simp
  have hpre :
      (StatMech.ConfigSpace.shift g : PairSiteConfig d → PairSiteConfig d) ⁻¹'
          pairDisjointInfiniteHighAt x =
        pairDisjointInfiniteHighAt (0 : Site d) := by
    ext omega
    change StatMech.ConfigSpace.shift g omega ∈
        pairDisjointInfiniteHighAt x ↔
      omega ∈ pairDisjointInfiniteHighAt (0 : Site d)
    rw [← hg0]
    exact pairDisjointInfiniteHighAt_shift g omega 0
  calc
    nu (pairDisjointInfiniteHighAt x) =
        nu ((StatMech.ConfigSpace.shift g :
          PairSiteConfig d → PairSiteConfig d) ⁻¹'
            pairDisjointInfiniteHighAt x) :=
      (hinv.measure_preimage g
        (measurableSet_pairDisjointInfiniteHighAt x)).symm
    _ = nu (pairDisjointInfiniteHighAt (0 : Site d)) := by rw [hpre]
    _ = 0 := hzero


def pairHasDisjointInfiniteHighCluster : Set (PairSiteConfig d) :=
  {omega | ∃ x : Site d, omega ∈ pairDisjointInfiniteHighAt x}

theorem pairHasDisjointInfiniteHighCluster_eq_iUnion :
    pairHasDisjointInfiniteHighCluster (d := d) =
      ⋃ x : Site d, pairDisjointInfiniteHighAt x := by
  ext omega
  simp [pairHasDisjointInfiniteHighCluster]

theorem measurableSet_pairHasDisjointInfiniteHighCluster :
    MeasurableSet (pairHasDisjointInfiniteHighCluster (d := d)) := by
  rw [pairHasDisjointInfiniteHighCluster_eq_iUnion]
  exact MeasurableSet.iUnion measurableSet_pairDisjointInfiniteHighAt



theorem pairHighClusterAbsorption_compl_eq :
    {omega : PairSiteConfig d | PairHighClusterAbsorption omega}ᶜ =
      pairHasDisjointInfiniteHighCluster := by
  ext omega
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  simp [PairHighClusterAbsorption, pairHasDisjointInfiniteHighCluster,
    pairDisjointInfiniteHighAt]



theorem pairHighClusterAbsorption_ae_of_origin_disjoint_null
    (nu : Measure (PairSiteConfig d)) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
    (hzero : nu (pairDisjointInfiniteHighAt (0 : Site d)) = 0) :
    ∀ᵐ omega ∂nu, PairHighClusterAbsorption omega := by
  have hbad : nu (pairHasDisjointInfiniteHighCluster (d := d)) = 0 := by
    rw [pairHasDisjointInfiniteHighCluster_eq_iUnion]
    apply measure_iUnion_null
    exact pairDisjointInfiniteHighAt_measure_zero_of_origin nu hinv hzero
  have hcompl :
      nu {omega : PairSiteConfig d | PairHighClusterAbsorption omega}ᶜ = 0 := by
    rw [pairHighClusterAbsorption_compl_eq]
    exact hbad
  have hfull :
      nu {omega : PairSiteConfig d | PairHighClusterAbsorption omega} = 1 :=
    (prob_compl_eq_zero_iff
      measurableSet_pairHighClusterAbsorption).mp hcompl
  apply (ae_iff_measure_eq
    measurableSet_pairHighClusterAbsorption.nullMeasurableSet).2
  simpa using hfull



theorem pairDisjointInfiniteHighAt_subset_finiteNearest_union_core
    (x : Site d) :
    pairDisjointInfiniteHighAt x ⊆
      pairHasFiniteNearestInfiniteHighCluster ∪ pairStep3CoreAt x := by
  intro omega homega
  by_cases hfinite : (pairNearestHighSet omega x).Finite
  · exact Or.inl ⟨x, homega.1, hfinite⟩
  · exact Or.inr ⟨homega, hfinite⟩



theorem interpolatedHighPair_origin_disjoint_null_of_step3Core
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hinv : IsTripleFieldTranslationInvariant mu)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (T q.1))} = 1)
    (hcore : (interpolatedHighPairLaw T mu)
      (pairStep3CoreAt (0 : Site d)) = 0) :
    (interpolatedHighPairLaw T mu)
      (pairDisjointInfiniteHighAt (0 : Site d)) = 0 := by
  have hfinite :=
    interpolatedHighPair_finiteNearestInfiniteHighCluster_measure_zero
      T mu hinv hlow
  apply measure_mono_null
    (pairDisjointInfiniteHighAt_subset_finiteNearest_union_core 0)
  exact measure_union_null hfinite hcore



theorem interpolatedHighPair_absorption_ae_of_step3Core
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hinv : IsTripleFieldTranslationInvariant mu)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (T q.1))} = 1)
    (hcore : (interpolatedHighPairLaw T mu)
      (pairStep3CoreAt (0 : Site d)) = 0) :
    ∀ᵐ q ∂mu, PairHighClusterAbsorption (interpolatedHighPair T q) := by
  letI : IsProbabilityMeasure (interpolatedHighPairLaw T mu) := by
    unfold interpolatedHighPairLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_interpolatedHighPair T).aemeasurable
  have habsorb : ∀ᵐ omega ∂interpolatedHighPairLaw T mu,
      PairHighClusterAbsorption omega :=
    pairHighClusterAbsorption_ae_of_origin_disjoint_null
      (interpolatedHighPairLaw T mu)
      (interpolatedHighPairLaw_isTranslationInvariant T mu hinv)
      (interpolatedHighPair_origin_disjoint_null_of_step3Core
        T mu hinv hlow hcore)
  exact (ae_map_iff (measurable_interpolatedHighPair T).aemeasurable
    measurableSet_pairHighClusterAbsorption).mp habsorb




theorem highOutput_cluster_count_ae_le_one_of_step3Core
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (T q.1))} = 1)
    (hcore : (interpolatedHighPairLaw T mu)
      (pairStep3CoreAt (0 : Site d)) = 0) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
  apply highOutput_cluster_count_ae_le_one_of_absorption
    T mu hd herg epsilon hepsilon hinsert hmono hlow
  exact interpolatedHighPair_absorption_ae_of_step3Core
    T mu herg.1 hlow hcore

end StatMech.FrontierA
