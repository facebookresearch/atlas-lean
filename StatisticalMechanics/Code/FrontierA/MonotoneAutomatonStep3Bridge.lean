/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral
import Code.FrontierA.MonotoneAutomatonSingleSiteStability
import Code.FrontierA.MultivaluedMap

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}





theorem one_le_numInfiniteClusters_siteToBond_iff
    (eta : ConfigSpace (Site d)) :
    1 ≤ numInfiniteClusters d (siteToBond eta) ↔
      ∃ x : Site d, (cluster d (siteToBond eta) x).Infinite := by
  unfold numInfiniteClusters
  rw [Set.one_le_encard_iff_nonempty]
  constructor
  · rintro ⟨C, hCinf, x, hCx⟩
    refine ⟨x, ?_⟩
    rw [← hCx]
    exact hCinf
  · rintro ⟨x, hx⟩
    exact ⟨cluster d (siteToBond eta) x, hx, x, rfl⟩


theorem one_le_numInfiniteClusters_siteToBond_mono
    {eta eta' : ConfigSpace (Site d)} (h : eta ≤ eta')
    (hperco : 1 ≤ numInfiniteClusters d (siteToBond eta)) :
    1 ≤ numInfiniteClusters d (siteToBond eta') := by
  rw [one_le_numInfiniteClusters_siteToBond_iff] at hperco ⊢
  obtain ⟨x, hx⟩ := hperco
  refine ⟨x, hx.mono ?_⟩
  intro y hy
  exact connected_mono (siteToBond_mono h) hy



theorem measurableSet_interpolatedSite_percolates
    (T : MonotoneAutomaton d) :
    MeasurableSet {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (interpolatedSite T q))} := by
  change MeasurableSet
    ((numInfiniteClusters d ∘ siteToBond ∘ interpolatedSite T) ⁻¹' Set.Ici 1)
  exact (measurable_numInfiniteClusters.comp
    (measurable_siteToBond.comp (measurable_interpolatedSite T)))
      MeasurableSet.of_discrete



theorem measurableSet_lowOutput_percolates
    (T : MonotoneAutomaton d) :
    MeasurableSet {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (T q.1))} := by
  change MeasurableSet
    ((numInfiniteClusters d ∘ siteToBond ∘ fun q : FieldTriple d => T q.1)
      ⁻¹' Set.Ici 1)
  exact (measurable_numInfiniteClusters.comp
    (measurable_siteToBond.comp (T.measurable_toFun.comp measurable_fst)))
      MeasurableSet.of_discrete



theorem interpolatedSite_percolates_of_lowOutput
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedSiteLaw T mu)
        {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1 := by
  have hsub : {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (T q.1))} ⊆
      {q | 1 ≤ numInfiniteClusters d
        (siteToBond (interpolatedSite T q))} := by
    intro q hq
    exact one_le_numInfiniteClusters_siteToBond_mono
      (automatonLow_le_interpolated T q) hq
  have hfull : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (interpolatedSite T q))} = 1 := by
    apply le_antisymm prob_le_one
    exact hlow ▸ measure_mono hsub
  let B : Set (ConfigSpace (Site d)) :=
    {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)}
  have hB : MeasurableSet B := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond) ⁻¹' Set.Ici 1)
    exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
      MeasurableSet.of_discrete
  change (interpolatedSiteLaw T mu) B = 1
  unfold interpolatedSiteLaw
  rw [Measure.map_apply (measurable_interpolatedSite T) hB]
  simpa [B] using hfull






theorem interpolatedSite_cluster_count_ae_one_of_lowOutput
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
  letI : IsProbabilityMeasure (interpolatedSiteLaw T mu) := by
    unfold interpolatedSiteLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_interpolatedSite T).aemeasurable
  exact site_cluster_count_ae_one_general
    (interpolatedSiteLaw T mu) hd
    (interpolatedSiteLaw_isErgodic T mu herg)
    epsilon hepsilon
    (interpolatedSiteLaw_hasInsertionLowerBound T mu epsilon hinsert)
    (interpolatedSite_percolates_of_lowOutput T mu hlow)





def pairHasFiniteNearestInfiniteHighCluster : Set (PairSiteConfig d) :=
  {omega | ∃ x : Site d, (pairHighCluster omega x).Infinite ∧
    (pairNearestHighSet omega x).Finite}

theorem measurableSet_pairHasFiniteNearestInfiniteHighCluster :
    MeasurableSet (pairHasFiniteNearestInfiniteHighCluster (d := d)) := by
  have heq : pairHasFiniteNearestInfiniteHighCluster (d := d) =
      ⋃ x : Site d, {omega | (pairHighCluster omega x).Infinite} ∩
        {omega | (pairNearestHighSet omega x).Finite} := by
    ext omega
    simp [pairHasFiniteNearestInfiniteHighCluster]
  rw [heq]
  exact MeasurableSet.iUnion fun x =>
    (measurableSet_pairHighInfinite x).inter
      (measurableSet_pairNearestHighSet_finite x)



theorem interpolatedHighPair_lowInfinite_nonempty_of_lowOutput
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedHighPairLaw T mu)
      {omega | (pairLowInfiniteVertices omega).Nonempty} = 1 := by
  have hsub : {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (T q.1))} ⊆
      (interpolatedHighPair T) ⁻¹'
        {omega | (pairLowInfiniteVertices omega).Nonempty} := by
    intro q hq
    have haux := one_le_numInfiniteClusters_siteToBond_mono
      (automatonLow_le_interpolated T q) hq
    obtain ⟨x, hx⟩ :=
      (one_le_numInfiniteClusters_siteToBond_iff
        (interpolatedSite T q)).mp haux
    exact pairLowInfiniteVertices_nonempty (interpolatedHighPair T q) hx
  have hfull : mu ((interpolatedHighPair T) ⁻¹'
      {omega | (pairLowInfiniteVertices omega).Nonempty}) = 1 := by
    apply le_antisymm prob_le_one
    exact hlow ▸ measure_mono hsub
  rw [interpolatedHighPairLaw, Measure.map_apply
    (measurable_interpolatedHighPair T)
    measurableSet_pairLowInfiniteVertices_nonempty]
  exact hfull




theorem interpolatedHighPair_finiteNearestInfiniteHighCluster_measure_zero
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hinv : IsTripleFieldTranslationInvariant mu)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedHighPairLaw T mu)
      (pairHasFiniteNearestInfiniteHighCluster (d := d)) = 0 := by
  letI : IsProbabilityMeasure (interpolatedHighPairLaw T mu) := by
    unfold interpolatedHighPairLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_interpolatedHighPair T).aemeasurable
  let lowNonempty : Set (PairSiteConfig d) :=
    {omega | (pairLowInfiniteVertices omega).Nonempty}
  have hlowFull : (interpolatedHighPairLaw T mu) lowNonempty = 1 :=
    interpolatedHighPair_lowInfinite_nonempty_of_lowOutput T mu hlow
  have hlowCompl : (interpolatedHighPairLaw T mu) lowNonemptyᶜ = 0 := by
    rw [measure_compl measurableSet_pairLowInfiniteVertices_nonempty
      (measure_ne_top _ _), hlowFull]
    simp
  have hbad : (interpolatedHighPairLaw T mu)
      (pairHasFiniteNearestHighCluster (d := d)) = 0 :=
    interpolatedHighPair_no_finite_nearest T mu hinv
  apply measure_mono_null (t :=
    pairHasFiniteNearestHighCluster (d := d) ∪ lowNonemptyᶜ)
  · intro omega homega
    by_cases hlowOmega : omega ∈ lowNonempty
    · left
      exact ⟨hlowOmega, homega⟩
    · exact Or.inr hlowOmega
  · exact measure_union_null hbad hlowCompl




def TripleEventIgnoresHighAt (x : Site d) (A : Set (FieldTriple d)) : Prop :=
  ∀ q q' : FieldTriple d, q.1 = q'.1 → q.2.1 = q'.2.1 →
    (∀ y ≠ x, q.2.2 y = q'.2.2 y) → (q ∈ A ↔ q' ∈ A)


def HasHighInsertionLowerBound (mu : Measure (FieldTriple d))
    (t : NNReal) (epsilon : ℝ≥0∞) : Prop :=
  ∀ (x : Site d) (A : Set (FieldTriple d)), MeasurableSet A →
    TripleEventIgnoresHighAt x A →
    epsilon * mu A ≤ mu (A ∩ {q | t ≤ q.2.2 x})


def TripleEventIgnoresHighOn (S : Finset (Site d))
    (A : Set (FieldTriple d)) : Prop :=
  ∀ q q' : FieldTriple d, q.1 = q'.1 → q.2.1 = q'.2.1 →
    (∀ y ∉ S, q.2.2 y = q'.2.2 y) → (q ∈ A ↔ q' ∈ A)


def highThresholdOn (t : NNReal) (S : Finset (Site d)) :
    Set (FieldTriple d) :=
  {q | ∀ x ∈ S, t ≤ q.2.2 x}

theorem measurableSet_highThresholdOn (t : NNReal) (S : Finset (Site d)) :
    MeasurableSet (highThresholdOn (d := d) t S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [highThresholdOn]
  | @insert x S hx ih =>
      have heq : highThresholdOn (d := d) t (insert x S) =
          highThresholdOn t S ∩ {q | t ≤ q.2.2 x} := by
        ext q
        simp [highThresholdOn, and_comm]
      rw [heq]
      apply ih.inter
      have hcoord : Measurable (fun q : FieldTriple d => q.2.2 x) :=
        (measurable_pi_apply x).comp measurable_snd.snd
      exact hcoord measurableSet_Ici



theorem highOutput_eq_true_of_highThresholdOn
    (T : MonotoneAutomaton d) (q : FieldTriple d) (S : Finset (Site d))
    (hq : q ∈ highThresholdOn T.threshold S) (x : Site d) (hx : x ∈ S) :
    T q.2.2 x = true := by
  exact T.occupationThreshold q.2.2 x (hq x hx)




theorem highInsertionLowerBound_finset
    (mu : Measure (FieldTriple d)) (t : NNReal) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu t epsilon)
    (S : Finset (Site d)) (A : Set (FieldTriple d))
    (hAmeas : MeasurableSet A) (hignore : TripleEventIgnoresHighOn S A) :
    epsilon ^ S.card * mu A ≤ mu (A ∩ highThresholdOn t S) := by
  classical
  induction S using Finset.induction_on generalizing A with
  | empty =>
      simp [highThresholdOn]
  | @insert x S hx ih =>
      let B : Set (FieldTriple d) := A ∩ {q | t ≤ q.2.2 x}
      have hxIgnore : TripleEventIgnoresHighAt x A := by
        intro q q' hlow hmiddle hhigh
        apply hignore q q' hlow hmiddle
        intro y hy
        exact hhigh y (fun hyx => hy (hyx ▸ Finset.mem_insert_self x S))
      have hsingle : epsilon * mu A ≤ mu B :=
        hinsert x A hAmeas hxIgnore
      have hBmeas : MeasurableSet B := by
        apply hAmeas.inter
        have hcoord : Measurable (fun q : FieldTriple d => q.2.2 x) :=
          (measurable_pi_apply x).comp measurable_snd.snd
        exact hcoord measurableSet_Ici
      have hBignore : TripleEventIgnoresHighOn S B := by
        intro q q' hlow hmiddle hhigh
        have hAiff : q ∈ A ↔ q' ∈ A := by
          apply hignore q q' hlow hmiddle
          intro y hyInsert
          exact hhigh y (fun hyS => hyInsert (Finset.mem_insert_of_mem hyS))
        have hxEq : q.2.2 x = q'.2.2 x := hhigh x hx
        simp only [B, Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [hAiff, hxEq]
      have hrec := ih B hBmeas hBignore
      have hsets : B ∩ highThresholdOn t S =
          A ∩ highThresholdOn t (insert x S) := by
        ext q
        simp [B, highThresholdOn, and_left_comm, and_assoc]
      rw [hsets] at hrec
      rw [Finset.card_insert_of_notMem hx, pow_succ]
      calc
        epsilon ^ S.card * epsilon * mu A =
            epsilon ^ S.card * (epsilon * mu A) := by ring
        _ ≤ epsilon ^ S.card * mu B := by gcongr
        _ ≤ mu (A ∩ highThresholdOn t (insert x S)) := hrec






def PairHighClusterAbsorption (omega : PairSiteConfig d) : Prop :=
  ∀ x : Site d, (pairHighCluster omega x).Infinite →
    (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty


theorem measurableSet_pairHighCluster_meets_lowInfinite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d |
      (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty} := by
  have heq : {omega : PairSiteConfig d |
      (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty} =
      ⋃ y : Site d, {omega | y ∈ pairHighCluster omega x} ∩
        {omega | y ∈ pairLowInfiniteVertices omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact Set.nonempty_def
  rw [heq]
  exact MeasurableSet.iUnion fun y =>
    (measurableSet_pairHighConnected x y).inter
      (measurableSet_pairLowInfinite y)


theorem measurableSet_pairHighClusterAbsorption :
    MeasurableSet {omega : PairSiteConfig d |
      PairHighClusterAbsorption omega} := by
  have heq : {omega : PairSiteConfig d | PairHighClusterAbsorption omega} =
      ⋂ x : Site d,
        {omega | ¬(pairHighCluster omega x).Infinite} ∪
          {omega | (pairHighCluster omega x ∩
            pairLowInfiniteVertices omega).Nonempty} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
    constructor
    · intro h x
      by_cases hx : (pairHighCluster omega x).Infinite
      · exact Or.inr (h x hx)
      · exact Or.inl hx
    · intro h x hx
      rcases h x with hnot | hmeet
      · exact (hnot hx).elim
      · exact hmeet
  rw [heq]
  exact MeasurableSet.iInter fun x =>
    (measurableSet_pairHighInfinite x).compl.union
      (measurableSet_pairHighCluster_meets_lowInfinite x)



theorem high_cluster_count_le_one_of_low_unique_of_absorption
    (omega : PairSiteConfig d)
    (hlow : numInfiniteClusters d
      (siteToBond (pairSiteLeft omega)) = 1)
    (hnested : pairSiteLeft omega ≤ pairSiteRight omega)
    (habsorb : PairHighClusterAbsorption omega) :
    numInfiniteClusters d (siteToBond (pairSiteRight omega)) ≤ 1 := by
  unfold numInfiniteClusters at hlow ⊢
  rw [Set.encard_le_one_iff_subsingleton]
  intro C hC D hD
  obtain ⟨hCinf, x, rfl⟩ := hC
  obtain ⟨hDinf, y, rfl⟩ := hD
  obtain ⟨a, hax, halow⟩ := habsorb x hCinf
  obtain ⟨b, hby, hblow⟩ := habsorb y hDinf
  have hlowSub : (infiniteClusters d
      (siteToBond (pairSiteLeft omega))).Subsingleton := by
    rw [← Set.encard_le_one_iff_subsingleton, hlow]
  have habClusters : cluster d (siteToBond (pairSiteLeft omega)) a =
      cluster d (siteToBond (pairSiteLeft omega)) b := by
    apply hlowSub
    · exact ⟨halow, a, rfl⟩
    · exact ⟨hblow, b, rfl⟩
  have habLow : Connected d (siteToBond (pairSiteLeft omega)) a b := by
    apply mem_cluster.mp
    rw [habClusters]
    exact self_mem_cluster _ b
  have habHigh : Connected d (siteToBond (pairSiteRight omega)) a b :=
    connected_mono (siteToBond_mono hnested) habLow
  have hxy : Connected d (siteToBond (pairSiteRight omega)) x y :=
    hax.trans (habHigh.trans hby.symm)
  exact cluster_eq_of_connected hxy





theorem highOutput_cluster_count_ae_le_one_of_absorption
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
    (habsorb : ∀ᵐ q ∂mu,
      PairHighClusterAbsorption (interpolatedHighPair T q)) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
  have hauxLaw := interpolatedSite_cluster_count_ae_one_of_lowOutput
    T mu hd herg epsilon hepsilon hinsert hlow
  have hauxMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (interpolatedSite T q)) = 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘ interpolatedSite T) ⁻¹' {1})
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp (measurable_interpolatedSite T)))
        MeasurableSet.of_discrete
  have hauxField : mu {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (interpolatedSite T q)) = 1} = 1 := by
    let B : Set (ConfigSpace (Site d)) :=
      {eta | numInfiniteClusters d (siteToBond eta) = 1}
    have hB : MeasurableSet B := by
      change MeasurableSet
        ((numInfiniteClusters d ∘ siteToBond) ⁻¹' ({1} : Set ℕ∞))
      exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
        MeasurableSet.of_discrete
    change (interpolatedSiteLaw T mu) B = 1 at hauxLaw
    unfold interpolatedSiteLaw at hauxLaw
    rw [Measure.map_apply (measurable_interpolatedSite T) hB] at hauxLaw
    simpa [B] using hauxLaw
  have hauxAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (interpolatedSite T q)) = 1 := by
    apply (ae_iff_measure_eq hauxMeas.nullMeasurableSet).2
    simpa using hauxField
  have hresultAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1 := by
    filter_upwards [hauxAE, hmono, habsorb] with q hunique hqmono hqabsorb
    exact high_cluster_count_le_one_of_low_unique_of_absorption
      (interpolatedHighPair T q) hunique
      (interpolatedHighPair_nested T q hqmono) hqabsorb
  have hresultMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘
        fun q : FieldTriple d => T q.2.2) ⁻¹' Set.Iic 1)
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp
        (T.measurable_toFun.comp measurable_snd.snd)))
          MeasurableSet.of_discrete
  have := (ae_iff_measure_eq hresultMeas.nullMeasurableSet).1 hresultAE
  simpa using this



theorem highOutput_cluster_count_ae_one_of_absorption
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
    (habsorb : ∀ᵐ q ∂mu,
      PairHighClusterAbsorption (interpolatedHighPair T q)) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) = 1} = 1 := by
  have hleFull := highOutput_cluster_count_ae_le_one_of_absorption
    T mu hd herg epsilon hepsilon hinsert hmono hlow habsorb
  have hlowAE : ∀ᵐ q ∂mu,
      1 ≤ numInfiniteClusters d (siteToBond (T q.1)) := by
    apply (ae_iff_measure_eq
      (measurableSet_lowOutput_percolates T).nullMeasurableSet).2
    simpa using hlow
  have hleMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘
        fun q : FieldTriple d => T q.2.2) ⁻¹' Set.Iic 1)
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp
        (T.measurable_toFun.comp measurable_snd.snd)))
          MeasurableSet.of_discrete
  have hleAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1 := by
    apply (ae_iff_measure_eq hleMeas.nullMeasurableSet).2
    simpa using hleFull
  have honeAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (T q.2.2)) = 1 := by
    filter_upwards [hlowAE, hmono, hleAE] with q hqLow hqMono hqLe
    apply le_antisymm hqLe
    exact one_le_numInfiniteClusters_siteToBond_mono
      (T.monotone (hqMono.1.trans hqMono.2)) hqLow
  have honeMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (T q.2.2)) = 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘
        fun q : FieldTriple d => T q.2.2) ⁻¹' {1})
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp
        (T.measurable_toFun.comp measurable_snd.snd)))
          MeasurableSet.of_discrete
  calc
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) = 1} = mu Set.univ :=
      (ae_iff_measure_eq honeMeas.nullMeasurableSet).1 honeAE
    _ = 1 := measure_univ

end StatMech.FrontierA
