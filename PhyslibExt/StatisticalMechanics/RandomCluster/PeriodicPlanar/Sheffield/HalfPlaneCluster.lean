/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneExclusion
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectanglePreference
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalErgodicity
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AxisSwap
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AxisNegation

/-!
# Infinite clusters inside a half-plane

Clusters restricted to a region, the event that a half-plane contains an infinite cluster, its
translation invariance and zero–one law, and escape estimates when it has probability zero.

## i. Overview

`clusterWithinSet ω A x` is the set of vertices joined to `x` by an open path inside `A`.
Exhausting `A` by orbit boxes shows that "this cluster is infinite" is measurable and is the
decreasing limit of the events "the cluster reaches outside the box of radius `n`".
`rightHalfPlaneHasInfiniteCluster r` is the event that `H_r = {x ≥ r}` contains an infinite
cluster of the restricted configuration. Its probability does not depend on `r` under a
translation-invariant measure; it equals the probability of the shift-invariant event that every
right half-plane contains an infinite cluster, so ergodicity gives a zero–one law. When the
probability is zero, the probability that a fixed finite set in `H_r` reaches outside the box of
radius `n` within `H_r` tends to zero, which bounds rectangle side-connection events.
The file also transfers ergodicity to the axis-swapped and axis-negated periodic structures.

Headline fidelity:
- `rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one` is conditional on ergodicity of the
  measure under the lattice translations.
- `rightHalfPlaneHasInfiniteCluster_measure_eq_boundary` (independence of `r`) is conditional on
  translation invariance.
- The escape estimates are conditional on the half-plane event having probability zero.
- The remaining set identities and measurability results are unconditional.

## ii. Key results

- `PeriodicGraph.clusterWithinSet`, `PeriodicGraph.measurableSet_clusterWithinSet_infinite`
- `PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster`
- `PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary`
- `PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one`
- `PeriodicPlaneEmbedding.rightHalfPlane_finiteSetEscape_measureReal_tendsto_zero`

## iii. Table of contents

- A. Ergodicity of the reflected periodic structures
- B. Clusters within a region
- C. Infinite clusters within a region
- D. The half-plane infinite-cluster event
- E. Escape from finite sets

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §4.3 (ergodicity and zero–one laws).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Ergodicity of the reflected periodic structures -/

omit [Countable V] in
/-- Ergodicity is preserved when the two lattice axes are swapped. -/
lemma PeriodicGraph.axisSwap_isErgodic
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hErgodic : P.IsErgodic mu) : P.axisSwap.IsErgodic mu := by
  refine ⟨P.axisSwap_isTranslationInvariant mu hErgodic.1, ?_⟩
  intro s hs hinvariant
  apply hErgodic.2 s hs
  intro z
  have h := hinvariant (siteAxisSwap z)
  change P.configTranslate (siteAxisSwap (siteAxisSwap z)) ⁻¹' s = s at h
  simpa using h

omit [Countable V] in
/-- Ergodicity is preserved when a lattice axis is negated. -/
lemma PeriodicGraph.axisNeg_isErgodic
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hErgodic : P.IsErgodic mu) : P.axisNeg.IsErgodic mu := by
  refine ⟨P.axisNeg_isTranslationInvariant mu hErgodic.1, ?_⟩
  intro s hs hinvariant
  apply hErgodic.2 s hs
  intro z
  have h := hinvariant (-z)
  change P.configTranslate (-(-z)) ⁻¹' s = s at h
  simpa using h

/-! ## B. Clusters within a region -/

/-- The open cluster of `x` inside `A`: vertices joined to `x` by an open path with all vertices
in `A`. -/
def PeriodicGraph.clusterWithinSet
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) (x : V) : Set V :=
  {y | omega ∈ P.connectedWithinSet A x y}

omit [Countable V] in
lemma PeriodicGraph.mem_clusterWithinSet
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) (x y : V) :
    y ∈ P.clusterWithinSet omega A x ↔
      omega ∈ P.connectedWithinSet A x y :=
  Iff.rfl

omit [Countable V] in
/-- A connection within `A` takes place within `A ∩` some orbit box. -/
lemma PeriodicGraph.iUnion_connectedWithinSet_inter_orbitBox
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    (⋃ n : Nat, P.connectedWithinSet
      (A ∩ (P.orbitBox n : Set V)) x y) =
        P.connectedWithinSet A x y := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 homega
    exact P.connectedWithinSet_mono_region inter_subset_left x y hn
  · rintro omega ⟨l, hchain, hlast, hregion⟩
    choose index hindex using fun v : V => P.exists_mem_orbitBox v
    let support : Finset V := (x :: l).toFinset
    let N : Nat := ∑ v ∈ support, index v
    have hsupport (v : V) (hv : v ∈ x :: l) :
        v ∈ (P.orbitBox N : Set V) := by
      have hvSupport : v ∈ support := by
        simpa [support] using hv
      have hle : index v ≤ N := by
        dsimp only [N]
        exact Finset.single_le_sum
          (fun z _hz => Nat.zero_le (index z)) hvSupport
      exact P.orbitBox_mono hle (hindex v)
    apply Set.mem_iUnion.2
    refine ⟨N, l, hchain, hlast, ?_⟩
    intro v hv
    exact ⟨hregion v hv, hsupport v hv⟩

omit [Countable V] in
lemma PeriodicGraph.iUnion_setConnectionWithin_inter_orbitBox
    (P : PeriodicGraph V) (A S T : Set V) :
    (⋃ n : Nat, P.setConnectionWithin
      (A ∩ (P.orbitBox n : Set V)) S T) =
        P.setConnectionWithin A S T := by
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨n, x, hx, y, hy, hxy⟩ := by
      simpa only [Set.mem_iUnion, PeriodicGraph.setConnectionWithin,
        Set.mem_ofPred_eq] using homega
    exact ⟨x, hx, y, hy,
      P.connectedWithinSet_mono_region inter_subset_left x y hxy⟩
  · rintro omega ⟨x, hx, y, hy, hxy⟩
    rw [← P.iUnion_connectedWithinSet_inter_orbitBox A x y] at hxy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hxy
    apply Set.mem_iUnion.2
    exact ⟨n, x, hx, y, hy, hn⟩

omit [Countable V] in
lemma PeriodicGraph.setConnectionWithin_inter_orbitBox_mono
    (P : PeriodicGraph V) (A S T : Set V) :
    Monotone (fun n => P.setConnectionWithin
      (A ∩ (P.orbitBox n : Set V)) S T) := by
  intro n N hnN
  exact P.setConnectionWithin_mono_region
    (inter_subset_inter_right _ (fun _ hv => P.orbitBox_mono hnN hv)) S T

omit [Countable V] in
lemma PeriodicGraph.setConnectionWithin_inter_orbitBox_measureReal_tendsto
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (A S T : Set V) :
    Tendsto (fun n => mu.real (P.setConnectionWithin
      (A ∩ (P.orbitBox n : Set V)) S T)) atTop
      (nhds (mu.real (P.setConnectionWithin A S T))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (P.setConnectionWithin_inter_orbitBox_mono A S T)
  rw [P.iUnion_setConnectionWithin_inter_orbitBox A S T] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

omit [Countable V] in
lemma PeriodicGraph.clusterWithinSet_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A : Set V) (x : V) :
    P.shift z '' P.clusterWithinSet omega A x =
      P.clusterWithinSet (P.configTranslate z omega)
        (P.shift z '' A) (P.shift z x) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (P.connectedWithinSet_configTranslate z omega A x u).2 hu
  · intro hy
    let u := P.shift (-z) y
    have hyBack : P.shift z u = y := by
      simp [u]
    refine ⟨u, ?_, hyBack⟩
    rw [← hyBack] at hy
    exact (P.connectedWithinSet_configTranslate z omega A x u).1 hy

omit [Countable V] in
/-- A restricted cluster is infinite iff it reaches outside every orbit box. -/
lemma PeriodicGraph.clusterWithinSet_infinite_iff_orbitBox_escape
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) (x : V) :
    (P.clusterWithinSet omega A x).Infinite ↔
      ∀ n : Nat, ∃ y : V,
        y ∉ (P.orbitBox n : Set V) ∧
          omega ∈ P.connectedWithinSet A x y := by
  classical
  constructor
  · intro hinfinite n
    by_contra hnot
    push Not at hnot
    apply hinfinite
    exact (P.orbitBox n).finite_toSet.subset fun y hy =>
      Classical.byContradiction fun hyBox =>
        hnot y hyBox (by simpa [PeriodicGraph.clusterWithinSet] using hy)
  · intro hescape hfinite
    choose index hindex using fun y : V => P.exists_mem_orbitBox y
    let N : Nat := ∑ y ∈ hfinite.toFinset, index y
    have hsubset : P.clusterWithinSet omega A x ⊆
        (P.orbitBox N : Set V) := by
      intro y hy
      have hyFinset : y ∈ hfinite.toFinset := by
        simpa using hy
      have hle : index y ≤ N := by
        dsimp only [N]
        exact Finset.single_le_sum
          (fun z _hz => Nat.zero_le (index z)) hyFinset
      exact P.orbitBox_mono hle (hindex y)
    obtain ⟨y, hyOutside, hyConnect⟩ := hescape N
    exact hyOutside (hsubset (by
      simpa [PeriodicGraph.clusterWithinSet] using hyConnect))

/-- The event that a restricted cluster is infinite is measurable. -/
lemma PeriodicGraph.measurableSet_clusterWithinSet_infinite
    (P : PeriodicGraph V) (A : Set V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega A x).Infinite} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega A x).Infinite} =
      ⋂ n : Nat, ⋃ y : V, ⋃ (_hy : y ∉ (P.orbitBox n : Set V)),
        P.connectedWithinSet A x y := by
    ext omega
    rw [Set.mem_ofPred_eq]
    constructor
    · intro hinfinite
      rw [P.clusterWithinSet_infinite_iff_orbitBox_escape] at hinfinite
      rw [Set.mem_iInter]
      intro n
      obtain ⟨y, hyOutside, hyConnect⟩ := hinfinite n
      exact Set.mem_iUnion.2 ⟨y,
        Set.mem_iUnion.2 ⟨hyOutside, hyConnect⟩⟩
    · intro hmember
      rw [P.clusterWithinSet_infinite_iff_orbitBox_escape]
      intro n
      have hn := Set.mem_iInter.1 hmember n
      obtain ⟨y, hy⟩ := Set.mem_iUnion.1 hn
      obtain ⟨hyOutside, hyConnect⟩ := Set.mem_iUnion.1 hy
      exact ⟨y, hyOutside, hyConnect⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun _hy =>
      P.connectedWithinSet_measurableSet A x y

/-- The event that the cluster of `x` inside `A` contains a vertex outside the orbit box of
radius `n`. -/
def PeriodicGraph.clusterWithinSetEscape
    (P : PeriodicGraph V) (A : Set V) (x : V) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ y : V, ⋃ (_hy : y ∉ (P.orbitBox n : Set V)),
    P.connectedWithinSet A x y

lemma PeriodicGraph.clusterWithinSetEscape_measurableSet
    (P : PeriodicGraph V) (A : Set V) (x : V) (n : Nat) :
    MeasurableSet (P.clusterWithinSetEscape A x n) :=
  MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
    P.connectedWithinSet_measurableSet A x y

omit [Countable V] in
lemma PeriodicGraph.clusterWithinSetEscape_antitone
    (P : PeriodicGraph V) (A : Set V) (x : V) :
    Antitone (P.clusterWithinSetEscape A x) := by
  intro n N hnN omega homega
  obtain ⟨y, hyOutside, hyConnect⟩ := by
    simpa only [PeriodicGraph.clusterWithinSetEscape,
      Set.mem_iUnion] using homega
  have hyOutsideSmall : y ∉ (P.orbitBox n : Set V) := by
    intro hySmall
    exact hyOutside (P.orbitBox_mono hnN hySmall)
  simp only [PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
  exact ⟨y, hyOutsideSmall, hyConnect⟩

omit [Countable V] in
/-- The escape events decrease to the event that the restricted cluster is infinite. -/
lemma PeriodicGraph.iInter_clusterWithinSetEscape
    (P : PeriodicGraph V) (A : Set V) (x : V) :
    (⋂ n : Nat, P.clusterWithinSetEscape A x n) =
      {omega : ConfigSpace (Sym2 V) |
        (P.clusterWithinSet omega A x).Infinite} := by
  ext omega
  rw [Set.mem_iInter, Set.mem_ofPred_eq,
    P.clusterWithinSet_infinite_iff_orbitBox_escape]
  constructor
  · intro h n
    obtain ⟨y, hyOutside, hyConnect⟩ := by
      simpa only [PeriodicGraph.clusterWithinSetEscape,
        Set.mem_iUnion] using h n
    exact ⟨y, hyOutside, hyConnect⟩
  · intro h n
    obtain ⟨y, hyOutside, hyConnect⟩ := h n
    simp only [PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
    exact ⟨y, hyOutside, hyConnect⟩

lemma PeriodicGraph.clusterWithinSetEscape_measureReal_tendsto
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (A : Set V) (x : V) :
    Tendsto (fun n => mu.real (P.clusterWithinSetEscape A x n))
      atTop (nhds (mu.real {omega : ConfigSpace (Sym2 V) |
        (P.clusterWithinSet omega A x).Infinite})) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (P.clusterWithinSetEscape A x n)) atTop
      (nhds (mu (⋂ n : Nat, P.clusterWithinSetEscape A x n))) :=
    tendsto_measure_iInter_atTop
      (fun n => (P.clusterWithinSetEscape_measurableSet A x n).nullMeasurableSet)
      (P.clusterWithinSetEscape_antitone A x)
      ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_clusterWithinSetEscape A x] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

/-! ## C. Infinite clusters within a region -/

/-- Some vertex of `A` has an infinite open cluster inside `A`. -/
def PeriodicGraph.HasInfiniteClusterWithin
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) : Prop :=
  ∃ x ∈ A, (P.clusterWithinSet omega A x).Infinite

omit [Countable V] in
lemma PeriodicGraph.hasInfiniteClusterWithin_mono
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    {A B : Set V} (hAB : A ⊆ B) :
    P.HasInfiniteClusterWithin omega A →
      P.HasInfiniteClusterWithin omega B := by
  rintro ⟨x, hxA, hinfinite⟩
  refine ⟨x, hAB hxA, hinfinite.mono ?_⟩
  intro y hy
  exact P.connectedWithinSet_mono_region hAB x y hy

omit [Countable V] in
lemma PeriodicGraph.hasInfiniteClusterWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A : Set V) :
    P.HasInfiniteClusterWithin (P.configTranslate z omega)
        (P.shift z '' A) ↔
      P.HasInfiniteClusterWithin omega A := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hinfinite⟩
    refine ⟨x, hx, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x] at hinfinite
    exact hinfinite.of_image (P.shift z)
  · rintro ⟨x, hx, hinfinite⟩
    refine ⟨P.shift z x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x]
    exact hinfinite.image (P.shift z).injective.injOn

lemma PeriodicGraph.measurableSet_hasInfiniteClusterWithin
    (P : PeriodicGraph V) (A : Set V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteClusterWithin omega A} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteClusterWithin omega A} =
      ⋃ x : V, ⋃ (_hx : x ∈ A),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega A x).Infinite} := by
    ext omega
    simp [PeriodicGraph.HasInfiniteClusterWithin]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    P.measurableSet_clusterWithinSet_infinite A x

/-- Some vertex of `S` has an infinite open cluster inside `A`. -/
def PeriodicGraph.setHitsInfiniteWithin
    (P : PeriodicGraph V) (A S : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.clusterWithinSet omega A x).Infinite}

omit [Countable V] in
lemma PeriodicGraph.setHitsInfiniteWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A S : Set V) :
    P.configTranslate z omega ∈ P.setHitsInfiniteWithin
        (P.shift z '' A) (P.shift z '' S) ↔
      omega ∈ P.setHitsInfiniteWithin A S := by
  constructor
  · rintro ⟨_, ⟨x, hxS, rfl⟩, hinfinite⟩
    refine ⟨x, hxS, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x] at hinfinite
    exact hinfinite.of_image (P.shift z)
  · rintro ⟨x, hxS, hinfinite⟩
    refine ⟨P.shift z x, ⟨x, hxS, rfl⟩, ?_⟩
    rw [← P.clusterWithinSet_configTranslate z omega A x]
    exact hinfinite.image (P.shift z).injective.injOn

lemma PeriodicGraph.setHitsInfiniteWithin_measurableSet
    (P : PeriodicGraph V) (A S : Set V) :
    MeasurableSet (P.setHitsInfiniteWithin A S) := by
  have heq : P.setHitsInfiniteWithin A S =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega A x).Infinite} := by
    ext omega
    simp [PeriodicGraph.setHitsInfiniteWithin]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    P.measurableSet_clusterWithinSet_infinite A x

lemma PeriodicGraph.setHitsInfiniteWithin_translate_measureReal_eq
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (A S : Set V) :
    mu.real (P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) =
      mu.real (P.setHitsInfiniteWithin A S) := by
  have hpre : P.configTranslate z ⁻¹'
      P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S) =
        P.setHitsInfiniteWithin A S := by
    ext omega
    exact P.setHitsInfiniteWithin_configTranslate z omega A S
  calc
    mu.real (P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) =
        mu.real (P.configTranslate z ⁻¹'
          P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) := by
      exact congrArg ENNReal.toReal ((hTI z).measure_preimage
        (P.setHitsInfiniteWithin_measurableSet
          (P.shift z '' A) (P.shift z '' S)).nullMeasurableSet).symm
    _ = mu.real (P.setHitsInfiniteWithin A S) := by rw [hpre]

/-! ## D. The half-plane infinite-cluster event -/

/-- The right half-plane `H_r = {x ≥ r}` contains an infinite open cluster of the configuration
restricted to `H_r`. -/
def PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | P.HasInfiniteClusterWithin omega
    (E.rightHalfPlaneVertices r)}

omit [Countable V] in
lemma PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (r : Real) :
    P.shift z '' E.rightHalfPlaneVertices r =
      E.rightHalfPlaneVertices (r + z 0) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change r + (z 0 : Real) ≤ E.vertexCoord (P.shift z u) 0
    rw [E.vertexCoord_shift]
    simpa [add_comm] using add_le_add_right hu (z 0 : Real)
  · intro hx
    let u := P.shift (-z) x
    have hux : P.shift z u = x := by simp [u]
    refine ⟨u, ?_, hux⟩
    change r ≤ E.vertexCoord u 0
    change r + (z 0 : Real) ≤ E.vertexCoord x 0 at hx
    rw [← hux, E.vertexCoord_shift] at hx
    exact le_of_add_le_add_right hx

omit [Countable V] in
lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_translate_preimage
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (r : Real) :
    P.configTranslate z ⁻¹'
        E.rightHalfPlaneHasInfiniteCluster (r + z 0) =
      E.rightHalfPlaneHasInfiniteCluster r := by
  ext omega
  change P.HasInfiniteClusterWithin (P.configTranslate z omega)
      (E.rightHalfPlaneVertices (r + z 0)) ↔
    P.HasInfiniteClusterWithin omega (E.rightHalfPlaneVertices r)
  rw [← E.shift_image_rightHalfPlaneVertices z r]
  exact P.hasInfiniteClusterWithin_configTranslate z omega
    (E.rightHalfPlaneVertices r)

lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    MeasurableSet (E.rightHalfPlaneHasInfiniteCluster r) :=
  P.measurableSet_hasInfiniteClusterWithin (E.rightHalfPlaneVertices r)

omit [Countable V] in
lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_antitone
    (E : PeriodicPlaneEmbedding P) :
    Antitone E.rightHalfPlaneHasInfiniteCluster := by
  intro r s hrs omega homega
  exact P.hasInfiniteClusterWithin_mono omega
    (fun v hv => hrs.trans hv) homega

lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (r : Real) :
    mu (E.rightHalfPlaneHasInfiniteCluster (r + z 0)) =
      mu (E.rightHalfPlaneHasInfiniteCluster r) := by
  rw [← E.rightHalfPlaneHasInfiniteCluster_translate_preimage z r]
  exact ((hTI z).measure_preimage
    (E.rightHalfPlaneHasInfiniteCluster_measurableSet
      (r + z 0)).nullMeasurableSet).symm

/-- Under a translation-invariant measure the probability that `H_r` contains an infinite cluster
does not depend on `r`. -/
lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (r s : Real) :
    mu (E.rightHalfPlaneHasInfiniteCluster r) =
      mu (E.rightHalfPlaneHasInfiniteCluster s) := by
  wlog hrs : r ≤ s generalizing r s
  · exact (this s r (le_of_not_ge hrs)).symm
  obtain ⟨n, hn⟩ := exists_nat_ge (s - r)
  let z : Site 2 := fun i => if i = 0 then (n : Int) else 0
  have hz0 : (z 0 : Real) = n := by simp [z]
  have hsn : s ≤ r + (z 0 : Real) := by
    rw [hz0]
    linarith
  have hperiod := E.rightHalfPlaneHasInfiniteCluster_measure_eq mu hTI z r
  apply le_antisymm
  · rw [← hperiod]
    exact measure_mono
      (E.rightHalfPlaneHasInfiniteCluster_antitone hsn)
  · exact measure_mono
      (E.rightHalfPlaneHasInfiniteCluster_antitone hrs)

/-- Every right half-plane `H_n`, `n ∈ ℕ`, contains an infinite cluster; a translation-invariant
event. -/
def PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity
    (E : PeriodicPlaneEmbedding P) : Set (ConfigSpace (Sym2 V)) :=
  ⋂ n : Nat, E.rightHalfPlaneHasInfiniteCluster n

lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet
    (E : PeriodicPlaneEmbedding P) :
    MeasurableSet E.rightHalfPlaneHasInfiniteClusterAtInfinity :=
  MeasurableSet.iInter fun n =>
    E.rightHalfPlaneHasInfiniteCluster_measurableSet n

omit [Countable V] in
lemma PeriodicPlaneEmbedding.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) :
    omega ∈ E.rightHalfPlaneHasInfiniteClusterAtInfinity ↔
      ∀ r : Real, omega ∈ E.rightHalfPlaneHasInfiniteCluster r := by
  constructor
  · intro h r
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact E.rightHalfPlaneHasInfiniteCluster_antitone hn
      (Set.mem_iInter.1 h n)
  · intro h
    rw [PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity,
      Set.mem_iInter]
    exact fun n => h n

omit [Countable V] in
lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage
    (E : PeriodicPlaneEmbedding P) (z : Site 2) :
    P.configTranslate z ⁻¹'
        E.rightHalfPlaneHasInfiniteClusterAtInfinity =
      E.rightHalfPlaneHasInfiniteClusterAtInfinity := by
  ext omega
  rw [Set.mem_preimage,
    E.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff,
    E.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff]
  constructor
  · intro h r
    have hz := h (r + (z 0 : Real))
    have hpre := E.rightHalfPlaneHasInfiniteCluster_translate_preimage z r
    exact (Set.ext_iff.1 hpre omega).1 hz
  · intro h r
    have hz := h (r - (z 0 : Real))
    have hpre := E.rightHalfPlaneHasInfiniteCluster_translate_preimage
      z (r - (z 0 : Real))
    have hr : r - (z 0 : Real) + z 0 = r := by ring
    rw [hr] at hpre
    exact (Set.ext_iff.1 hpre omega).2 hz

lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r : Real) :
    mu E.rightHalfPlaneHasInfiniteClusterAtInfinity =
      mu (E.rightHalfPlaneHasInfiniteCluster r) := by
  let A : Nat → Set (ConfigSpace (Sym2 V)) := fun n =>
    E.rightHalfPlaneHasInfiniteCluster (n : Real)
  have hraw := tendsto_measure_iInter_atTop (μ := mu) (s := A)
    (fun n => (E.rightHalfPlaneHasInfiniteCluster_measurableSet n).nullMeasurableSet)
    (fun _ _ h => E.rightHalfPlaneHasInfiniteCluster_antitone
      (by exact_mod_cast h))
    ⟨0, measure_ne_top mu _⟩
  have hinter : (⋂ n : Nat, A n) =
      E.rightHalfPlaneHasInfiniteClusterAtInfinity := rfl
  rw [hinter] at hraw
  have hmeasure : Tendsto
      (fun n : Nat => mu (E.rightHalfPlaneHasInfiniteCluster n)) atTop
      (nhds (mu E.rightHalfPlaneHasInfiniteClusterAtInfinity)) := by
    exact hraw
  have hconstant : Tendsto
      (fun n : Nat => mu (E.rightHalfPlaneHasInfiniteCluster n)) atTop
      (nhds (mu (E.rightHalfPlaneHasInfiniteCluster r))) := by
    have hfun : (fun n : Nat =>
        mu (E.rightHalfPlaneHasInfiniteCluster n)) =
        fun _n : Nat => mu (E.rightHalfPlaneHasInfiniteCluster r) := by
      funext n
      exact E.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary
        mu hTI n r
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hmeasure hconstant

/-- Zero–one law: under an ergodic measure, the right half-plane contains an infinite cluster
with probability zero or one. -/
theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hErgodic : P.IsErgodic mu) (r : Real) :
    mu (E.rightHalfPlaneHasInfiniteCluster r) = 0 ∨
      mu (E.rightHalfPlaneHasInfiniteCluster r) = 1 := by
  have htail := hErgodic.2
    E.rightHalfPlaneHasInfiniteClusterAtInfinity
    E.rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet
    E.rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage
  rw [E.rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq
    mu hErgodic.1 r] at htail
  exact htail

omit [Countable V] in
lemma PeriodicPlaneEmbedding.iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    (⋃ n : Nat, P.setHitsInfiniteWithin (E.rightHalfPlaneVertices r)
      ((P.orbitBox n : Set V) ∩ E.rightHalfPlaneVertices r)) =
        E.rightHalfPlaneHasInfiniteCluster r := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, x, hx, hinfinite⟩ := by
      simpa only [Set.mem_iUnion, PeriodicGraph.setHitsInfiniteWithin,
        Set.mem_ofPred_eq] using h
    exact ⟨x, hx.2, hinfinite⟩
  · rintro ⟨x, hxHalfPlane, hinfinite⟩
    obtain ⟨n, hxBox⟩ := P.exists_mem_orbitBox x
    apply Set.mem_iUnion.2
    exact ⟨n, x, ⟨hxBox, hxHalfPlane⟩, hinfinite⟩

omit [Countable V] in
lemma PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_of_orbitBox
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (r : Real)
    (hzero : ∀ n : Nat, mu (P.setHitsInfiniteWithin
      (E.rightHalfPlaneVertices r)
      ((P.orbitBox n : Set V) ∩ E.rightHalfPlaneVertices r)) = 0) :
    mu (E.rightHalfPlaneHasInfiniteCluster r) = 0 := by
  rw [← E.iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane r]
  exact measure_iUnion_null hzero

/-- If `H_r` almost surely has no infinite cluster, the probability that the cluster of a fixed
vertex inside `H_r` leaves the box of radius `n` tends to zero. -/
lemma PeriodicPlaneEmbedding.rightHalfPlane_vertexEscape_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (x : V) (hx : x ∈ E.rightHalfPlaneVertices r)
    (hnoInfinite : mu (E.rightHalfPlaneHasInfiniteCluster r) = 0) :
    Tendsto (fun n => mu.real
      (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n))
      atTop (nhds 0) := by
  have hsubset : {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) x).Infinite} ⊆
        E.rightHalfPlaneHasInfiniteCluster r := by
    intro omega hinfinite
    exact ⟨x, hx, hinfinite⟩
  have hzero : mu.real {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) x).Infinite} =
        0 := by
    rw [Measure.real, measure_mono_null hsubset hnoInfinite]
    rfl
  simpa [hzero] using P.clusterWithinSetEscape_measureReal_tendsto
    mu (E.rightHalfPlaneVertices r) x

/-! ## E. Escape from finite sets -/

/-- Some vertex of the finite set `L` has its cluster inside `A` reaching outside the orbit box
of radius `n`. -/
def PeriodicGraph.finiteSetEscapeWithin
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ L, P.clusterWithinSetEscape A x n

lemma PeriodicGraph.finiteSetEscapeWithin_measurableSet
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) (n : Nat) :
    MeasurableSet (P.finiteSetEscapeWithin A L n) :=
  L.measurableSet_biUnion fun x _hx =>
    P.clusterWithinSetEscape_measurableSet A x n

omit [Countable V] in
lemma PeriodicGraph.iInter_finiteSetEscapeWithin
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) :
    (⋂ n : Nat, P.finiteSetEscapeWithin A L n) =
      P.setHitsInfiniteWithin A (L : Set V) := by
  classical
  ext omega
  constructor
  · intro hescape
    by_contra hnot
    have hfinite (x : V) (hx : x ∈ L) :
        ¬(P.clusterWithinSet omega A x).Infinite := by
      intro hinfinite
      apply hnot
      exact ⟨x, by simpa using hx, hinfinite⟩
    have hexists (x : V) (hx : x ∈ L) : ∃ n : Nat,
        omega ∉ P.clusterWithinSetEscape A x n := by
      by_contra hall
      push Not at hall
      apply hfinite x hx
      rw [P.clusterWithinSet_infinite_iff_orbitBox_escape]
      intro n
      have hn := hall n
      obtain ⟨y, hyOutside, hyConnect⟩ := by
        simpa only [PeriodicGraph.clusterWithinSetEscape,
          Set.mem_iUnion] using hn
      exact ⟨y, hyOutside, hyConnect⟩
    let cutoff : V → Nat := fun x =>
      if hx : x ∈ L then (hexists x hx).choose else 0
    have hcutoff (x : V) (hx : x ∈ L) :
        omega ∉ P.clusterWithinSetEscape A x (cutoff x) := by
      simpa [cutoff, hx] using (hexists x hx).choose_spec
    let N : Nat := ∑ x ∈ L, cutoff x
    have hN := Set.mem_iInter.1 hescape N
    simp only [PeriodicGraph.finiteSetEscapeWithin, Set.mem_iUnion] at hN
    obtain ⟨x, hx, hxEscape⟩ := hN
    have hle : cutoff x ≤ N := by
      dsimp only [N]
      exact Finset.single_le_sum
        (fun y _hy => Nat.zero_le (cutoff y)) hx
    exact hcutoff x hx
      (P.clusterWithinSetEscape_antitone A x hle hxEscape)
  · rintro ⟨x, hxL, hinfinite⟩
    rw [Set.mem_iInter]
    intro n
    simp only [PeriodicGraph.finiteSetEscapeWithin, Set.mem_iUnion]
    refine ⟨x, by simpa using hxL, ?_⟩
    rw [P.clusterWithinSet_infinite_iff_orbitBox_escape] at hinfinite
    obtain ⟨y, hyOutside, hyConnect⟩ := hinfinite n
    simp only [PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
    exact ⟨y, hyOutside, hyConnect⟩

omit [Countable V] in
lemma PeriodicGraph.finiteSetEscapeWithin_antitone
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) :
    Antitone (P.finiteSetEscapeWithin A L) := by
  intro n N hnN omega homega
  simp only [PeriodicGraph.finiteSetEscapeWithin, Set.mem_iUnion] at homega ⊢
  obtain ⟨x, hx, hxEscape⟩ := homega
  exact ⟨x, hx, P.clusterWithinSetEscape_antitone A x hnN hxEscape⟩

lemma PeriodicGraph.finiteSetEscapeWithin_measureReal_tendsto
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (A : Set V) (L : Finset V) :
    Tendsto (fun n => mu.real (P.finiteSetEscapeWithin A L n))
      atTop (nhds (mu.real (P.setHitsInfiniteWithin A (L : Set V)))) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (P.finiteSetEscapeWithin A L n)) atTop
      (nhds (mu (⋂ n : Nat, P.finiteSetEscapeWithin A L n))) :=
    tendsto_measure_iInter_atTop
      (fun n => (P.finiteSetEscapeWithin_measurableSet A L n).nullMeasurableSet)
      (P.finiteSetEscapeWithin_antitone A L)
      ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_finiteSetEscapeWithin A L] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

/-- If `H_r` almost surely has no infinite cluster, escape of a fixed finite set in `H_r` from
large boxes has probability tending to zero. -/
lemma PeriodicPlaneEmbedding.rightHalfPlane_finiteSetEscape_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (L : Finset V)
    (hL : (L : Set V) ⊆ E.rightHalfPlaneVertices r)
    (hnoInfinite : mu (E.rightHalfPlaneHasInfiniteCluster r) = 0) :
    Tendsto (fun n => mu.real
      (P.finiteSetEscapeWithin (E.rightHalfPlaneVertices r) L n))
      atTop (nhds 0) := by
  have hsingle (x : V) (hx : x ∈ L) : Tendsto (fun n => mu.real
      (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n))
      atTop (nhds 0) :=
    E.rightHalfPlane_vertexEscape_measureReal_tendsto_zero
      mu r x (hL (by simpa using hx)) hnoInfinite
  have hsum : Tendsto (fun n => ∑ x ∈ L, mu.real
      (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum L (fun x hx => hsingle x hx)
  apply squeeze_zero
  · exact fun _ => measureReal_nonneg
  · intro n
    exact measureReal_biUnion_finset_le L
      (fun x => P.clusterWithinSetEscape
        (E.rightHalfPlaneVertices r) x n)
  · exact hsum

omit [Countable V] in
lemma PeriodicPlaneEmbedding.rectSideConnectionEvent_subset_finiteSetEscapeWithin
    (E : PeriodicPlaneEmbedding P)
    {a b c d : Real} {L : Finset V} {side A : Set V} {n : Nat}
    (hrect : E.rectVertices a b c d ⊆ A)
    (hside : side ⊆ (P.orbitBox n : Set V)ᶜ) :
    E.rectSideConnectionEvent a b c d (L : Set V) side ⊆
      P.finiteSetEscapeWithin A L n := by
  rintro omega ⟨x, hxL, _hxInfinite, y, hySide, hxy⟩
  simp only [PeriodicGraph.finiteSetEscapeWithin,
    PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
  refine ⟨x, hxL, y, hside hySide, ?_⟩
  exact P.connectedWithinSet_mono_region hrect x y hxy

omit [Countable V] in
/-- A rectangle side-connection event from `L` to a side outside a box is bounded by the escape
event of `L` from that box. -/
lemma PeriodicPlaneEmbedding.rectSideConnection_measureReal_le_finiteSetEscapeWithin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d : Real} {L : Finset V} {side A : Set V} {n : Nat}
    (hrect : E.rectVertices a b c d ⊆ A)
    (hside : side ⊆ (P.orbitBox n : Set V)ᶜ) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V) side) ≤
      mu.real (P.finiteSetEscapeWithin A L n) :=
  measureReal_mono
    (E.rectSideConnectionEvent_subset_finiteSetEscapeWithin hrect hside)

end StatMech.FK.PeriodicPlanar
