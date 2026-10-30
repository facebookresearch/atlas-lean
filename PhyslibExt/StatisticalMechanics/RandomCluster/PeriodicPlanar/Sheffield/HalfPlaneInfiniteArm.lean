/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneTranslation

/-!
# Infinite arms to the boundary of a half-plane

Events that a source set lies in an infinite cluster connected inside a region to a target set,
lower bounds for arms from sources in a half-plane to its boundary and boundary rays, and
vertically adjacent sources whose arms reach opposite boundary rays.

## i. Overview

`infiniteSetConnectionWithin A S T` is the event that some `x ∈ S` lies in an infinite cluster and
is connected within `A` to some vertex of `T`. For `A = H_r = {x ≥ r}` and `T = ∂H_r` this is an
"infinite arm" to the boundary. Under uniqueness and FKG its probability is at least
`P(S meets ∞) P(T' meets ∞)` for any `T'` outside `H_r`, hence tends to one along orbit boxes.
The boundary splits into the lower ray `{y ≤ s}` and the upper ray `{y ≥ s}`; arm probabilities
to rays increase to the boundary-arm probability as the cut moves, and are invariant under
vertical lattice translations. The FKG square-root trick gives, for the preferred ray,
`P(arm to ray) ≥ 1 - √(1 - P(arm to ∂H_r))`. A discrete crossover argument over vertical
translates produces a translate `z` such that the arm from `S + z e₂` to the lower ray and the arm
from `S + (z + 1) e₂` to the upper ray both have probability at least
`1 - √(1 - P(arm to ∂H_r)) - ε`.

Headline fidelity:
- `infiniteBoundaryConnection_measureReal_ge_mul` and the box and finite-source consequences are
  conditional on FKG, translation invariance (where used) and almost sure uniqueness.
- The square-root bounds are conditional on FKG and on the displayed preference hypothesis
  (`hpref`), which is a genuine assumption on the ordering of the two ray probabilities.
- `exists_adjacent_infiniteBoundaryRays_measureReal_ge`, `exists_twoStep_…` and
  `exists_separated_…` are conditional on FKG and translation invariance only; uniqueness is not
  needed.
- The ray exhaustions, vertical invariance and discrete crossover lemmas are unconditional.

## ii. Key results

- `PeriodicGraph.infiniteSetConnectionWithin`
- `PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_mul`
- `PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_measureReal_gt`
- `PeriodicPlaneEmbedding.exists_separated_infiniteBoundaryRays_measureReal_ge`

## iii. Table of contents

- A. Infinite-cluster connections within a region
- B. Arms to the half-plane boundary
- C. Arms to boundary rays
- D. Square-root bounds for the preferred ray
- E. Vertically translated sources
- F. Adjacent sources with arms to opposite rays

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §4 (FKG and the square-root trick).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Infinite-cluster connections within a region -/

/-- Infinite arm event: some `x ∈ S` lies in an infinite open cluster and is connected within `A`
to some vertex of `T`. -/
def PeriodicGraph.infiniteSetConnectionWithin
    (P : PeriodicGraph V) (A S T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite ∧
    ∃ y ∈ T, omega ∈ P.connectedWithinSet A x y}

lemma PeriodicGraph.infiniteSetConnectionWithin_measurableSet
    (P : PeriodicGraph V) (A S T : Set V) :
    MeasurableSet (P.infiniteSetConnectionWithin A S T) := by
  classical
  have heq : P.infiniteSetConnectionWithin A S T =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          ⋃ y : V, ⋃ (_hy : y ∈ T), P.connectedWithinSet A x y := by
    ext omega
    simp only [PeriodicGraph.infiniteSetConnectionWithin, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, hinf, y, hy, hxy⟩
      exact ⟨x, hx, hinf, y, hy, hxy⟩
    · rintro ⟨x, hx, hinf, y, hy, hxy⟩
      exact ⟨x, hx, hinf, y, hy, hxy⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    (P.measurableSet_cluster_infinite x).inter
      (MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
        P.connectedWithinSet_measurableSet A x y)

omit [Countable V] in
lemma PeriodicGraph.infiniteSetConnectionWithin_isIncreasing
    (P : PeriodicGraph V) (A S T : Set V) :
    IsIncreasing (P.infiniteSetConnectionWithin A S T) := by
  intro omega eta home
  rintro ⟨x, hx, hinf, y, hy, hxy⟩
  exact ⟨x, hx, P.clusterInfinite_isIncreasing x home hinf,
    y, hy, P.connectedWithinSet_isIncreasing A x y home hxy⟩

omit [Countable V] in
lemma PeriodicGraph.infiniteSetConnectionWithin_mono_target
    (P : PeriodicGraph V) (A S : Set V) {T U : Set V} (hTU : T ⊆ U) :
    P.infiniteSetConnectionWithin A S T ⊆
      P.infiniteSetConnectionWithin A S U := by
  rintro omega ⟨x, hx, hinf, y, hy, hxy⟩
  exact ⟨x, hx, hinf, y, hTU hy, hxy⟩

omit [Countable V] in
lemma PeriodicGraph.infiniteSetConnectionWithin_union_target
    (P : PeriodicGraph V) (A S T U : Set V) :
    P.infiniteSetConnectionWithin A S (T ∪ U) =
      P.infiniteSetConnectionWithin A S T ∪
        P.infiniteSetConnectionWithin A S U := by
  ext omega
  constructor
  · rintro ⟨x, hx, hinf, y, hy, hxy⟩
    rcases hy with hy | hy
    · exact Or.inl ⟨x, hx, hinf, y, hy, hxy⟩
    · exact Or.inr ⟨x, hx, hinf, y, hy, hxy⟩
  · rintro (h | h)
    · obtain ⟨x, hx, hinf, y, hy, hxy⟩ := h
      exact ⟨x, hx, hinf, y, Or.inl hy, hxy⟩
    · obtain ⟨x, hx, hinf, y, hy, hxy⟩ := h
      exact ⟨x, hx, hinf, y, Or.inr hy, hxy⟩

omit [Countable V] in
lemma PeriodicGraph.infiniteSetConnectionWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A S T : Set V) :
    P.configTranslate z omega ∈
        P.infiniteSetConnectionWithin (P.shift z '' A)
          (P.shift z '' S) (P.shift z '' T) ↔
      omega ∈ P.infiniteSetConnectionWithin A S T := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hinf, _, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨x, hx, (P.cluster_infinite_configTranslate z omega x).mp hinf,
      y, hy, (P.connectedWithinSet_configTranslate z omega A x y).mp hxy⟩
  · rintro ⟨x, hx, hinf, y, hy, hxy⟩
    exact ⟨P.shift z x, ⟨x, hx, rfl⟩,
      (P.cluster_infinite_configTranslate z omega x).mpr hinf,
      P.shift z y, ⟨y, hy, rfl⟩,
      (P.connectedWithinSet_configTranslate z omega A x y).mpr hxy⟩

/-! ## B. Arms to the half-plane boundary -/

omit [Countable V] in
/-- If the infinite cluster is unique and meets both `S ⊆ H_r` and `T ⊆ H_rᶜ`, then `S` has an
infinite arm to `∂H_r` within `H_r`. -/
lemma PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : ℝ) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩
        (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  rintro omega ⟨hunique, ⟨x, hxS, hxinf⟩, ⟨y, hyT, hyinf⟩⟩
  have hxH := hS hxS
  have hyH : y ∉ E.rightHalfPlaneVertices r := hT hyT
  have hxy : y ∈ P.cluster omega x := hunique.2 x y hxinf hyinf
  obtain ⟨b, hb, hxb⟩ :=
    E.connectedWithin_rightHalfPlane_boundary_of_reachable omega r hxH hyH hxy
  exact ⟨x, hxS, hxinf, b, hb, hxb⟩

/-- FKG lower bound for the infinite arm from `S ⊆ H_r` to `∂H_r`, assuming FKG and almost sure
uniqueness. -/
lemma PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_mul
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)) := by
  let U : Set (ConfigSpace (Sym2 V)) := {omega |
    P.HasUniqueInfiniteCluster omega}
  let A : Set (ConfigSpace (Sym2 V)) := P.setHitsInfinite S
  let B : Set (ConfigSpace (Sym2 V)) := P.setHitsInfinite T
  let C : Set (ConfigSpace (Sym2 V)) :=
    P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
      (E.rightHalfPlaneBoundaryVertices r)
  have hprod : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B (P.setHitsInfinite_measurableSet S)
      (P.setHitsInfinite_measurableSet T)
      (P.setHitsInfinite_isIncreasing S) (P.setHitsInfinite_isIncreasing T)
  have hUae : ∀ᵐ omega ∂mu, omega ∈ U :=
    (mem_ae_iff_prob_eq_one P.measurableSet_hasUniqueInfiniteCluster).2
      hunique
  have hABleC : (A ∩ B : Set (ConfigSpace (Sym2 V))) ≤ᵐ[mu] C := by
    filter_upwards [hUae] with omega hU hAB
    exact E.unique_two_sides_subset_infiniteBoundaryConnection r hS hT
      ⟨hU, hAB⟩
  have hmeasure : mu (A ∩ B) ≤ mu C := measure_mono_ae hABleC
  have hreal : mu.real (A ∩ B) ≤ mu.real C :=
    ENNReal.toReal_mono (measure_ne_top mu C) hmeasure
  exact hprod.trans hreal

lemma PeriodicGraph.infiniteSetConnectionWithin_translate_measureReal_eq
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (A S T : Set V) :
    mu.real (P.infiniteSetConnectionWithin (P.shift z '' A)
        (P.shift z '' S) (P.shift z '' T)) =
      mu.real (P.infiniteSetConnectionWithin A S T) := by
  let C := P.infiniteSetConnectionWithin (P.shift z '' A)
    (P.shift z '' S) (P.shift z '' T)
  have hpre : P.configTranslate z ⁻¹' C =
      P.infiniteSetConnectionWithin A S T := by
    ext omega
    exact P.infiniteSetConnectionWithin_configTranslate z omega A S T
  have hm := (hTI z).measure_preimage
    (P.infiniteSetConnectionWithin_measurableSet
      (P.shift z '' A) (P.shift z '' S) (P.shift z '' T)).nullMeasurableSet
  change mu.real C = _
  rw [hpre] at hm
  exact congrArg ENNReal.toReal hm.symm

lemma PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (S : Set V) (z : Site 2)
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    (mu.real (P.setHitsInfinite S)) ^ 2 ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)) := by
  have hmul := E.infiniteBoundaryConnection_measureReal_ge_mul mu hFKG
    hunique r hS hT
  rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z S] at hmul
  simpa [pow_two] using hmul

lemma PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (N : Nat) (z₀ : Site 2)
    (hinside : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
      E.rightHalfPlaneVertices r) :
    (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift z₀ '' (P.orbitBox N : Set V))
        (E.rightHalfPlaneBoundaryVertices r)) := by
  obtain ⟨zL, hzL⟩ := E.exists_shift_orbitBox_subset_leftComplement N r
  let S : Set V := P.shift z₀ '' (P.orbitBox N : Set V)
  let zRel := zL - z₀
  have houtside : P.shift zRel '' S ⊆
      (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hshift : P.shift zRel (P.shift z₀ v) = P.shift zL v := by
      rw [← P.shift_add]
      simp [zRel]
    rw [hshift]
    exact hzL v hv
  have hbound := E.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
    mu hFKG hTI hunique r S zRel hinside houtside
  have hmass : mu.real (P.setHitsInfinite S) =
      mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [S]
    rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
    rfl
  rw [hmass] at hbound
  exact hbound

/-- Finite sources in `H_r` whose infinite arm to `∂H_r` has probability tending to one (FKG,
translation invariance, almost sure uniqueness). -/
lemma PeriodicPlaneEmbedding.exists_infiniteBoundaryConnection_sequence_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) :
    ∃ S : ℕ → Set V,
      (∀ N, (S N).Finite) ∧
      (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧
      Tendsto (fun N => mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S N)
          (E.rightHalfPlaneBoundaryVertices r))) atTop (nhds 1) := by
  choose z₀ z₁ hinside houtside using fun N =>
    E.exists_opposite_translated_orbitBox N r
  let S : ℕ → Set V := fun N => P.shift (z₀ N) '' (P.orbitBox N : Set V)
  refine ⟨S, ?_, fun N => hinside N, ?_⟩
  · intro N
    exact (P.orbitBox N).finite_toSet.image (P.shift (z₀ N))
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hlower : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower (tendsto_const_nhds (x := (1 : ℝ)))
  · intro N
    have hsq := E.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
      mu hFKG hTI hunique r (S N) (z₁ N) (hinside N) (houtside N)
    have hmass : mu.real (P.setHitsInfinite (S N)) =
        mu.real (P.orbitBoxHitsInfinite N) := by
      dsimp only [S]
      rw [P.setHitsInfinite_translate_measureReal_eq mu hTI (z₀ N)]
      rfl
    rwa [hmass] at hsq
  · intro N
    exact measureReal_le_one

/-! ## C. Arms to boundary rays -/

omit [Countable V] in
lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Monotone (fun n : Nat =>
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r n)) := by
  intro n N hnN
  apply P.infiniteSetConnectionWithin_mono_target
  rintro y ⟨hyB, hy⟩
  refine ⟨hyB, ?_⟩
  change E.vertexCoord y 1 ≤ (n : Real) at hy
  change E.vertexCoord y 1 ≤ (N : Real)
  exact hy.trans (by exact_mod_cast hnN)

omit [Countable V] in
/-- Arms to the lower rays `{y ≤ n}` exhaust arms to `∂H_r`. Special case `s = 0` of
`iUnion_infiniteLowerBoundaryRay_connection_add` up to rewriting `0 + n`. -/
lemma PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r n)) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, x, hx, hinf, y, ⟨hyB, _hy⟩, hxy⟩ :=
      Set.mem_iUnion.mp homega
    exact ⟨x, hx, hinf, y, hyB, hxy⟩
  · rintro ⟨x, hx, hinf, y, hyB, hxy⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (E.vertexCoord y 1)
    exact Set.mem_iUnion.2 ⟨n, x, hx, hinf, y, ⟨hyB, hn⟩, hxy⟩

omit [Countable V] in
/-- Lower-ray arm probabilities converge to the boundary-arm probability. Special case `s = 0` of
`infiniteLowerBoundaryRay_measureReal_tendsto_add` up to rewriting. -/
lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r n))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.infiniteLowerBoundaryRay_connection_mono r S)
  rw [E.iUnion_infiniteLowerBoundaryRay_connection r S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

omit [Countable V] in
lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_neg
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Monotone (fun n : Nat =>
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (-(n : Real)))) := by
  intro n N hnN
  apply P.infiniteSetConnectionWithin_mono_target
  rintro y ⟨hyB, hy⟩
  refine ⟨hyB, ?_⟩
  change -(n : Real) ≤ E.vertexCoord y 1 at hy
  change -(N : Real) ≤ E.vertexCoord y 1
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  linarith

omit [Countable V] in
/-- Arms to the upper rays `{y ≥ -n}` exhaust arms to `∂H_r`. Special case `s = 0` of
`iUnion_infiniteUpperBoundaryRay_connection_sub` up to rewriting `0 - n`. -/
lemma PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_neg
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (-(n : Real)))) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, x, hx, hinf, y, ⟨hyB, _hy⟩, hxy⟩ :=
      Set.mem_iUnion.mp homega
    exact ⟨x, hx, hinf, y, hyB, hxy⟩
  · rintro ⟨x, hx, hinf, y, hyB, hxy⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (-E.vertexCoord y 1)
    have hy : -(n : Real) ≤ E.vertexCoord y 1 := by linarith
    exact Set.mem_iUnion.2 ⟨n, x, hx, hinf, y, ⟨hyB, hy⟩, hxy⟩

omit [Countable V] in
/-- Upper-ray arm probabilities converge to the boundary-arm probability. Special case `s = 0` of
`infiniteUpperBoundaryRay_measureReal_tendsto_sub` up to rewriting. -/
lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_neg
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (-(n : Real))))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.infiniteUpperBoundaryRay_connection_mono_neg r S)
  rw [E.iUnion_infiniteUpperBoundaryRay_connection_neg r S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

omit [Countable V] in
lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono_add
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    Monotone (fun n : Nat =>
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r (s + n))) := by
  intro n N hnN
  apply P.infiniteSetConnectionWithin_mono_target
  rintro y ⟨hyB, hy⟩
  refine ⟨hyB, ?_⟩
  change E.vertexCoord y 1 ≤ s + (n : Real) at hy
  change E.vertexCoord y 1 ≤ s + (N : Real)
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  linarith

omit [Countable V] in
lemma PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection_add
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    (⋃ n : Nat, P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r (s + n))) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, x, hx, hinf, y, ⟨hyB, _hy⟩, hxy⟩ :=
      Set.mem_iUnion.mp homega
    exact ⟨x, hx, hinf, y, hyB, hxy⟩
  · rintro ⟨x, hx, hinf, y, hyB, hxy⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (E.vertexCoord y 1 - s)
    have hy : E.vertexCoord y 1 ≤ s + (n : Real) := by linarith
    exact Set.mem_iUnion.2 ⟨n, x, hx, hinf, y, ⟨hyB, hy⟩, hxy⟩

omit [Countable V] in
lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto_add
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r (s + n)))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.infiniteLowerBoundaryRay_connection_mono_add r s S)
  rw [E.iUnion_infiniteLowerBoundaryRay_connection_add r s S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

omit [Countable V] in
lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_sub
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    Monotone (fun n : Nat =>
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (s - n))) := by
  intro n N hnN
  apply P.infiniteSetConnectionWithin_mono_target
  rintro y ⟨hyB, hy⟩
  refine ⟨hyB, ?_⟩
  change s - (n : Real) ≤ E.vertexCoord y 1 at hy
  change s - (N : Real) ≤ E.vertexCoord y 1
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  linarith

omit [Countable V] in
lemma PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_sub
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    (⋃ n : Nat, P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (s - n))) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, x, hx, hinf, y, ⟨hyB, _hy⟩, hxy⟩ :=
      Set.mem_iUnion.mp homega
    exact ⟨x, hx, hinf, y, hyB, hxy⟩
  · rintro ⟨x, hx, hinf, y, hyB, hxy⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (s - E.vertexCoord y 1)
    have hy : s - (n : Real) ≤ E.vertexCoord y 1 := by linarith
    exact Set.mem_iUnion.2 ⟨n, x, hx, hinf, y, ⟨hyB, hy⟩, hxy⟩

omit [Countable V] in
lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_sub
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (s - n)))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.infiniteUpperBoundaryRay_connection_mono_sub r s S)
  rw [E.iUnion_infiniteUpperBoundaryRay_connection_sub r s S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int) (r s : Real) (S : Set V) :
    mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.lowerBoundaryRayVertices r (s + t))) =
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) := by
  have hpre : P.configTranslate (verticalShift t) ⁻¹'
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.lowerBoundaryRayVertices r (s + t)) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s) := by
    ext omega
    have h := P.infiniteSetConnectionWithin_configTranslate
      (verticalShift t) omega (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)
    rw [E.shift_image_rightHalfPlaneVertices_vertical,
      E.shift_image_lowerBoundaryRayVertices_vertical] at h
    exact h
  have hm := (hTI (verticalShift t)).measure_preimage
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
      (E.lowerBoundaryRayVertices r (s + t))).nullMeasurableSet
  rw [hpre] at hm
  exact congrArg ENNReal.toReal hm.symm

lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int) (r s : Real) (S : Set V) :
    mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.upperBoundaryRayVertices r (s + t))) =
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) := by
  have hpre : P.configTranslate (verticalShift t) ⁻¹'
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.upperBoundaryRayVertices r (s + t)) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s) := by
    ext omega
    have h := P.infiniteSetConnectionWithin_configTranslate
      (verticalShift t) omega (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)
    rw [E.shift_image_rightHalfPlaneVertices_vertical,
      E.shift_image_upperBoundaryRayVertices_vertical] at h
    exact h
  have hm := (hTI (verticalShift t)).measure_preimage
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
      (E.upperBoundaryRayVertices r (s + t))).nullMeasurableSet
  rw [hpre] at hm
  exact congrArg ENNReal.toReal hm.symm

lemma PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int) (r : Real) (S : Set V) :
    mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.rightHalfPlaneBoundaryVertices r)) =
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)) := by
  have hpre : P.configTranslate (verticalShift t) ⁻¹'
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.rightHalfPlaneBoundaryVertices r) =
      P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
    ext omega
    have h := P.infiniteSetConnectionWithin_configTranslate
      (verticalShift t) omega (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)
    rw [E.shift_image_rightHalfPlaneVertices_vertical,
      E.shift_image_rightHalfPlaneBoundaryVertices_vertical] at h
    exact h
  have hm := (hTI (verticalShift t)).measure_preimage
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
      (E.rightHalfPlaneBoundaryVertices r)).nullMeasurableSet
  rw [hpre] at hm
  exact congrArg ENNReal.toReal hm.symm

/-! ## D. Square-root bounds for the preferred ray -/

/-- Square-root trick: if the lower ray is preferred, its arm probability is at least `1 - √(1 -
P(arm to ∂H_r))` (FKG). Special case `ε = 0` of
`infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub` up to rewriting. -/
lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (r s : Real) (S : Set V)
    (hpref : mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s))) :
    1 - Real.sqrt (1 - mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r))) ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) := by
  have h := directional_sqrt_trick mu hFKG
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) hpref
  rw [← P.infiniteSetConnectionWithin_union_target,
    ← E.boundary_eq_lower_union_upper] at h
  exact h

/-- Square-root trick for a preferred upper ray (FKG). Special case `ε = 0` of
`infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub` up to rewriting. -/
lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (r s : Real) (S : Set V)
    (hpref : mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s))) :
    1 - Real.sqrt (1 - mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r))) ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) := by
  have h := directional_sqrt_trick mu hFKG
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) hpref
  rw [← P.infiniteSetConnectionWithin_union_target,
    Set.union_comm, ← E.boundary_eq_lower_union_upper] at h
  exact h

lemma PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (r s : Real) (S : Set V) {epsilon : Real}
    (hepsilon : 0 ≤ epsilon)
    (hpref : mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) + epsilon) :
    1 - Real.sqrt (1 - mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) := by
  let L := P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.lowerBoundaryRayVertices r s)
  let U := P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.upperBoundaryRayVertices r s)
  have hsqrt := measurable_sqrt_trick mu hFKG
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
  have hunion : L ∪ U = P.infiniteSetConnectionWithin
      (E.rightHalfPlaneVertices r) S
      (E.rightHalfPlaneBoundaryVertices r) := by
    dsimp only [L, U]
    rw [← P.infiniteSetConnectionWithin_union_target,
      ← E.boundary_eq_lower_union_upper]
  change 1 - Real.sqrt (1 - mu.real (L ∪ U)) ≤
      max (mu.real L) (mu.real U) at hsqrt
  rw [hunion] at hsqrt
  have hmax : max (mu.real L) (mu.real U) ≤ mu.real L + epsilon :=
    max_le (le_add_of_nonneg_right hepsilon) hpref
  change 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real L
  linarith

lemma PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (r s : Real) (S : Set V) {epsilon : Real}
    (hepsilon : 0 ≤ epsilon)
    (hpref : mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) + epsilon) :
    1 - Real.sqrt (1 - mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) := by
  let L := P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.lowerBoundaryRayVertices r s)
  let U := P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.upperBoundaryRayVertices r s)
  have hsqrt := measurable_sqrt_trick mu hFKG
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_isIncreasing
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s))
  have hunion : L ∪ U = P.infiniteSetConnectionWithin
      (E.rightHalfPlaneVertices r) S
      (E.rightHalfPlaneBoundaryVertices r) := by
    dsimp only [L, U]
    rw [← P.infiniteSetConnectionWithin_union_target,
      ← E.boundary_eq_lower_union_upper]
  change 1 - Real.sqrt (1 - mu.real (L ∪ U)) ≤
      max (mu.real L) (mu.real U) at hsqrt
  rw [hunion] at hsqrt
  have hmax : max (mu.real L) (mu.real U) ≤ mu.real U + epsilon :=
    max_le hpref (le_add_of_nonneg_right hepsilon)
  change 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤ mu.real U
  linarith

/-! ## E. Vertically translated sources -/

/-- Shifting the sources down, the arm probability to the lower ray `{y ≤ 0}` converges to the
boundary-arm probability. Special case `s = 0` of
`shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at`. -/
lemma PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift (-(n : Int))) '' S)
        (E.lowerBoundaryRayVertices r 0))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hbase := E.infiniteLowerBoundaryRay_measureReal_tendsto mu r S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.infiniteLowerBoundaryRay_measureReal_vertical
    mu hTI (-(n : Int)) r (n : Real) S
  simpa using hmove.symm

/-- Shifting the sources up, the arm probability to the upper ray `{y ≥ 0}` converges to the
boundary-arm probability. Special case `s = 0` of
`shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at`. -/
lemma PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift (n : Int)) '' S)
        (E.upperBoundaryRayVertices r 0))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hbase := E.infiniteUpperBoundaryRay_measureReal_tendsto_neg mu r S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.infiniteUpperBoundaryRay_measureReal_vertical
    mu hTI (n : Int) r (-(n : Real)) S
  simpa using hmove.symm

lemma PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift (-(n : Int))) '' S)
        (E.lowerBoundaryRayVertices r s))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hbase := E.infiniteLowerBoundaryRay_measureReal_tendsto_add mu r s S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.infiniteLowerBoundaryRay_measureReal_vertical
    mu hTI (-(n : Int)) r (s + (n : Real)) S
  simpa using hmove.symm

lemma PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift (n : Int)) '' S)
        (E.upperBoundaryRayVertices r s))) atTop
      (nhds (mu.real (P.infiniteSetConnectionWithin
        (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hbase := E.infiniteUpperBoundaryRay_measureReal_tendsto_sub mu r s S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.infiniteUpperBoundaryRay_measureReal_vertical
    mu hTI (n : Int) r (s - (n : Real)) S
  simpa using hmove.symm

/-- A finite source in `H_r` has an infinite arm to `∂H_r` with probability above `1 - ε`.
Special case `R = r` of `exists_finite_infiniteBoundaryConnection_with_margin_gt`
(`HalfPlaneInteriorArm`). -/
lemma PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ S : Set V, S.Finite ∧ S ⊆ E.rightHalfPlaneVertices r ∧
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r)) := by
  obtain ⟨S, hfinite, hsubset, ht⟩ :=
    E.exists_infiniteBoundaryConnection_sequence_tendsto_one
      mu hFKG hTI hunique r
  have hev : ∀ᶠ N in atTop, 1 - epsilon < mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (S N)
        (E.rightHalfPlaneBoundaryVertices r)) :=
    (tendsto_order.1 ht).1 (1 - epsilon) (sub_lt_self 1 hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  exact ⟨S N, hfinite N, hsubset N, hN⟩

/-- Finite sources in `H_r` with infinite arms to the lower ray `{y ≤ 0}` and to the upper ray
`{y ≥ 1}`, each with probability above `1 - ε` (FKG, translation invariance, almost sure
uniqueness). Special case `R = r` of
`exists_finite_opposite_infiniteBoundaryRays_with_margin_gt` (`HalfPlaneInteriorArm`). -/
theorem PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L R : Set V,
      L.Finite ∧ R.Finite ∧
      L ⊆ E.rightHalfPlaneVertices r ∧
      R ⊆ E.rightHalfPlaneVertices r ∧
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) L
          (E.lowerBoundaryRayVertices r 0)) ∧
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) R
          (E.upperBoundaryRayVertices r 1)) := by
  obtain ⟨S, hSfinite, hSH, hSmass⟩ :=
    E.exists_finite_infiniteBoundaryConnection_measureReal_gt
      mu hFKG hTI hunique r hepsilon
  have hlower :=
    E.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto mu hTI r S
  have hlowerEventually : ∀ᶠ n : Nat in atTop,
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (-(n : Int))) '' S)
          (E.lowerBoundaryRayVertices r 0)) :=
    (tendsto_order.1 hlower).1 (1 - epsilon) hSmass
  obtain ⟨nL, hnL⟩ := hlowerEventually.exists
  have hupper :=
    E.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto mu hTI r S
  have hupperEventually : ∀ᶠ n : Nat in atTop,
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (n : Int)) '' S)
          (E.upperBoundaryRayVertices r 0)) :=
    (tendsto_order.1 hupper).1 (1 - epsilon) hSmass
  obtain ⟨nR, hnR⟩ := hupperEventually.exists
  let L := P.shift (verticalShift (-(nL : Int))) '' S
  let R₀ := P.shift (verticalShift (nR : Int)) '' S
  let R := P.shift (verticalShift 1) '' R₀
  refine ⟨L, R, hSfinite.image _, (hSfinite.image _).image _, ?_, ?_, hnL, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (E.shift_mem_rightHalfPlaneVertices_vertical _ r x).mpr (hSH hx)
  · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact (E.shift_mem_rightHalfPlaneVertices_vertical 1 r _).mpr
      ((E.shift_mem_rightHalfPlaneVertices_vertical _ r y).mpr (hSH hy))
  · have hmove := E.infiniteUpperBoundaryRay_measureReal_vertical
      mu hTI 1 r 0 R₀
    have hmove' : mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift 1) '' R₀)
          (E.upperBoundaryRayVertices r 1)) =
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) R₀
          (E.upperBoundaryRayVertices r 0)) := by
      simpa using hmove
    change 1 - epsilon < mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift 1) '' R₀)
        (E.upperBoundaryRayVertices r 1))
    rw [hmove']
    exact hnR

/-! ## F. Adjacent sources with arms to opposite rays -/

/-- Discrete crossover: if the upper sequence is at most the lower one at `a` and at least it at
`a + k + 1`, the order flips between two consecutive indices. -/
lemma exists_adjacent_preference_crossover
    (lower upper : Nat → Real) (a k : Nat)
    (hstart : upper a ≤ lower a)
    (hend : lower (a + k + 1) ≤ upper (a + k + 1)) :
    ∃ t : Nat,
      a ≤ t ∧ t < a + k + 1 ∧
      upper t ≤ lower t ∧ lower (t + 1) ≤ upper (t + 1) := by
  induction k generalizing a with
  | zero =>
      exact ⟨a, le_rfl, by omega, hstart, by simpa using hend⟩
  | succ k ih =>
      by_cases hnext : lower (a + 1) ≤ upper (a + 1)
      · exact ⟨a, le_rfl, by omega, hstart, hnext⟩
      · have hnext' : upper (a + 1) ≤ lower (a + 1) :=
          le_of_lt (lt_of_not_ge hnext)
        have hend' : lower ((a + 1) + k + 1) ≤
            upper ((a + 1) + k + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
        obtain ⟨t, hat, htb, ht, htnext⟩ := ih (a + 1) hnext' hend'
        exact ⟨t, by omega, by omega, ht, htnext⟩

/-- Discrete crossover with tolerance `ε`. Generalizes `exists_adjacent_preference_crossover`
(the case `ε = 0` up to rewriting). -/
lemma exists_adjacent_approximate_preference_crossover
    (lower upper : Nat → Real) (epsilon : Real) (a k : Nat)
    (hepsilon : 0 ≤ epsilon)
    (hstart : upper a ≤ lower a + epsilon)
    (hend : lower (a + k + 1) ≤ upper (a + k + 1) + epsilon) :
    ∃ t : Nat,
      a ≤ t ∧ t < a + k + 1 ∧
      upper t ≤ lower t + epsilon ∧
        lower (t + 1) ≤ upper (t + 1) + epsilon := by
  induction k generalizing a with
  | zero =>
      exact ⟨a, le_rfl, by omega, hstart, by simpa using hend⟩
  | succ k ih =>
      by_cases hnext : lower (a + 1) ≤ upper (a + 1) + epsilon
      · exact ⟨a, le_rfl, by omega, hstart, hnext⟩
      · have hnext' : upper (a + 1) ≤ lower (a + 1) + epsilon := by
          have hlt := lt_of_not_ge hnext
          linarith
        have hend' : lower ((a + 1) + k + 1) ≤
            upper ((a + 1) + k + 1) + epsilon := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
        obtain ⟨t, hat, htb, ht, htnext⟩ := ih (a + 1) hnext' hend'
        exact ⟨t, by omega, by omega, ht, htnext⟩

/-- Vertical lattice shifts add. -/
lemma verticalShift_add (a b : Int) :
    verticalShift (a + b) = verticalShift a + verticalShift b := by
  ext i
  fin_cases i <;> simp [verticalShift]

omit [Countable V] in
lemma PeriodicGraph.shift_image_vertical_add
    (P : PeriodicGraph V) (a b : Int) (S : Set V) :
    P.shift (verticalShift b) '' (P.shift (verticalShift a) '' S) =
      P.shift (verticalShift (a + b)) '' S := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [← P.shift_add, verticalShift_add]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨P.shift (verticalShift a) x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← P.shift_add, verticalShift_add]

/-- Some vertical translate `S + z e₂` has an arm to the lower ray `{y ≤ s}` and `S + (z + 1) e₂`
has an arm to the upper ray `{y ≥ s}`, each with probability at least `1 - √(1 - P(arm to
∂H_r)) - ε` (FKG, translation invariance). Special case `t = 0` of
`exists_separated_infiniteBoundaryRays_measureReal_ge` up to rewriting. -/
lemma PeriodicPlaneEmbedding.exists_adjacent_infiniteBoundaryRays_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (r s : Real) (S : Set V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Int,
      1 - Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
            (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift z) '' S)
          (E.lowerBoundaryRayVertices r s)) ∧
      1 - Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
            (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (z + 1)) '' S)
          (E.upperBoundaryRayVertices r s)) := by
  let F := mu.real (P.infiniteSetConnectionWithin
    (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))
  let lower : Int → Real := fun t => mu.real
    (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
      (P.shift (verticalShift t) '' S) (E.lowerBoundaryRayVertices r s))
  let upper : Int → Real := fun t => mu.real
    (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
      (P.shift (verticalShift t) '' S) (E.upperBoundaryRayVertices r s))
  have hlowerT : Tendsto (fun n : Nat => lower (-(n : Int))) atTop (nhds F) := by
    simpa only [lower, F] using
      E.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at mu hTI r s S
  have hupperT : Tendsto (fun n : Nat => upper (n : Int)) atTop (nhds F) := by
    simpa only [upper, F] using
      E.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at mu hTI r s S
  have hlowerEv : ∀ᶠ n : Nat in atTop, F - epsilon < lower (-(n : Int)) :=
    (tendsto_order.1 hlowerT).1 (F - epsilon) (sub_lt_self F hepsilon)
  have hupperEv : ∀ᶠ n : Nat in atTop, F - epsilon < upper (n : Int) :=
    (tendsto_order.1 hupperT).1 (F - epsilon) (sub_lt_self F hepsilon)
  have hboth : ∀ᶠ n : Nat in atTop,
      1 ≤ n ∧ F - epsilon < lower (-(n : Int)) ∧
        F - epsilon < upper (n : Int) := by
    filter_upwards [eventually_ge_atTop 1, hlowerEv, hupperEv] with n hn hl hu
    exact ⟨hn, hl, hu⟩
  obtain ⟨N, hN, hNlower, hNupper⟩ := hboth.exists
  have hlower_le (t : Int) : lower t ≤ F := by
    calc
      lower t ≤ mu.real (P.infiniteSetConnectionWithin
          (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
          (E.rightHalfPlaneBoundaryVertices r)) :=
        measureReal_mono (P.infiniteSetConnectionWithin_mono_target
          (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
          (fun _ hy => hy.1))
      _ = F := by
        simpa only [F] using
          E.infiniteBoundaryConnection_measureReal_vertical mu hTI t r S
  have hupper_le (t : Int) : upper t ≤ F := by
    calc
      upper t ≤ mu.real (P.infiniteSetConnectionWithin
          (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
          (E.rightHalfPlaneBoundaryVertices r)) :=
        measureReal_mono (P.infiniteSetConnectionWithin_mono_target
          (E.rightHalfPlaneVertices r) (P.shift (verticalShift t) '' S)
          (fun _ hy => hy.1))
      _ = F := by
        simpa only [F] using
          E.infiniteBoundaryConnection_measureReal_vertical mu hTI t r S
  let f : Nat → Real := fun n => lower ((n : Int) - (N : Int))
  let g : Nat → Real := fun n => upper ((n : Int) - (N : Int))
  have hf0 : f 0 = lower (-(N : Int)) := by simp [f]
  have hg0 : g 0 = upper (-(N : Int)) := by simp [g]
  have hfend : f (2 * N) = lower (N : Int) := by
    simp only [f]
    congr 2
    omega
  have hgend : g (2 * N) = upper (N : Int) := by
    simp only [g]
    congr 2
    omega
  have hstart : g 0 ≤ f 0 + epsilon := by
    rw [hf0, hg0]
    have := hupper_le (-(N : Int))
    linarith
  have hend : f (2 * N) ≤ g (2 * N) + epsilon := by
    rw [hfend, hgend]
    have := hlower_le (N : Int)
    linarith
  let k := 2 * N - 1
  have hk : k + 1 = 2 * N := by dsimp only [k]; omega
  obtain ⟨t, _ht0, _htend, htLower, htUpper⟩ :=
    exists_adjacent_approximate_preference_crossover f g epsilon 0 k
      hepsilon.le (by simpa using hstart) (by simpa [hk] using hend)
  let z : Int := (t : Int) - (N : Int)
  refine ⟨z, ?_, ?_⟩
  · have hsqrt := E.infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub
      mu hFKG r s (P.shift (verticalShift z) '' S) hepsilon.le ?_
    · have hfull :=
        E.infiniteBoundaryConnection_measureReal_vertical mu hTI z r S
      rw [hfull] at hsqrt
      exact hsqrt
    · simpa only [lower, upper, z, f, g] using htLower
  · have hznext : ((t + 1 : Nat) : Int) - (N : Int) = z + 1 := by
      dsimp only [z]
      omega
    have hsqrt := E.infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub
      mu hFKG r s (P.shift (verticalShift (z + 1)) '' S) hepsilon.le ?_
    · have hfull := E.infiniteBoundaryConnection_measureReal_vertical
        mu hTI (z + 1) r S
      rw [hfull] at hsqrt
      exact hsqrt
    · simpa only [lower, upper, f, g, hznext] using htUpper

/-- Two-step version: arms from `S + z e₂` to `{y ≤ 0}` and from `S + (z + 2) e₂` to `{y ≥ 1}`.
Special case `s = 0`, `t = 1` of `exists_separated_infiniteBoundaryRays_measureReal_ge` up to
rewriting. -/
lemma PeriodicPlaneEmbedding.exists_twoStep_infiniteBoundaryRays_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (r : Real) (S : Set V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Int,
      1 - Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
            (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift z) '' S)
          (E.lowerBoundaryRayVertices r 0)) ∧
      1 - Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
            (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (z + 2)) '' S)
          (E.upperBoundaryRayVertices r 1)) := by
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_adjacent_infiniteBoundaryRays_measureReal_ge
      mu hFKG hTI r 0 S hepsilon
  refine ⟨z, hlower, ?_⟩
  have hmove := E.infiniteUpperBoundaryRay_measureReal_vertical
    mu hTI 1 r 0 (P.shift (verticalShift (z + 1)) '' S)
  have himage :
      P.shift (verticalShift 1) ''
          (P.shift (verticalShift (z + 1)) '' S) =
        P.shift (verticalShift (z + 2)) '' S := by
    rw [P.shift_image_vertical_add,
      show (z + 1) + 1 = z + 2 by omega]
  rw [himage] at hmove
  have hmove' :
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (z + 2)) '' S)
          (E.upperBoundaryRayVertices r 1)) =
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (z + 1)) '' S)
          (E.upperBoundaryRayVertices r 0)) := by
    simpa using hmove
  rwa [hmove']

/-- Separated version: some vertical translate `S + z e₂` has an arm to `{y ≤ s}` and `S + (z + 1
+ t) e₂` has an arm to `{y ≥ s + t}`, each with probability at least `1 - √(1 - P(arm to
∂H_r)) - ε` (FKG, translation invariance). -/
theorem PeriodicPlaneEmbedding.exists_separated_infiniteBoundaryRays_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (r s : Real) (t : Int) (S : Set V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Int,
      1 - Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
            (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift z) '' S)
          (E.lowerBoundaryRayVertices r s)) ∧
      1 - Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
            (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift (z + 1 + t)) '' S)
          (E.upperBoundaryRayVertices r (s + t))) := by
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_adjacent_infiniteBoundaryRays_measureReal_ge
      mu hFKG hTI r s S hepsilon
  refine ⟨z, hlower, ?_⟩
  have hmove := E.infiniteUpperBoundaryRay_measureReal_vertical
    mu hTI t r s (P.shift (verticalShift (z + 1)) '' S)
  have himage :
      P.shift (verticalShift t) ''
          (P.shift (verticalShift (z + 1)) '' S) =
        P.shift (verticalShift (z + 1 + t)) '' S :=
    P.shift_image_vertical_add (z + 1) t S
  rw [himage] at hmove
  rwa [hmove]

end StatMech.FK.PeriodicPlanar
