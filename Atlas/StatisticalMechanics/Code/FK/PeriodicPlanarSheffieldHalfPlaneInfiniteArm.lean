/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



def PeriodicGraph.infiniteSetConnectionWithin
    (P : PeriodicGraph V) (A S T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite ∧
    ∃ y ∈ T, omega ∈ P.connectedWithinSet A x y}

theorem PeriodicGraph.infiniteSetConnectionWithin_measurableSet
    (P : PeriodicGraph V) (A S T : Set V) :
    MeasurableSet (P.infiniteSetConnectionWithin A S T) := by
  classical
  have heq : P.infiniteSetConnectionWithin A S T =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          ⋃ y : V, ⋃ (_hy : y ∈ T), P.connectedWithinSet A x y := by
    ext omega
    simp only [PeriodicGraph.infiniteSetConnectionWithin, Set.mem_setOf_eq,
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

theorem PeriodicGraph.infiniteSetConnectionWithin_isIncreasing
    (P : PeriodicGraph V) (A S T : Set V) :
    IsIncreasing (P.infiniteSetConnectionWithin A S T) := by
  intro omega eta home
  rintro ⟨x, hx, hinf, y, hy, hxy⟩
  exact ⟨x, hx, P.clusterInfinite_isIncreasing x home hinf,
    y, hy, P.connectedWithinSet_isIncreasing A x y home hxy⟩

theorem PeriodicGraph.infiniteSetConnectionWithin_mono_target
    (P : PeriodicGraph V) (A S : Set V) {T U : Set V} (hTU : T ⊆ U) :
    P.infiniteSetConnectionWithin A S T ⊆
      P.infiniteSetConnectionWithin A S U := by
  rintro omega ⟨x, hx, hinf, y, hy, hxy⟩
  exact ⟨x, hx, hinf, y, hTU hy, hxy⟩

theorem PeriodicGraph.infiniteSetConnectionWithin_union_target
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


theorem PeriodicGraph.infiniteSetConnectionWithin_configTranslate
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



theorem PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteBoundaryConnection
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



theorem PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_mul
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

theorem PeriodicGraph.infiniteSetConnectionWithin_translate_measureReal_eq
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

theorem PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
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



theorem PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift
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



theorem PeriodicPlaneEmbedding.exists_infiniteBoundaryConnection_sequence_tendsto_one
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



theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono
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

theorem PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection
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

theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto
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

theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_neg
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

theorem PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_neg
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

theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_neg
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



theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_connection_mono_add
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

theorem PeriodicPlaneEmbedding.iUnion_infiniteLowerBoundaryRay_connection_add
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

theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_tendsto_add
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

theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_connection_mono_sub
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

theorem PeriodicPlaneEmbedding.iUnion_infiniteUpperBoundaryRay_connection_sub
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

theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_tendsto_sub
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

theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_vertical
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

theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_vertical
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



theorem PeriodicPlaneEmbedding.infiniteBoundaryConnection_measureReal_vertical
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



theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt
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



theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt
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


theorem PeriodicPlaneEmbedding.infiniteLowerBoundaryRay_measureReal_ge_sqrt_sub
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


theorem PeriodicPlaneEmbedding.infiniteUpperBoundaryRay_measureReal_ge_sqrt_sub
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

theorem PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto
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

theorem PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto
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

theorem PeriodicPlaneEmbedding.shift_down_infiniteLowerBoundaryRay_measureReal_tendsto_at
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

theorem PeriodicPlaneEmbedding.shift_up_infiniteUpperBoundaryRay_measureReal_tendsto_at
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



theorem PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_measureReal_gt
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






theorem exists_adjacent_preference_crossover
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



theorem exists_adjacent_approximate_preference_crossover
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


theorem verticalShift_add (a b : Int) :
    verticalShift (a + b) = verticalShift a + verticalShift b := by
  ext i
  fin_cases i <;> simp [verticalShift]

theorem PeriodicGraph.shift_image_vertical_add
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




theorem PeriodicPlaneEmbedding.exists_adjacent_infiniteBoundaryRays_measureReal_ge
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



theorem PeriodicPlaneEmbedding.exists_twoStep_infiniteBoundaryRays_measureReal_ge
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
