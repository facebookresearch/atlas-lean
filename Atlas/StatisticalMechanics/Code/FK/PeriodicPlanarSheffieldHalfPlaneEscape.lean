/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FK.PeriodicPlanarSheffieldHalfPlane

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicGraph.mem_connectedWithinSet_of_walk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {A : Set V} {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hp : ∀ v ∈ p.support, v ∈ A) :
    omega ∈ P.connectedWithinSet A x y := by
  refine ⟨p.support.tail, ?_, ?_, ?_⟩
  · rw [p.cons_tail_support]
    exact p.isChain_adj_support
  · simpa only [p.cons_tail_support] using p.getLast_support
  · rwa [p.cons_tail_support]




theorem PeriodicPlaneEmbedding.exists_boundary_walk_of_walk_to_left
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r : ℝ)
    {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hx : x ∈ E.rightHalfPlaneVertices r)
    (hy : y ∉ E.rightHalfPlaneVertices r) :
    ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
      ∃ q : (P.openSubgraph omega).Walk x b,
        ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ E.rightHalfPlaneVertices r
      · obtain ⟨b, hb, q, hq⟩ := ih hz hy
        refine ⟨b, hb, q.cons hxz, ?_⟩
        intro v hv
        rw [SimpleGraph.Walk.support_cons] at hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hx
        · exact hq v hv
      · refine ⟨x, ?_, .nil, ?_⟩
        · refine ⟨hx, z, hxz.1, ?_⟩
          exact lt_of_not_ge hz
        · simpa using hx




theorem PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_boundary_of_reachable
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r : ℝ)
    {x y : V} (hx : x ∈ E.rightHalfPlaneVertices r)
    (hy : y ∉ E.rightHalfPlaneVertices r)
    (hxy : y ∈ P.cluster omega x) :
    ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
  obtain ⟨p⟩ := hxy
  obtain ⟨b, hb, q, hq⟩ :=
    E.exists_boundary_walk_of_walk_to_left omega r p hx hy
  exact ⟨b, hb, P.mem_connectedWithinSet_of_walk q hq⟩




def PeriodicGraph.setHitsInfinite
    (P : PeriodicGraph V) (S : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite}

theorem PeriodicGraph.setHitsInfinite_measurableSet
    (P : PeriodicGraph V) (S : Set V) :
    MeasurableSet (P.setHitsInfinite S) := by
  classical
  have heq : P.setHitsInfinite S =
      ⋃ x : V, if x ∈ S then
        {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega x).Infinite} else ∅ := by
    ext omega
    simp [PeriodicGraph.setHitsInfinite]
  rw [heq]
  exact MeasurableSet.iUnion fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using P.measurableSet_cluster_infinite x
    · simp [hx]

theorem PeriodicGraph.setHitsInfinite_isIncreasing
    (P : PeriodicGraph V) (S : Set V) :
    IsIncreasing (P.setHitsInfinite S) := by
  intro omega eta home
  rintro ⟨x, hx, hinf⟩
  exact ⟨x, hx, P.clusterInfinite_isIncreasing x home hinf⟩



theorem PeriodicGraph.setHitsInfinite_translate_preimage
    (P : PeriodicGraph V) (z : Site 2) (S : Set V) :
    P.configTranslate z ⁻¹' P.setHitsInfinite (P.shift z '' S) =
      P.setHitsInfinite S := by
  ext omega
  simp only [Set.mem_preimage, PeriodicGraph.setHitsInfinite,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, hinf⟩
    exact ⟨u, hu, (P.cluster_infinite_configTranslate z omega u).mp hinf⟩
  · rintro ⟨u, hu, hinf⟩
    exact ⟨P.shift z u, ⟨u, hu, rfl⟩,
      (P.cluster_infinite_configTranslate z omega u).mpr hinf⟩

theorem PeriodicGraph.setHitsInfinite_translate_measureReal_eq
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (S : Set V) :
    mu.real (P.setHitsInfinite (P.shift z '' S)) =
      mu.real (P.setHitsInfinite S) := by
  have hmeasure := (hTI z).measure_preimage
    (P.setHitsInfinite_measurableSet (P.shift z '' S)).nullMeasurableSet
  rw [P.setHitsInfinite_translate_preimage z S] at hmeasure
  exact congrArg ENNReal.toReal hmeasure.symm

@[simp] theorem PeriodicGraph.setHitsInfinite_orbitBox
    (P : PeriodicGraph V) (N : ℕ) :
    P.setHitsInfinite (P.orbitBox N : Set V) =
      P.orbitBoxHitsInfinite N := rfl



theorem PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_leftComplement
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) :
    ∃ z : Site 2, ∀ v ∈ P.orbitBox N,
      P.shift z v ∉ E.rightHalfPlaneVertices r := by
  classical
  let M : ℝ := ∑ v ∈ P.orbitBox N, |E.vertexCoord v 0 - r|
  obtain ⟨n, hn⟩ := exists_nat_ge M
  let z : Site 2 := fun _ => -((n + 1 : ℕ) : ℤ)
  refine ⟨z, ?_⟩
  intro v hv
  have hterm : |E.vertexCoord v 0 - r| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum
      (fun w _hw => abs_nonneg (E.vertexCoord w 0 - r)) hv
  have hdiff : E.vertexCoord v 0 - r ≤ M :=
    (le_abs_self (E.vertexCoord v 0 - r)).trans hterm
  change ¬ r ≤ E.vertexCoord (P.shift z v) 0
  rw [E.vertexCoord_shift]
  have hz : (z 0 : ℝ) = -(n + 1 : ℝ) := by simp [z]
  rw [hz]
  push_neg
  norm_num at *
  linarith




theorem PeriodicPlaneEmbedding.exists_opposite_translated_orbitBox
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) :
    ∃ z₀ z₁ : Site 2,
      P.shift z₀ '' (P.orbitBox N : Set V) ⊆
        E.rightHalfPlaneVertices r ∧
      P.shift z₁ '' (P.shift z₀ '' (P.orbitBox N : Set V)) ⊆
        (E.rightHalfPlaneVertices r)ᶜ := by
  obtain ⟨zR, hzR⟩ := E.exists_shift_orbitBox_subset_rightHalfPlane N r
  obtain ⟨zL, hzL⟩ := E.exists_shift_orbitBox_subset_leftComplement N r
  let zRel := zL - zR
  refine ⟨zR, zRel, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hzR v hv
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hshift : P.shift zRel (P.shift zR v) = P.shift zL v := by
      rw [← P.shift_add]
      simp [zRel]
    rw [hshift]
    exact hzL v hv




theorem PeriodicPlaneEmbedding.unique_two_sides_subset_boundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : ℝ) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩
        (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  rintro omega ⟨hunique, ⟨x, hxS, hxinf⟩, ⟨y, hyT, hyinf⟩⟩
  have hxH := hS hxS
  have hyH : y ∉ E.rightHalfPlaneVertices r := hT hyT
  have hxy : y ∈ P.cluster omega x := hunique.2 x y hxinf hyinf
  obtain ⟨b, hb, hxb⟩ :=
    E.connectedWithin_rightHalfPlane_boundary_of_reachable omega r hxH hyH hxy
  exact ⟨x, hxS, b, hb, hxb⟩





theorem PeriodicPlaneEmbedding.boundaryConnection_measureReal_ge_mul
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)) := by
  let U : Set (ConfigSpace (Sym2 V)) := {omega |
    P.HasUniqueInfiniteCluster omega}
  let A : Set (ConfigSpace (Sym2 V)) := P.setHitsInfinite S
  let B : Set (ConfigSpace (Sym2 V)) := P.setHitsInfinite T
  let C : Set (ConfigSpace (Sym2 V)) :=
    P.setConnectionWithin (E.rightHalfPlaneVertices r) S
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
    exact E.unique_two_sides_subset_boundaryConnection r hS hT
      ⟨hU, hAB⟩
  have hmeasure : mu (A ∩ B) ≤ mu C := measure_mono_ae hABleC
  have hreal : mu.real (A ∩ B) ≤ mu.real C :=
    ENNReal.toReal_mono (measure_ne_top mu C) hmeasure
  exact hprod.trans hreal



theorem PeriodicPlaneEmbedding.boundaryConnection_measureReal_ge_sq_of_translate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (S : Set V) (z : Site 2)
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    (mu.real (P.setHitsInfinite S)) ^ 2 ≤
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)) := by
  have hmul := E.boundaryConnection_measureReal_ge_mul mu hFKG
    hunique r hS hT
  rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z S] at hmul
  simpa [pow_two] using hmul





theorem PeriodicPlaneEmbedding.exists_boundaryConnection_ge_orbitBox_sq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (N : ℕ) :
    ∃ S : Set V, S ⊆ E.rightHalfPlaneVertices r ∧
      (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
        mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r)) := by
  obtain ⟨z₀, z₁, hinside, houtside⟩ :=
    E.exists_opposite_translated_orbitBox N r
  let S : Set V := P.shift z₀ '' (P.orbitBox N : Set V)
  refine ⟨S, hinside, ?_⟩
  have hsq := E.boundaryConnection_measureReal_ge_sq_of_translate
    mu hFKG hTI hunique r S z₁ hinside houtside
  have hmass : mu.real (P.setHitsInfinite S) =
      mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [S]
    rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
    rfl
  rwa [hmass] at hsq




theorem PeriodicPlaneEmbedding.exists_boundaryConnection_sequence_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) :
    ∃ S : ℕ → Set V,
      (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧
      Tendsto (fun N => mu.real
        (P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N)
          (E.rightHalfPlaneBoundaryVertices r))) atTop (nhds 1) := by
  choose S hS hbound using fun N =>
    E.exists_boundaryConnection_ge_orbitBox_sq mu hFKG hTI hunique r N
  refine ⟨S, hS, ?_⟩
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
  · exact hbound
  · intro N
    exact measureReal_le_one




theorem PeriodicPlaneEmbedding.exists_boundaryRay_max_sequence_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (s : ℕ → ℝ) :
    ∃ S : ℕ → Set V,
      (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧
      Tendsto (fun N => max
        (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N)
          (E.lowerBoundaryRayVertices r (s N))))
        (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N)
          (E.upperBoundaryRayVertices r (s N))))) atTop (nhds 1) := by
  obtain ⟨S, hS, hfull⟩ :=
    E.exists_boundaryConnection_sequence_tendsto_one mu hFKG hTI hunique r
  refine ⟨S, hS, ?_⟩
  let L : ℕ → Set (ConfigSpace (Sym2 V)) := fun N =>
    P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N)
      (E.lowerBoundaryRayVertices r (s N))
  let U : ℕ → Set (ConfigSpace (Sym2 V)) := fun N =>
    P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N)
      (E.upperBoundaryRayVertices r (s N))
  let F : ℕ → Set (ConfigSpace (Sym2 V)) := fun N =>
    P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N)
      (E.rightHalfPlaneBoundaryVertices r)
  have hFU : ∀ N, L N ∪ U N = F N := by
    intro N
    dsimp only [L, U, F]
    rw [← P.setConnectionWithin_union_target,
      ← E.boundary_eq_lower_union_upper]
  have hsqrt : ∀ N,
      1 - Real.sqrt (1 - mu.real (F N)) ≤
        max (mu.real (L N)) (mu.real (U N)) := by
    intro N
    have h := measurable_sqrt_trick mu hFKG
      (P.setConnectionWithin_isIncreasing (E.rightHalfPlaneVertices r) (S N)
        (E.lowerBoundaryRayVertices r (s N)))
      (P.setConnectionWithin_isIncreasing (E.rightHalfPlaneVertices r) (S N)
        (E.upperBoundaryRayVertices r (s N)))
      (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r) (S N)
        (E.lowerBoundaryRayVertices r (s N)))
      (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r) (S N)
        (E.upperBoundaryRayVertices r (s N)))
    change 1 - Real.sqrt (1 - mu.real (L N ∪ U N)) ≤
      max (mu.real (L N)) (mu.real (U N)) at h
    rwa [hFU N] at h
  have hfull' : Tendsto (fun N => mu.real (F N)) atTop (nhds 1) := by
    simpa only [F] using hfull
  have hmiss : Tendsto (fun N => 1 - mu.real (F N)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hfull'
  have hlower : Tendsto (fun N => 1 - Real.sqrt (1 - mu.real (F N)))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hmiss.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower (tendsto_const_nhds (x := (1 : ℝ)))
  · exact hsqrt
  · intro N
    exact max_le measureReal_le_one measureReal_le_one

end StatMech.FK.PeriodicPlanar
