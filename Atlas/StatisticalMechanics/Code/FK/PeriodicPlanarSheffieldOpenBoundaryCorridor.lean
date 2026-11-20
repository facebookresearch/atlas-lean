/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldOpenBoundarySource





open Filter MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_boundary_eq
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    E.infiniteOpenBoundaryConnectionTo r S
      (E.rightHalfPlaneBoundaryVertices r) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro h
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ h
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    exact ⟨x, hxS, hxInfinite, b, hb, hb, z, hbz, hz, hbzOpen, hxb⟩

theorem PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_mono_add
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    Monotone (fun n : Nat => E.infiniteOpenBoundaryConnectionTo r S
      (E.lowerBoundaryRayVertices r (s + n))) := by
  intro n N hnN omega
  rintro ⟨x, hxS, hxInfinite, b, hb, hbBoundary,
    z, hbz, hz, hbzOpen, hxb⟩
  refine ⟨x, hxS, hxInfinite, b, ?_, hbBoundary,
    z, hbz, hz, hbzOpen, hxb⟩
  have hbY := hb.2
  refine ⟨hb.1, ?_⟩
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  change E.vertexCoord b 1 ≤ s + (n : Real) at hbY
  change E.vertexCoord b 1 ≤ s + (N : Real)
  linarith

theorem PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection_add
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S
      (E.lowerBoundaryRayVertices r (s + n))) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, h⟩ := Set.mem_iUnion.1 homega
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ h
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (E.vertexCoord b 1 - s)
    have hbn : E.vertexCoord b 1 ≤ s + (n : Real) := by linarith
    exact Set.mem_iUnion.2 ⟨n, x, hxS, hxInfinite, b,
      ⟨hb, hbn⟩, hb, z, hbz, hz, hbzOpen, hxb⟩

theorem PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_tendsto_add
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (E.infiniteOpenBoundaryConnectionTo r S
        (E.lowerBoundaryRayVertices r (s + n)))) atTop
      (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.infiniteOpenLowerBoundaryConnection_mono_add r s S)
  rw [E.iUnion_infiniteOpenLowerBoundaryConnection_add r s S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

theorem PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_mono_sub
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    Monotone (fun n : Nat => E.infiniteOpenBoundaryConnectionTo r S
      (E.upperBoundaryRayVertices r (s - n))) := by
  intro n N hnN omega
  rintro ⟨x, hxS, hxInfinite, b, hb, hbBoundary,
    z, hbz, hz, hbzOpen, hxb⟩
  refine ⟨x, hxS, hxInfinite, b, ?_, hbBoundary,
    z, hbz, hz, hbzOpen, hxb⟩
  have hbY := hb.2
  refine ⟨hb.1, ?_⟩
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  change s - (n : Real) ≤ E.vertexCoord b 1 at hbY
  change s - (N : Real) ≤ E.vertexCoord b 1
  linarith

theorem PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection_sub
    (E : PeriodicPlaneEmbedding P) (r s : Real) (S : Set V) :
    (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S
      (E.upperBoundaryRayVertices r (s - n))) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, h⟩ := Set.mem_iUnion.1 homega
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ h
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (s - E.vertexCoord b 1)
    have hbn : s - (n : Real) ≤ E.vertexCoord b 1 := by linarith
    exact Set.mem_iUnion.2 ⟨n, x, hxS, hxInfinite, b,
      ⟨hb, hbn⟩, hb, z, hbz, hz, hbzOpen, hxb⟩

theorem PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_tendsto_sub
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (E.infiniteOpenBoundaryConnectionTo r S
        (E.upperBoundaryRayVertices r (s - n)))) atTop
      (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.infiniteOpenUpperBoundaryConnection_mono_sub r s S)
  rw [E.iUnion_infiniteOpenUpperBoundaryConnection_sub r s S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int)
    (r : Real) (S : Set V) :
    mu.real (E.infiniteOpenBoundaryConnection r
      (P.shift (verticalShift t) '' S)) =
        mu.real (E.infiniteOpenBoundaryConnection r S) := by
  let A := E.infiniteOpenBoundaryConnection r
    (P.shift (verticalShift t) '' S)
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      E.infiniteOpenBoundaryConnection r S := by
    ext omega
    change P.configTranslate (verticalShift t) omega ∈ A ↔
      omega ∈ E.infiniteOpenBoundaryConnection r S
    dsimp only [A]
    rw [← E.infiniteOpenBoundaryConnectionTo_boundary_eq r
      (P.shift (verticalShift t) '' S)]
    rw [← E.infiniteOpenBoundaryConnectionTo_boundary_eq r S]
    have h := E.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
      t omega r S (E.rightHalfPlaneBoundaryVertices r)
    rw [E.shift_image_rightHalfPlaneBoundaryVertices_vertical] at h
    exact h
  have hm := (hTI (verticalShift t)).measure_preimage
    (E.infiniteOpenBoundaryConnection_measurableSet r
      (P.shift (verticalShift t) '' S)).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm

theorem PeriodicPlaneEmbedding.shift_down_infiniteOpenLowerBoundary_tendsto_at
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift (-(n : Int))) '' S)
        (E.lowerBoundaryRayVertices r s))) atTop
      (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
  have hbase := E.infiniteOpenLowerBoundaryConnection_tendsto_add mu r s S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.infiniteOpenLowerBoundaryConnection_measureReal_vertical
    mu hTI (-(n : Int)) r (s + (n : Real)) S
  simpa using hmove.symm

theorem PeriodicPlaneEmbedding.shift_up_infiniteOpenUpperBoundary_tendsto_at
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r s : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift (n : Int)) '' S)
        (E.upperBoundaryRayVertices r s))) atTop
      (nhds (mu.real (E.infiniteOpenBoundaryConnection r S))) := by
  have hbase := E.infiniteOpenUpperBoundaryConnection_tendsto_sub mu r s S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.infiniteOpenUpperBoundaryConnection_measureReal_vertical
    mu hTI (n : Int) r (s - (n : Real)) S
  simpa using hmove.symm



theorem PeriodicPlaneEmbedding.exists_finite_infiniteOpenBoundaryConnection_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ S : Finset V,
      (S : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon < mu.real
        (E.infiniteOpenBoundaryConnection r (S : Set V)) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hsq := (P.orbitBoxHitsInfinite_real_tendsto_one mu hexists).pow 2
  have hev : ∀ᶠ N in atTop,
      1 - epsilon < (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 :=
    (tendsto_order.1 (by simpa using hsq)).1
      (1 - epsilon) (sub_lt_self 1 hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨z₀, hz₀⟩ := E.exists_shift_orbitBox_subset_rightHalfPlane N R
  obtain ⟨zL, hzL⟩ := E.exists_shift_orbitBox_subset_leftComplement N r
  let z₁ := zL - z₀
  have hinsideR : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
      E.rightHalfPlaneVertices R := by
    rintro _ ⟨v, hv, rfl⟩
    exact hz₀ v hv
  have hinside : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
      E.rightHalfPlaneVertices r := fun _ hx => hrR.trans (hinsideR hx)
  have houtside : P.shift z₁ ''
      (P.shift z₀ '' (P.orbitBox N : Set V)) ⊆
        (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hshift : P.shift z₁ (P.shift z₀ v) = P.shift zL v := by
      rw [← P.shift_add]
      simp [z₁]
    rw [hshift]
    exact hzL v hv
  let S := (P.orbitBox N).image (P.shift z₀)
  refine ⟨S, ?_, ?_⟩
  · simpa only [S, Finset.coe_image] using hinsideR
  · have hbound :=
      E.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate
        mu hFKG hTI hunique r
          (P.shift z₀ '' (P.orbitBox N : Set V)) z₁ hinside houtside
    have hmass : mu.real
        (P.setHitsInfinite (P.shift z₀ '' (P.orbitBox N : Set V))) =
        mu.real (P.orbitBoxHitsInfinite N) := by
      rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
      rfl
    rw [hmass] at hbound
    exact hN.trans_le (by simpa only [S, Finset.coe_image] using hbound)



theorem PeriodicPlaneEmbedding.exists_finite_opposite_infiniteOpenBoundaryRays_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R c d : Real} (hrR : r ≤ R)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (U : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon < mu.real
        (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
          (E.lowerBoundaryRayVertices r c)) ∧
      1 - epsilon < mu.real
        (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
          (E.upperBoundaryRayVertices r d)) := by
  obtain ⟨S, hSR, hSmass⟩ :=
    E.exists_finite_infiniteOpenBoundaryConnection_gt
      mu hFKG hTI hunique hrR hepsilon
  have hlower := E.shift_down_infiniteOpenLowerBoundary_tendsto_at
    mu hTI r c (S : Set V)
  have hupper := E.shift_up_infiniteOpenUpperBoundary_tendsto_at
    mu hTI r d (S : Set V)
  have hlowerEv : ∀ᶠ n : Nat in atTop, 1 - epsilon < mu.real
      (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift (-(n : Int))) '' (S : Set V))
        (E.lowerBoundaryRayVertices r c)) :=
    (tendsto_order.1 hlower).1 (1 - epsilon) (by
      exact hSmass)
  have hupperEv : ∀ᶠ n : Nat in atTop, 1 - epsilon < mu.real
      (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift (n : Int)) '' (S : Set V))
        (E.upperBoundaryRayVertices r d)) :=
    (tendsto_order.1 hupper).1 (1 - epsilon) (by
      exact hSmass)
  obtain ⟨nL, hnL⟩ := hlowerEv.exists
  obtain ⟨nU, hnU⟩ := hupperEv.exists
  let L := S.image (P.shift (verticalShift (-(nL : Int))))
  let U := S.image (P.shift (verticalShift (nU : Int)))
  refine ⟨L, U, ?_, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical _ R y).mpr (hSR hy)
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical _ R y).mpr (hSR hy)
  · simpa only [L, Finset.coe_image] using hnL
  · simpa only [U, Finset.coe_image] using hnU

end StatMech.FK.PeriodicPlanar
