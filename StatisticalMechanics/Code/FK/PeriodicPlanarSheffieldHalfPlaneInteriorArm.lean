/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm





open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicPlaneEmbedding.exists_opposite_translated_orbitBox_with_margin
    (E : PeriodicPlaneEmbedding P) (N : Nat) (r R : Real) :
    ∃ z₀ z₁ : Site 2,
      P.shift z₀ '' (P.orbitBox N : Set V) ⊆
        E.rightHalfPlaneVertices R ∧
      P.shift z₁ '' (P.shift z₀ '' (P.orbitBox N : Set V)) ⊆
        (E.rightHalfPlaneVertices r)ᶜ := by
  obtain ⟨zR, hzR⟩ := E.exists_shift_orbitBox_subset_rightHalfPlane N R
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



theorem PeriodicPlaneEmbedding.exists_finite_infiniteBoundaryConnection_with_margin_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ S : Set V, S.Finite ∧ S ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r)) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hev : ∀ᶠ N in atTop,
      1 - epsilon < (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 :=
    (tendsto_order.1 hsq).1 (1 - epsilon) (sub_lt_self 1 hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨z₀, z₁, hdeep, houtside⟩ :=
    E.exists_opposite_translated_orbitBox_with_margin N r R
  let S : Set V := P.shift z₀ '' (P.orbitBox N : Set V)
  have hSr : S ⊆ E.rightHalfPlaneVertices r := by
    intro x hx
    exact hrR.trans (hdeep hx)
  have hbound := E.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
    mu hFKG hTI hunique r S z₁ hSr houtside
  have hmass : mu.real (P.setHitsInfinite S) =
      mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [S]
    rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
    rfl
  rw [hmass] at hbound
  exact ⟨S, (P.orbitBox N).finite_toSet.image _, hdeep,
    hN.trans_le hbound⟩



theorem PeriodicPlaneEmbedding.exists_finite_opposite_infiniteBoundaryRays_with_margin_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Set V,
      L.Finite ∧ U.Finite ∧
      L ⊆ E.rightHalfPlaneVertices R ∧
      U ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) L
          (E.lowerBoundaryRayVertices r 0)) ∧
      1 - epsilon < mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) U
          (E.upperBoundaryRayVertices r 1)) := by
  obtain ⟨S, hSfinite, hSR, hSmass⟩ :=
    E.exists_finite_infiniteBoundaryConnection_with_margin_gt
      mu hFKG hTI hunique hrR hepsilon
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
  obtain ⟨nU, hnU⟩ := hupperEventually.exists
  let L := P.shift (verticalShift (-(nL : Int))) '' S
  let U₀ := P.shift (verticalShift (nU : Int)) '' S
  let U := P.shift (verticalShift 1) '' U₀
  refine ⟨L, U, hSfinite.image _, (hSfinite.image _).image _, ?_, ?_, hnL, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (E.shift_mem_rightHalfPlaneVertices_vertical _ R x).mpr (hSR hx)
  · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact (E.shift_mem_rightHalfPlaneVertices_vertical 1 R _).mpr
      ((E.shift_mem_rightHalfPlaneVertices_vertical _ R y).mpr (hSR hy))
  · have hmove := E.infiniteUpperBoundaryRay_measureReal_vertical
      mu hTI 1 r 0 U₀
    have hmove' : mu.real
        (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift 1) '' U₀)
          (E.upperBoundaryRayVertices r 1)) =
        mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) U₀
          (E.upperBoundaryRayVertices r 0)) := by
      simpa using hmove
    change 1 - epsilon < mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift 1) '' U₀)
        (E.upperBoundaryRayVertices r 1))
    rw [hmove']
    exact hnU

end StatMech.FK.PeriodicPlanar
