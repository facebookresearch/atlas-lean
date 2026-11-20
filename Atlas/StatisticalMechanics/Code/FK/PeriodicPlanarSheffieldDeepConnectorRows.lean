/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldOpenBoundaryCrossover
import Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure





open Filter MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}





theorem
    PeriodicPlaneEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int) (N : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ width : Nat,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (U : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      U = L.image (P.shift (verticalShift (1 + t))) ∧
      1 - 2 * Real.sqrt
          (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) -
          3 * epsilon <
        mu.real (E.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R s (s + t) width L U) := by
  obtain ⟨z₀, width, hSdeep, _hSsepDeep, hmerge⟩ :=
    E.exists_inward_separated_stripPlacement_with_margin
      mu hTI hunique (r := R) (R := R) le_rfl t
        (P.orbitBox N) hepsilon
  let S := (P.orbitBox N).image (P.shift z₀)
  let Ssep := S.image (P.shift (verticalShift (1 + t)))
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_separated_infiniteOpenBoundaryRays_measureReal_ge
      mu hFKG hTI r s t (S : Set V) hepsilon
  let L := S.image (P.shift (verticalShift z))
  let U := Ssep.image (P.shift (verticalShift z))
  have hU : U = L.image (P.shift (verticalShift (1 + t))) := by
    ext y
    simp only [U, L, Ssep, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift z) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift (1 + t)) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  have hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices R := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical z R u).mpr
      (hSdeep hu)
  have hUdeep : (U : Set V) ⊆ E.rightHalfPlaneVertices R := by
    rw [hU]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical (1 + t) R u).mpr
      (hLdeep hu)
  have hmerge' : mu.real
      (E.halfPlaneStripPairMergeErrorUnion R width L U) < epsilon := by
    have hv := E.halfPlaneStripPairMergeErrorUnion_measureReal_vertical
      mu hTI z R width S Ssep
    change mu.real (E.halfPlaneStripPairMergeErrorUnion R width
      (S.image (P.shift (verticalShift z)))
      (Ssep.image (P.shift (verticalShift z)))) < epsilon
    rw [hv]
    exact hmerge
  obtain ⟨zLeft, hzLeft⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N r
  let zOutside := zLeft - z₀
  have hSinside : (S : Set V) ⊆ E.rightHalfPlaneVertices r := by
    intro x hx
    exact hrR.trans (hSdeep hx)
  have hSoutside : P.shift zOutside '' (S : Set V) ⊆
      (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨w, hwS, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
    have hshift : P.shift zOutside (P.shift z₀ v) = P.shift zLeft v := by
      rw [← P.shift_add]
      simp [zOutside]
    rw [hshift]
    exact hzLeft v hv
  have hfull :=
    E.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate
      mu hFKG hTI hunique r (S : Set V) zOutside hSinside hSoutside
  have hmass : mu.real (P.setHitsInfinite (S : Set V)) =
      mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [S]
    rw [Finset.coe_image,
      P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
    rfl
  rw [hmass] at hfull
  have hsqrt : Real.sqrt
      (1 - mu.real (E.infiniteOpenBoundaryConnection r (S : Set V))) ≤
      Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hlower' : 1 - Real.sqrt
      (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) - epsilon ≤
      mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
        (E.lowerBoundaryRayVertices r s)) := by
    have hsource : 1 - Real.sqrt
          (1 - mu.real (E.infiniteOpenBoundaryConnection r (S : Set V))) -
          epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
          (E.lowerBoundaryRayVertices r s)) := by
      simpa only [L, Finset.coe_image] using hlower
    linarith
  have hupper' : 1 - Real.sqrt
      (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) - epsilon ≤
      mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
        (E.upperBoundaryRayVertices r (s + t))) := by
    have hsource : 1 - Real.sqrt
          (1 - mu.real (E.infiniteOpenBoundaryConnection r (S : Set V))) -
          epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
          (E.upperBoundaryRayVertices r (s + t))) := by
      have himage : P.shift (verticalShift (1 + t)) ''
          (P.shift (verticalShift z) '' (S : Set V)) =
          P.shift (verticalShift (z + 1 + t)) '' (S : Set V) := by
        rw [P.shift_image_vertical_add]
        congr 3
        ring_nf
      rw [hU]
      simpa only [L, Finset.coe_image, himage] using hupper
    linarith
  refine ⟨L, U, width, hLdeep, hUdeep, hU, ?_⟩
  have hbound :=
    E.finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge
      mu r R s (s + t) width L U
  linarith

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair




noncomputable def finiteDeepConnectorBandSchedule_of_separatedRows
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (rDual : Real) (band : Nat)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int)
    (hdisjoint : ∀ (L U : Finset V) (width : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift (verticalShift (1 + t))) →
      Disjoint
        (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R s (s + t) width L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(band : Real)) band)) :
    D.FiniteDeepConnectorBandSchedule mu rDual band := by
  let epsilon : Nat → Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hrow (n : Nat) : ∃ L U : Finset V, ∃ width : Nat,
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R ∧
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R ∧
      U = L.image (P.shift (verticalShift (1 + t))) ∧
      1 - 2 * Real.sqrt
          (1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2) -
          3 * epsilon n <
        mu.real
          (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
            r R s (s + t) width L U) :=
    D.primalEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt
      mu hFKG hTI hunique hrR s t n (hepsilon n)
  choose lower upper width hlowerDeep hupperDeep htranslate hmass using hrow
  refine
    { rPrimal := fun _ => r
      Rdeep := fun _ => R
      cArm := fun _ => s
      dArm := fun _ => s + t
      width := width
      lower := lower
      upper := upper
      tendsto_one := ?_
      disjoint_band := fun n =>
        hdisjoint (lower n) (upper n) (width n)
          (hlowerDeep n) (hupperDeep n) (htranslate n) }
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto (fun n : Nat =>
      (mu.real (P.orbitBoxHitsInfinite n)) ^ 2) atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hmiss : Tendsto (fun n : Nat =>
      1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hsq
  have hsqrt : Tendsto (fun n : Nat => Real.sqrt
      (1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2))
      atTop (nhds 0) := by
    simpa using hmiss.sqrt
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlowerLimit : Tendsto (fun n : Nat =>
      1 - 2 * Real.sqrt
          (1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2) -
        3 * epsilon n) atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : Real))).sub
        (hsqrt.const_mul 2)).sub (hepsilonZero.const_mul 3)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerLimit tendsto_const_nhds
      (fun n => (hmass n).le) (fun _ => measureReal_le_one)




theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rDual : Real) {r R : Real} (hrR : r ≤ R)
    (s : Nat → Real) (t : Nat → Int)
    (hdisjoint : ∀ (band : Nat) (L U : Finset V) (width : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift (verticalShift (1 + t band))) →
      Disjoint
        (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R (s band) (s band + t band) width L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(band : Real)) band)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  apply
    D.complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules
      mu hdualErgodic hdualUnique rDual
  intro band
  exact D.finiteDeepConnectorBandSchedule_of_separatedRows
    mu hFKG hTI hunique rDual band hrR (s band) (t band)
      (hdisjoint band)

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
