/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldOpenBoundaryCorridor








open Filter MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicPlaneEmbedding.exists_adjacent_infiniteOpenBoundaryRays_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (r s : Real) (S : Set V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Int,
      1 - Real.sqrt (1 - mu.real
          (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r
          (P.shift (verticalShift z) '' S)
          (E.lowerBoundaryRayVertices r s)) ∧
      1 - Real.sqrt (1 - mu.real
          (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r
          (P.shift (verticalShift (z + 1)) '' S)
          (E.upperBoundaryRayVertices r s)) := by
  let F := mu.real (E.infiniteOpenBoundaryConnection r S)
  let lower : Int → Real := fun t => mu.real
    (E.infiniteOpenBoundaryConnectionTo r
      (P.shift (verticalShift t) '' S)
      (E.lowerBoundaryRayVertices r s))
  let upper : Int → Real := fun t => mu.real
    (E.infiniteOpenBoundaryConnectionTo r
      (P.shift (verticalShift t) '' S)
      (E.upperBoundaryRayVertices r s))
  have hlowerT : Tendsto (fun n : Nat => lower (-(n : Int)))
      atTop (nhds F) := by
    simpa only [lower, F] using
      E.shift_down_infiniteOpenLowerBoundary_tendsto_at mu hTI r s S
  have hupperT : Tendsto (fun n : Nat => upper (n : Int))
      atTop (nhds F) := by
    simpa only [upper, F] using
      E.shift_up_infiniteOpenUpperBoundary_tendsto_at mu hTI r s S
  have hlowerEv : ∀ᶠ n : Nat in atTop,
      F - epsilon < lower (-(n : Int)) :=
    (tendsto_order.1 hlowerT).1 (F - epsilon)
      (sub_lt_self F hepsilon)
  have hupperEv : ∀ᶠ n : Nat in atTop,
      F - epsilon < upper (n : Int) :=
    (tendsto_order.1 hupperT).1 (F - epsilon)
      (sub_lt_self F hepsilon)
  have hboth : ∀ᶠ n : Nat in atTop,
      1 ≤ n ∧ F - epsilon < lower (-(n : Int)) ∧
        F - epsilon < upper (n : Int) := by
    filter_upwards [eventually_ge_atTop 1, hlowerEv, hupperEv]
      with n hn hl hu
    exact ⟨hn, hl, hu⟩
  obtain ⟨N, hN, hNlower, hNupper⟩ := hboth.exists
  have hlower_le (t : Int) : lower t ≤ F := by
    calc
      lower t ≤ mu.real (E.infiniteOpenBoundaryConnection r
          (P.shift (verticalShift t) '' S)) :=
        measureReal_mono
          (E.infiniteOpenBoundaryConnectionTo_subset r _ _)
      _ = F := by
        simpa only [F] using
          E.infiniteOpenBoundaryConnection_measureReal_vertical
            mu hTI t r S
  have hupper_le (t : Int) : upper t ≤ F := by
    calc
      upper t ≤ mu.real (E.infiniteOpenBoundaryConnection r
          (P.shift (verticalShift t) '' S)) :=
        measureReal_mono
          (E.infiniteOpenBoundaryConnectionTo_subset r _ _)
      _ = F := by
        simpa only [F] using
          E.infiniteOpenBoundaryConnection_measureReal_vertical
            mu hTI t r S
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
  have hk : k + 1 = 2 * N := by
    dsimp only [k]
    omega
  obtain ⟨t, _ht0, _htend, htLower, htUpper⟩ :=
    exists_adjacent_approximate_preference_crossover f g epsilon 0 k
      hepsilon.le (by simpa using hstart) (by simpa [hk] using hend)
  let z : Int := (t : Int) - (N : Int)
  refine ⟨z, ?_, ?_⟩
  · let L := E.infiniteOpenBoundaryConnectionTo r
      (P.shift (verticalShift z) '' S)
      (E.lowerBoundaryRayVertices r s)
    let U := E.infiniteOpenBoundaryConnectionTo r
      (P.shift (verticalShift z) '' S)
      (E.upperBoundaryRayVertices r s)
    have hsqrt := measurable_sqrt_trick mu hFKG (A := L) (B := U)
      (by
        dsimp only [L]
        exact E.infiniteOpenBoundaryConnectionTo_isIncreasing r _ _)
      (by
        dsimp only [U]
        exact E.infiniteOpenBoundaryConnectionTo_isIncreasing r _ _)
      (by
        dsimp only [L]
        exact E.infiniteOpenBoundaryConnectionTo_measurableSet r _ _)
      (by
        dsimp only [U]
        exact E.infiniteOpenBoundaryConnectionTo_measurableSet r _ _)
    have hunion : L ∪ U = E.infiniteOpenBoundaryConnection r
        (P.shift (verticalShift z) '' S) := by
      exact E.infiniteOpenBoundaryConnectionTo_lower_union_upper r s _
    have hfull := E.infiniteOpenBoundaryConnection_measureReal_vertical
      mu hTI z r S
    have hpref : mu.real U ≤ mu.real L + epsilon := by
      simpa only [L, U, lower, upper, z, f, g] using htLower
    change 1 - Real.sqrt (1 - F) - epsilon ≤ lower z
    change 1 - Real.sqrt (1 - mu.real (L ∪ U)) ≤
      max (mu.real L) (mu.real U) at hsqrt
    rw [hunion, hfull] at hsqrt
    change 1 - Real.sqrt (1 - F) ≤
      max (mu.real L) (mu.real U) at hsqrt
    have hmax : max (mu.real L) (mu.real U) ≤ mu.real L + epsilon :=
      max_le (le_add_of_nonneg_right hepsilon.le) hpref
    have : 1 - Real.sqrt (1 - F) ≤ mu.real L + epsilon :=
      hsqrt.trans hmax
    simpa only [L, lower] using (sub_le_iff_le_add.mpr this)
  · have hznext : ((t + 1 : Nat) : Int) - (N : Int) = z + 1 := by
      dsimp only [z]
      omega
    let L := E.infiniteOpenBoundaryConnectionTo r
      (P.shift (verticalShift (z + 1)) '' S)
      (E.lowerBoundaryRayVertices r s)
    let U := E.infiniteOpenBoundaryConnectionTo r
      (P.shift (verticalShift (z + 1)) '' S)
      (E.upperBoundaryRayVertices r s)
    have hsqrt := measurable_sqrt_trick mu hFKG (A := L) (B := U)
      (by
        dsimp only [L]
        exact E.infiniteOpenBoundaryConnectionTo_isIncreasing r _ _)
      (by
        dsimp only [U]
        exact E.infiniteOpenBoundaryConnectionTo_isIncreasing r _ _)
      (by
        dsimp only [L]
        exact E.infiniteOpenBoundaryConnectionTo_measurableSet r _ _)
      (by
        dsimp only [U]
        exact E.infiniteOpenBoundaryConnectionTo_measurableSet r _ _)
    have hunion : L ∪ U = E.infiniteOpenBoundaryConnection r
        (P.shift (verticalShift (z + 1)) '' S) := by
      exact E.infiniteOpenBoundaryConnectionTo_lower_union_upper r s _
    have hfull := E.infiniteOpenBoundaryConnection_measureReal_vertical
      mu hTI (z + 1) r S
    have hpref : mu.real L ≤ mu.real U + epsilon := by
      simpa only [L, U, lower, upper, f, g, hznext] using htUpper
    change 1 - Real.sqrt (1 - F) - epsilon ≤ upper (z + 1)
    change 1 - Real.sqrt (1 - mu.real (L ∪ U)) ≤
      max (mu.real L) (mu.real U) at hsqrt
    rw [hunion, hfull] at hsqrt
    change 1 - Real.sqrt (1 - F) ≤
      max (mu.real L) (mu.real U) at hsqrt
    have hmax : max (mu.real L) (mu.real U) ≤ mu.real U + epsilon :=
      max_le hpref (le_add_of_nonneg_right hepsilon.le)
    have : 1 - Real.sqrt (1 - F) ≤ mu.real U + epsilon :=
      hsqrt.trans hmax
    simpa only [U, upper] using (sub_le_iff_le_add.mpr this)



theorem PeriodicPlaneEmbedding.exists_separated_infiniteOpenBoundaryRays_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (r s : Real) (t : Int) (S : Set V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Int,
      1 - Real.sqrt (1 - mu.real
          (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r
          (P.shift (verticalShift z) '' S)
          (E.lowerBoundaryRayVertices r s)) ∧
      1 - Real.sqrt (1 - mu.real
          (E.infiniteOpenBoundaryConnection r S)) - epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r
          (P.shift (verticalShift (z + 1 + t)) '' S)
          (E.upperBoundaryRayVertices r (s + t))) := by
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_adjacent_infiniteOpenBoundaryRays_measureReal_ge
      mu hFKG hTI r s S hepsilon
  refine ⟨z, hlower, ?_⟩
  have hmove := E.infiniteOpenUpperBoundaryConnection_measureReal_vertical
    mu hTI t r s (P.shift (verticalShift (z + 1)) '' S)
  have himage :
      P.shift (verticalShift t) ''
          (P.shift (verticalShift (z + 1)) '' S) =
        P.shift (verticalShift (z + 1 + t)) '' S :=
    P.shift_image_vertical_add (z + 1) t S
  rw [himage] at hmove
  rwa [hmove]

end StatMech.FK.PeriodicPlanar
