/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldPreferenceClosure
import Code.FK.PeriodicPlanarSheffieldRectanglePreference











open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice




theorem exists_common_approximate_preference_grid_witness
    {n m : Nat} (hn : 0 < n) (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (bottom top left right : PreferenceGridVertex n m → Real)
    (hbottom : ∀ i : Fin (n + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (n + 1),
      bottom (i, Fin.last m) + epsilon < top (i, Fin.last m))
    (hleft : ∀ j : Fin (m + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (m + 1),
      left (Fin.last n, j) + epsilon < right (Fin.last n, j)) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex n m,
      top x ≤ bottom x + epsilon ∧
      right x ≤ left x + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      bottom xVertical ≤ top xVertical + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      left xHorizontal ≤ right xHorizontal + epsilon := by
  let vertical : PreferenceGridVertex n m → Bool := fun x =>
    decide (top x ≤ bottom x + epsilon)
  let horizontal : PreferenceGridVertex n m → Bool := fun x =>
    decide (right x ≤ left x + epsilon)
  have hvBottom : ∀ i : Fin (n + 1), vertical (i, 0) = true := by
    intro i
    simp [vertical, hbottom i]
  have hvTop : ∀ i : Fin (n + 1), vertical (i, Fin.last m) = false := by
    intro i
    simp [vertical, not_le.mpr (htop i)]
  have hhLeft : ∀ j : Fin (m + 1), horizontal (0, j) = true := by
    intro j
    simp [horizontal, hleft j]
  have hhRight : ∀ j : Fin (m + 1), horizontal (Fin.last n, j) = false := by
    intro j
    simp [horizontal, not_le.mpr (hright j)]
  obtain ⟨x, hxv, hxh, ⟨xVertical, hxVertical, hxvFalse⟩,
      ⟨xHorizontal, hxHorizontal, hxhFalse⟩⟩ :=
    exists_common_preference_grid_witness hn vertical horizontal true false
      hvBottom hvTop (by decide) hhLeft hhRight
  have hxv' : top x ≤ bottom x + epsilon := by
    simpa [vertical] using hxv
  have hxh' : right x ≤ left x + epsilon := by
    simpa [horizontal] using hxh
  have hxvNot : ¬top xVertical ≤ bottom xVertical + epsilon := by
    simpa [vertical] using hxvFalse
  have hxhNot : ¬right xHorizontal ≤ left xHorizontal + epsilon := by
    simpa [horizontal] using hxhFalse
  exact ⟨x, xVertical, xHorizontal, hxv', hxh', hxVertical,
    by linarith, hxHorizontal, by linarith⟩





theorem exists_common_weak_approximate_preference_grid_witness
    {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (bottom top left right : PreferenceGridVertex n m → Real)
    (hbottom : ∀ i : Fin (n + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (n + 1),
      bottom (i, Fin.last m) ≤ top (i, Fin.last m) + epsilon)
    (hleft : ∀ j : Fin (m + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (m + 1),
      left (Fin.last n, j) ≤ right (Fin.last n, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex n m,
      top x ≤ bottom x + epsilon ∧
      right x ≤ left x + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      bottom xVertical ≤ top xVertical + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      left xHorizontal ≤ right xHorizontal + epsilon := by
  let vertical : PreferenceGridVertex n m → Bool := fun x =>
    if x.2 = Fin.last m then false else
      decide (top x ≤ bottom x + epsilon)
  let horizontal : PreferenceGridVertex n m → Bool := fun x =>
    if x.1 = Fin.last n then false else
      decide (right x ≤ left x + epsilon)
  have hzeroLastM : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hzeroLastN : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hvBottom : ∀ i : Fin (n + 1), vertical (i, 0) = true := by
    intro i
    simp [vertical, hzeroLastM, hbottom i]
  have hvTop : ∀ i : Fin (n + 1),
      vertical (i, Fin.last m) = false := by
    intro i
    simp [vertical]
  have hhLeft : ∀ j : Fin (m + 1), horizontal (0, j) = true := by
    intro j
    simp [horizontal, hzeroLastN, hleft j]
  have hhRight : ∀ j : Fin (m + 1),
      horizontal (Fin.last n, j) = false := by
    intro j
    simp [horizontal]
  obtain ⟨x, hxv, hxh, ⟨xVertical, hxVertical, hxvFalse⟩,
      ⟨xHorizontal, hxHorizontal, hxhFalse⟩⟩ :=
    exists_common_preference_grid_witness hn vertical horizontal true false
      hvBottom hvTop (by decide) hhLeft hhRight
  have hxv' : top x ≤ bottom x + epsilon := by
    by_cases htopRow : x.2 = Fin.last m
    · simp [vertical, htopRow] at hxv
    · simpa [vertical, htopRow] using hxv
  have hxh' : right x ≤ left x + epsilon := by
    by_cases hrightCol : x.1 = Fin.last n
    · simp [horizontal, hrightCol] at hxh
    · simpa [horizontal, hrightCol] using hxh
  have hxvOpposite : bottom xVertical ≤ top xVertical + epsilon := by
    by_cases htopRow : xVertical.2 = Fin.last m
    · have hxEq : xVertical = (xVertical.1, Fin.last m) :=
        Prod.ext rfl htopRow
      rw [hxEq]
      exact htop xVertical.1
    · have hnot : ¬top xVertical ≤ bottom xVertical + epsilon := by
        simpa [vertical, htopRow] using hxvFalse
      linarith
  have hxhOpposite : left xHorizontal ≤ right xHorizontal + epsilon := by
    by_cases hrightCol : xHorizontal.1 = Fin.last n
    · have hxEq : xHorizontal = (Fin.last n, xHorizontal.2) :=
        Prod.ext hrightCol rfl
      rw [hxEq]
      exact hright xHorizontal.2
    · have hnot : ¬right xHorizontal ≤ left xHorizontal + epsilon := by
        simpa [horizontal, hrightCol] using hxhFalse
      linarith
  exact ⟨x, xVertical, xHorizontal, hxv', hxh', hxVertical,
    hxvOpposite, hxHorizontal, hxhOpposite⟩



def rectangleEndpointPreferenceError {n m : Nat}
    (bottom top left right : PreferenceGridVertex n m → Real) : Real :=
  (∑ i : Fin (n + 1), max (top (i, 0) - bottom (i, 0)) 0) +
  (∑ i : Fin (n + 1),
    max (bottom (i, Fin.last m) - top (i, Fin.last m)) 0) +
  (∑ j : Fin (m + 1), max (right (0, j) - left (0, j)) 0) +
  ∑ j : Fin (m + 1),
    max (left (Fin.last n, j) - right (Fin.last n, j)) 0

theorem rectangleEndpointPreferenceError_nonneg {n m : Nat}
    (bottom top left right : PreferenceGridVertex n m → Real) :
    0 ≤ rectangleEndpointPreferenceError bottom top left right := by
  unfold rectangleEndpointPreferenceError
  positivity



theorem rectangleEndpointPreferenceError_bounds {n m : Nat}
    (bottom top left right : PreferenceGridVertex n m → Real) :
    (∀ i : Fin (n + 1), top (i, 0) ≤ bottom (i, 0) +
      rectangleEndpointPreferenceError bottom top left right) ∧
    (∀ i : Fin (n + 1), bottom (i, Fin.last m) ≤ top (i, Fin.last m) +
      rectangleEndpointPreferenceError bottom top left right) ∧
    (∀ j : Fin (m + 1), right (0, j) ≤ left (0, j) +
      rectangleEndpointPreferenceError bottom top left right) ∧
    ∀ j : Fin (m + 1), left (Fin.last n, j) ≤ right (Fin.last n, j) +
      rectangleEndpointPreferenceError bottom top left right := by
  let eB : Fin (n + 1) → Real := fun i =>
    max (top (i, 0) - bottom (i, 0)) 0
  let eT : Fin (n + 1) → Real := fun i =>
    max (bottom (i, Fin.last m) - top (i, Fin.last m)) 0
  let eL : Fin (m + 1) → Real := fun j =>
    max (right (0, j) - left (0, j)) 0
  let eR : Fin (m + 1) → Real := fun j =>
    max (left (Fin.last n, j) - right (Fin.last n, j)) 0
  have hsumB (i : Fin (n + 1)) : eB i ≤ ∑ k, eB k := by
    exact Finset.single_le_sum (s := Finset.univ) (f := eB)
      (fun k _ => by dsimp only [eB]; exact le_max_right _ _)
      (Finset.mem_univ i)
  have hsumT (i : Fin (n + 1)) : eT i ≤ ∑ k, eT k := by
    exact Finset.single_le_sum (s := Finset.univ) (f := eT)
      (fun k _ => by dsimp only [eT]; exact le_max_right _ _)
      (Finset.mem_univ i)
  have hsumL (j : Fin (m + 1)) : eL j ≤ ∑ k, eL k := by
    exact Finset.single_le_sum (s := Finset.univ) (f := eL)
      (fun k _ => by dsimp only [eL]; exact le_max_right _ _)
      (Finset.mem_univ j)
  have hsumR (j : Fin (m + 1)) : eR j ≤ ∑ k, eR k := by
    exact Finset.single_le_sum (s := Finset.univ) (f := eR)
      (fun k _ => by dsimp only [eR]; exact le_max_right _ _)
      (Finset.mem_univ j)
  have hnonnegB : 0 ≤ ∑ k, eB k := by positivity
  have hnonnegT : 0 ≤ ∑ k, eT k := by positivity
  have hnonnegL : 0 ≤ ∑ k, eL k := by positivity
  have hnonnegR : 0 ≤ ∑ k, eR k := by positivity
  refine ⟨fun i => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩
  · have hd : top (i, 0) - bottom (i, 0) ≤ eB i := le_max_left _ _
    have htotal : eB i ≤
        (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k := by
      calc
        eB i ≤ ∑ k, eB k := hsumB i
        _ ≤ (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) +
            ∑ k, eR k := by linarith
    change top (i, 0) ≤ bottom (i, 0) +
      ((∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k)
    linarith
  · have hd : bottom (i, Fin.last m) - top (i, Fin.last m) ≤ eT i :=
      le_max_left _ _
    have htotal : eT i ≤
        (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k := by
      calc
        eT i ≤ ∑ k, eT k := hsumT i
        _ ≤ (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) +
            ∑ k, eR k := by linarith
    change bottom (i, Fin.last m) ≤ top (i, Fin.last m) +
      ((∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k)
    linarith
  · have hd : right (0, j) - left (0, j) ≤ eL j := le_max_left _ _
    have htotal : eL j ≤
        (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k := by
      calc
        eL j ≤ ∑ k, eL k := hsumL j
        _ ≤ (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) +
            ∑ k, eR k := by linarith
    change right (0, j) ≤ left (0, j) +
      ((∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k)
    linarith
  · have hd : left (Fin.last n, j) - right (Fin.last n, j) ≤ eR j :=
      le_max_left _ _
    have htotal : eR j ≤
        (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k := by
      calc
        eR j ≤ ∑ k, eR k := hsumR j
        _ ≤ (∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) +
            ∑ k, eR k := by linarith
    change left (Fin.last n, j) ≤ right (Fin.last n, j) +
      ((∑ k, eB k) + (∑ k, eT k) + (∑ k, eL k) + ∑ k, eR k)
    linarith




theorem rectangleEndpointPreferenceError_tendsto_zero {n m : Nat}
    (bottom top left right : Nat → PreferenceGridVertex n m → Real)
    (hbottomOne : ∀ i : Fin (n + 1),
      Tendsto (fun N => bottom N (i, 0)) atTop (nhds 1))
    (htopOne : ∀ i : Fin (n + 1),
      Tendsto (fun N => top N (i, Fin.last m)) atTop (nhds 1))
    (hleftOne : ∀ j : Fin (m + 1),
      Tendsto (fun N => left N (0, j)) atTop (nhds 1))
    (hrightOne : ∀ j : Fin (m + 1),
      Tendsto (fun N => right N (Fin.last n, j)) atTop (nhds 1))
    (hbottomLe : ∀ N x, bottom N x ≤ 1)
    (htopLe : ∀ N x, top N x ≤ 1)
    (hleftLe : ∀ N x, left N x ≤ 1)
    (hrightLe : ∀ N x, right N x ≤ 1) :
    Tendsto (fun N => rectangleEndpointPreferenceError
      (bottom N) (top N) (left N) (right N)) atTop (nhds 0) := by
  have htermBottom (i : Fin (n + 1)) : Tendsto (fun N =>
      max (top N (i, 0) - bottom N (i, 0)) 0) atTop (nhds 0) := by
    have hupper : Tendsto (fun N => 1 - bottom N (i, 0)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub (hbottomOne i)
    exact squeeze_zero (fun _ => le_max_right _ _) (fun N =>
      max_le (by linarith [htopLe N (i, 0)])
        (by linarith [hbottomLe N (i, 0)])) hupper
  have htermTop (i : Fin (n + 1)) : Tendsto (fun N =>
      max (bottom N (i, Fin.last m) - top N (i, Fin.last m)) 0)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun N => 1 - top N (i, Fin.last m))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub (htopOne i)
    exact squeeze_zero (fun _ => le_max_right _ _) (fun N =>
      max_le (by linarith [hbottomLe N (i, Fin.last m)])
        (by linarith [htopLe N (i, Fin.last m)])) hupper
  have htermLeft (j : Fin (m + 1)) : Tendsto (fun N =>
      max (right N (0, j) - left N (0, j)) 0) atTop (nhds 0) := by
    have hupper : Tendsto (fun N => 1 - left N (0, j)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub (hleftOne j)
    exact squeeze_zero (fun _ => le_max_right _ _) (fun N =>
      max_le (by linarith [hrightLe N (0, j)])
        (by linarith [hleftLe N (0, j)])) hupper
  have htermRight (j : Fin (m + 1)) : Tendsto (fun N =>
      max (left N (Fin.last n, j) - right N (Fin.last n, j)) 0)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun N => 1 - right N (Fin.last n, j))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub (hrightOne j)
    exact squeeze_zero (fun _ => le_max_right _ _) (fun N =>
      max_le (by linarith [hleftLe N (Fin.last n, j)])
        (by linarith [hrightLe N (Fin.last n, j)])) hupper
  have hsumBottom := tendsto_finsetSum Finset.univ
    (fun i _ => htermBottom i)
  have hsumTop := tendsto_finsetSum Finset.univ
    (fun i _ => htermTop i)
  have hsumLeft := tendsto_finsetSum Finset.univ
    (fun j _ => htermLeft j)
  have hsumRight := tendsto_finsetSum Finset.univ
    (fun j _ => htermRight j)
  simpa [rectangleEndpointPreferenceError] using
    (((hsumBottom.add hsumTop).add hsumLeft).add hsumRight)

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicPlaneEmbedding.preference_max_bottom_left_add_epsilon_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hS : S ⊆ E.rectVertices a b c d)
    (hBottomTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) + epsilon)
    (hLeftRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) + epsilon) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      max
        (mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d)))
        (mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectLeftBoundaryVertices a b c d))) + epsilon := by
  let B := E.rectSideConnectionEvent a b c d S
    (E.rectBottomBoundaryVertices a b c d)
  let T := E.rectSideConnectionEvent a b c d S
    (E.rectTopBoundaryVertices a b c d)
  let L := E.rectSideConnectionEvent a b c d S
    (E.rectLeftBoundaryVertices a b c d)
  let R := E.rectSideConnectionEvent a b c d S
    (E.rectRightBoundaryVertices a b c d)
  have hfour := four_event_sqrt_trick mu hFKG
    (E.rectSideConnectionEvent_isIncreasing a b c d S
      (E.rectBottomBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_isIncreasing a b c d S
      (E.rectTopBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_isIncreasing a b c d S
      (E.rectLeftBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_isIncreasing a b c d S
      (E.rectRightBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_measurableSet a b c d S
      (E.rectBottomBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_measurableSet a b c d S
      (E.rectTopBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_measurableSet a b c d S
      (E.rectLeftBoundaryVertices a b c d))
    (E.rectSideConnectionEvent_measurableSet a b c d S
      (E.rectRightBoundaryVertices a b c d))
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (B ∪ (T ∪ (L ∪ R))) :=
    measureReal_mono
      (E.setHitsInfinite_subset_rectSideConnection_union a b c d S hS)
  have hsqrt :
      Real.sqrt (Real.sqrt (1 - mu.real (B ∪ (T ∪ (L ∪ R))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  have hB : mu.real B ≤ max (mu.real B) (mu.real L) + epsilon :=
    (le_max_left _ _).trans (le_add_of_nonneg_right hepsilon)
  have hL : mu.real L ≤ max (mu.real B) (mu.real L) + epsilon :=
    (le_max_right _ _).trans (le_add_of_nonneg_right hepsilon)
  have hT : mu.real T ≤ max (mu.real B) (mu.real L) + epsilon := by
    dsimp only [B, T, L, R] at hBottomTop ⊢
    linarith [le_max_left (mu.real B) (mu.real L)]
  have hR : mu.real R ≤ max (mu.real B) (mu.real L) + epsilon := by
    dsimp only [B, T, L, R] at hLeftRight ⊢
    linarith [le_max_right (mu.real B) (mu.real L)]
  have hmax : max (max (mu.real B) (mu.real T))
      (max (mu.real L) (mu.real R)) ≤
        max (mu.real B) (mu.real L) + epsilon :=
    max_le (max_le hB hT) (max_le hL hR)
  dsimp only [B, T, L, R] at hfour hsqrt hmax ⊢
  linarith


theorem PeriodicPlaneEmbedding.verticalCrossing_ge_approxPreferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (epsilon : Real)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) + epsilon) :
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    A * (H * A - M - epsilon) - M ≤
      mu.real (E.verticalCrossingEvent a b c d) := by
  dsimp only
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectBottomBoundaryVertices a b c d)
  have htop :
      mu.real (P.setHitsInfinite (R : Set V)) *
          mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectBottomBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) - epsilon ≤
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectTopBoundaryVertices a b c d)) := by
    linarith
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left htop hAnonneg
  have hcross := E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
    mu hFKG a b c d L R
  nlinarith


theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_approxPreferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (epsilon : Real)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) + epsilon) :
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectLeftBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    A * (H * A - M - epsilon) - M ≤
      mu.real (E.horizontalCrossingEvent a b c d) := by
  dsimp only
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectLeftBoundaryVertices a b c d)
  have hright :
      mu.real (P.setHitsInfinite (R : Set V)) *
          mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectLeftBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) - epsilon ≤
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectRightBoundaryVertices a b c d)) := by
    linarith
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hright hAnonneg
  have hcross := E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
    mu hFKG a b c d L R
  nlinarith





theorem PeriodicPlaneEmbedding.exists_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real)
    {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (source : PreferenceGridVertex n m → Finset V)
    (bottom top left right : PreferenceGridVertex n m → Real)
    (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
    (hbottomScore : ∀ x, bottom x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (htopScore : ∀ x, top x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hleftScore : ∀ x, left x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hrightScore : ∀ x, right x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectRightBoundaryVertices a b c d)))
    (hbottom : ∀ i : Fin (n + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (n + 1),
      bottom (i, Fin.last m) ≤ top (i, Fin.last m) + epsilon)
    (hleft : ∀ j : Fin (m + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (m + 1),
      left (Fin.last n, j) ≤ right (Fin.last n, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex n m,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon ∧
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xVertical)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xVertical)) ≤
          mu.real (E.verticalCrossingEvent a b c d)) ∨
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon ∧
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xHorizontal)) ≤
          mu.real (E.horizontalCrossingEvent a b c d))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal, hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness hn hm epsilon hepsilon
      bottom top left right hbottom htop hleft hright
  have hpref := E.preference_max_bottom_left_add_epsilon_ge_fourthRoot
    mu hFKG a b c d (source x : Set V) epsilon hepsilon (hsource x)
    (by simpa [hbottomScore x, htopScore x] using hxBottom)
    (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x ≤ bottom x
  · left
    have hroot :
        1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer := E.verticalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a b c d (source x) (source xVertical) epsilon
      (by simpa [hbottomScore xVertical, htopScore xVertical] using
        hxVerticalOpposite)
    rw [← hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x ≤ left x := le_of_not_ge hLB
    have hroot :
        1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a b c d (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
        hxHorizontalOpposite)
    rw [← hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩




theorem PeriodicPlaneEmbedding.exists_intrinsicEndpointError_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real)
    {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (source : PreferenceGridVertex n m → Finset V)
    (bottom top left right : PreferenceGridVertex n m → Real)
    (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
    (hbottomScore : ∀ x, bottom x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectBottomBoundaryVertices a b c d)))
    (htopScore : ∀ x, top x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectTopBoundaryVertices a b c d)))
    (hleftScore : ∀ x, left x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectLeftBoundaryVertices a b c d)))
    (hrightScore : ∀ x, right x = mu.real
      (E.rectSideConnectionEvent a b c d (source x : Set V)
        (E.rectRightBoundaryVertices a b c d))) :
    let epsilon := rectangleEndpointPreferenceError bottom top left right
    ∃ x xVertical xHorizontal : PreferenceGridVertex n m,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon ∧
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xVertical)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xVertical)) ≤
          mu.real (E.verticalCrossingEvent a b c d)) ∨
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon ∧
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x -
              mu.real (E.rectanglePairMergeErrorUnion a b c d
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a b c d
              (source x) (source xHorizontal)) ≤
          mu.real (E.horizontalCrossingEvent a b c d))) := by
  dsimp only
  obtain ⟨hbottom, htop, hleft, hright⟩ :=
    rectangleEndpointPreferenceError_bounds bottom top left right
  exact E.exists_approxPreferredSide_crossing_branch mu hFKG a b c d hn hm
    (rectangleEndpointPreferenceError bottom top left right)
    (rectangleEndpointPreferenceError_nonneg bottom top left right)
    source bottom top left right hsource hbottomScore htopScore hleftScore
    hrightScore hbottom htop hleft hright



theorem crossing_max_tendsto_one_of_approxPreferredSide_branches
    (A Hv Hh Mv Mh epsilon Cv Ch : Nat → Real)
    (hA : Tendsto A atTop (nhds 1))
    (hHv : Tendsto Hv atTop (nhds 1))
    (hHh : Tendsto Hh atTop (nhds 1))
    (hMv : Tendsto Mv atTop (nhds 0))
    (hMh : Tendsto Mh atTop (nhds 0))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hbranch : ∀ N,
      A N * (Hv N * A N - Mv N - epsilon N) - Mv N ≤ Cv N ∨
      A N * (Hh N * A N - Mh N - epsilon N) - Mh N ≤ Ch N)
    (hCv : ∀ N, Cv N ≤ 1) (hCh : ∀ N, Ch N ≤ 1) :
    Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
  let Lv := fun N => A N * (Hv N * A N - Mv N - epsilon N) - Mv N
  let Lh := fun N => A N * (Hh N * A N - Mh N - epsilon N) - Mh N
  have hLv : Tendsto Lv atTop (nhds 1) := by
    dsimp only [Lv]
    convert hA.mul (((hHv.mul hA).sub hMv).sub hepsilon) |>.sub hMv using 1 <;>
      norm_num
  have hLh : Tendsto Lh atTop (nhds 1) := by
    dsimp only [Lh]
    convert hA.mul (((hHh.mul hA).sub hMh).sub hepsilon) |>.sub hMh using 1 <;>
      norm_num
  have hmin : Tendsto (fun N => min (Lv N) (Lh N)) atTop (nhds 1) := by
    simpa using hLv.min hLh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hmin tendsto_const_nhds
  · intro N
    rcases hbranch N with hV | hH
    · exact (min_le_left _ _).trans (hV.trans (le_max_left _ _))
    · exact (min_le_right _ _).trans (hH.trans (le_max_right _ _))
  · intro N
    exact max_le (hCv N) (hCh N)





theorem crossing_selected_tendsto_one_of_approxPreferredSide_branches
    (branch : Nat -> Bool)
    (A Hv Hh Mv Mh epsilon Cv Ch : Nat -> Real)
    (hA : Tendsto A atTop (nhds 1))
    (hHv : Tendsto Hv atTop (nhds 1))
    (hHh : Tendsto Hh atTop (nhds 1))
    (hMv : Tendsto Mv atTop (nhds 0))
    (hMh : Tendsto Mh atTop (nhds 0))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hvertical : forall N, branch N = true ->
      A N * (Hv N * A N - Mv N - epsilon N) - Mv N <= Cv N)
    (hhorizontal : forall N, branch N = false ->
      A N * (Hh N * A N - Mh N - epsilon N) - Mh N <= Ch N)
    (hCv : forall N, Cv N <= 1) (hCh : forall N, Ch N <= 1) :
    Tendsto (fun N => if branch N then Cv N else Ch N)
      atTop (nhds 1) := by
  let Lv := fun N => A N * (Hv N * A N - Mv N - epsilon N) - Mv N
  let Lh := fun N => A N * (Hh N * A N - Mh N - epsilon N) - Mh N
  have hLv : Tendsto Lv atTop (nhds 1) := by
    dsimp only [Lv]
    convert hA.mul (((hHv.mul hA).sub hMv).sub hepsilon) |>.sub hMv
      using 1 <;> norm_num
  have hLh : Tendsto Lh atTop (nhds 1) := by
    dsimp only [Lh]
    convert hA.mul (((hHh.mul hA).sub hMh).sub hepsilon) |>.sub hMh
      using 1 <;> norm_num
  have hmin : Tendsto (fun N => min (Lv N) (Lh N)) atTop (nhds 1) := by
    simpa using hLv.min hLh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hmin tendsto_const_nhds
  · intro N
    cases hbranch : branch N
    · simpa [hbranch] using
        (min_le_right (Lv N) (Lh N)).trans
          (hhorizontal N hbranch)
    · simpa [hbranch] using
        (min_le_left (Lv N) (Lh N)).trans
          (hvertical N hbranch)
  · intro N
    cases hbranch : branch N
    · simpa [hbranch] using hCh N
    · simpa [hbranch] using hCv N





theorem crossing_max_tendsto_one_of_approxPreferredSide_root_branches
    (root A Hv Hh Mv Mh epsilon Cv Ch : Nat → Real)
    (hroot : Tendsto root atTop (nhds 1))
    (hrootA : ∀ N, root N ≤ A N + epsilon N)
    (hAupper : ∀ N, A N ≤ 1)
    (hHv : Tendsto Hv atTop (nhds 1))
    (hHh : Tendsto Hh atTop (nhds 1))
    (hMv : Tendsto Mv atTop (nhds 0))
    (hMh : Tendsto Mh atTop (nhds 0))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hbranch : ∀ N,
      A N * (Hv N * A N - Mv N - epsilon N) - Mv N ≤ Cv N ∨
      A N * (Hh N * A N - Mh N - epsilon N) - Mh N ≤ Ch N)
    (hCv : ∀ N, Cv N ≤ 1) (hCh : ∀ N, Ch N ≤ 1) :
    Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
  have hlower : Tendsto (fun N => root N - epsilon N) atTop (nhds 1) := by
    convert hroot.sub hepsilon using 1 <;> norm_num
  have hA : Tendsto A atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro N
      linarith [hrootA N]
    · exact hAupper
  exact crossing_max_tendsto_one_of_approxPreferredSide_branches
    A Hv Hh Mv Mh epsilon Cv Ch hA hHv hHh hMv hMh hepsilon
    hbranch hCv hCh


theorem crossing_selected_tendsto_one_of_approxPreferredSide_root_branches
    (branch : Nat -> Bool)
    (root A Hv Hh Mv Mh epsilon Cv Ch : Nat -> Real)
    (hroot : Tendsto root atTop (nhds 1))
    (hrootA : forall N, root N <= A N + epsilon N)
    (hAupper : forall N, A N <= 1)
    (hHv : Tendsto Hv atTop (nhds 1))
    (hHh : Tendsto Hh atTop (nhds 1))
    (hMv : Tendsto Mv atTop (nhds 0))
    (hMh : Tendsto Mh atTop (nhds 0))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hvertical : forall N, branch N = true ->
      A N * (Hv N * A N - Mv N - epsilon N) - Mv N <= Cv N)
    (hhorizontal : forall N, branch N = false ->
      A N * (Hh N * A N - Mh N - epsilon N) - Mh N <= Ch N)
    (hCv : forall N, Cv N <= 1) (hCh : forall N, Ch N <= 1) :
    Tendsto (fun N => if branch N then Cv N else Ch N)
      atTop (nhds 1) := by
  have hlower : Tendsto (fun N => root N - epsilon N) atTop (nhds 1) := by
    convert hroot.sub hepsilon using 1 <;> norm_num
  have hA : Tendsto A atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro N
      linarith [hrootA N]
    · exact hAupper
  exact crossing_selected_tendsto_one_of_approxPreferredSide_branches
    branch A Hv Hh Mv Mh epsilon Cv Ch hA hHv hHh hMv hMh hepsilon
    hvertical hhorizontal hCv hCh

end StatMech.FK.PeriodicPlanar
