/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldBoundaryEnlargement
import Code.FK.PeriodicPlanarSheffieldRectangleTranslation
import Code.FK.PeriodicPlanarSheffieldApproximatePreference
import Code.FK.PeriodicPlanarSheffieldTemplateGridAssembly











open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

omit [Countable V] in
theorem PeriodicGraph.shift_image_shift
    (P : PeriodicGraph V) (z w : Site 2) (S : Set V) :
    P.shift w '' (P.shift z '' S) = P.shift (z + w) '' S := by
  rw [Set.image_image]
  apply congrArg (fun f : V → V => f '' S)
  funext x
  exact (P.shift_add z w x).symm



theorem exists_cofinalIndex_weightedFourDefects_tendsto_zero
    (fBottom fTop fLeft fRight : Nat → Real)
    (hfBottom : Tendsto fBottom atTop (nhds 1))
    (hfTop : Tendsto fTop atTop (nhds 1))
    (hfLeft : Tendsto fLeft atTop (nhds 1))
    (hfRight : Tendsto fRight atTop (nhds 1))
    (hfBottomLe : ∀ n, fBottom n ≤ 1)
    (hfTopLe : ∀ n, fTop n ≤ 1)
    (hfLeftLe : ∀ n, fLeft n ≤ 1)
    (hfRightLe : ∀ n, fRight n ≤ 1)
    (width height : Nat → Nat) :
    ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧
      Tendsto (fun n =>
        (width n + 1 : Real) * (1 - fBottom (index n)) +
        (width n + 1 : Real) * (1 - fTop (index n)) +
        (height n + 1 : Real) * (1 - fLeft (index n)) +
        (height n + 1 : Real) * (1 - fRight (index n)))
        atTop (nhds 0) := by
  let weight : Nat → Real := fun n =>
    2 * (width n + 1 : Real) + 2 * (height n + 1 : Real)
  let epsilon : Nat → Real := fun n =>
    1 / (weight n * (n + 1 : Real))
  have hweight (n : Nat) : 0 < weight n := by
    dsimp only [weight]
    positivity
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  choose nBottom hnBottom using fun n =>
    (Metric.tendsto_atTop.1 hfBottom) (epsilon n) (hepsilon n)
  choose nTop hnTop using fun n =>
    (Metric.tendsto_atTop.1 hfTop) (epsilon n) (hepsilon n)
  choose nLeft hnLeft using fun n =>
    (Metric.tendsto_atTop.1 hfLeft) (epsilon n) (hepsilon n)
  choose nRight hnRight using fun n =>
    (Metric.tendsto_atTop.1 hfRight) (epsilon n) (hepsilon n)
  let index : Nat → Nat := fun n =>
    max n (max (nBottom n) (max (nTop n) (max (nLeft n) (nRight n))))
  have hindex (n : Nat) : n ≤ index n := by
    exact Nat.le_max_left _ _
  have hBottom (n : Nat) :
      1 - fBottom (index n) < epsilon n := by
    have hdist := hnBottom n (index n) (le_trans (Nat.le_max_left _ _)
      (Nat.le_max_right n _))
    rw [Real.dist_eq] at hdist
    have habs : |fBottom (index n) - 1| = 1 - fBottom (index n) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hfBottomLe (index n)))]
      ring
    rwa [habs] at hdist
  have hTop (n : Nat) : 1 - fTop (index n) < epsilon n := by
    have hle : nTop n ≤ index n := by
      dsimp only [index]
      omega
    have hdist := hnTop n (index n) hle
    rw [Real.dist_eq] at hdist
    have habs : |fTop (index n) - 1| = 1 - fTop (index n) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hfTopLe (index n)))]
      ring
    rwa [habs] at hdist
  have hLeft (n : Nat) : 1 - fLeft (index n) < epsilon n := by
    have hle : nLeft n ≤ index n := by
      dsimp only [index]
      omega
    have hdist := hnLeft n (index n) hle
    rw [Real.dist_eq] at hdist
    have habs : |fLeft (index n) - 1| = 1 - fLeft (index n) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hfLeftLe (index n)))]
      ring
    rwa [habs] at hdist
  have hRight (n : Nat) : 1 - fRight (index n) < epsilon n := by
    have hle : nRight n ≤ index n := by
      dsimp only [index]
      omega
    have hdist := hnRight n (index n) hle
    rw [Real.dist_eq] at hdist
    have habs : |fRight (index n) - 1| = 1 - fRight (index n) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hfRightLe (index n)))]
      ring
    rwa [habs] at hdist
  refine ⟨index, hindex, ?_⟩
  have hnonneg (n : Nat) : 0 ≤
      (width n + 1 : Real) * (1 - fBottom (index n)) +
      (width n + 1 : Real) * (1 - fTop (index n)) +
      (height n + 1 : Real) * (1 - fLeft (index n)) +
      (height n + 1 : Real) * (1 - fRight (index n)) := by
    have hw0 : 0 ≤ (width n + 1 : Real) := by positivity
    have hh0 : 0 ≤ (height n + 1 : Real) := by positivity
    have hB0 : 0 ≤ 1 - fBottom (index n) :=
      sub_nonneg.mpr (hfBottomLe (index n))
    have hT0 : 0 ≤ 1 - fTop (index n) :=
      sub_nonneg.mpr (hfTopLe (index n))
    have hL0 : 0 ≤ 1 - fLeft (index n) :=
      sub_nonneg.mpr (hfLeftLe (index n))
    have hR0 : 0 ≤ 1 - fRight (index n) :=
      sub_nonneg.mpr (hfRightLe (index n))
    positivity
  have hupper (n : Nat) :
      (width n + 1 : Real) * (1 - fBottom (index n)) +
        (width n + 1 : Real) * (1 - fTop (index n)) +
        (height n + 1 : Real) * (1 - fLeft (index n)) +
        (height n + 1 : Real) * (1 - fRight (index n)) ≤
          1 / (n + 1 : Real) := by
    have hsum :
        (width n + 1 : Real) * (1 - fBottom (index n)) +
          (width n + 1 : Real) * (1 - fTop (index n)) +
          (height n + 1 : Real) * (1 - fLeft (index n)) +
          (height n + 1 : Real) * (1 - fRight (index n)) <
            weight n * epsilon n := by
      have hw : 0 < (width n + 1 : Real) := by positivity
      have hh : 0 < (height n + 1 : Real) := by positivity
      nlinarith [hBottom n, hTop n, hLeft n, hRight n]
    have heq : weight n * epsilon n = 1 / (n + 1 : Real) := by
      dsimp only [epsilon]
      field_simp [ne_of_gt (hweight n)]
    linarith
  apply squeeze_zero hnonneg hupper
  exact tendsto_one_div_add_atTop_nhds_zero_nat





theorem exists_cofinalIndex_finsetSum_tendsto_zero
    (f : Nat → Nat → Real)
    (hf : ∀ k, Tendsto (f k) atTop (nhds 0)) :
    ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), f k (index n))
        atTop (nhds 0) := by
  have hrow (n : Nat) : Tendsto
      (fun m => ∑ k ∈ Finset.range (n + 1), f k m)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.range (n + 1))
      (fun k _hk => hf k)
  have hepsilon (n : Nat) : 0 < (1 : Real) / (n + 1) := by positivity
  choose threshold hthreshold using fun n =>
    (Metric.tendsto_atTop.1 (hrow n))
      ((1 : Real) / (n + 1)) (hepsilon n)
  let index : Nat → Nat := fun n => max n (threshold n)
  have hindex (n : Nat) : n ≤ index n := Nat.le_max_left _ _
  have hdist (n : Nat) :
      dist (∑ k ∈ Finset.range (n + 1), f k (index n)) 0 <
        (1 : Real) / (n + 1) :=
    hthreshold n (index n) (Nat.le_max_right _ _)
  refine ⟨index, hindex, ?_⟩
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero
  · exact fun _ => abs_nonneg _
  · intro n
    change |∑ k ∈ Finset.range (n + 1), f k (index n)| ≤
      (1 : Real) / (n + 1)
    simpa [Real.dist_eq] using le_of_lt (hdist n)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat



theorem rectangleEndpointPreferenceError_le_boundaryDefects
    {n m : Nat}
    (bottom top left right : PreferenceGridVertex n m → Real)
    (deltaBottom deltaTop deltaLeft deltaRight : Real)
    (hdeltaBottom : 0 ≤ deltaBottom) (hdeltaTop : 0 ≤ deltaTop)
    (hdeltaLeft : 0 ≤ deltaLeft) (hdeltaRight : 0 ≤ deltaRight)
    (hbottom : ∀ i : Fin (n + 1),
      1 - deltaBottom ≤ bottom (i, 0))
    (htop : ∀ i : Fin (n + 1),
      1 - deltaTop ≤ top (i, Fin.last m))
    (hleft : ∀ j : Fin (m + 1),
      1 - deltaLeft ≤ left (0, j))
    (hright : ∀ j : Fin (m + 1),
      1 - deltaRight ≤ right (Fin.last n, j))
    (hbottomLe : ∀ x, bottom x ≤ 1) (htopLe : ∀ x, top x ≤ 1)
    (hleftLe : ∀ x, left x ≤ 1) (hrightLe : ∀ x, right x ≤ 1) :
    rectangleEndpointPreferenceError bottom top left right ≤
      (n + 1 : Real) * deltaBottom + (n + 1 : Real) * deltaTop +
        (m + 1 : Real) * deltaLeft + (m + 1 : Real) * deltaRight := by
  have hB : ∑ i : Fin (n + 1),
      max (top (i, 0) - bottom (i, 0)) 0 ≤
        (n + 1 : Real) * deltaBottom := by
    calc
      ∑ i : Fin (n + 1), max (top (i, 0) - bottom (i, 0)) 0 ≤
          ∑ _i : Fin (n + 1), deltaBottom := by
            apply Finset.sum_le_sum
            intro i _hi
            exact max_le (by linarith [htopLe (i, 0), hbottom i])
              hdeltaBottom
      _ = (n + 1 : Real) * deltaBottom := by simp
  have hT : ∑ i : Fin (n + 1),
      max (bottom (i, Fin.last m) - top (i, Fin.last m)) 0 ≤
        (n + 1 : Real) * deltaTop := by
    calc
      ∑ i : Fin (n + 1),
          max (bottom (i, Fin.last m) - top (i, Fin.last m)) 0 ≤
          ∑ _i : Fin (n + 1), deltaTop := by
            apply Finset.sum_le_sum
            intro i _hi
            exact max_le (by linarith [hbottomLe (i, Fin.last m), htop i])
              hdeltaTop
      _ = (n + 1 : Real) * deltaTop := by simp
  have hL : ∑ j : Fin (m + 1),
      max (right (0, j) - left (0, j)) 0 ≤
        (m + 1 : Real) * deltaLeft := by
    calc
      ∑ j : Fin (m + 1), max (right (0, j) - left (0, j)) 0 ≤
          ∑ _j : Fin (m + 1), deltaLeft := by
            apply Finset.sum_le_sum
            intro j _hj
            exact max_le (by linarith [hrightLe (0, j), hleft j]) hdeltaLeft
      _ = (m + 1 : Real) * deltaLeft := by simp
  have hR : ∑ j : Fin (m + 1),
      max (left (Fin.last n, j) - right (Fin.last n, j)) 0 ≤
        (m + 1 : Real) * deltaRight := by
    calc
      ∑ j : Fin (m + 1),
          max (left (Fin.last n, j) - right (Fin.last n, j)) 0 ≤
          ∑ _j : Fin (m + 1), deltaRight := by
            apply Finset.sum_le_sum
            intro j _hj
            exact max_le (by linarith [hleftLe (Fin.last n, j), hright j])
              hdeltaRight
      _ = (m + 1 : Real) * deltaRight := by simp
  unfold rectangleEndpointPreferenceError
  linarith



theorem rectangleEndpointPreferenceError_le_boundaryProbabilities
    {n m : Nat}
    (bottom top left right : PreferenceGridVertex n m → Real)
    (pBottom pTop pLeft pRight : Real)
    (hpBottom : pBottom ≤ 1) (hpTop : pTop ≤ 1)
    (hpLeft : pLeft ≤ 1) (hpRight : pRight ≤ 1)
    (hbottom : ∀ i : Fin (n + 1), pBottom ≤ bottom (i, 0))
    (htop : ∀ i : Fin (n + 1), pTop ≤ top (i, Fin.last m))
    (hleft : ∀ j : Fin (m + 1), pLeft ≤ left (0, j))
    (hright : ∀ j : Fin (m + 1), pRight ≤ right (Fin.last n, j))
    (hbottomLe : ∀ x, bottom x ≤ 1) (htopLe : ∀ x, top x ≤ 1)
    (hleftLe : ∀ x, left x ≤ 1) (hrightLe : ∀ x, right x ≤ 1) :
    rectangleEndpointPreferenceError bottom top left right ≤
      (n + 1 : Real) * (1 - pBottom) + (n + 1 : Real) * (1 - pTop) +
        (m + 1 : Real) * (1 - pLeft) + (m + 1 : Real) * (1 - pRight) := by
  apply rectangleEndpointPreferenceError_le_boundaryDefects
    bottom top left right (1 - pBottom) (1 - pTop) (1 - pLeft) (1 - pRight)
  · linarith
  · linarith
  · linarith
  · linarith
  · simpa using hbottom
  · simpa using htop
  · simpa using hleft
  · simpa using hright
  · exact hbottomLe
  · exact htopLe
  · exact hleftLe
  · exact hrightLe




theorem rectangleEndpointPreferenceError_tendsto_zero_of_boundaryProbabilities
    (width height : Nat → Nat)
    (bottom top left right : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real)
    (pBottom pTop pLeft pRight : Nat → Real)
    (hpBottom : ∀ n, pBottom n ≤ 1) (hpTop : ∀ n, pTop n ≤ 1)
    (hpLeft : ∀ n, pLeft n ≤ 1) (hpRight : ∀ n, pRight n ≤ 1)
    (hbottom : ∀ n (i : Fin (width n + 1)),
      pBottom n ≤ bottom n (i, 0))
    (htop : ∀ n (i : Fin (width n + 1)),
      pTop n ≤ top n (i, Fin.last (height n)))
    (hleft : ∀ n (j : Fin (height n + 1)),
      pLeft n ≤ left n (0, j))
    (hright : ∀ n (j : Fin (height n + 1)),
      pRight n ≤ right n (Fin.last (width n), j))
    (hbottomLe : ∀ n x, bottom n x ≤ 1)
    (htopLe : ∀ n x, top n x ≤ 1)
    (hleftLe : ∀ n x, left n x ≤ 1)
    (hrightLe : ∀ n x, right n x ≤ 1)
    (hdefects : Tendsto (fun n =>
      (width n + 1 : Real) * (1 - pBottom n) +
      (width n + 1 : Real) * (1 - pTop n) +
      (height n + 1 : Real) * (1 - pLeft n) +
      (height n + 1 : Real) * (1 - pRight n)) atTop (nhds 0)) :
    Tendsto (fun n => rectangleEndpointPreferenceError
      (bottom n) (top n) (left n) (right n)) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun n => rectangleEndpointPreferenceError_nonneg
      (bottom n) (top n) (left n) (right n)
  · intro n
    exact rectangleEndpointPreferenceError_le_boundaryProbabilities
      (bottom n) (top n) (left n) (right n)
      (pBottom n) (pTop n) (pLeft n) (pRight n)
      (hpBottom n) (hpTop n) (hpLeft n) (hpRight n)
      (hbottom n) (htop n) (hleft n) (hright n)
      (hbottomLe n) (htopLe n) (hleftLe n) (hrightLe n)
  · exact hdefects



theorem PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect
    (E : PeriodicPlaneEmbedding P)
    {n m : Nat} (base : Site 2) (S : Set V)
    {a b c d a' b' c' d' : Real}
    (hbase : P.shift base '' S ⊆ E.rectVertices a b c d)
    (ha : a' ≤ a) (hb : b + n ≤ b')
    (hc : c' ≤ c) (hd : d + m ≤ d') :
    ∀ v : PreferenceGridVertex n m,
      P.shift (base + preferenceGridSite v) '' S ⊆
        E.rectVertices a' b' c' d' := by
  intro v x hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [P.shift_add]
  let z := preferenceGridSite v
  have huBase : P.shift base u ∈ E.rectVertices a b c d :=
    hbase ⟨u, hu, rfl⟩
  have huShift : P.shift z (P.shift base u) ∈
      E.rectVertices (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
    (E.shift_mem_rectVertices z a b c d (P.shift base u)).2 huBase
  have hz0 : 0 ≤ (z 0 : Real) := by
    dsimp only [z, preferenceGridSite]
    positivity
  have hz1 : 0 ≤ (z 1 : Real) := by
    dsimp only [z, preferenceGridSite]
    positivity
  have hz0le : (z 0 : Real) ≤ n := by
    dsimp only [z, preferenceGridSite]
    exact_mod_cast Nat.le_of_lt_succ v.1.isLt
  have hz1le : (z 1 : Real) ≤ m := by
    dsimp only [z, preferenceGridSite]
    exact_mod_cast Nat.le_of_lt_succ v.2.isLt
  have hza : a' ≤ a + (z 0 : Real) := by linarith
  have hzb : b + (z 0 : Real) ≤ b' := by linarith
  have hzc : c' ≤ c + (z 1 : Real) := by linarith
  have hzd : d + (z 1 : Real) ≤ d' := by linarith
  exact E.rectVertices_mono
    hza hzb hzc hzd huShift

set_option linter.unusedVariables false in



theorem PeriodicPlaneEmbedding.exists_uniformTemplate_intrinsicError_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
        atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a b c d : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      Tendsto (fun n => rectangleEndpointPreferenceError
        (bottom n) (top n) (left n) (right n)) atTop (nhds 0) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_approxPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d bottom top left right
    hsource hrect hbottomScore htopScore hleftScore hrightScore herror
  let epsilon : Nat → Real := fun n => rectangleEndpointPreferenceError
    (bottom n) (top n) (left n) (right n)
  apply hcross width height hwidth hheight base a b c d epsilon
    bottom top left right herror
  · exact fun n => rectangleEndpointPreferenceError_nonneg
      (bottom n) (top n) (left n) (right n)
  · exact hsource
  · exact hrect
  · exact hbottomScore
  · exact htopScore
  · exact hleftScore
  · exact hrightScore
  · intro n
    exact (rectangleEndpointPreferenceError_bounds
      (bottom n) (top n) (left n) (right n)).1
  · intro n
    exact (rectangleEndpointPreferenceError_bounds
      (bottom n) (top n) (left n) (right n)).2.1
  · intro n
    exact (rectangleEndpointPreferenceError_bounds
      (bottom n) (top n) (left n) (right n)).2.2.1
  · intro n
    exact (rectangleEndpointPreferenceError_bounds
      (bottom n) (top n) (left n) (right n)).2.2.2

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
        atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a b c d : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real)
      (pBottom pTop pLeft pRight : Nat → Real),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n, pBottom n ≤ 1) → (∀ n, pTop n ≤ 1) →
      (∀ n, pLeft n ≤ 1) → (∀ n, pRight n ≤ 1) →
      (∀ n (i : Fin (width n + 1)),
        pBottom n ≤ bottom n (i, 0)) →
      (∀ n (i : Fin (width n + 1)),
        pTop n ≤ top n (i, Fin.last (height n))) →
      (∀ n (j : Fin (height n + 1)),
        pLeft n ≤ left n (0, j)) →
      (∀ n (j : Fin (height n + 1)),
        pRight n ≤ right n (Fin.last (width n), j)) →
      Tendsto (fun n =>
        (width n + 1 : Real) * (1 - pBottom n) +
        (width n + 1 : Real) * (1 - pTop n) +
        (height n + 1 : Real) * (1 - pLeft n) +
        (height n + 1 : Real) * (1 - pRight n)) atTop (nhds 0) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_intrinsicError_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d bottom top left right
    pBottom pTop pLeft pRight hsource hrect hbottomScore htopScore
    hleftScore hrightScore hpBottom hpTop hpLeft hpRight
    hbottom htop hleft hright hdefects
  apply hcross width height hwidth hheight base a b c d
    bottom top left right hsource hrect hbottomScore htopScore
      hleftScore hrightScore
  apply rectangleEndpointPreferenceError_tendsto_zero_of_boundaryProbabilities
    width height bottom top left right pBottom pTop pLeft pRight
    hpBottom hpTop hpLeft hpRight hbottom htop hleft hright
  · intro n x
    rw [hbottomScore n x]
    exact measureReal_le_one
  · intro n x
    rw [htopScore n x]
    exact measureReal_le_one
  · intro n x
    rw [hleftScore n x]
    exact measureReal_le_one
  · intro n x
    rw [hrightScore n x]
    exact measureReal_le_one
  · exact hdefects



theorem PeriodicPlaneEmbedding.rectLeftConnection_tangential_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (hz : z 0 = 0) (a b c d b' c' d' : Real)
    (S : Set V)
    (hb : b + (z 0 : Real) ≤ b')
    (hc : c' ≤ c + (z 1 : Real))
    (hd : d + (z 1 : Real) ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b' c' d'
        (P.shift z '' S) (E.rectLeftBoundaryVertices a b' c' d')) := by
  have htranslate := E.rectLeftConnection_translate_measureReal_eq
    mu hTI z a b c d S
  have ha : a + (z 0 : Real) = a := by simp [hz]
  rw [ha] at htranslate
  rw [← htranslate]
  exact measureReal_mono
    (E.rectLeftConnectionEvent_mono_otherBounds
      (P.shift z '' S) hb hc hd)



theorem PeriodicPlaneEmbedding.rectRightConnection_tangential_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (hz : z 0 = 0) (a b c d a' c' d' : Real)
    (S : Set V)
    (ha : a' ≤ a + (z 0 : Real))
    (hc : c' ≤ c + (z 1 : Real))
    (hd : d + (z 1 : Real) ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b c' d'
        (P.shift z '' S) (E.rectRightBoundaryVertices a' b c' d')) := by
  have htranslate := E.rectRightConnection_translate_measureReal_eq
    mu hTI z a b c d S
  have hb : b + (z 0 : Real) = b := by simp [hz]
  rw [hb] at htranslate
  rw [← htranslate]
  exact measureReal_mono
    (E.rectRightConnectionEvent_mono_otherBounds
      (P.shift z '' S) ha hc hd)



theorem PeriodicPlaneEmbedding.rectBottomConnection_tangential_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (hz : z 1 = 0) (a b c d a' b' d' : Real)
    (S : Set V)
    (ha : a' ≤ a + (z 0 : Real))
    (hb : b + (z 0 : Real) ≤ b')
    (hd : d + (z 1 : Real) ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c d'
        (P.shift z '' S) (E.rectBottomBoundaryVertices a' b' c d')) := by
  have htranslate := E.rectBottomConnection_translate_measureReal_eq
    mu hTI z a b c d S
  have hc : c + (z 1 : Real) = c := by simp [hz]
  rw [hc] at htranslate
  rw [← htranslate]
  exact measureReal_mono
    (E.rectBottomConnectionEvent_mono_otherBounds
      (P.shift z '' S) ha hb hd)



theorem PeriodicPlaneEmbedding.rectTopConnection_tangential_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (hz : z 1 = 0) (a b c d a' b' c' : Real)
    (S : Set V)
    (ha : a' ≤ a + (z 0 : Real))
    (hb : b + (z 0 : Real) ≤ b')
    (hc : c' ≤ c + (z 1 : Real)) :
    mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c' d
        (P.shift z '' S) (E.rectTopBoundaryVertices a' b' c' d)) := by
  have htranslate := E.rectTopConnection_translate_measureReal_eq
    mu hTI z a b c d S
  have hd : d + (z 1 : Real) = d := by simp [hz]
  rw [hd] at htranslate
  rw [← htranslate]
  exact measureReal_mono
    (E.rectTopConnectionEvent_mono_otherBounds
      (P.shift z '' S) ha hb hc)

end StatMech.FK.PeriodicPlanar
