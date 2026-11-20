/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWInsetLeftSourceAttachment

















open Finset SimpleGraph Set MeasureTheory

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section





def rlc_affineFlipYFun (k : Int) (x : Site 2) : Site 2 :=
  ![x 0, k - x 1]

def rlc_affineFlipY (k : Int) : Site 2 ≃ Site 2 where
  toFun := rlc_affineFlipYFun k
  invFun := rlc_affineFlipYFun k
  left_inv x := by funext i; fin_cases i <;> simp [rlc_affineFlipYFun]
  right_inv x := by funext i; fin_cases i <;> simp [rlc_affineFlipYFun]

@[simp] theorem rlc_affineFlipY_zero (k : Int) (x : Site 2) :
    rlc_affineFlipY k x 0 = x 0 := by
  simp [rlc_affineFlipY, rlc_affineFlipYFun]

@[simp] theorem rlc_affineFlipY_one (k : Int) (x : Site 2) :
    rlc_affineFlipY k x 1 = k - x 1 := by
  simp [rlc_affineFlipY, rlc_affineFlipYFun]

@[simp] theorem rlc_affineFlipY_involutive (k : Int) (x : Site 2) :
    rlc_affineFlipY k (rlc_affineFlipY k x) = x := by
  exact (rlc_affineFlipY k).left_inv x

theorem rlc_adj_affineFlipY (k : Int) (x y : Site 2) :
    (hypercubicLattice 2).Adj x y ↔
      (hypercubicLattice 2).Adj (rlc_affineFlipY k x) (rlc_affineFlipY k y) := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [rlc_affineFlipY_zero, rlc_affineFlipY_one]
  rw [show (k - x 1) - (k - y 1) = -(x 1 - y 1) by ring,
    Int.natAbs_neg]

noncomputable def rlc_affineFlipYEdge (k : Int) :
    Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  sym2Congr (rlc_affineFlipY k)

theorem rlc_affineFlipYEdge_symm_apply (k : Int) (e : Sym2 (Site 2)) :
    (rlc_affineFlipYEdge k).symm e = e.map (rlc_affineFlipY k) := by
  simp [rlc_affineFlipYEdge, sym2Congr, rlc_affineFlipY]

noncomputable def rlc_affineFlipYConfig (k : Int) :
    ConfigSpace (Sym2 (Site 2)) -> ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) (rlc_affineFlipYEdge k)

theorem rlc_affineFlipYConfig_apply (k : Int)
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rlc_affineFlipYConfig k omega e = omega (e.map (rlc_affineFlipY k)) := by
  rw [rlc_affineFlipYConfig, Equiv.piCongrLeft_apply, eq_rec_constant,
    rlc_affineFlipYEdge_symm_apply]

theorem rlc_affineFlipYConfig_involutive (k : Int)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_affineFlipYConfig k (rlc_affineFlipYConfig k omega) = omega := by
  funext e
  rw [rlc_affineFlipYConfig_apply, rlc_affineFlipYConfig_apply]
  induction e using Sym2.inductionOn with
  | _ x y => simp

theorem rlc_affineFlipYConfig_measurable (k : Int) :
    Measurable (rlc_affineFlipYConfig k) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool)
    (rlc_affineFlipYEdge k)).measurable

theorem rlc_affineFlipY_measurePreserving (k : Int) (p : NNReal) (hp : p <= 1) :
    MeasurePreserving (rlc_affineFlipYConfig k)
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) := by
  refine ⟨rlc_affineFlipYConfig_measurable k, ?_⟩
  rw [rlc_affineFlipYConfig]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure p hp)
    (rlc_affineFlipYEdge k)

theorem rlc_mem_rect_affineFlipY (a b c d k : Int) (hcd : c + d = k)
    (x : Site 2) :
    x ∈ rect a b c d ↔ rlc_affineFlipY k x ∈ rect a b c d := by
  simp only [mem_rect, rlc_affineFlipY_zero, rlc_affineFlipY_one]
  omega

theorem rlc_mem_leftSide_affineFlipY (a b c d k : Int) (hcd : c + d = k)
    (x : Site 2) :
    x ∈ leftSide a b c d ↔ rlc_affineFlipY k x ∈ leftSide a b c d := by
  rw [mem_leftSide, mem_leftSide]
  exact and_congr (rlc_mem_rect_affineFlipY a b c d k hcd x) (by simp)

theorem rlc_mem_rightSide_affineFlipY (a b c d k : Int) (hcd : c + d = k)
    (x : Site 2) :
    x ∈ rightSide a b c d ↔ rlc_affineFlipY k x ∈ rightSide a b c d := by
  rw [mem_rightSide, mem_rightSide]
  exact and_congr (rlc_mem_rect_affineFlipY a b c d k hcd x) (by simp)

theorem rlc_isOpenEdge_affineFlipY (k : Int)
    (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    IsOpenEdge 2 (rlc_affineFlipYConfig k omega) x y ↔
      IsOpenEdge 2 omega (rlc_affineFlipY k x) (rlc_affineFlipY k y) := by
  unfold IsOpenEdge
  have hedge : (s(x, y) : Sym2 (Site 2)).map (rlc_affineFlipY k) =
      s(rlc_affineFlipY k x, rlc_affineFlipY k y) := Sym2.map_mk _ _ _
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨(rlc_adj_affineFlipY k x y).mp hadj, ?_⟩
    rwa [rlc_affineFlipYConfig_apply, hedge] at hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨(rlc_adj_affineFlipY k x y).mpr hadj, ?_⟩
    rwa [rlc_affineFlipYConfig_apply, hedge]

noncomputable def rlc_affineFlipYInducedHom (a b c d k : Int)
    (hcd : c + d = k) (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (rect a b c d) →g
      openSubgraphInduce 2 (rlc_affineFlipYConfig k omega) (rect a b c d) where
  toFun := fun x =>
    ⟨rlc_affineFlipY k (x : Site 2),
      (rlc_mem_rect_affineFlipY a b c d k hcd x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (rlc_affineFlipYConfig k omega)
      (rlc_affineFlipY k (x : Site 2)) (rlc_affineFlipY k (y : Site 2))
    rw [rlc_isOpenEdge_affineFlipY]
    simpa using hxy

theorem rlc_affineFlipY_lrRestricted (a b c d k : Int) (hcd : c + d = k)
    (L R : Set (Site 2)) (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_lrRestrictedEvent a b c d L R ->
      rlc_affineFlipYConfig k omega ∈ rlc_lrRestrictedEvent a b c d
        (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) := by
  rintro ⟨x, y, hxL, hyR, hxy⟩
  let xf : leftSide a b c d :=
    ⟨rlc_affineFlipY k (x : Site 2),
      (rlc_mem_leftSide_affineFlipY a b c d k hcd x).mp x.2⟩
  let yf : rightSide a b c d :=
    ⟨rlc_affineFlipY k (y : Site 2),
      (rlc_mem_rightSide_affineFlipY a b c d k hcd y).mp y.2⟩
  refine ⟨xf, yf, ⟨x, hxL, rfl⟩, ⟨y, hyR, rfl⟩, ?_⟩
  exact hxy.map (rlc_affineFlipYInducedHom a b c d k hcd omega)

theorem rlc_affineFlipY_image_image (k : Int) (L : Set (Site 2)) :
    rlc_affineFlipY k '' (rlc_affineFlipY k '' L) = L := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzx⟩
    have hzx' : z = x := by simpa using hzx
    rwa [hzx'] at hz
  · intro hx
    exact ⟨rlc_affineFlipY k x,
      ⟨x, hx, rfl⟩, rlc_affineFlipY_involutive k x⟩

theorem rlc_affineFlipY_lrRestricted_prob_eq (a b c d k : Int)
    (hcd : c + d = k) (L R : Set (Site 2)) (p : NNReal) (hp : p <= 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (rlc_lrRestrictedEvent a b c d L R) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (rlc_lrRestrictedEvent a b c d
          (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R)) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpre : rlc_affineFlipYConfig k ⁻¹' rlc_lrRestrictedEvent a b c d L R =
      rlc_lrRestrictedEvent a b c d
        (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) := by
    ext omega
    constructor
    · intro h
      have ht := rlc_affineFlipY_lrRestricted a b c d k hcd L R
        (rlc_affineFlipYConfig k omega) h
      rwa [rlc_affineFlipYConfig_involutive] at ht
    · intro h
      have ht := rlc_affineFlipY_lrRestricted a b c d k hcd
        (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) omega h
      simpa only [rlc_affineFlipY_image_image] using ht
  calc
    mu.real (rlc_lrRestrictedEvent a b c d L R) =
        mu.real (rlc_affineFlipYConfig k ⁻¹'
          rlc_lrRestrictedEvent a b c d L R) :=
      ((rlc_affineFlipY_measurePreserving k p hp).measureReal_preimage
        (measurableSet_of_dependsOn
          (rlc_lrRestrictedEvent_dependsOn a b c d L R)).nullMeasurableSet).symm
    _ = mu.real (rlc_lrRestrictedEvent a b c d
          (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R)) := by rw [hpre]

theorem rlc_affineFlipY_image_univ (k : Int) :
    rlc_affineFlipY k '' (Set.univ : Set (Site 2)) = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨rlc_affineFlipY k x, Set.mem_univ _,
      rlc_affineFlipY_involutive k x⟩

theorem rlc_negOneFlip_image_upper :
    rlc_affineFlipY (-1) '' rlc_upperHalf = rlc_strictLowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 <= y 1 at hy
    change -1 - y 1 < 0
    omega
  · intro hx
    change x 1 < 0 at hx
    refine ⟨rlc_affineFlipY (-1) x, ?_, rlc_affineFlipY_involutive (-1) x⟩
    change 0 <= -1 - x 1
    omega

theorem rlc_negOneFlip_image_strictLower :
    rlc_affineFlipY (-1) '' rlc_strictLowerHalf = rlc_upperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y 1 < 0 at hy
    change 0 <= -1 - y 1
    omega
  · intro hx
    change 0 <= x 1 at hx
    refine ⟨rlc_affineFlipY (-1) x, ?_, rlc_affineFlipY_involutive (-1) x⟩
    change -1 - x 1 < 0
    omega

theorem rlc_oneFlip_image_strictUpper :
    rlc_affineFlipY 1 '' rlc_strictUpperHalf = rlc_lowerHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 < y 1 at hy
    change 1 - y 1 <= 0
    omega
  · intro hx
    change x 1 <= 0 at hx
    refine ⟨rlc_affineFlipY 1 x, ?_, rlc_affineFlipY_involutive 1 x⟩
    change 0 < 1 - x 1
    omega

theorem rlc_oneFlip_image_lower :
    rlc_affineFlipY 1 '' rlc_lowerHalf = rlc_strictUpperHalf := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y 1 <= 0 at hy
    change 0 < 1 - y 1
    omega
  · intro hx
    change 0 < x 1 at hx
    refine ⟨rlc_affineFlipY 1 x, ?_, rlc_affineFlipY_involutive 1 x⟩
    change 1 - x 1 <= 0
    omega



theorem rlc_lrRestricted_of_three (a b c d : Int) (hab : a < b) (hcd : c < d)
    (L R : Set (Site 2)) :
    rlc_lrRestrictedEvent a b c d Set.univ R ∩
        rlc_lrRestrictedEvent a b c d L Set.univ ∩
        verticalCrossingEvent a b c d ⊆
      rlc_lrRestrictedEvent a b c d L R := by
  intro omega homega
  obtain ⟨⟨hupper, hlower⟩, hvertical⟩ := homega
  obtain ⟨xu, yu, _hxu, hyu, hcu⟩ := hupper
  obtain ⟨xl, yl, hxl, _hyl, hcl⟩ := hlower
  obtain ⟨xb, yt, hcv⟩ := hvertical
  have hsep : vsFix_VSeparatesHFixed omega a b a b c d :=
    vsFix_arc_sides_imp omega a b a b c d
      (StatMech.Lattice.jec_vsFix_arc_sides omega hab hcd.le)
  have hmeet : HVMeetProperty omega a b a b c d :=
    vsFix_hvMeet omega a b a b c d hsep
  obtain ⟨zu, _hzuO, hzuH, hcuzu, hcvzu⟩ :=
    hmeet (le_refl a) hab.le (le_refl b) xu yu hcu xb yt hcv
  obtain ⟨zl, _hzlO, hzlH, hclzl, hcvzl⟩ :=
    hmeet (le_refl a) hab.le (le_refl b) xl yl hcl xb yt hcv
  have hzlzu : ConnectedWithin 2 omega (rect a b c d)
      ⟨zl, hzlH⟩ ⟨zu, hzuH⟩ := by
    simpa only using hcvzl.symm.trans hcvzu
  have hconn : ConnectedWithin 2 omega (rect a b c d)
      ⟨(xl : Site 2), leftSide_subset xl.2⟩
      ⟨(yu : Site 2), rightSide_subset yu.2⟩ :=
    hclzl.trans (hzlzu.trans (hcuzu.symm.trans hcu))
  exact ⟨xl, yu, hxl, hyu, hconn⟩

theorem rlc_half_localization_of_reflected_union
    (H A A' : Set (ConfigSpace (Sym2 (Site 2)))) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real H)
    (hsub : H ⊆ A ∪ A')
    (heq : rba_selfDualMeasure.real A = rba_selfDualMeasure.real A') :
    alpha / 2 <= rba_selfDualMeasure.real A := by
  have hmono : rba_selfDualMeasure.real H <=
      rba_selfDualMeasure.real (A ∪ A') :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := rba_selfDualMeasure) A A'
  rw [← heq] at hunion
  linarith



def rlc_insetRightOddToUpper (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) Set.univ rlc_upperHalf

def rlc_insetRightOddToStrictLower (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) Set.univ rlc_strictLowerHalf

def rlc_insetRightOddStrictLowerToRight (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) rlc_strictLowerHalf Set.univ

def rlc_insetRightOddUpperToRight (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) rlc_upperHalf Set.univ

def rlc_insetRightOddSourceCoreEvent (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1)
    rlc_strictLowerHalf rlc_upperHalf

theorem rlc_insetRightOdd_right_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetRightOddToUpper n) =
      rba_selfDualMeasure.real (rlc_insetRightOddToStrictLower n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    1 (2 * n) (-n) (n - 1) (-1) (by ring)
    Set.univ rlc_upperHalf (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetRightOddToUpper,
    rlc_insetRightOddToStrictLower, rlc_affineFlipY_image_univ,
    rlc_negOneFlip_image_upper] using h

theorem rlc_insetRightOdd_left_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetRightOddStrictLowerToRight n) =
      rba_selfDualMeasure.real (rlc_insetRightOddUpperToRight n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    1 (2 * n) (-n) (n - 1) (-1) (by ring)
    rlc_strictLowerHalf Set.univ (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetRightOddStrictLowerToRight,
    rlc_insetRightOddUpperToRight, rlc_affineFlipY_image_univ,
    rlc_negOneFlip_image_strictLower] using h

theorem rlc_insetRightOdd_horizontal_subset_right (n : Int) :
    horizontalCrossingEvent 1 (2 * n) (-n) (n - 1) ⊆
      rlc_insetRightOddToUpper n ∪ rlc_insetRightOddToStrictLower n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hy : 0 <= (y : Site 2) 1
  · exact Or.inl ⟨x, y, Set.mem_univ _, hy, hxy⟩
  · exact Or.inr ⟨x, y, Set.mem_univ _, lt_of_not_ge hy, hxy⟩

theorem rlc_insetRightOdd_horizontal_subset_left (n : Int) :
    horizontalCrossingEvent 1 (2 * n) (-n) (n - 1) ⊆
      rlc_insetRightOddStrictLowerToRight n ∪ rlc_insetRightOddUpperToRight n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hx : (x : Site 2) 1 < 0
  · exact Or.inl ⟨x, y, hx, Set.mem_univ _, hxy⟩
  · exact Or.inr ⟨x, y, le_of_not_gt hx, Set.mem_univ _, hxy⟩

theorem rlc_insetRightOddToUpper_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1))) :
    alpha / 2 <= rba_selfDualMeasure.real (rlc_insetRightOddToUpper n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetRightOdd_horizontal_subset_right n)
    (rlc_insetRightOdd_right_reflection_prob n)

theorem rlc_insetRightOddStrictLowerToRight_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1))) :
    alpha / 2 <= rba_selfDualMeasure.real
      (rlc_insetRightOddStrictLowerToRight n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetRightOdd_horizontal_subset_left n)
    (rlc_insetRightOdd_left_reflection_prob n)

theorem rlc_insetRightOdd_horizontal_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
  have hbase := rlc_square_half (2 * n - 1) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * n - 1) 0 (2 * n - 1) (![1, -n] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * n - 1) 0 (2 * n - 1))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * n - 1) 0 (2 * n - 1)) := by
    simpa [show 2 * n - 1 + 1 = 2 * n by ring,
      show 2 * n - 1 + -n = n - 1 by ring] using htrans
  rwa [heq]

theorem rlc_insetRightOdd_vertical_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (verticalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
  have hH := rlc_insetRightOdd_horizontal_half n hn
  have hswap := crf_verticalCrossing_eq_horizontal_swap
    1 (2 * n) (-n) (n - 1)
    (rlc_horizontalCrossing_measurableSet (-n) (n - 1) 1 (2 * n))
  have htrans := cti_horizontalCrossing_translation_invariant
    (-n) (n - 1) 1 (2 * n) (![n + 1, -n - 1] : Site 2)
    (rlc_horizontalCrossing_measurableSet (-n) (n - 1) 1 (2 * n))
  have heq : rba_selfDualMeasure.real
      (verticalCrossingEvent 1 (2 * n) (-n) (n - 1)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
    rw [hswap]
    simpa [show -n + (n + 1) = 1 by ring,
      show n - 1 + (n + 1) = 2 * n by ring,
      show 1 + (-n - 1) = -n by ring,
      show 2 * n + (-n - 1) = n - 1 by ring] using htrans.symm
  rwa [heq]

theorem rlc_insetRightOddSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetRightOddSourceCoreEvent n) := by
  let F := (rect_finite 1 (2 * n) (-n) (n - 1)).toFinset
  have h := rlc_diagonal_event_lower_bound (2⁻¹ : NNReal) half_le_one
    ((1 : Real) / 2) (by norm_num)
    (rlc_insetRightOddToUpper n)
    (rlc_insetRightOddStrictLowerToRight n)
    (verticalCrossingEvent 1 (2 * n) (-n) (n - 1))
    (rlc_insetRightOddSourceCoreEvent n)
    (edgesWithinFinset F) (edgesWithinFinset F) (edgesWithinFinset F)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing _ _ _ _)
    (by simpa [F, rlc_insetRightOddToUpper] using
      (rlc_lrRestrictedEvent_dependsOn 1 (2 * n) (-n) (n - 1)
        Set.univ rlc_upperHalf))
    (by simpa [F, rlc_insetRightOddStrictLowerToRight] using
      (rlc_lrRestrictedEvent_dependsOn 1 (2 * n) (-n) (n - 1)
        rlc_strictLowerHalf Set.univ))
    (by simpa [F] using
      rlc_verticalCrossing_dependsOn 1 (2 * n) (-n) (n - 1))
    (rlc_insetRightOddToUpper_half n ((1 : Real) / 2)
      (rlc_insetRightOdd_horizontal_half n hn))
    (rlc_insetRightOddStrictLowerToRight_half n ((1 : Real) / 2)
      (rlc_insetRightOdd_horizontal_half n hn))
    (rlc_insetRightOdd_vertical_half n hn)
    (rlc_lrRestricted_of_three 1 (2 * n) (-n) (n - 1)
      (by omega) (by omega) rlc_strictLowerHalf rlc_upperHalf)
  norm_num at h
  simpa [rba_selfDualMeasure] using h



def rlc_insetLeftOddToStrictUpper (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n Set.univ rlc_strictUpperHalf

def rlc_insetLeftOddToLower (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n Set.univ rlc_lowerHalf

def rlc_insetLeftOddLowerToRight (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n rlc_lowerHalf Set.univ

def rlc_insetLeftOddStrictUpperToRight (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n rlc_strictUpperHalf Set.univ

def rlc_insetLeftOddSourceCoreEvent (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n
    rlc_lowerHalf rlc_strictUpperHalf

theorem rlc_insetLeftOdd_right_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetLeftOddToStrictUpper n) =
      rba_selfDualMeasure.real (rlc_insetLeftOddToLower n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    (-2 * n) (-1) (1 - n) n 1 (by ring)
    Set.univ rlc_strictUpperHalf (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetLeftOddToStrictUpper,
    rlc_insetLeftOddToLower, rlc_affineFlipY_image_univ,
    rlc_oneFlip_image_strictUpper] using h

theorem rlc_insetLeftOdd_left_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetLeftOddLowerToRight n) =
      rba_selfDualMeasure.real (rlc_insetLeftOddStrictUpperToRight n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    (-2 * n) (-1) (1 - n) n 1 (by ring)
    rlc_lowerHalf Set.univ (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetLeftOddLowerToRight,
    rlc_insetLeftOddStrictUpperToRight, rlc_affineFlipY_image_univ,
    rlc_oneFlip_image_lower] using h

theorem rlc_insetLeftOdd_horizontal_subset_right (n : Int) :
    horizontalCrossingEvent (-2 * n) (-1) (1 - n) n ⊆
      rlc_insetLeftOddToStrictUpper n ∪ rlc_insetLeftOddToLower n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hy : 0 < (y : Site 2) 1
  · exact Or.inl ⟨x, y, Set.mem_univ _, hy, hxy⟩
  · exact Or.inr ⟨x, y, Set.mem_univ _, le_of_not_gt hy, hxy⟩

theorem rlc_insetLeftOdd_horizontal_subset_left (n : Int) :
    horizontalCrossingEvent (-2 * n) (-1) (1 - n) n ⊆
      rlc_insetLeftOddLowerToRight n ∪ rlc_insetLeftOddStrictUpperToRight n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hx : (x : Site 2) 1 <= 0
  · exact Or.inl ⟨x, y, hx, Set.mem_univ _, hxy⟩
  · exact Or.inr ⟨x, y, lt_of_not_ge hx, Set.mem_univ _, hxy⟩

theorem rlc_insetLeftOddToStrictUpper_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n)) :
    alpha / 2 <= rba_selfDualMeasure.real (rlc_insetLeftOddToStrictUpper n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetLeftOdd_horizontal_subset_right n)
    (rlc_insetLeftOdd_right_reflection_prob n)

theorem rlc_insetLeftOddLowerToRight_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n)) :
    alpha / 2 <= rba_selfDualMeasure.real (rlc_insetLeftOddLowerToRight n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetLeftOdd_horizontal_subset_left n)
    (rlc_insetLeftOdd_left_reflection_prob n)

theorem rlc_insetLeftOdd_horizontal_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
  have hbase := rlc_square_half (2 * n - 1) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * n - 1) 0 (2 * n - 1) (![-2 * n, 1 - n] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * n - 1) 0 (2 * n - 1))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * n - 1) 0 (2 * n - 1)) := by
    simpa [show 2 * n - 1 + -(2 * n) = -1 by ring,
      show 2 * n - 1 + (1 - n) = n by ring] using htrans
  rwa [heq]

theorem rlc_insetLeftOdd_vertical_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (verticalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
  have hH := rlc_insetLeftOdd_horizontal_half n hn
  have hswap := crf_verticalCrossing_eq_horizontal_swap
    (-2 * n) (-1) (1 - n) n
    (rlc_horizontalCrossing_measurableSet (1 - n) n (-2 * n) (-1))
  have htrans := cti_horizontalCrossing_translation_invariant
    (1 - n) n (-2 * n) (-1) (![-n - 1, n + 1] : Site 2)
    (rlc_horizontalCrossing_measurableSet (1 - n) n (-2 * n) (-1))
  have heq : rba_selfDualMeasure.real
      (verticalCrossingEvent (-2 * n) (-1) (1 - n) n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
    rw [hswap]
    simpa [show 1 - n + (-n - 1) = -2 * n by ring,
      show n + (-n - 1) = -1 by ring,
      show -(2 * n) + (n + 1) = 1 - n by ring,
      show -1 + (n + 1) = n by ring] using htrans.symm
  rwa [heq]

theorem rlc_insetLeftOddSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetLeftOddSourceCoreEvent n) := by
  let F := (rect_finite (-2 * n) (-1) (1 - n) n).toFinset
  have h := rlc_diagonal_event_lower_bound (2⁻¹ : NNReal) half_le_one
    ((1 : Real) / 2) (by norm_num)
    (rlc_insetLeftOddToStrictUpper n)
    (rlc_insetLeftOddLowerToRight n)
    (verticalCrossingEvent (-2 * n) (-1) (1 - n) n)
    (rlc_insetLeftOddSourceCoreEvent n)
    (edgesWithinFinset F) (edgesWithinFinset F) (edgesWithinFinset F)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing _ _ _ _)
    (by simpa [F, rlc_insetLeftOddToStrictUpper] using
      (rlc_lrRestrictedEvent_dependsOn (-2 * n) (-1) (1 - n) n
        Set.univ rlc_strictUpperHalf))
    (by simpa [F, rlc_insetLeftOddLowerToRight] using
      (rlc_lrRestrictedEvent_dependsOn (-2 * n) (-1) (1 - n) n
        rlc_lowerHalf Set.univ))
    (by simpa [F] using
      rlc_verticalCrossing_dependsOn (-2 * n) (-1) (1 - n) n)
    (rlc_insetLeftOddToStrictUpper_half n ((1 : Real) / 2)
      (rlc_insetLeftOdd_horizontal_half n hn))
    (rlc_insetLeftOddLowerToRight_half n ((1 : Real) / 2)
      (rlc_insetLeftOdd_horizontal_half n hn))
    (rlc_insetLeftOdd_vertical_half n hn)
    (rlc_lrRestricted_of_three (-2 * n) (-1) (1 - n) n
      (by omega) (by omega) rlc_lowerHalf rlc_strictUpperHalf)
  norm_num at h
  simpa [rba_selfDualMeasure] using h



theorem rlc_insetRightOddSourceCore_subset (n : Int) :
    rlc_insetRightOddSourceCoreEvent n ⊆ rlc_insetRightSourceCoreEvent n := by
  rintro omega ⟨x, y, hx, hy, hxy⟩
  have hsub : rect 1 (2 * n) (-n) (n - 1) ⊆ rect 1 (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  let xl : leftSide 1 (2 * n) (-n) n :=
    ⟨x, hsub (leftSide_subset x.2), x.2.2⟩
  let yr : rightSide 1 (2 * n) (-n) n :=
    ⟨y, hsub (rightSide_subset y.2), y.2.2⟩
  refine ⟨xl, yr, hx, hy, ?_⟩
  simpa [xl, yr] using
    (StatMech.RSW.Strip.connectedWithin_mono_set omega hsub hxy)

theorem rlc_insetLeftOddSourceCore_subset (n : Int) :
    rlc_insetLeftOddSourceCoreEvent n ⊆ rlc_insetLeftSourceCoreEvent n := by
  rintro omega ⟨x, y, hx, hy, hxy⟩
  have hsub : rect (-2 * n) (-1) (1 - n) n ⊆
      rect (-2 * n) (-1) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  let xl : leftSide (-2 * n) (-1) (-n) n :=
    ⟨x, hsub (leftSide_subset x.2), x.2.2⟩
  let yr : rightSide (-2 * n) (-1) (-n) n :=
    ⟨y, hsub (rightSide_subset y.2), y.2.2⟩
  refine ⟨xl, yr, hx, hy, ?_⟩
  simpa [xl, yr] using
    (StatMech.RSW.Strip.connectedWithin_mono_set omega hsub hxy)

theorem rlc_insetRightSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetRightSourceCoreEvent n) :=
  (rlc_insetRightOddSourceCore_mass_lower n hn).trans
    (measureReal_mono (rlc_insetRightOddSourceCore_subset n))

theorem rlc_insetLeftSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetLeftSourceCoreEvent n) :=
  (rlc_insetLeftOddSourceCore_mass_lower n hn).trans
    (measureReal_mono (rlc_insetLeftOddSourceCore_subset n))

theorem rlc_strictAxisRightSourceEvent_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 64 <=
      rba_selfDualMeasure.real (rlc_strictAxisRightSourceEvent n) := by
  have hatt := rlc_insetRightSourceCore_to_strictAxis_mass
    (2⁻¹ : NNReal) half_le_one n
  have hcore := rlc_insetRightSourceCore_mass_lower n hn
  have hmul : (1 : Real) / 64 <=
      ((2⁻¹ : NNReal) : Real) *
        rba_selfDualMeasure.real (rlc_insetRightSourceCoreEvent n) := by
    norm_num
    linarith
  exact hmul.trans (by simpa [rba_selfDualMeasure] using hatt)

theorem rlc_strictAxisLeftSourceEvent_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 64 <=
      rba_selfDualMeasure.real (rlc_strictAxisLeftSourceEvent n) := by
  have hatt := rlc_insetLeftSourceCore_to_strictAxis_mass
    (2⁻¹ : NNReal) half_le_one n
  have hcore := rlc_insetLeftSourceCore_mass_lower n hn
  have hmul : (1 : Real) / 64 <=
      ((2⁻¹ : NNReal) : Real) *
        rba_selfDualMeasure.real (rlc_insetLeftSourceCoreEvent n) := by
    norm_num
    linarith
  exact hmul.trans (by simpa [rba_selfDualMeasure] using hatt)

theorem rlc_strictAxisStoppedDiagonalEvent_mass_lower_unconditional
    {n : Int} (hn : 0 < n)
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    (1 : Real) / 4096 <=
      rba_selfDualMeasure.real (rlc_strictAxisStoppedDiagonalEvent n) := by
  have h := rlc_strictAxisStoppedDiagonalEvent_mass_lower
    (2⁻¹ : NNReal) half_le_one hn hright hleft (a := (1 : Real) / 64)
    (b := (1 : Real) / 64) (by norm_num)
    (rlc_strictAxisRightSourceEvent_mass_lower n hn)
    (rlc_strictAxisLeftSourceEvent_mass_lower n hn)
  norm_num at h
  simpa [rba_selfDualMeasure] using h

end

end StatMech.Universality
