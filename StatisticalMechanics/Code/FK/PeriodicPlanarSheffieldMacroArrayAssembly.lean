/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldAdjacentHeight
import Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge








open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}





structure PeriodicPlaneEmbedding.NormalBoundaryBandFamily
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (p : Real) where
  baseLeft : Site 2
  baseRight : Site 2
  baseBottom : Site 2
  baseTop : Site 2
  radiusLeft : Nat → Nat
  radiusRight : Nat → Nat
  radiusBottom : Nat → Nat
  radiusTop : Nat → Nat
  left : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseLeft + horizontalShift i.val) '' (S : Set V) ⊆
        E.rectVertices 0 (radiusLeft margin)
          (-(radiusLeft margin : Real)) (radiusLeft margin) ∧
      p < mu.real (E.rectSideConnectionEvent
        0 (radiusLeft margin) (-(radiusLeft margin : Real))
        (radiusLeft margin)
        (P.shift (baseLeft + horizontalShift i.val) '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 (radiusLeft margin)
          (-(radiusLeft margin : Real)) (radiusLeft margin)))
  right : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusRight margin : Real)) 0
          (-(radiusRight margin : Real)) (radiusRight margin) ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusRight margin : Real)) 0
        (-(radiusRight margin : Real)) (radiusRight margin)
        (P.shift (baseRight + horizontalShift (-(i.val : Int))) ''
          (S : Set V))
        (E.rectRightBoundaryVertices (-(radiusRight margin : Real)) 0
          (-(radiusRight margin : Real)) (radiusRight margin)))
  bottom : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseBottom + verticalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(radiusBottom margin : Real)) (radiusBottom margin)
          0 (radiusBottom margin) ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusBottom margin : Real)) (radiusBottom margin)
        0 (radiusBottom margin)
        (P.shift (baseBottom + verticalShift i.val) '' (S : Set V))
        (E.rectBottomBoundaryVertices (-(radiusBottom margin : Real))
          (radiusBottom margin) 0 (radiusBottom margin)))
  top : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusTop margin : Real)) (radiusTop margin)
          (-(radiusTop margin : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusTop margin : Real)) (radiusTop margin)
        (-(radiusTop margin : Real)) 0
        (P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectTopBoundaryVertices (-(radiusTop margin : Real))
          (radiusTop margin) (-(radiusTop margin : Real)) 0))


def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (margin : Nat) :
    E.NormalBoundaryBandSeed mu S margin p where
  baseLeft := family.baseLeft
  baseRight := family.baseRight
  baseBottom := family.baseBottom
  baseTop := family.baseTop
  radiusLeft := family.radiusLeft margin
  radiusRight := family.radiusRight margin
  radiusBottom := family.radiusBottom margin
  radiusTop := family.radiusTop margin
  left := family.left margin
  right := family.right margin
  bottom := family.bottom margin
  top := family.top margin




theorem PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandFamily
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (N : Nat) {delta : Real} (hdelta : 0 < delta) :
    Nonempty (E.NormalBoundaryBandFamily mu (P.orbitBox N)
      ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
  classical
  obtain ⟨baseLeft, hbaseLeft⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseRight, hbaseRight⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N 0
  obtain ⟨baseBottomSwap, hbaseBottom⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseTopSwap, hbaseTop⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_leftComplement N 0
  let baseBottom := siteAxisSwap baseBottomSwap
  let baseTop := siteAxisSwap baseTopSwap
  have hinsideLeft (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseLeft + horizontalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseLeft u hu
    change 0 ≤ E.vertexCoord (P.shift baseLeft u) 0 at h
    simp only [E.vertexCoord_shift] at h
    change 0 ≤ E.vertexCoord
      (P.shift (baseLeft + horizontalShift i.val) u) 0
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h (show (0 : Real) ≤ i.val by positivity)
  have hinsideRight (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseRight + horizontalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 0 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseRight u hu
    change ¬ (0 ≤ E.vertexCoord (P.shift baseRight u) 0) at h
    simp only [E.vertexCoord_shift] at h
    change E.vertexCoord
      (P.shift (baseRight + horizontalShift (-(i.val : Int))) u) 0 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [horizontalShift_zero_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  have hinsideBottom (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseBottom + verticalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ {u | 0 ≤ E.vertexCoord u 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseBottom u (by rw [P.axisSwap_orbitBox]; exact hu)
    change 0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseBottomSwap u) 0 at h
    have h' : 0 ≤ E.vertexCoord (P.shift baseBottom u) 1 := by
      simpa [baseBottom, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change 0 ≤ E.vertexCoord
      (P.shift (baseBottom + verticalShift i.val) u) 1
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h' (show (0 : Real) ≤ i.val by positivity)
  have hinsideTop (margin : Nat) (i : Fin (margin + 1)) :
      P.shift (baseTop + verticalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 1 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseTop u (by rw [P.axisSwap_orbitBox]; exact hu)
    change ¬ (0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseTopSwap u) 0) at h
    have h' : ¬ (0 ≤ E.vertexCoord (P.shift baseTop u) 1) := by
      simpa [baseTop, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change E.vertexCoord
      (P.shift (baseTop + verticalShift (-(i.val : Int))) u) 1 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [verticalShift_one_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  choose radiusLeft hleft using fun margin ↦
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦ baseLeft + horizontalShift i.val)
      (hinsideLeft margin) hdelta
  choose radiusRight hright using fun margin ↦
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦
        baseRight + horizontalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideRight margin) hdelta
  choose radiusBottom hbottom using fun margin ↦
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦ baseBottom + verticalShift i.val)
      (hinsideBottom margin) hdelta
  choose radiusTop htop using fun margin ↦
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) ↦
        baseTop + verticalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideTop margin) hdelta
  exact ⟨{
    baseLeft := baseLeft
    baseRight := baseRight
    baseBottom := baseBottom
    baseTop := baseTop
    radiusLeft := radiusLeft
    radiusRight := radiusRight
    radiusBottom := radiusBottom
    radiusTop := radiusTop
    left := by
      intro margin
      simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent] using hleft margin
    right := by
      intro margin
      simpa using hright margin
    bottom := by
      intro margin
      simpa using hbottom margin
    top := by
      intro margin
      simpa using htop margin }⟩



def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.horizontalRadiusRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (horizontalMargin : Nat) : Nat :=
  max
    (((family.radiusLeft horizontalMargin : Int) +
      family.baseLeft 1 - family.baseBottom 1).toNat)
    (((family.radiusRight horizontalMargin : Int) +
      family.baseRight 1 - family.baseBottom 1).toNat)



def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.verticalRadiusRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin : Nat) : Nat :=
  max
    (((family.radiusBottom verticalMargin : Int) +
      family.baseBottom 0 - family.baseLeft 0).toNat)
    (((family.radiusTop verticalMargin : Int) +
      family.baseTop 0 - family.baseLeft 0).toNat)

private theorem int_le_nat_of_toNat_le {x : Int} {n : Nat}
    (h : x.toNat ≤ n) : x ≤ n := by
  by_cases hx : 0 ≤ x
  · have h' : (x.toNat : Int) ≤ (n : Int) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg hx] at h'
  · have : x < 0 := lt_of_not_ge hx
    omega





theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧
      Tendsto vertical atTop atTop ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
          family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
          family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
          family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
          family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) := by
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences
      family.horizontalRadiusRequirement family.verticalRadiusRequirement
  refine ⟨horizontal, vertical, hh, hv, ?_, ?_, ?_, ?_⟩
  · intro n
    have hle : (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat) ≤ vertical n :=
      (Nat.le_max_left _ _).trans (hhv n)
    have := int_le_nat_of_toNat_le hle
    omega
  · intro n
    have hle : (((family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 - family.baseBottom 1).toNat) ≤ vertical n :=
      (Nat.le_max_right _ _).trans (hhv n)
    have := int_le_nat_of_toNat_le hle
    omega
  · intro n
    have hle : (((family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 - family.baseLeft 0).toNat) ≤
        horizontal (n + 1) :=
      (Nat.le_max_left _ _).trans (hvh n)
    have := int_le_nat_of_toNat_le hle
    omega
  · intro n
    have hle : (((family.radiusTop (vertical n) : Int) +
        family.baseTop 0 - family.baseLeft 0).toNat) ≤
        horizontal (n + 1) :=
      (Nat.le_max_right _ _).trans (hvh n)
    have := int_le_nat_of_toNat_le hle
    omega

set_option linter.unusedVariables false in




theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.mixedBoundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (horizontalMargin verticalMargin width height : Nat)
    (hfitLeft : (family.radiusLeft horizontalMargin : Int) +
      family.baseLeft 1 ≤ family.baseBottom 1 + verticalMargin)
    (hfitRight : (family.radiusRight horizontalMargin : Int) +
      family.baseRight 1 ≤ family.baseBottom 1 + verticalMargin) :
    let gridBase : Site 2 := fun i ↦ if i = 0 then
      family.baseLeft 0 + horizontalMargin
    else family.baseBottom 1 + verticalMargin
    let b0 : Int := gridBase 0 + width -
      (family.baseRight 0 - horizontalMargin)
    let d1 : Int := gridBase 1 + height -
      (family.baseTop 1 - verticalMargin)
    let bottomLower : Int := gridBase 0 - family.baseBottom 0 -
      family.radiusBottom verticalMargin
    let topLower : Int := gridBase 0 - family.baseTop 0 -
      family.radiusTop verticalMargin
    let a1 : Int := min 0 (min bottomLower topLower)
    let bottomUpper : Int := gridBase 0 + width - family.baseBottom 0 +
      family.radiusBottom verticalMargin
    let topUpper : Int := gridBase 0 + width - family.baseTop 0 +
      family.radiusTop verticalMargin
    let b1 : Int := max b0 (max bottomUpper topUpper)
    let leftUpper : Int := gridBase 1 + height - family.baseLeft 1 +
      family.radiusLeft horizontalMargin
    let rightUpper : Int := gridBase 1 + height - family.baseRight 1 +
      family.radiusRight horizontalMargin
    let d0 : Int := max d1 (max leftUpper rightUpper)
    ((family.radiusLeft horizontalMargin : Int) ≤ b0) →
    ((family.radiusRight horizontalMargin : Int) ≤ b0) →
    ((family.radiusBottom verticalMargin : Int) ≤ d1) →
    ((family.radiusTop verticalMargin : Int) ≤ d1) →
    ((a1 : Real) ≤ 0 ∧ (b0 : Real) ≤ b1 ∧
      (0 : Real) ≤ 0 ∧ (d1 : Real) ≤ d0) ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent a1 b1 0 d1
        (P.shift (gridBase + preferenceGridSite
          (i, (0 : Fin (height + 1)))) '' (S : Set V))
        (E.rectBottomBoundaryVertices a1 b1 0 d1))) ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent a1 b1 0 d1
        (P.shift (gridBase + preferenceGridSite
          (i, Fin.last height)) '' (S : Set V))
        (E.rectTopBoundaryVertices a1 b1 0 d1))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b0 0 d0
        (P.shift (gridBase + preferenceGridSite
          ((0 : Fin (width + 1)), j)) '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 b0 0 d0))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b0 0 d0
        (P.shift (gridBase + preferenceGridSite
          (Fin.last width, j)) '' (S : Set V))
        (E.rectRightBoundaryVertices 0 b0 0 d0))) := by
  dsimp only
  intro hbLeft hbRight hdBottom hdTop
  let gridBase : Site 2 := fun i ↦ if i = 0 then
    family.baseLeft 0 + horizontalMargin
  else family.baseBottom 1 + verticalMargin
  let b0 : Int := gridBase 0 + width -
    (family.baseRight 0 - horizontalMargin)
  let d1 : Int := gridBase 1 + height -
    (family.baseTop 1 - verticalMargin)
  let bottomLower : Int := gridBase 0 - family.baseBottom 0 -
    family.radiusBottom verticalMargin
  let topLower : Int := gridBase 0 - family.baseTop 0 -
    family.radiusTop verticalMargin
  let a1 : Int := min 0 (min bottomLower topLower)
  let bottomUpper : Int := gridBase 0 + width - family.baseBottom 0 +
    family.radiusBottom verticalMargin
  let topUpper : Int := gridBase 0 + width - family.baseTop 0 +
    family.radiusTop verticalMargin
  let b1 : Int := max b0 (max bottomUpper topUpper)
  let leftUpper : Int := gridBase 1 + height - family.baseLeft 1 +
    family.radiusLeft horizontalMargin
  let rightUpper : Int := gridBase 1 + height - family.baseRight 1 +
    family.radiusRight horizontalMargin
  let d0 : Int := max d1 (max leftUpper rightUpper)
  have hgrid0 : gridBase 0 = family.baseLeft 0 + horizontalMargin := by
    simp [gridBase]
  have hgrid1 : gridBase 1 = family.baseBottom 1 + verticalMargin := by
    simp [gridBase]
  change (family.radiusLeft horizontalMargin : Int) ≤ b0 at hbLeft
  change (family.radiusRight horizontalMargin : Int) ≤ b0 at hbRight
  change (family.radiusBottom verticalMargin : Int) ≤ d1 at hdBottom
  change (family.radiusTop verticalMargin : Int) ≤ d1 at hdTop
  change (((a1 : Real) ≤ 0 ∧ (b0 : Real) ≤ b1 ∧
      (0 : Real) ≤ 0 ∧ (d1 : Real) ≤ d0) ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent a1 b1 0 d1
        (P.shift (gridBase + preferenceGridSite
          (i, (0 : Fin (height + 1)))) '' (S : Set V))
        (E.rectBottomBoundaryVertices a1 b1 0 d1))) ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent a1 b1 0 d1
        (P.shift (gridBase + preferenceGridSite
          (i, Fin.last height)) '' (S : Set V))
        (E.rectTopBoundaryVertices a1 b1 0 d1))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b0 0 d0
        (P.shift (gridBase + preferenceGridSite
          ((0 : Fin (width + 1)), j)) '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 b0 0 d0))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b0 0 d0
        (P.shift (gridBase + preferenceGridSite
          (Fin.last width, j)) '' (S : Set V))
        (E.rectRightBoundaryVertices 0 b0 0 d0))))
  have hnested : ((a1 : Real) ≤ 0 ∧ (b0 : Real) ≤ b1 ∧
      (0 : Real) ≤ 0 ∧ (d1 : Real) ≤ d0) := by
    dsimp only [a1, b1, d0]
    constructor
    · exact_mod_cast min_le_left 0 (min bottomLower topLower)
    constructor
    · exact_mod_cast le_max_left b0 (max bottomUpper topUpper)
    constructor
    · norm_num
    · exact_mod_cast le_max_left d1 (max leftUpper rightUpper)
  refine ⟨hnested, ?_, ?_, ?_, ?_⟩
  · intro i
    let seed := family.seed E verticalMargin
    let z : Site 2 := gridBase + horizontalShift i.val -
      (family.baseBottom + verticalShift verticalMargin)
    have ha : (a1 : Real) ≤
        -(seed.radiusBottom : Real) + z 0 := by
      have hmin : a1 ≤ bottomLower :=
        (min_le_right 0 (min bottomLower topLower)).trans
          (min_le_left bottomLower topLower)
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, bottomLower, gridBase] at hmin ⊢
      simp only [Pi.add_apply, Pi.sub_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_sub,
        Int.cast_neg, Int.cast_natCast]
      norm_num at ⊢
      exact_mod_cast (by omega :
        (family.radiusBottom verticalMargin : Int) + a1 ≤
          family.baseLeft 0 + horizontalMargin + i.val -
            family.baseBottom 0)
    have hb : (seed.radiusBottom : Real) + z 0 ≤ b1 := by
      have hi : (i.val : Int) ≤ width := by omega
      have hupper : bottomUpper ≤ b1 :=
        (le_max_left bottomUpper topUpper).trans
          (le_max_right b0 (max bottomUpper topUpper))
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed]
      simp only [z, gridBase, Pi.add_apply, Pi.sub_apply,
        horizontalShift_zero_apply, verticalShift_zero_apply,
        Int.cast_add, Int.cast_sub, Int.cast_natCast]
      have htarget : (family.radiusBottom verticalMargin : Int) +
          (family.baseLeft 0 + horizontalMargin + i.val -
            family.baseBottom 0) ≤ b1 := by
        apply le_trans _ hupper
        simp only [bottomUpper, hgrid0]
        omega
      norm_num at ⊢
      exact_mod_cast htarget
    have hd : (seed.radiusBottom : Real) + z 1 ≤ d1 := by
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, gridBase] at ⊢
      simp only [Pi.add_apply, Pi.sub_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_sub,
        Int.cast_natCast]
      norm_num at ⊢
      exact_mod_cast (by simpa [d1, gridBase] using hdBottom)
    have hscore := seed.bottom_translate_to_rect E mu hTI
      (Fin.last verticalMargin) z (a1 : Real) (b1 : Real) (d1 : Real)
      ha hb hd
    have hz1 : z 1 = 0 := by
      simp [z, gridBase]
    have hsource : P.shift z ''
        (P.shift (family.baseBottom + verticalShift
          ((Fin.last verticalMargin).val : Int)) '' (S : Set V)) =
      P.shift (gridBase + preferenceGridSite
        (i, (0 : Fin (height + 1)))) '' (S : Set V) := by
      rw [P.shift_image_shift]
      apply congrArg (fun w : Site 2 ↦ P.shift w '' (S : Set V))
      dsimp only [z]
      have hlast : (Fin.last verticalMargin).val = verticalMargin := rfl
      rw [hlast]
      funext k
      fin_cases k <;> simp [gridBase, preferenceGridSite] <;> omega
    rw [← hsource]
    simpa [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
      hz1] using hscore.2
  · intro i
    let seed := family.seed E verticalMargin
    let z : Site 2 := gridBase + horizontalShift i.val + verticalShift height -
      (family.baseTop + verticalShift (-(verticalMargin : Int)))
    have ha : (a1 : Real) ≤ -(seed.radiusTop : Real) + z 0 := by
      have hmin : a1 ≤ topLower :=
        (min_le_right 0 (min bottomLower topLower)).trans
          (min_le_right bottomLower topLower)
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, topLower, gridBase] at hmin ⊢
      simp only [Pi.add_apply, Pi.sub_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_sub,
        Int.cast_neg, Int.cast_natCast]
      norm_num at ⊢
      exact_mod_cast (by omega :
        (family.radiusTop verticalMargin : Int) + a1 ≤
          family.baseLeft 0 + horizontalMargin + i.val -
            family.baseTop 0)
    have hb : (seed.radiusTop : Real) + z 0 ≤ b1 := by
      have hupper : topUpper ≤ b1 :=
        (le_max_right bottomUpper topUpper).trans
          (le_max_right b0 (max bottomUpper topUpper))
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed]
      simp only [z, gridBase, Pi.add_apply, Pi.sub_apply,
        horizontalShift_zero_apply, verticalShift_zero_apply,
        Int.cast_add, Int.cast_sub, Int.cast_natCast]
      have hi : (i.val : Int) ≤ width := by omega
      have htarget : (family.radiusTop verticalMargin : Int) +
          (family.baseLeft 0 + horizontalMargin + i.val -
            family.baseTop 0) ≤ b1 := by
        apply le_trans _ hupper
        simp only [topUpper, hgrid0]
        omega
      norm_num at ⊢
      exact_mod_cast htarget
    have hc : (0 : Real) ≤ -(seed.radiusTop : Real) + z 1 := by
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, d1, gridBase] at hdTop ⊢
      simp only [Pi.add_apply, Pi.sub_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_sub,
        Int.cast_neg, Int.cast_natCast]
      norm_num at ⊢
      exact_mod_cast (by simpa [d1, gridBase] using hdTop)
    have hscore := seed.top_translate_to_rect E mu hTI
      (Fin.last verticalMargin) z (a1 : Real) (b1 : Real) 0 ha hb hc
    have hz1 : z 1 = d1 := by
      simp [z, d1, gridBase, sub_eq_add_neg]
    have hsource : P.shift z ''
        (P.shift (family.baseTop + verticalShift
          (-((Fin.last verticalMargin).val : Int))) '' (S : Set V)) =
      P.shift (gridBase + preferenceGridSite
        (i, Fin.last height)) '' (S : Set V) := by
      rw [P.shift_image_shift]
      apply congrArg (fun w : Site 2 ↦ P.shift w '' (S : Set V))
      dsimp only [z]
      have hvlast : (Fin.last verticalMargin).val = verticalMargin := rfl
      rw [hvlast]
      funext k
      fin_cases k <;>
        simp [gridBase, preferenceGridSite, sub_eq_add_neg] <;> omega
    rw [← hsource]
    simpa [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
      hz1] using hscore.2
  · intro j
    let seed := family.seed E horizontalMargin
    let z : Site 2 := gridBase + verticalShift j.val -
      (family.baseLeft + horizontalShift horizontalMargin)
    have hb : (seed.radiusLeft : Real) + z 0 ≤ b0 := by
      exact_mod_cast (by simpa [z, gridBase] using hbLeft)
    have hc : (0 : Real) ≤ -(seed.radiusLeft : Real) + z 1 := by
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, gridBase] at hfitLeft ⊢
      simp only [Pi.add_apply, Pi.sub_apply, verticalShift_one_apply,
        horizontalShift_one_apply, Int.cast_add, Int.cast_sub,
        Int.cast_neg, Int.cast_natCast]
      norm_num at ⊢
      have hj : (0 : Int) ≤ j.val := by omega
      exact_mod_cast (by omega :
        (family.radiusLeft horizontalMargin : Int) ≤
          family.baseBottom 1 + verticalMargin + j.val -
            family.baseLeft 1)
    have hd : (seed.radiusLeft : Real) + z 1 ≤ d0 := by
      have hupper : leftUpper ≤ d0 :=
        (le_max_left leftUpper rightUpper).trans
          (le_max_right d1 (max leftUpper rightUpper))
      have hj : (j.val : Int) ≤ height := by omega
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed]
      simp only [z, gridBase, Pi.add_apply, Pi.sub_apply,
        verticalShift_one_apply, horizontalShift_one_apply,
        Int.cast_add, Int.cast_sub, Int.cast_natCast]
      have htarget : (family.radiusLeft horizontalMargin : Int) +
          (family.baseBottom 1 + verticalMargin + j.val -
            family.baseLeft 1) ≤ d0 := by
        apply le_trans _ hupper
        simp only [leftUpper, hgrid1]
        omega
      norm_num at ⊢
      exact_mod_cast htarget
    have hscore := seed.left_translate_to_rect E mu hTI
      (Fin.last horizontalMargin) z (b0 : Real) 0 (d0 : Real) hb hc hd
    have hz0 : z 0 = 0 := by simp [z, gridBase]
    have hsource : P.shift z ''
        (P.shift (family.baseLeft + horizontalShift
          ((Fin.last horizontalMargin).val : Int)) '' (S : Set V)) =
      P.shift (gridBase + preferenceGridSite
        ((0 : Fin (width + 1)), j)) '' (S : Set V) := by
      rw [P.shift_image_shift]
      apply congrArg (fun w : Site 2 ↦ P.shift w '' (S : Set V))
      dsimp only [z]
      have hlast : (Fin.last horizontalMargin).val = horizontalMargin := rfl
      rw [hlast]
      funext k
      fin_cases k <;> simp [gridBase, preferenceGridSite] <;> omega
    rw [← hsource]
    simpa [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
      hz0] using hscore.2
  · intro j
    let seed := family.seed E horizontalMargin
    let z : Site 2 := gridBase + horizontalShift width + verticalShift j.val -
      (family.baseRight + horizontalShift (-(horizontalMargin : Int)))
    have ha : (0 : Real) ≤ -(seed.radiusRight : Real) + z 0 := by
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, b0, gridBase] at hbRight ⊢
      simp only [Pi.add_apply, Pi.sub_apply, verticalShift_zero_apply,
        horizontalShift_zero_apply, Int.cast_add, Int.cast_sub,
        Int.cast_neg, Int.cast_natCast]
      exact_mod_cast (by simpa [b0, gridBase] using hbRight)
    have hc : (0 : Real) ≤ -(seed.radiusRight : Real) + z 1 := by
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
        z, gridBase] at hfitRight ⊢
      simp only [Pi.add_apply, Pi.sub_apply, verticalShift_one_apply,
        horizontalShift_one_apply, Int.cast_add, Int.cast_sub,
        Int.cast_neg, Int.cast_natCast]
      norm_num at ⊢
      have hj : (0 : Int) ≤ j.val := by omega
      exact_mod_cast (by omega :
        (family.radiusRight horizontalMargin : Int) ≤
          family.baseBottom 1 + verticalMargin + j.val -
            family.baseRight 1)
    have hd : (seed.radiusRight : Real) + z 1 ≤ d0 := by
      have hupper : rightUpper ≤ d0 :=
        (le_max_right leftUpper rightUpper).trans
          (le_max_right d1 (max leftUpper rightUpper))
      have hj : (j.val : Int) ≤ height := by omega
      dsimp only [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed]
      simp only [z, gridBase, Pi.add_apply, Pi.sub_apply,
        verticalShift_one_apply, horizontalShift_one_apply,
        Int.cast_add, Int.cast_sub, Int.cast_natCast]
      have htarget : (family.radiusRight horizontalMargin : Int) +
          (family.baseBottom 1 + verticalMargin + j.val -
            family.baseRight 1) ≤ d0 := by
        apply le_trans _ hupper
        simp only [rightUpper, hgrid1]
        omega
      norm_num at ⊢
      exact_mod_cast htarget
    have hscore := seed.right_translate_to_rect E mu hTI
      (Fin.last horizontalMargin) z 0 0 (d0 : Real) ha hc hd
    have hz0 : z 0 = b0 := by
      simp [z, b0, gridBase, sub_eq_add_neg]
    have hsource : P.shift z ''
        (P.shift (family.baseRight + horizontalShift
          (-((Fin.last horizontalMargin).val : Int))) '' (S : Set V)) =
      P.shift (gridBase + preferenceGridSite
        (Fin.last width, j)) '' (S : Set V) := by
      rw [P.shift_image_shift]
      apply congrArg (fun w : Site 2 ↦ P.shift w '' (S : Set V))
      dsimp only [z]
      have hvlast : (Fin.last horizontalMargin).val = horizontalMargin := rfl
      rw [hvlast]
      funext k
      fin_cases k <;>
        simp [gridBase, preferenceGridSite, sub_eq_add_neg] <;> omega
    rw [← hsource]
    simpa [seed, PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed,
      hz0] using hscore.2

omit [Countable V] in


theorem PeriodicPlaneEmbedding.rectSideConnection_component_le_template
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (component template : Finset V)
    (base : Site 2) (side : Set V) (hcomponent : component ⊆ template) :
    mu.real (E.rectSideConnectionEvent a b c d
        (component.image (P.shift base) : Set V) side) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (template.image (P.shift base) : Set V) side) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  apply E.rectSideConnectionEvent_mono_source
  exact_mod_cast (Finset.image_mono (P.shift base)) hcomponent

omit [Countable V] in

theorem PeriodicPlaneEmbedding.rectSideConnection_leftComponent_le_fourShift
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (S : Finset V)
    (zLeft zRight zBottom zTop base : Site 2) (side : Set V) :
    mu.real (E.rectSideConnectionEvent a b c d
        ((S.image (P.shift zLeft)).image (P.shift base) : Set V) side) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift base) : Set V) side) :=
  E.rectSideConnection_component_le_template mu a b c d
    (S.image (P.shift zLeft))
    (P.fourShiftTemplate S zLeft zRight zBottom zTop) base side
    (P.image_subset_fourShiftTemplate S zLeft zRight zBottom zTop)

omit [Countable V] in

theorem PeriodicPlaneEmbedding.rectSideConnection_rightComponent_le_fourShift
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (S : Finset V)
    (zLeft zRight zBottom zTop base : Site 2) (side : Set V) :
    mu.real (E.rectSideConnectionEvent a b c d
        ((S.image (P.shift zRight)).image (P.shift base) : Set V) side) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift base) : Set V) side) :=
  E.rectSideConnection_component_le_template mu a b c d
    (S.image (P.shift zRight))
    (P.fourShiftTemplate S zLeft zRight zBottom zTop) base side
    (P.image_right_subset_fourShiftTemplate S zLeft zRight zBottom zTop)

omit [Countable V] in

theorem PeriodicPlaneEmbedding.rectSideConnection_bottomComponent_le_fourShift
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (S : Finset V)
    (zLeft zRight zBottom zTop base : Site 2) (side : Set V) :
    mu.real (E.rectSideConnectionEvent a b c d
        ((S.image (P.shift zBottom)).image (P.shift base) : Set V) side) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift base) : Set V) side) :=
  E.rectSideConnection_component_le_template mu a b c d
    (S.image (P.shift zBottom))
    (P.fourShiftTemplate S zLeft zRight zBottom zTop) base side
    (P.image_bottom_subset_fourShiftTemplate S zLeft zRight zBottom zTop)

omit [Countable V] in

theorem PeriodicPlaneEmbedding.rectSideConnection_topComponent_le_fourShift
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (S : Finset V)
    (zLeft zRight zBottom zTop base : Site 2) (side : Set V) :
    mu.real (E.rectSideConnectionEvent a b c d
        ((S.image (P.shift zTop)).image (P.shift base) : Set V) side) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift base) : Set V) side) :=
  E.rectSideConnection_component_le_template mu a b c d
    (S.image (P.shift zTop))
    (P.fourShiftTemplate S zLeft zRight zBottom zTop) base side
    (P.image_top_subset_fourShiftTemplate S zLeft zRight zBottom zTop)

omit [Countable V] in


theorem PeriodicGraph.fourShiftTemplate_image_subset
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop base : Site 2) (R : Set V)
    (hleft : ((S.image (P.shift zLeft)).image (P.shift base) : Set V) ⊆ R)
    (hright : ((S.image (P.shift zRight)).image (P.shift base) : Set V) ⊆ R)
    (hbottom : ((S.image (P.shift zBottom)).image (P.shift base) : Set V) ⊆ R)
    (htop : ((S.image (P.shift zTop)).image (P.shift base) : Set V) ⊆ R) :
    ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
      (P.shift base) : Set V) ⊆ R := by
  intro x hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_coe,
    Finset.mem_image, Finset.mem_union] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rcases hu with (hu | hu) | (hu | hu)
  · have hu' : u ∈ S.image (P.shift zLeft) := by
      simpa only [Finset.mem_image] using hu
    exact hleft (by exact_mod_cast Finset.mem_image.mpr ⟨u, hu', rfl⟩)
  · have hu' : u ∈ S.image (P.shift zRight) := by
      simpa only [Finset.mem_image] using hu
    exact hright (by exact_mod_cast Finset.mem_image.mpr ⟨u, hu', rfl⟩)
  · have hu' : u ∈ S.image (P.shift zBottom) := by
      simpa only [Finset.mem_image] using hu
    exact hbottom (by exact_mod_cast Finset.mem_image.mpr ⟨u, hu', rfl⟩)
  · have hu' : u ∈ S.image (P.shift zTop) := by
      simpa only [Finset.mem_image] using hu
    exact htop (by exact_mod_cast Finset.mem_image.mpr ⟨u, hu', rfl⟩)

omit [Countable V] in
theorem boundaryGridBase_add
    (baseLeft baseBottom z : Site 2) :
    boundaryGridBase (baseLeft + z) (baseBottom + z) =
      boundaryGridBase baseLeft baseBottom + z := by
  funext i
  fin_cases i <;> simp [boundaryGridBase]

omit [Countable V] in
@[simp] theorem boundaryGridWidth_add
    (extent : Nat) (baseLeft baseRight z : Site 2) :
    boundaryGridWidth extent (baseLeft + z) (baseRight + z) =
      boundaryGridWidth extent baseLeft baseRight := by
  simp only [boundaryGridWidth, Pi.add_apply]
  congr 1
  omega

omit [Countable V] in
@[simp] theorem boundaryGridHeight_add
    (extent : Nat) (baseBottom baseTop z : Site 2) :
    boundaryGridHeight extent (baseBottom + z) (baseTop + z) =
      boundaryGridHeight extent baseBottom baseTop := by
  simp only [boundaryGridHeight, Pi.add_apply]
  congr 1
  omega




theorem PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.grid_subset_translated
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {radius : Nat → Nat}
    (data : E.ConnectorReadyCommonSquareData mu radius)
    (n extentX extentY : Nat) (z : Site 2)
    (hposX : 0 < data.baseRight n 0 + (extentX : Int) -
      data.baseLeft n 0)
    (hposY : 0 < data.baseTop n 1 + (extentY : Int) -
      data.baseBottom n 1) :
    ∀ v : PreferenceGridVertex
        (boundaryGridWidth extentX (data.baseLeft n) (data.baseRight n))
        (boundaryGridHeight extentY (data.baseBottom n) (data.baseTop n)),
      P.shift (boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) +
          preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices
          (-(data.M n : Real) + z 0)
          ((data.M n + extentX : Nat) + (z 0 : Int))
          (-(data.M n : Real) + z 1)
          ((data.M n + extentY : Nat) + (z 1 : Int)) := by
  intro v x hx
  let base := boundaryGridBase (data.baseLeft n) (data.baseBottom n)
  have hgrid := E.preferenceGrid_translatedSet_subset_rect_of_commonSquare
    (data.M n) extentX extentY
    (data.baseLeft n) (data.baseRight n) (data.baseBottom n) (data.baseTop n)
    hposX hposY
    (P.orbitBox (P.bufferedRadius (radius n)) : Set V)
    (data.connectorLeft n) (data.connectorRight n)
    (data.connectorBottom n) (data.connectorTop n) v
  have hbase : boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) =
      base + z := boundaryGridBase_add _ _ _
  rw [hbase] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [show base + z + preferenceGridSite v =
      (base + preferenceGridSite v) + z by abel, P.shift_add]
  have hu0 := hgrid ⟨u, hu, rfl⟩
  have hshift := (E.shift_mem_rectVertices z
    (-(data.M n : Real)) (data.M n + extentX : Real)
    (-(data.M n : Real)) (data.M n + extentY : Real)
    (P.shift (base + preferenceGridSite v) u)).2 hu0
  simpa only [Nat.cast_add, Int.cast_add, Int.cast_natCast] using hshift



theorem PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.grid_subset_translated_of_le
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {radius : Nat → Nat}
    (data : E.ConnectorReadyCommonSquareData mu radius)
    (n extentX extentY smallRadius : Nat) (z : Site 2)
    (hsmall : smallRadius ≤ radius n)
    (hposX : 0 < data.baseRight n 0 + (extentX : Int) -
      data.baseLeft n 0)
    (hposY : 0 < data.baseTop n 1 + (extentY : Int) -
      data.baseBottom n 1) :
    ∀ v : PreferenceGridVertex
        (boundaryGridWidth extentX (data.baseLeft n) (data.baseRight n))
        (boundaryGridHeight extentY (data.baseBottom n) (data.baseTop n)),
      P.shift (boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) +
          preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius smallRadius) : Set V) ⊆
        E.rectVertices
          (-(data.M n : Real) + z 0)
          ((data.M n + extentX : Nat) + (z 0 : Int))
          (-(data.M n : Real) + z 1)
          ((data.M n + extentY : Nat) + (z 1 : Int)) := by
  intro v
  apply (Set.image_mono (fun u hu ↦
    P.orbitBox_mono (P.bufferedRadius_strictMono.monotone hsmall) hu)).trans
  exact data.grid_subset_translated E n extentX extentY z hposX hposY v



theorem PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.template_grid_subset_translated
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {radius : Nat → Nat}
    (data : E.ConnectorReadyCommonSquareData mu radius)
    (n extentX extentY templateRadius : Nat) (z : Site 2)
    (htemplate : templateRadius ≤ radius n)
    (hposX : 0 < data.baseRight n 0 + (extentX : Int) -
      data.baseLeft n 0)
    (hposY : 0 < data.baseTop n 1 + (extentY : Int) -
      data.baseBottom n 1) :
    ∀ v : PreferenceGridVertex
        (boundaryGridWidth extentX (data.baseLeft n) (data.baseRight n))
        (boundaryGridHeight extentY (data.baseBottom n) (data.baseTop n)),
      P.shift (boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) +
          preferenceGridSite v) '' (P.orbitBox templateRadius : Set V) ⊆
        E.rectVertices
          (-(data.M n : Real) + z 0)
          ((data.M n + extentX : Nat) + (z 0 : Int))
          (-(data.M n : Real) + z 1)
          ((data.M n + extentY : Nat) + (z 1 : Int)) := by
  intro v
  apply (Set.image_mono (fun u hu ↦
    P.orbitBox_mono (htemplate.trans (P.id_le_bufferedRadius _)) hu)).trans
  exact data.grid_subset_translated E n extentX extentY z hposX hposY v

end StatMech.FK.PeriodicPlanar
