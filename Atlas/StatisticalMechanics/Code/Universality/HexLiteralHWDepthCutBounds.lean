/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexLiteralHWDepthAugment

namespace StatMech.Universality

open HexWalk

noncomputable section



theorem hlhda_physical_white_depth_pos (ws : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
    (T : ℕ)
    (hbounds : ∀ j, j ≤ ws.length →
      0 ≤ hlhd_depth ws hleg j ∧ hlhd_depth ws hleg j ≤ T)
    {k : ℕ} (hk : k < ws.length)
    (hwhite : (hlhc_prefixCoord ws hleg.1 k).color = .white) :
    0 < hlhd_depth ws hleg k := by
  have hkBounds := hbounds k hk.le
  by_contra hnot
  have hkZero : hlhd_depth ws hleg k = 0 := by omega
  have hkne : k ≠ 0 := by
    intro hk0
    subst k
    have hc := congrArg HexAWCoord.color
      (hlhda_prefixCoord_zero ws hleg)
    rw [hwhite] at hc
    simp [hexAWOriginCoord] at hc
  have hkprev : k - 1 < ws.length := by omega
  obtain ⟨ein, hein⟩ := hlhc_prefixCoord_adjacent ws hleg (k - 1) hkprev
  have hksucc : k - 1 + 1 = k := by omega
  rw [hksucc] at hein
  have hinCases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ws hleg.1 (k - 1)) ein
  have hinZero : ein = 0 := by
    rcases hinCases with hinc | hdec | hflat
    · have hdepth := hinc.1
      rw [hein] at hdepth
      have hprev := (hbounds (k - 1) (by omega)).1
      change 0 ≤ hexAWDepth
        (hlhc_prefixCoord ws hleg.1 (k - 1)) at hprev
      change hexAWDepth (hlhc_prefixCoord ws hleg.1 k) = 0 at hkZero
      omega
    · have hblack := hlhda_neighbor_color_white hdec.2.1 hein
      rw [hwhite] at hblack
      contradiction
    · exact hflat.2
  obtain ⟨eout, heout⟩ := hlhc_prefixCoord_adjacent ws hleg k hk
  have houtCases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ws hleg.1 k) eout
  have houtZero : eout = 0 := by
    rcases houtCases with hinc | hdec | hflat
    · have hcolor := hinc.2.1
      rw [hwhite] at hcolor
      contradiction
    · have hdepth := hdec.1
      rw [heout] at hdepth
      have hnext := (hbounds (k + 1) (by omega)).1
      change 0 ≤ hexAWDepth
        (hlhc_prefixCoord ws hleg.1 (k + 1)) at hnext
      change hexAWDepth (hlhc_prefixCoord ws hleg.1 k) = 0 at hkZero
      omega
    · exact hflat.2
  rw [hinZero] at hein
  rw [houtZero] at heout
  have hback := congrArg (fun c => hexAWNeighbor c 0) hein
  simp only [hexAWNeighbor_invol] at hback
  have heq : hlhc_prefixCoord ws hleg.1 (k - 1) =
      hlhc_prefixCoord ws hleg.1 (k + 1) := hback.trans heout
  have hidx := hlhda_prefixCoord_injective ws hleg
    (k := k - 1) (l := k + 1) (by omega) (by omega) heq
  omega



theorem hlhda_physical_black_depth_lt (ws : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
    (T : ℕ) (hT : 0 < T)
    (hbounds : ∀ j, j ≤ ws.length →
      0 ≤ hlhd_depth ws hleg j ∧ hlhd_depth ws hleg j ≤ T)
    {k : ℕ} (hk : k < ws.length)
    (hblack : (hlhc_prefixCoord ws hleg.1 k).color = .black) :
    hlhd_depth ws hleg k < T := by
  have hkBounds := hbounds k hk.le
  by_contra hnot
  have hkTop : hlhd_depth ws hleg k = T := by omega
  have hkne : k ≠ 0 := by
    intro hk0
    subst k
    rw [hlhda_depth_zero] at hkTop
    omega
  have hkprev : k - 1 < ws.length := by omega
  obtain ⟨ein, hein⟩ := hlhc_prefixCoord_adjacent ws hleg (k - 1) hkprev
  have hksucc : k - 1 + 1 = k := by omega
  rw [hksucc] at hein
  have hinZero : ein = 0 := by
    apply hlhd_neighbor_black_max_edge_zero
      (hlhc_prefixCoord ws hleg.1 (k - 1))
      (hlhc_prefixCoord ws hleg.1 k) ein hein hblack
    have hprev := (hbounds (k - 1) (by omega)).2
    change hexAWDepth (hlhc_prefixCoord ws hleg.1 (k - 1)) ≤ T at hprev
    change hexAWDepth (hlhc_prefixCoord ws hleg.1 k) = T at hkTop
    omega
  obtain ⟨eout, heout⟩ := hlhc_prefixCoord_adjacent ws hleg k hk
  have houtCases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ws hleg.1 k) eout
  have houtZero : eout = 0 := by
    rcases houtCases with hinc | hdec | hflat
    · have hdepth := hinc.1
      rw [heout] at hdepth
      have hnext := (hbounds (k + 1) (by omega)).2
      change hexAWDepth (hlhc_prefixCoord ws hleg.1 (k + 1)) ≤ T at hnext
      change hexAWDepth (hlhc_prefixCoord ws hleg.1 k) = T at hkTop
      omega
    · have hcolor := hdec.2.1
      rw [hblack] at hcolor
      contradiction
    · exact hflat.2
  rw [hinZero] at hein
  rw [houtZero] at heout
  have hback := congrArg (fun c => hexAWNeighbor c 0) hein
  simp only [hexAWNeighbor_invol] at hback
  have heq : hlhc_prefixCoord ws hleg.1 (k - 1) =
      hlhc_prefixCoord ws hleg.1 (k + 1) := hback.trans heout
  have hidx := hlhda_prefixCoord_injective ws hleg
    (k := k - 1) (l := k + 1) (by omega) (by omega) heq
  omega



theorem hlhda_physical_book_bounds (ws : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
    (T : ℕ) (hT : 0 < T)
    (hbounds : ∀ j, j ≤ ws.length →
      0 ≤ hlhd_depth ws hleg j ∧ hlhd_depth ws hleg j ≤ T)
    {k : ℕ} (hk : k < ws.length) :
    0 ≤ hexAWBookRe2 (hlhc_prefixCoord ws hleg.1 k) ∧
      hexAWBookRe2 (hlhc_prefixCoord ws hleg.1 k) ≤ 3 * T := by
  let c := hlhc_prefixCoord ws hleg.1 k
  have hkBounds := hbounds k hk.le
  change 0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T
  cases hc : c.color with
  | black =>
      have hlt := hlhda_physical_black_depth_lt ws hleg T hT
        hbounds hk hc
      have hkBounds' : 0 ≤ hexAWDepth c ∧ hexAWDepth c ≤ T := by
        simpa only [c, hlhd_depth] using hkBounds
      have hlt' : hexAWDepth c < T := by
        simpa only [c, hlhd_depth] using hlt
      simp only [hexAWBookRe2, hc]
      omega
  | white =>
      have hpos := hlhda_physical_white_depth_pos ws hleg T
        hbounds hk hc
      have hkBounds' : 0 ≤ hexAWDepth c ∧ hexAWDepth c ≤ T := by
        simpa only [c, hlhd_depth] using hkBounds
      have hpos' : 0 < hexAWDepth c := by
        simpa only [c, hlhd_depth] using hpos
      simp only [hexAWBookRe2, hc]
      omega

end

end StatMech.Universality
