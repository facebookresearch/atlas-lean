/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadLevelOne
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber0BlocksA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber0BlocksB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber0BlocksC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber0BlocksD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1BlocksA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1BlocksB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1BlocksC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1BlocksD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber2BlocksA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber2BlocksB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber2BlocksC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber2BlocksD

/-! Complete binary Ω-orbit coverage by the actual octad-axis stabilizer from five genuine roots.
The induced dual action is reduced by a descending forest on 256 values, and each of the three
root fibers by kernel-checked descending forests of stabilizer words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem octadAct_inv_mul (h : H) (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalBinaryAct h⁻¹ (generatedAxisGlobalBinaryAct h x) = x := by
  rw [← generatedAxisGlobalBinaryAct_mul, inv_mul_cancel]
  apply Subtype.ext
  change co1BinaryAction (projH 1) x.val = x.val
  rw [map_one, map_one]
  rfl

/-- Every genuine binary Ω-orbit point has a singular mask in adapted coordinates. -/
theorem generatedAxisGlobalTwelveOctadCoord_singular (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalMaskSingular
      (generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows
        (generatedAxisGlobalTwelveOctadCoord x)) = true := by
  rw [← generatedAxisGlobalTwelveOctadMask_eq_coord, generatedAxisGlobalMaskSingular_iff,
    generatedAxisGlobalTwelveOctadMask_decode]
  exact generatedAxisGlobalBinary_squareQuad x

/-- A point whose mask is a root mask is the corresponding root point. -/
theorem generatedAxisGlobalTwelveOctad_of_root_mask (x : generatedAxisGlobalBinaryOrbit)
    (h : (∃ j : Fin 5, generatedAxisGlobalTwelveOctadMask x = generatedAxisGlobalTwelveOctadRootMask j) ∨
      (∃ j : Fin 5, generatedAxisGlobalTwelveOctadMask x =
        generatedAxisGlobalTwelveOctadExcludedMask j)) :
    ∃ j : Fin 5, ∃ c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
      generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveOctadRootPoint j) = x := by
  rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
  · refine ⟨j, 1, Subgroup.one_mem _, ?_⟩
    have he : generatedAxisGlobalTwelveOctadRootPoint j = x := by
      apply generatedAxisGlobalTwelveOctadMask_injective
      rw [generatedAxisGlobalTwelveOctadRootPoint_mask, hj]
    rw [he]
    apply Subtype.ext
    change co1BinaryAction (projH 1) x.val = x.val
    rw [map_one, map_one]
    rfl
  · exfalso
    apply generatedAxisGlobalTwelveOctadExcluded_not_mem j
    rw [← hj, generatedAxisGlobalTwelveOctadMask_decode]
    exact x.property

/-- Every point of fiber 0 satisfies the reference descent step. -/
theorem generatedAxisGlobalTwelveOctadFiber0_step (t : ℕ) (ht : t < 65536) : generatedAxisGlobalTwelveOctadFiber0Step t := by
  apply generatedAxisGlobalTwelveOctadFiber0Check_sound
  have key : ∀ b : Fin 16, generatedAxisGlobalTwelveOctadFiber0Loop (4096 * b.val) 4096 = true := by
    intro b
    fin_cases b
    · exact generatedAxisGlobalTwelveOctadFiber0Block00
    · exact generatedAxisGlobalTwelveOctadFiber0Block01
    · exact generatedAxisGlobalTwelveOctadFiber0Block02
    · exact generatedAxisGlobalTwelveOctadFiber0Block03
    · exact generatedAxisGlobalTwelveOctadFiber0Block04
    · exact generatedAxisGlobalTwelveOctadFiber0Block05
    · exact generatedAxisGlobalTwelveOctadFiber0Block06
    · exact generatedAxisGlobalTwelveOctadFiber0Block07
    · exact generatedAxisGlobalTwelveOctadFiber0Block08
    · exact generatedAxisGlobalTwelveOctadFiber0Block09
    · exact generatedAxisGlobalTwelveOctadFiber0Block10
    · exact generatedAxisGlobalTwelveOctadFiber0Block11
    · exact generatedAxisGlobalTwelveOctadFiber0Block12
    · exact generatedAxisGlobalTwelveOctadFiber0Block13
    · exact generatedAxisGlobalTwelveOctadFiber0Block14
    · exact generatedAxisGlobalTwelveOctadFiber0Block15
  have hb : t / 4096 < 16 := by omega
  have h := generatedAxisGlobalTwelveOctadFiber0Loop_sound 4096 (4096 * (t / 4096)) (key ⟨t / 4096, hb⟩) (t % 4096)
    (Nat.mod_lt _ (by norm_num))
  rwa [show 4096 * (t / 4096) + t % 4096 = t by omega] at h

set_option maxHeartbeats 4000000 in
-- Classify the fiber roots by their genuine masks.
/-- Every root of fiber 0 has a root mask or an excluded mask. -/
theorem generatedAxisGlobalTwelveOctadFiber0_roots : ∀ t ∈ generatedAxisGlobalTwelveOctadFiber0Roots,
    (∃ j : Fin 5, generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows (t + 0) =
      generatedAxisGlobalTwelveOctadRootMask j) ∨
    (∃ j : Fin 5, generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows (t + 0) =
      generatedAxisGlobalTwelveOctadExcludedMask j) := by
  decide +kernel

/-- Every Ω-orbit point in fiber 0 is covered from the five roots. -/
theorem generatedAxisGlobalTwelveOctadFiber0_cover : ∀ n : ℕ, ∀ x : generatedAxisGlobalBinaryOrbit,
    generatedAxisGlobalTwelveOctadCoord x >>> 16 = 0 →
      generatedAxisGlobalTwelveOctadFiber0Rank (generatedAxisGlobalTwelveOctadCoord x % 65536) = n →
      ∃ j : Fin 5, ∃ c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveOctadRootPoint j) = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hy hn
    have hlt := generatedAxisGlobalTwelveOctadCoord_lt x
    have hc : generatedAxisGlobalTwelveOctadCoord x =
        generatedAxisGlobalTwelveOctadCoord x % 65536 + 0 := by
      rw [Nat.shiftRight_eq_div_pow] at hy
      norm_num at hy
      omega
    have hs := generatedAxisGlobalTwelveOctadCoord_singular x
    rw [hc] at hs
    rcases generatedAxisGlobalTwelveOctadFiber0_step _ (Nat.mod_lt _ (by norm_num)) hs with hr | ⟨hy', hdesc⟩
    · apply generatedAxisGlobalTwelveOctad_of_root_mask
      rw [generatedAxisGlobalTwelveOctadMask_eq_coord, hc]
      exact generatedAxisGlobalTwelveOctadFiber0_roots _ hr
    · let w := generatedAxisGlobalTwelveOctadFiber0Words.getD (generatedAxisGlobalTwelveOctadFiber0Edge (generatedAxisGlobalTwelveOctadCoord x % 65536)) []
      have hrows : generatedAxisGlobalTwelveOctadFiber0WordRows.getD
          (generatedAxisGlobalTwelveOctadFiber0Edge (generatedAxisGlobalTwelveOctadCoord x % 65536))
          (generatedAxisGlobalTwelveOctadWordRows []) = generatedAxisGlobalTwelveOctadWordRows w := by
        rw [generatedAxisGlobalTwelveOctadFiber0WordRows_certificate, List.getD_map]
      let x' := generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadWord w) x
      have hx' : generatedAxisGlobalTwelveOctadCoord x' =
          generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadFiber0WordRows.getD
            (generatedAxisGlobalTwelveOctadFiber0Edge (generatedAxisGlobalTwelveOctadCoord x % 65536))
            (generatedAxisGlobalTwelveOctadWordRows []))
            (generatedAxisGlobalTwelveOctadCoord x % 65536 + 0) := by
        rw [generatedAxisGlobalTwelveOctadWord_coord, hrows, ← hc]
      obtain ⟨j, c, hcm, hcx⟩ := ih _ (by rw [← hn, hx']; exact hdesc) x' (by rw [hx']; exact hy')
        rfl
      refine ⟨j, (generatedAxisGlobalTwelveOctadWord w)⁻¹ * c,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (generatedAxisGlobalTwelveOctadWord_mem w)) hcm, ?_⟩
      rw [generatedAxisGlobalBinaryAct_mul, hcx]
      exact octadAct_inv_mul _ x

/-- Every point of fiber 1 satisfies the reference descent step. -/
theorem generatedAxisGlobalTwelveOctadFiber1_step (t : ℕ) (ht : t < 65536) : generatedAxisGlobalTwelveOctadFiber1Step t := by
  apply generatedAxisGlobalTwelveOctadFiber1Check_sound
  have key : ∀ b : Fin 16, generatedAxisGlobalTwelveOctadFiber1Loop (4096 * b.val) 4096 = true := by
    intro b
    fin_cases b
    · exact generatedAxisGlobalTwelveOctadFiber1Block00
    · exact generatedAxisGlobalTwelveOctadFiber1Block01
    · exact generatedAxisGlobalTwelveOctadFiber1Block02
    · exact generatedAxisGlobalTwelveOctadFiber1Block03
    · exact generatedAxisGlobalTwelveOctadFiber1Block04
    · exact generatedAxisGlobalTwelveOctadFiber1Block05
    · exact generatedAxisGlobalTwelveOctadFiber1Block06
    · exact generatedAxisGlobalTwelveOctadFiber1Block07
    · exact generatedAxisGlobalTwelveOctadFiber1Block08
    · exact generatedAxisGlobalTwelveOctadFiber1Block09
    · exact generatedAxisGlobalTwelveOctadFiber1Block10
    · exact generatedAxisGlobalTwelveOctadFiber1Block11
    · exact generatedAxisGlobalTwelveOctadFiber1Block12
    · exact generatedAxisGlobalTwelveOctadFiber1Block13
    · exact generatedAxisGlobalTwelveOctadFiber1Block14
    · exact generatedAxisGlobalTwelveOctadFiber1Block15
  have hb : t / 4096 < 16 := by omega
  have h := generatedAxisGlobalTwelveOctadFiber1Loop_sound 4096 (4096 * (t / 4096)) (key ⟨t / 4096, hb⟩) (t % 4096)
    (Nat.mod_lt _ (by norm_num))
  rwa [show 4096 * (t / 4096) + t % 4096 = t by omega] at h

set_option maxHeartbeats 4000000 in
-- Classify the fiber roots by their genuine masks.
/-- Every root of fiber 1 has a root mask or an excluded mask. -/
theorem generatedAxisGlobalTwelveOctadFiber1_roots : ∀ t ∈ generatedAxisGlobalTwelveOctadFiber1Roots,
    (∃ j : Fin 5, generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows (t + 65536) =
      generatedAxisGlobalTwelveOctadRootMask j) ∨
    (∃ j : Fin 5, generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows (t + 65536) =
      generatedAxisGlobalTwelveOctadExcludedMask j) := by
  decide +kernel

/-- Every Ω-orbit point in fiber 1 is covered from the five roots. -/
theorem generatedAxisGlobalTwelveOctadFiber1_cover : ∀ n : ℕ, ∀ x : generatedAxisGlobalBinaryOrbit,
    generatedAxisGlobalTwelveOctadCoord x >>> 16 = 1 →
      generatedAxisGlobalTwelveOctadFiber1Rank (generatedAxisGlobalTwelveOctadCoord x % 65536) = n →
      ∃ j : Fin 5, ∃ c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveOctadRootPoint j) = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hy hn
    have hlt := generatedAxisGlobalTwelveOctadCoord_lt x
    have hc : generatedAxisGlobalTwelveOctadCoord x =
        generatedAxisGlobalTwelveOctadCoord x % 65536 + 65536 := by
      rw [Nat.shiftRight_eq_div_pow] at hy
      norm_num at hy
      omega
    have hs := generatedAxisGlobalTwelveOctadCoord_singular x
    rw [hc] at hs
    rcases generatedAxisGlobalTwelveOctadFiber1_step _ (Nat.mod_lt _ (by norm_num)) hs with hr | ⟨hy', hdesc⟩
    · apply generatedAxisGlobalTwelveOctad_of_root_mask
      rw [generatedAxisGlobalTwelveOctadMask_eq_coord, hc]
      exact generatedAxisGlobalTwelveOctadFiber1_roots _ hr
    · let w := generatedAxisGlobalTwelveOctadFiber1Words.getD (generatedAxisGlobalTwelveOctadFiber1Edge (generatedAxisGlobalTwelveOctadCoord x % 65536)) []
      have hrows : generatedAxisGlobalTwelveOctadFiber1WordRows.getD
          (generatedAxisGlobalTwelveOctadFiber1Edge (generatedAxisGlobalTwelveOctadCoord x % 65536))
          (generatedAxisGlobalTwelveOctadWordRows []) = generatedAxisGlobalTwelveOctadWordRows w := by
        rw [generatedAxisGlobalTwelveOctadFiber1WordRows_certificate, List.getD_map]
      let x' := generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadWord w) x
      have hx' : generatedAxisGlobalTwelveOctadCoord x' =
          generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadFiber1WordRows.getD
            (generatedAxisGlobalTwelveOctadFiber1Edge (generatedAxisGlobalTwelveOctadCoord x % 65536))
            (generatedAxisGlobalTwelveOctadWordRows []))
            (generatedAxisGlobalTwelveOctadCoord x % 65536 + 65536) := by
        rw [generatedAxisGlobalTwelveOctadWord_coord, hrows, ← hc]
      obtain ⟨j, c, hcm, hcx⟩ := ih _ (by rw [← hn, hx']; exact hdesc) x' (by rw [hx']; exact hy')
        rfl
      refine ⟨j, (generatedAxisGlobalTwelveOctadWord w)⁻¹ * c,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (generatedAxisGlobalTwelveOctadWord_mem w)) hcm, ?_⟩
      rw [generatedAxisGlobalBinaryAct_mul, hcx]
      exact octadAct_inv_mul _ x

/-- Every point of fiber 2 satisfies the reference descent step. -/
theorem generatedAxisGlobalTwelveOctadFiber2_step (t : ℕ) (ht : t < 65536) : generatedAxisGlobalTwelveOctadFiber2Step t := by
  apply generatedAxisGlobalTwelveOctadFiber2Check_sound
  have key : ∀ b : Fin 16, generatedAxisGlobalTwelveOctadFiber2Loop (4096 * b.val) 4096 = true := by
    intro b
    fin_cases b
    · exact generatedAxisGlobalTwelveOctadFiber2Block00
    · exact generatedAxisGlobalTwelveOctadFiber2Block01
    · exact generatedAxisGlobalTwelveOctadFiber2Block02
    · exact generatedAxisGlobalTwelveOctadFiber2Block03
    · exact generatedAxisGlobalTwelveOctadFiber2Block04
    · exact generatedAxisGlobalTwelveOctadFiber2Block05
    · exact generatedAxisGlobalTwelveOctadFiber2Block06
    · exact generatedAxisGlobalTwelveOctadFiber2Block07
    · exact generatedAxisGlobalTwelveOctadFiber2Block08
    · exact generatedAxisGlobalTwelveOctadFiber2Block09
    · exact generatedAxisGlobalTwelveOctadFiber2Block10
    · exact generatedAxisGlobalTwelveOctadFiber2Block11
    · exact generatedAxisGlobalTwelveOctadFiber2Block12
    · exact generatedAxisGlobalTwelveOctadFiber2Block13
    · exact generatedAxisGlobalTwelveOctadFiber2Block14
    · exact generatedAxisGlobalTwelveOctadFiber2Block15
  have hb : t / 4096 < 16 := by omega
  have h := generatedAxisGlobalTwelveOctadFiber2Loop_sound 4096 (4096 * (t / 4096)) (key ⟨t / 4096, hb⟩) (t % 4096)
    (Nat.mod_lt _ (by norm_num))
  rwa [show 4096 * (t / 4096) + t % 4096 = t by omega] at h

set_option maxHeartbeats 4000000 in
-- Classify the fiber roots by their genuine masks.
/-- Every root of fiber 2 has a root mask or an excluded mask. -/
theorem generatedAxisGlobalTwelveOctadFiber2_roots : ∀ t ∈ generatedAxisGlobalTwelveOctadFiber2Roots,
    (∃ j : Fin 5, generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows (t + 131072) =
      generatedAxisGlobalTwelveOctadRootMask j) ∨
    (∃ j : Fin 5, generatedAxisGlobalMaskRowsAction generatedAxisGlobalTwelveOctadTRows (t + 131072) =
      generatedAxisGlobalTwelveOctadExcludedMask j) := by
  decide +kernel

/-- Every Ω-orbit point in fiber 2 is covered from the five roots. -/
theorem generatedAxisGlobalTwelveOctadFiber2_cover : ∀ n : ℕ, ∀ x : generatedAxisGlobalBinaryOrbit,
    generatedAxisGlobalTwelveOctadCoord x >>> 16 = 2 →
      generatedAxisGlobalTwelveOctadFiber2Rank (generatedAxisGlobalTwelveOctadCoord x % 65536) = n →
      ∃ j : Fin 5, ∃ c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveOctadRootPoint j) = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hy hn
    have hlt := generatedAxisGlobalTwelveOctadCoord_lt x
    have hc : generatedAxisGlobalTwelveOctadCoord x =
        generatedAxisGlobalTwelveOctadCoord x % 65536 + 131072 := by
      rw [Nat.shiftRight_eq_div_pow] at hy
      norm_num at hy
      omega
    have hs := generatedAxisGlobalTwelveOctadCoord_singular x
    rw [hc] at hs
    rcases generatedAxisGlobalTwelveOctadFiber2_step _ (Nat.mod_lt _ (by norm_num)) hs with hr | ⟨hy', hdesc⟩
    · apply generatedAxisGlobalTwelveOctad_of_root_mask
      rw [generatedAxisGlobalTwelveOctadMask_eq_coord, hc]
      exact generatedAxisGlobalTwelveOctadFiber2_roots _ hr
    · let w := generatedAxisGlobalTwelveOctadFiber2Words.getD (generatedAxisGlobalTwelveOctadFiber2Edge (generatedAxisGlobalTwelveOctadCoord x % 65536)) []
      have hrows : generatedAxisGlobalTwelveOctadFiber2WordRows.getD
          (generatedAxisGlobalTwelveOctadFiber2Edge (generatedAxisGlobalTwelveOctadCoord x % 65536))
          (generatedAxisGlobalTwelveOctadWordRows []) = generatedAxisGlobalTwelveOctadWordRows w := by
        rw [generatedAxisGlobalTwelveOctadFiber2WordRows_certificate, List.getD_map]
      let x' := generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadWord w) x
      have hx' : generatedAxisGlobalTwelveOctadCoord x' =
          generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveOctadFiber2WordRows.getD
            (generatedAxisGlobalTwelveOctadFiber2Edge (generatedAxisGlobalTwelveOctadCoord x % 65536))
            (generatedAxisGlobalTwelveOctadWordRows []))
            (generatedAxisGlobalTwelveOctadCoord x % 65536 + 131072) := by
        rw [generatedAxisGlobalTwelveOctadWord_coord, hrows, ← hc]
      obtain ⟨j, c, hcm, hcx⟩ := ih _ (by rw [← hn, hx']; exact hdesc) x' (by rw [hx']; exact hy')
        rfl
      refine ⟨j, (generatedAxisGlobalTwelveOctadWord w)⁻¹ * c,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (generatedAxisGlobalTwelveOctadWord_mem w)) hcm, ?_⟩
      rw [generatedAxisGlobalBinaryAct_mul, hcx]
      exact octadAct_inv_mul _ x

/-- Every Ω-orbit point is covered, by descent on the induced dual action. -/
theorem generatedAxisGlobalTwelveOctad_cover_aux : ∀ n : ℕ, ∀ x : generatedAxisGlobalBinaryOrbit,
    generatedAxisGlobalTwelveOctadLevelRank (generatedAxisGlobalTwelveOctadCoord x >>> 16) = n →
      ∃ j : Fin 5, ∃ c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveOctadRootPoint j) = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hn
    have hlt := generatedAxisGlobalTwelveOctadCoord_lt x
    have hy : generatedAxisGlobalTwelveOctadCoord x >>> 16 < 256 := by
      rw [Nat.shiftRight_eq_div_pow]
      norm_num
      omega
    rcases generatedAxisGlobalTwelveOctadLevel_certificate ⟨_, hy⟩ with h0 | h1 | h2 | hd
    · exact generatedAxisGlobalTwelveOctadFiber0_cover _ x h0 rfl
    · exact generatedAxisGlobalTwelveOctadFiber1_cover _ x h1 rfl
    · exact generatedAxisGlobalTwelveOctadFiber2_cover _ x h2 rfl
    · let e := generatedAxisGlobalTwelveOctadLevelEdge (generatedAxisGlobalTwelveOctadCoord x >>> 16)
      let x' := generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveOctadGenerator e).val x
      have hx' := generatedAxisGlobalTwelveOctadGenerator_coord_high e x
      obtain ⟨j, c, hcm, hcx⟩ := ih _ (by rw [← hn]; rw [← hx'] at hd; exact hd) x' rfl
      refine ⟨j, (generatedAxisGlobalTwelveOctadGenerator e).val⁻¹ * c,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (generatedAxisGlobalTwelveOctadGenerator e).property)
          hcm, ?_⟩
      rw [generatedAxisGlobalBinaryAct_mul, hcx]
      exact octadAct_inv_mul _ x

/-- The actual octad-axis stabilizer covers the entire genuine binary Ω orbit from five roots. -/
theorem generatedAxisGlobalTwelveOctad_binary_cover (x : generatedAxisGlobalBinaryOrbit) :
    ∃ j : Fin 5, ∃ c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
      generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveOctadRootPoint j) = x :=
  generatedAxisGlobalTwelveOctad_cover_aux _ x rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
