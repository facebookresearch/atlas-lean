/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10pChecks

/-! # The Fourth identification `R10p` (Sixth target): matrix and short parts

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR10pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false
/-- The denominators of the two packed tensors. -/
theorem fourthR10p_dens :
    tensorWordDenAll fourthR10pH = 4096 ∧
      (tensorWordDenAll fourthR10pG : ℚ) * fourthR10pSD = 16384 := by
  refine ⟨by decide, ?_⟩
  have h : tensorWordDenAll fourthR10pG = 512 := by decide
  rw [h]
  unfold fourthR10pSD
  norm_num

set_option maxRecDepth 100000 in
/-- The matrix part of the pairing. -/
theorem fourthR10p_pmat : triMatF true fourthR10pL fourthR10pW = 497 / 128 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short scales of the two representations. -/
theorem fourthR10p_sdens : fourthR10pL.sden = 1 / 8 ∧ fourthR10pW.sden = 1 / 32 := by
  constructor
  · rfl
  · decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the source representation fit the packed octad transform. -/
theorem fourthR10p_octok : octPackOk 32 fourthR10pL = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair terms of the short part of the pairing. -/
theorem fourthR10p_pspairs :
    (fourthR10pW.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF true fourthR10pL q.1)).sum =
      191 / 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthR10p_psoct :
    (fourthR10pW.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR10pL) b.1 q.1)).sum)).sum = 69376 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of the short part of the pairing. -/
theorem fourthR10p_psodd :
    (fourthR10pW.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthR10pL q.1)).sum =
      896 := by
  decide +kernel

/-- The short part of the pairing (packed octad Fourier). -/
theorem fourthR10p_pshort : triShortO 32 true fourthR10pL fourthR10pW = 8111 / 128 := by
  rw [triShortO]
  simp only [fourthR10p_octok, ↓reduceIte]
  rw [fourthR10p_pspairs, fourthR10p_psoct, fourthR10p_psodd]
  rw [fourthR10p_sdens.1, fourthR10p_sdens.2]
  norm_num

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
