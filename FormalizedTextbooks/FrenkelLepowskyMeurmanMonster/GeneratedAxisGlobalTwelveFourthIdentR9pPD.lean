/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pChecks

/-! # The Fourth identification `R9p` (Eighth target): octad short part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR9pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The octad short terms, part 0 (packed octad Fourier, integer form). -/
theorem fourthR9p_psoct0 :
    (((fourthR9pW.sh.oct).take 7297).map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR9pL) b.1 q.1)).sum)).sum = 7731712 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad short terms, part 1 (packed octad Fourier, integer form). -/
theorem fourthR9p_psoct1 :
    (((((fourthR9pW.sh.oct).drop 7297)).take 7297).map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR9pL) b.1 q.1)).sum)).sum = 4784640 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad short terms, part 2 (packed octad Fourier, integer form). -/
theorem fourthR9p_psoct2 :
    (((((fourthR9pW.sh.oct).drop 7297)).drop 7297).map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR9pL) b.1 q.1)).sum)).sum = 5309440 := by
  decide +kernel

/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthR9p_psoct :
    (fourthR9pW.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR9pL) b.1 q.1)).sum)).sum = 17825792 := by
  rw [← List.take_append_drop 7297 (fourthR9pW.sh.oct), List.map_append, List.sum_append, fourthR9p_psoct0,
    ← List.take_append_drop 7297 ((fourthR9pW.sh.oct).drop 7297), List.map_append, List.sum_append, fourthR9p_psoct1,
    fourthR9p_psoct2]
  norm_num

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
