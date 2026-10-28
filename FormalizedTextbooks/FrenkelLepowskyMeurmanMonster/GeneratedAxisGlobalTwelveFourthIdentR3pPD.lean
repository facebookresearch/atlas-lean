/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pChecks

/-! # The Fourth identification `R3p` (Twelfth target): octad short part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR3pChecks`, evaluated in its own kernel checks (one module
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
theorem fourthR3p_psoct0 :
    (((fourthR3pW.sh.oct).take 7946).map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR3pL) b.1 q.1)).sum)).sum = 94288 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad short terms, part 1 (packed octad Fourier, integer form). -/
theorem fourthR3p_psoct1 :
    (((((fourthR3pW.sh.oct).drop 7946)).take 7947).map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR3pL) b.1 q.1)).sum)).sum = 97112 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad short terms, part 2 (packed octad Fourier, integer form). -/
theorem fourthR3p_psoct2 :
    (((((fourthR3pW.sh.oct).drop 7946)).drop 7947).map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR3pL) b.1 q.1)).sum)).sum = 84056 := by
  decide +kernel

/-- The octad terms of the short part of the pairing (packed octad Fourier, integer form). -/
theorem fourthR3p_psoct :
    (fourthR3pW.sh.oct.map (fun b => (b.2.map (fun q =>
      q.2 * octZ 32 true (octPackX 32 true fourthR3pL) b.1 q.1)).sum)).sum = 275456 := by
  rw [← List.take_append_drop 7946 (fourthR3pW.sh.oct), List.map_append, List.sum_append, fourthR3p_psoct0,
    ← List.take_append_drop 7947 ((fourthR3pW.sh.oct).drop 7946), List.map_append, List.sum_append, fourthR3p_psoct1,
    fourthR3p_psoct2]
  norm_num

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
