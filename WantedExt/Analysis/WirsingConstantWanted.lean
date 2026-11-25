/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.WirsingConstantUpperBound

@[expose] public section

namespace MathlibExt.Analysis.WirsingConstantWanted

open MathlibExt.Analysis.WirsingConstant

/-!
# Catalogue bounds for the Wirsing constant

The certified Mayer--Roepstorff interval from Optimization Problems
record 83a, with its lower bound requested and its upper bound proved for
`wirsingConstant` — the subdominant
absolute eigenvalue over eigenfunctions holomorphic on the Mayer disk,
as defined in `MathlibExt/Analysis/WirsingConstant.lean` (not over all
continuous eigenfunctions, where the interval fails). The sharper
2026 certified spectral enclosure at 175 digits is recorded in the
Sources entry and omitted; no spectral computation is supplied here.
-/

/-- **Mayer–Roepstorff lower bound for the Wirsing constant.** The
Wirsing constant is at least $0.30366299$.

Source: Mayer and Roepstorff (1987), eq. (5.20), catalogue lower
bound `0.30366299`, certified via generalized Temple inequalities.
Known literature result; its proof is not supplied here. -/
theorem_wanted mayerRoepstorffLowerBound_wanted :
    (30366299 / 100000000 : ℝ) ≤ wirsingConstant

end MathlibExt.Analysis.WirsingConstantWanted
