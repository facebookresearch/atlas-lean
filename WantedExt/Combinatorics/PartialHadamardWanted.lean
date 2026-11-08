/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.PartialHadamard

@[expose] public section

namespace MathlibExt.Combinatorics.PartialHadamardWanted

open MathlibExt.Combinatorics.PartialHadamard

/-!
# The cubic threshold for the partial Hadamard leading term

Both directions of the exact leading-term threshold recorded by
Optimization Problems 23c, as proof requests. The catalogue constant
`C_{23c}` itself (corrected formulas below the cubic scale) is not
formalized; see the model scope note.
-/

/-- Source: Davis, *Counting partial Hadamard matrices in the cubic
regime*, arXiv:2603.30013 (2026): the leading term is asymptotic in
the regime `t / n³ → ∞`. Known literature result (preprint); its
proof is not supplied here. -/
theorem_wanted davisCubicAdmissible_wanted :
    IsLeadingAdmissible 3

/-- Source: Davis (2026), same paper: a nonvanishing correction at
`t = Θ n³` for large fixed `Θ` blocks every smaller exponent for the
leading term alone. Known literature result (preprint); its proof is
not supplied here. -/
theorem_wanted davisCubicSharp_wanted :
    ∀ α : ℝ, α < 3 → ¬ IsLeadingAdmissible α

end MathlibExt.Combinatorics.PartialHadamardWanted
