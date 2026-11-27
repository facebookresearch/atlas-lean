/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Convex.DikinEllipsoid
public import MathlibExt.Analysis.Convex.SelfConcordant
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import MathlibExt.Analysis.Convex.SelfConcordantBoundsOfDikinLtOne
public import MathlibExt.Analysis.Convex.SelfConcordantDerivLeOfIsSelfConcordantBarrier

/-!
# Properties of self-concordant functions and barriers (wanted)

Three basic properties from A. Nemirovski, *Interior Point Polynomial Time Methods in Convex
Programming*, lecture notes (2004), Sections 2.2 and 3.2, stated with the directional derivatives
`DᵏF(x)[h, …, h]` written as derivatives at `0` of `t ↦ F (x + t h)`, as in
`MathlibExt.Analysis.Convex.SelfConcordant`; `|h|_x = (D²F(x)[h, h])^{1/2}` is the local norm.
The bounds `bounds_of_dikin_lt_one` are in
`MathlibExt.Analysis.Convex.SelfConcordantBoundsOfDikinLtOne`.
The property `deriv_le_of_isSelfConcordantBarrier` is in
`MathlibExt.Analysis.Convex.SelfConcordantDerivLeOfIsSelfConcordantBarrier`.
-/

@[expose] public section

open MathlibExt.Analysis.Convex.SelfConcordant

namespace WantedExt.Analysis.Convex.SelfConcordantWanted

export MathlibExt.Analysis.Convex.SelfConcordant (mem_of_dikin_lt_one)

end WantedExt.Analysis.Convex.SelfConcordantWanted
