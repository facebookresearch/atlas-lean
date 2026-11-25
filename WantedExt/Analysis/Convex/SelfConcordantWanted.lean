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

/-!
# Properties of self-concordant functions and barriers (wanted)

Three basic properties from A. Nemirovski, *Interior Point Polynomial Time Methods in Convex
Programming*, lecture notes (2004), Sections 2.2 and 3.2, stated with the directional derivatives
`DᵏF(x)[h, …, h]` written as derivatives at `0` of `t ↦ F (x + t h)`, as in
`MathlibExt.Analysis.Convex.SelfConcordant`; `|h|_x = (D²F(x)[h, h])^{1/2}` is the local norm.
-/

@[expose] public section

open MathlibExt.Analysis.Convex.SelfConcordant

namespace WantedExt.Analysis.Convex.SelfConcordantWanted

export MathlibExt.Analysis.Convex.SelfConcordant (mem_of_dikin_lt_one)

/-- **Bounds on a self-concordant function in the Dikin ellipsoid.** If `F` is self-concordant on
`Q`, `x ∈ Q` and `r = |h|_x < 1`, then with `ρ(s) = -log (1 - s) - s`,
`F(x) + DF(x)[h] + ρ(-r) ≤ F(x + h) ≤ F(x) + DF(x)[h] + ρ(r)`.
This is (2.4)–(2.5) in item I of Section 2.2 of A. Nemirovski, *Interior Point Polynomial Time
Methods in Convex Programming*, lecture notes (2004). -/
theorem_wanted bounds_of_dikin_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : E → ℝ} {Q : Set E} (hF : IsSelfConcordant F Q) {x h : E}
    (hx : x ∈ Q) (hr : √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0) < 1) :
    F x + deriv (fun t : ℝ => F (x + t • h)) 0 +
        (-Real.log (1 + √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) +
          √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) ≤ F (x + h) ∧
      F (x + h) ≤ F x + deriv (fun t : ℝ => F (x + t • h)) 0 +
        (-Real.log (1 - √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) -
          √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0))

/-- **Semiboundedness of a self-concordant barrier.** If `F` is a `ϑ`-self-concordant barrier for
`closure Q` (with interior `Q`), then `DF(x)[y - x] ≤ ϑ` for every `x ∈ Q` and every
`y ∈ closure Q`. This is (3.6), item I of Section 3.2 of A. Nemirovski, *Interior Point
Polynomial Time Methods in Convex Programming*, lecture notes (2004); it bounds the duality-type
gap along the central path of path-following methods. -/
theorem_wanted deriv_le_of_isSelfConcordantBarrier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : E → ℝ} {Q : Set E} {ϑ : ℝ}
    (hF : IsSelfConcordantBarrier F Q ϑ) {x y : E} (hx : x ∈ Q) (hy : y ∈ closure Q) :
    deriv (fun t : ℝ => F (x + t • (y - x))) 0 ≤ ϑ

end WantedExt.Analysis.Convex.SelfConcordantWanted
