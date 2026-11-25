/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.Height.SchurSiegelSmyth.AbsoluteTrace
public import MathlibExt.NumberTheory.Height.SchurSiegelSmyth.ClassicalUpperBound

@[expose] public section

namespace MathlibExt.NumberTheory.SchurSiegelSmyth

/-!
# Catalogue bounds for the Schur--Siegel--Smyth trace constant

The frozen catalogue bounds for constant C86a as proof requests against
`schurSiegelSmythConstant`, the extended-real supremum of the admissible
finite-exception lower bounds on absolute traces of totally positive
algebraic integers.

The provider proves the elementary framework (positivity of absolute
traces, admissibility of `0`, downward closure, and that admissible
bounds lie below the constant). The classical upper bound `2` follows from the integers
`4 cos^2 (π / n)`. The requests below include the milestone and best known lower bounds
from Smyth's auxiliary-function method and its refinements, Smith's upper bound
disproving `C₈₆ = 2`, and the best known upper bound from explicit limiting measures.
Intermediate historical lower
bounds between Smyth (1984) and Orloski--Sardari--Smith (2025) are
omitted as superseded by the best row. Decimal bounds are exact rationals
at the catalogue's displayed digits.
-/

/-- **Schur's lower bound for the Schur–Siegel–Smyth constant.** The Schur–Siegel–Smyth trace
constant $C_{86}$, an extended real number, satisfies $\sqrt{e} \le C_{86}$.

Source: Schur (1918), lower bound `√e ≤ C₈₆`. -/
theorem_wanted schur1918LowerBound_wanted :
    ((Real.sqrt (Real.exp 1) : ℝ) : EReal) ≤ schurSiegelSmythConstant

/-- **Smyth's lower bound for the Schur–Siegel–Smyth constant.** The Schur–Siegel–Smyth trace
constant $C_{86}$, an extended real number, satisfies $1.7719 \le C_{86}$.

Source: Smyth (1984), auxiliary-function lower bound
`1.7719 ≤ C₈₆`. -/
theorem_wanted smyth1984LowerBound_wanted :
    ((17719 / 10000 : ℝ) : EReal) ≤ schurSiegelSmythConstant

/-- **Orloski–Sardari–Smith lower bound for the Schur–Siegel–Smyth constant.** The
Schur–Siegel–Smyth trace constant $C_{86}$, an extended real number, satisfies
$1.80203 \le C_{86}$.

Source: Orloski--Sardari--Smith (2025), best known lower bound
`1.80203 ≤ C₈₆`. -/
theorem_wanted orloskiSardariSmith2025LowerBound_wanted :
    ((180203 / 100000 : ℝ) : EReal) ≤ schurSiegelSmythConstant

/-- **Smith's upper bound for the Schur–Siegel–Smyth trace constant.** The
Schur–Siegel–Smyth trace constant $C_{86}$, an extended real number, satisfies
$C_{86} < 1.89831$.

Source: Smith (2024), strict upper bound `C₈₆ < 1.89831` (the form of
Smith's theorem recorded in the neighbouring
`AlgebraicIntegersWanted` file as `lambda_SSS < 1.89831`), disproving
the conjectured value `2`: infinitely many totally positive algebraic
integers have absolute trace below `1.89831`. -/
theorem_wanted smith2024UpperBound_wanted :
    schurSiegelSmythConstant < ((189831 / 100000 : ℝ) : EReal)

/-- **Sardari–Orloski upper bound for the Schur–Siegel–Smyth constant.** The Schur–Siegel–Smyth
trace constant $C_{86}$, an extended real number, satisfies $C_{86} \le 1.8216$.

Source: Sardari--Orloski (2024), best known upper bound
`C₈₆ ≤ 1.8216` from explicit limiting measures. -/
theorem_wanted sardariOrloski2024UpperBound_wanted :
    schurSiegelSmythConstant ≤ ((18216 / 10000 : ℝ) : EReal)

end MathlibExt.NumberTheory.SchurSiegelSmyth
