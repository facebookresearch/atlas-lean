/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirring
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Araki–Lieb–Thirring inequality (wanted)

For positive-semidefinite matrices `A`, `B` and real `q ≥ 0`, `r ≥ 1`,
`tr (A^{1/2} B A^{1/2})^{rq} ≤ tr (A^{r/2} B^r A^{r/2})^q`, and the inequality reverses for
`0 ≤ r ≤ 1` (H. Araki, *On an inequality of Lieb and Thirring*, Lett. Math. Phys. 19 (1990)
167–170; stated as Theorem 1 of K. M. R. Audenaert, *On the Araki–Lieb–Thirring inequality*,
arXiv:math/0701129). The case `q = 1` is the Lieb–Thirring trace inequality
`tr (B^{1/2} A B^{1/2})^t ≤ tr (B^{t/2} A^t B^{t/2})` for `t ≥ 1` (E. H. Lieb and W. Thirring, in
*Studies in Mathematical Physics*, Princeton University Press, 1976, 269–303; E. A. Carlen, *Trace
inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009,
Theorem 7.4). Matrix powers are the continuous functional calculus `cfc (· ^ p)` of the real
power function. The reversed range is proved in the imported module.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Araki–Lieb–Thirring inequality.** For positive-semidefinite complex matrices `A` and `B`
and reals `q ≥ 0`, `r ≥ 1`,
`tr (A^{1/2} B A^{1/2})^{rq} ≤ tr (A^{r/2} B^r A^{r/2})^q`
(H. Araki, Lett. Math. Phys. 19 (1990) 167–170; K. M. R. Audenaert, arXiv:math/0701129,
Theorem 1, the case `r ≥ 1`). Both traces are real because both matrices are positive
semidefinite; the statement compares their real parts. -/
theorem_wanted araki_lieb_thirring {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 1 ≤ r) :
    RCLike.re (cfc (· ^ (r * q) : ℝ → ℝ)
        (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A * B * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A)).trace ≤
      RCLike.re (cfc (· ^ q : ℝ → ℝ)
        (cfc (· ^ (r / 2) : ℝ → ℝ) A * cfc (· ^ r : ℝ → ℝ) B *
          cfc (· ^ (r / 2) : ℝ → ℝ) A)).trace

end MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted
