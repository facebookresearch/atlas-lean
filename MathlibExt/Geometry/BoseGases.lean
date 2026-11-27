/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# The Lee–Huang–Yang error exponent

Theorem 1.2 of Fournais–Solovej does not name a value for the exponent. With
$t = \rho_\mu a^3$, equation (5.27) sets $X = t^{1/323}$. After factoring out $t^{1/2}$,
the error bracket in Theorem 6.8, equation (6.30), is
$X^2\mathcal{R} + (R/a)^2 t^{1/2} + X^{1/5}$. For $0 < t \le 1$, this is at most
$(\mathcal{R} + (R/a)^2 + 1)t^{1/1615}$, since $X^2 = t^{2/323}$ and
$X^{1/5} = t^{1/1615}$. In (4.4), the proof of Theorem 1.2 sets $\rho_\mu = \rho$,
which preserves the exponent and the inputs $\mathcal{R}$ and $R/a$ to the error coefficient.
-/

@[expose] public section

namespace MathlibExt.Geometry.BoseGasesWanted.BoseGases

/-- **Lee–Huang–Yang error exponent.** This definition chooses the explicit admissible value
$\eta = 1/1615$ in the error term $(\rho a^3)^{1/2 + \eta}$ of the Lee–Huang–Yang lower bound
(Theorem 1.2), where $\rho$ is the density and $a$ is the scattering length. The choice follows
from equations (5.27) and (6.30) and the substitution $\rho_\mu = \rho$ in (4.4). Theorem 1.2
itself gives no numerical value for $\eta$, and the choice is not claimed to be optimal.

Source: S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192
(3) 2020. The declaration name and type follow
https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14),
AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean, via
leanprover/lean-eval@38361be, problem `annals_bose_gases`. -/
noncomputable def η : ℝ := 1 / 1615

end MathlibExt.Geometry.BoseGasesWanted.BoseGases
