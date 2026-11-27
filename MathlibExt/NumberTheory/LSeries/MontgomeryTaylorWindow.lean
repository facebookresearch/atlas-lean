/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`zeta23/ChallengeDeps.lean` (§3, `cMT`) and its copy in `zeta23/Challenge.lean`
(anthropics/formal-math,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23):
Copyright (c) 2026 Anthropic, PBC (adapted counting conventions and statement types).
Released under the Apache License, Version 2.0; see the upstream LICENSE:
https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/LICENSE
Authors: Claude (as credited in `zeta23/formalization.yaml`; no per-file author list).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The Montgomery–Taylor window constant -/

@[expose] public noncomputable section

namespace ComplexZeroCounts

/-- **Montgomery–Taylor window constant.** This is $c_{\mathrm{MT}}$, not the window functional
$R(\psi_{\mathrm{MT}})$. For $\psi_{\mathrm{MT}}(s)=\cos(\sqrt{2}\,s)\mathbf{1}_{[-1/2,1/2]}(s)$,
$R(\psi_{\mathrm{MT}})=c_{\mathrm{MT}}^{-1}=1/2+\cot(1/\sqrt{2})/\sqrt{2}$.
The closed form for $c_{\mathrm{MT}}$ is
$\sqrt{2}\tan(1/\sqrt{2})/(1+\tan(1/\sqrt{2})/\sqrt{2})$.

Source: Alpöge and Furman, [arXiv:2608.13637v2](https://arxiv.org/abs/2608.13637v2),
Theorem A, (2.6), and Lemma 5.6 (5.13); Appendix A gives the closed form. -/
def montgomeryTaylorWindowConstant : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
    (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end ComplexZeroCounts
