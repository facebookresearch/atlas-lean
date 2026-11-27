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

/-- **Montgomery–Taylor window constant.** This is $c_{\mathrm{MT}}$, the reciprocal of the
window functional $R(\psi_{\mathrm{MT}})$ for
$\psi_{\mathrm{MT}}(s)=\cos(\sqrt{2}\,s)\mathbf{1}_{[-1/2,1/2]}(s)$.

For an even positive continuous window $\psi$ on $[-1/2,1/2]$, extend it by zero and use
$\widehat\psi(x)=\int_{\mathbb R}\psi(s)e^{-2\pi i sx}\,ds$ and
$g(x)=|\widehat\psi(x)/\widehat\psi(0)|^2$. Then $g$ is nonnegative and integrable,
$g(0)=1$, and $\widehat g$ is supported in $[-1,1]$. The window functional satisfies
$R(\psi)=1+M(g)$, where $M(g)=\widehat g(0)-\int_{-1}^1(1-|t|)\widehat g(t)\,dt$.
For the cosine window, $g$ gives the equality case of Corollary 14 below, so
$R(\psi_{\mathrm{MT}})=c_{\mathrm{MT}}^{-1}=1/2+\cot(1/\sqrt{2})/\sqrt{2}$.
The closed form for $c_{\mathrm{MT}}$ is
$\sqrt{2}\tan(1/\sqrt{2})/(1+\tan(1/\sqrt{2})/\sqrt{2})$.

Sources: Carneiro, Chandee, Littmann, and Milinovich, *J. Reine Angew. Math.* **725** (2017),
143–182, [doi:10.1515/crelle-2014-0078](https://doi.org/10.1515/crelle-2014-0078);
see (2.11) and §3.5, Corollary 14 and its remark, in the [author version](https://arxiv.org/abs/1406.5462v1).
The notation for the window and $R(\psi)$ is from Alpöge and Furman,
[arXiv:2608.13637v2](https://arxiv.org/abs/2608.13637v2), (2.6) and (5.13). -/
def montgomeryTaylorWindowConstant : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) /
    (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end ComplexZeroCounts
