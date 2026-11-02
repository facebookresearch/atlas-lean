/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Set Filter Topology Metric

namespace MathlibExt.Analysis.Complex.IsolatedSingularityWanted

/--
**Classification of isolated singularities.** Let $c \in \mathbb{C}$, let $r > 0$, and let
$f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the punctured disc
$\{z \in \mathbb{C} : 0 < |z - c| < r\}$. Then at least one of the following holds: there is a
function $g$ holomorphic on the disc $\{z \in \mathbb{C} : |z - c| < r\}$ that agrees with $f$ on
the punctured disc (removable singularity); or $|f(z)| \to \infty$ as $z \to c$ with $z \ne c$
(pole); or for every $r' > 0$ the image under $f$ of the punctured disc
$\{z \in \mathbb{C} : 0 < |z - c| < r'\}$ is dense in $\mathbb{C}$ (essential singularity,
Casorati–Weierstrass).

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "isolated singularities"; L. V. Ahlfors, Complex Analysis, 3rd ed.,
Ch. 4, §3.1 and §3.2 (removable singularities; zeros, poles and the Casorati-Weierstrass
theorem).
-/
theorem_wanted isolatedSingularity_trichotomy
    {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r \ {c})) :
    (∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball c r) ∧
      Set.EqOn f g (Metric.ball c r \ {c})) ∨
    Filter.Tendsto (fun z => ‖f z‖) (𝓝[≠] c) Filter.atTop ∨
    ∀ r' : ℝ, 0 < r' → Dense (f '' (Metric.ball c r' \ {c}))

end MathlibExt.Analysis.Complex.IsolatedSingularityWanted
