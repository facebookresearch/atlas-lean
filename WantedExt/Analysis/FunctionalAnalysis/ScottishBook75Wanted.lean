/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook75Wanted

/-- **Scottish Book Problem 75 (Mazur), general Banach-space form.** The claim that for every real
Banach space $E$, every set $R \subseteq E$, every continuous bilinear form $B$ on $E$ and every
real $\alpha \ne 0$ the following holds: if for some $\varepsilon > 0$ the values $|B(x, x)|$ are
bounded on the open $\varepsilon$-neighbourhood of $R$, that is, for the $x \in E$ with
$\operatorname{dist}(x, r) < \varepsilon$ for some $r \in R$, then for some $\delta > 0$ the values
$|B(x, x)|$ are bounded on the open $\delta$-neighbourhood of the scaled set
$\alpha R = \{\alpha r : r \in R\}$. -/
def ScottishBookProblem75Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : Set E) (B : E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ), α ≠ 0 →
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x r < ε) → |B x x| ≤ C) →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x (α • r) < δ) → |B x x| ≤ C

/--
**Mazur's Scottish Book Problem 75 fails in general Banach spaces.** The Scottish Book Problem 75
claim is false: there are a real Banach space $E$, a set $R \subseteq E$, a continuous bilinear
form $B$ on $E$ and a real $\alpha \ne 0$ such that $|B(x, x)|$ is bounded on some open
$\varepsilon$-neighbourhood of $R$ with $\varepsilon > 0$, but is unbounded on every open
$\delta$-neighbourhood of $\alpha R = \{\alpha r : r \in R\}$ with $\delta > 0$.

Source: S. Mazur, Problem 75 of the Scottish Book; refuted by
V. Pestov, whose counterexample to Problem 55 is a continuous
scalar-valued 2-polynomial `W` on `ℓ²`, bounded on an
`ε`-neighbourhood of an unbounded set `R`, but unbounded on
`(1 / 2) R`, hence unbounded on every neighbourhood of `(1 / 2) R`
("Two 1935 questions of Mazur about polynomials in Banach spaces:
a counter-example", 1997, arXiv:funct-an/9705002). Plichko and
Zagorodnyuk gave an independent negative solution ("On automatic
continuity and three problems of 'The Scottish Book' concerning the
boundedness of polynomial functionals", J. Math. Anal. Appl. 220
(1998), 477–494). In the Euclidean case the statement is true, per
typescript Ad 75.
-/
theorem_wanted mazur75_refuted : ¬ ScottishBookProblem75Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook75Wanted
