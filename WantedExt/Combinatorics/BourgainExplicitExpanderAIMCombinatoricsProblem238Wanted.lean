/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# x² + xy is an explicit two-variable expander over F_p (AIM additive combinatorics, Problem 3.1)

AIM workshop Recent trends in additive combinatorics, Problem 3.1 (J. Bourgain): find explicitly a
function `f : 𝔽_p × 𝔽_p → 𝔽_p` such that for every `A, B ⊆ 𝔽_p` with `|A|, |B| ∼ p^{1/2}` we have
`|f(A × B)| ≥ p^{1/2 + ε}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.BourgainExplicitExpanderAIMCombinatoricsProblem238Wanted

/-!
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.1 (J.
Bourgain). UnsolvedMath record UM-20001113 (`AIM-COMBINATORICS-0238`), dataset ulamai/UnsolvedMath
v1.8.0.

The explicit function is `f(x, y) = x² + xy` (Bourgain). `|A|, |B| ∼ p^{1/2}` is read as `p^{1/2} /
C ≤ |A|, |B| ≤ C p^{1/2}` for an arbitrary constant `C ≥ 1`. The exponent `ε` is one constant for
all `C` (the problem asks for a single `ε`); only the implied constant `c` and the threshold `p₀`
depend on `C`. Stevens and de Zeeuw's Corollary 12 gives `ε = 1/8` for every `C`.
-/

/-- **Bourgain's expander property for x² + xy.** The statement that there is a real
$\varepsilon > 0$ such that for every real $C \ge 1$ there are a real $c > 0$ and a natural number
$p_0$ such that for every prime $p \ge p_0$ and all sets $A, B \subseteq \mathbb{F}_p$ with
$\sqrt{p}/C \le |A| \le C\sqrt{p}$ and $\sqrt{p}/C \le |B| \le C\sqrt{p}$, the set
$\{a^2 + ab : a \in A,\ b \in B\}$ has at least $c\, p^{1/2 + \varepsilon}$ elements.

This says that $f(x, y) = x^2 + xy$ answers Bourgain's question (AIM, Recent trends in additive
combinatorics, Problem 3.1). -/
def bourgainExpanderSquarePlusProduct : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 1 ≤ C → ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
    ∀ A B : Finset (ZMod p),
      Real.sqrt p / C ≤ A.card → (A.card : ℝ) ≤ C * Real.sqrt p →
      Real.sqrt p / C ≤ B.card → (B.card : ℝ) ≤ C * Real.sqrt p →
      c * (p : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ ((A ×ˢ B).image fun x => x.1 ^ 2 + x.1 * x.2).card

/--
**x² + xy is an explicit expander over prime fields.** Bourgain's expander property for
$f(x, y) = x^2 + xy$ holds: there is a real $\varepsilon > 0$ such that for every real $C \ge 1$
there are a real $c > 0$ and a natural number $p_0$ such that for every prime $p \ge p_0$ and all
sets $A, B \subseteq \mathbb{F}_p$ with $\sqrt{p}/C \le |A| \le C\sqrt{p}$ and
$\sqrt{p}/C \le |B| \le C\sqrt{p}$, the set
$f(A, B) = \{a^2 + ab : a \in A,\ b \in B\}$ has at least $c\, p^{1/2 + \varepsilon}$ elements.

Bourgain proved that $|f(A, B)| \gtrsim p^{\eta}$ for some $\eta > \delta$ whenever
$|A| \sim |B| \sim p^{\delta}$ with $0 < \delta < 1$ (as Shen recalls; $\delta = 1/2$ is the AIM
question). Stevens and de Zeeuw (Corollary 12) later gave an explicit exponent:
$|f(A, B)| \gg \min\{|A|^{1/2} |B|^{3/4}, |B|^2\}$ for $A \ne \{0\}$ and $|A|^2 |B| \ll p^2$,
which for $|A|, |B|$ between $p^{1/2}/C$ and $C p^{1/2}$ is $\gg_C p^{5/8}$, so
$\varepsilon = 1/8$ works for every $C$.

Source: AIM workshop Recent trends in additive
combinatorics (2004), problem list collected by E. Croot and V. F. Lev,
https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.1 (J. Bourgain); resolution: J.
Bourgain, More on the sum-product phenomenon in prime fields and its applications, Int. J. Number
Theory 1 (2005), 1-32; explicit exponent: S. Stevens and F. de Zeeuw, An improved point-line
incidence bound over arbitrary fields, Bull. Lond. Math. Soc. 49 (2017), 842-858, arXiv:1609.06284;
C.-Y. Shen, On the sum product estimates and two variables expanders, Publ. Mat. 54 (2010), 149-157,
Shen, Section 1, recalling Bourgain: F(x, y) = x² + xy satisfies |F(A, B)| ≳ p^ε for some ε > δ
whenever |A| ∼ |B| ∼ p^δ, 0 < δ < 1 (δ = 1/2 is the AIM question); Stevens-de Zeeuw, Section 4 and
Corollary 12: for f(x, y) = x² + xy and finite A, B ⊂ F with A ≠ {0} (if char F = p > 0, assuming
|A|²|B| ≪ p²), |f(A, B)| ≫ min{|A|^{1/2}|B|^{3/4}, |B|²}; they recall Bourgain's theorem that |f(A,
B)| ≫ N^{1+δ} when |A| = |B| = N ≈ p^ε, https://doi.org/10.1112/blms.12077.
-/
public theorem_wanted bourgainExpanderSquarePlusProduct_holds : bourgainExpanderSquarePlusProduct

end MathlibExt.Combinatorics.BourgainExplicitExpanderAIMCombinatoricsProblem238Wanted
