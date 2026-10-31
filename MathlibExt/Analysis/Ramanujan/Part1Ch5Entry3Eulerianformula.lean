/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry8Eulerianformula

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Compatibility alias for Entry 8 (historically misnumbered as Entry 3); the
implementation lives in `Part1Ch5Entry8Eulerianformula.lean`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry3Eulerianformula

open Entry4 Entry8Eulerianformula

noncomputable section

/-- **Eulerian polynomials at 1 and -1 and two series for 1/(e^z + 1), under the old Entry 3
label.** Let $A(n,k)$ be the Eulerian numbers, given by $A(0,0) = 1$, $A(0,k) = 0$ for $k \ge 1$
and $A(n+1,k) = (k+1)A(n,k) + (n+1-k)A(n,k-1)$, where the last term is $0$ when $k = 0$; let
$\Psi_0(p) = 1$ and $\Psi_n(p) = \sum_{k=0}^{n-1} A(n,k)(-p)^k$ for $n \ge 1$, and let $B_m$ be
the Bernoulli numbers, with $B_1 = -\tfrac{1}{2}$. For every integer $n \ge 1$ and every complex
number $z$ with $|z| < \pi$, we have $e^z + 1 \ne 0$, $\Psi_n(-1) = n!$,
$\Psi_n(1) = 2^{n+1}(2^{n+1} - 1)B_{n+1}/(n+1)$, the series
$\sum_{j \ge 0} (1 - 2^{j+1}) B_{j+1} z^j/(j+1)!$ is summable with sum $1/(e^z + 1)$, and the
series $\sum_{m \ge 0} (-1)^m \Psi_m(1) z^m/(2^{m+1} m!)$ is summable with sum $1/(e^z + 1)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5, Entry 8.
-/
theorem ramanujan_part1_ch5_entry3_eulerianformula (n : ℕ) (z : ℂ)
    (hn : 1 ≤ n) (hz : ‖z‖ < Real.pi) :
    Complex.exp z + 1 ≠ 0 ∧
      chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) ∧
      chapter5Psi n (1 : ℂ) =
        (2 : ℂ) ^ (n + 1) * ((2 : ℂ) ^ (n + 1) - 1) *
          (bernoulli (n + 1) : ℂ) / (n + 1 : ℂ) ∧
      HasSum (chapter5Entry8BernoulliTerm z)
        (1 / (Complex.exp z + 1)) ∧
      HasSum (chapter5Entry8PsiTerm z)
        (1 / (Complex.exp z + 1)) :=
  Entry8Eulerianformula.ramanujan_part1_ch5_entry8_eulerianformula n z hn hz

end
end Entry3Eulerianformula
end MathlibExt.Analysis.Ramanujan.Part1Ch5
end
