/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multicolored sunflowers in (ℤ/3)ⁿ (Oberwolfach Reports 54/2012)

Oberwolfach workshop Complexity Theory (2012), Conjecture 7 (C. Umans; Alon, Shpilka and Umans):
there is `c > 0` such that every set `S` of triples in `((ℤ/3)ⁿ)³` with `|S| ≥ 3^{n(1-c)}` and `x +
y + z = 0` for all `(x, y, z) ∈ S` contains three triples with `x₁ + y₂ + z₃ = 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.MulticoloredSunflowerTernaryOWR12177Problem010Wanted

/-!
Source: C. Umans, in Complexity Theory, Oberwolfach Reports 9 (2012), no. 54, p. 3292, Conjecture 7,
DOI 10.4171/OWR/2012/54. UnsolvedMath record UM-30002241 (`OWR-12177-010`), dataset
ulamai/UnsolvedMath v1.8.0.

The three triples must not all be equal, and the bound is required only for `n > n₀`, as in Alon,
Shpilka and Umans's statement of the conjecture (On sunflowers and matrix multiplication, CCC 2012,
Conjecture 6), which the source cites; the source's wording has neither, and three copies of one
triple always qualify, while for `n = 0` the single triple `(0, 0, 0)` meets the size bound and has
no multicolored sunflower. `x + y + z = 0` says that `{x, y, z}` is a sunflower in `(ℤ/3)ⁿ` (in each
coordinate the entries are all equal or all distinct).
-/

/-- **Ternary vectors.** For a natural number $n$, the vectors of length $n$ over $\mathbb{Z}/3$,
that is, the functions from $\{0, 1, \dots, n - 1\}$ to $\mathbb{Z}/3$. -/
abbrev TernaryVec (n : ℕ) : Type := Fin n → ZMod 3

/-- **Multicolored sunflower.** Let $n$ be a natural number and let $S$ be a finite set of triples
$(x, y, z)$ of vectors in $(\mathbb{Z}/3)^n$. Then $S$ contains a multicolored sunflower if there
are triples $(x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \in S$, not all three equal, with
$x_1 + y_2 + z_3 = 0$. -/
def HasMulticoloredSunflower {n : ℕ} (S : Finset (TernaryVec n × TernaryVec n × TernaryVec n)) :
    Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ¬ (a = b ∧ b = c) ∧ a.1 + b.2.1 + c.2.2 = 0

/-- **Multicolored sunflower conjecture.** There are a real number $\varepsilon > 0$ and a natural
number $n_0$ such that for every $n > n_0$, every finite set $S$ of triples $(x, y, z)$ of vectors
in $(\mathbb{Z}/3)^n$ with $x + y + z = 0$ for every $(x, y, z) \in S$ and with
$|S| \ge 3^{(1 - \varepsilon) n}$ contains a multicolored sunflower: triples
$(x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \in S$, not all three equal, with
$x_1 + y_2 + z_3 = 0$.

The conjecture is due to Alon, Shpilka and Umans (Oberwolfach Report 54/2012, Conjecture 7). -/
def multicoloredSunflowerConjecture : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
    ∀ S : Finset (TernaryVec n × TernaryVec n × TernaryVec n),
      (∀ t ∈ S, t.1 + t.2.1 + t.2.2 = 0) → (3 : ℝ) ^ ((1 - ε) * n) ≤ S.card →
        HasMulticoloredSunflower S

/-- **The multicolored sunflower conjecture holds.** There are a real number $\varepsilon > 0$ and a
natural number $n_0$ such that for every $n > n_0$, every finite set $S$ of triples $(x, y, z)$ of
vectors in $(\mathbb{Z}/3)^n$ with $x + y + z = 0$ for every $(x, y, z) \in S$ and with
$|S| \ge 3^{(1 - \varepsilon) n}$ contains a multicolored sunflower: triples
$(x_1, y_1, z_1), (x_2, y_2, z_2), (x_3, y_3, z_3) \in S$, not all three equal, with
$x_1 + y_2 + z_3 = 0$.

This was resolved in the affirmative: a set $S$ as above with no multicolored sunflower is a
tricolored sum-free set ($x_a + y_b + z_c = 0$ only for $a = b = c$), and Blasiak, Church, Cohn,
Grochow, Naslund, Sawin and Umans proved (Theorem A′) that such sets in $(\mathbb{Z}/3)^n$ have at
most $3 \cdot 3^{(1 - \delta/\log 3) n}$ elements, $\delta = 0.0566\ldots$; Alon, Shpilka and Umans
had shown that this tricolored version of the cap set bound disproves the strong USP conjecture.

Source: C. Umans, in Complexity Theory, Oberwolfach Reports 9 (2012), no. 54, p.
3292, Conjecture 7, DOI 10.4171/OWR/2012/54; resolution: J. Blasiak, T. Church, H. Cohn, J. A.
Grochow, E. Naslund, W. F. Sawin and C. Umans, On cap sets and the group-theoretic approach to
matrix multiplication, Discrete Anal. 2017:3, arXiv:1605.06702, Theorem A′: for H ≅ (ℤ/q)ⁿ, q a
prime power, every tricolored sum-free set in H (Definition 3.1) has at most 3 |H|^{1 - δ/log q}
elements, δ = 0.0566...; Section 1: Alon, Shpilka and Umans showed that a tricolored version of the
cap set bounds would disprove the strong USP conjecture (the source's Theorem 8), and Theorem A
disproves it via their result; Kleinberg, Sawin and Speyer, arXiv:1607.00047, abstract, restate the
bound as 3 θⁿ, θ ≈ 2.755, https://arxiv.org/abs/1605.06702.
-/
public theorem_wanted multicoloredSunflowerConjecture_holds : multicoloredSunflowerConjecture

end MathlibExt.Combinatorics.MulticoloredSunflowerTernaryOWR12177Problem010Wanted
