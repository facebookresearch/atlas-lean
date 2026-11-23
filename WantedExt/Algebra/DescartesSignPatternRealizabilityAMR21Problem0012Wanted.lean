/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Realizability of admissible pairs in Descartes' rule of signs (Shapiro, Conjecture 7)

B. Shapiro, Problems around polynomials: the good, the bad and the ugly..., Conjecture 7 (J.
Forsgård, V. Kostov, B. Shapiro): for every sign pattern `σ`, each pair `(pos, neg)` admissible for
`σ` by Descartes' rule of signs with `pos > 0` and `neg > 0` is realizable by a real polynomial with
sign pattern `σ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Algebra.DescartesSignPatternRealizabilityAMR21Problem0012Wanted

/-!
Source: B. Shapiro, Problems around polynomials: the good, the bad and the ugly..., Arnold Math. J.
1 (2015), arXiv:1503.05295, Conjecture 7 (J. Forsgård, V. Kostov, B. Shapiro). UnsolvedMath record
UM-02200012 (`AMR-021-0012`), dataset ulamai/UnsolvedMath v1.8.0.

A sign pattern `σ₀, …, σ_d` lists the signs of the coefficients of `x⁰, …, x^d` (`true` = `+`); the
number of sign changes does not depend on the reading direction. Admissibility is `pos ≤ c`, `pos ≡
c`, `neg ≤ p`, `neg ≡ p (mod 2)` for `c` sign changes and `p = d - c` sign preservations.
Realizability is Cheriha–Gati–Kostov's notion: some polynomial with sign pattern `σ` has exactly
`pos` positive and `neg` negative roots, all of them simple; their non-realization theorem is stated
for this notion and presented as a counterexample to the conjecture. Shapiro's list and
Forsgård–Kostov–Shapiro count the roots with multiplicity instead.
-/

/-- The number `c` of sign changes of a sign pattern `σ₀, …, σ_d` (`true` = `+`). -/
def signChanges {d : ℕ} (σ : Fin (d + 1) → Bool) : ℕ :=
  (Finset.univ.filter fun k : Fin d => σ k.castSucc ≠ σ k.succ).card

/-- `(pos, neg)` is admissible for `σ`: with `c` sign changes and `p = d - c` sign preservations,
`pos ≤ c`, `pos ≡ c (mod 2)`, `neg ≤ p` and `neg ≡ p (mod 2)`. -/
def IsAdmissible {d : ℕ} (σ : Fin (d + 1) → Bool) (pos neg : ℕ) : Prop :=
  pos ≤ signChanges σ ∧ pos % 2 = signChanges σ % 2 ∧
    neg ≤ d - signChanges σ ∧ neg % 2 = (d - signChanges σ) % 2

open Classical in
/-- `(pos, neg)` is realizable for `σ` (Cheriha–Gati–Kostov): some real polynomial of degree `d`
whose coefficient of `xᵏ` is nonzero with sign `σ k` has exactly `pos` positive and `neg` negative
roots, all of them simple. -/
def IsRealizable {d : ℕ} (σ : Fin (d + 1) → Bool) (pos neg : ℕ) : Prop :=
  ∃ q : Polynomial ℝ, q.natDegree = d ∧
    (∀ k : Fin (d + 1), q.coeff k ≠ 0 ∧ (0 < q.coeff k ↔ σ k = true)) ∧ q.roots.Nodup ∧
    (q.roots.filter fun x => 0 < x).card = pos ∧ (q.roots.filter fun x => x < 0).card = neg

/-- Conjecture 7 of Shapiro's list (Forsgård–Kostov–Shapiro): for every sign pattern `σ`, every
admissible pair `(pos, neg)` with `pos > 0` and `neg > 0` is realizable. -/
def mixedAdmissiblePairsRealizable : Prop :=
  ∀ (d : ℕ) (σ : Fin (d + 1) → Bool) (pos neg : ℕ), 0 < pos → 0 < neg →
    IsAdmissible σ pos neg → IsRealizable σ pos neg

/--
Resolved false: Cheriha, Gati and Kostov proved that no real polynomial with the degree 9 sign
pattern `(+, -, -, -, -, +, +, +, +, -)` (leading coefficient first, Descartes pair `(3, 6)`) has
exactly one positive and six negative roots, all simple, although `(1, 6)` is admissible: a
counterexample with both components positive in the least possible degree (Kostov had one in degree
11). Source: B. Shapiro, Problems around polynomials: the good, the bad and the ugly..., Arnold
Math. J. 1 (2015), arXiv:1503.05295, Conjecture 7 (J. Forsgård, V. Kostov, B. Shapiro); resolution:
H. Cheriha, Y. Gati and V. P. Kostov, A non-realization theorem in the context of Descartes' rule of
signs, Annual of Sofia University, Fac. Math. Inform. 106 (2019), 25-51, arXiv:1911.12255; first
counterexample (degree 11): V. P. Kostov, Math. Bohem. 144 (2019), Theorem 1(1): the degree 9 sign
pattern σ⁰ = (+,-,-,-,-,+,+,+,+,-) is not realizable with the admissible pair (1, 6), realizable
meaning exactly pos simple positive and neg simple negative roots (Introduction); the abstract calls
this a counterexample to the conjecture that all non-realizable cases have pos = 0 or neg = 0,
https://arxiv.org/abs/1911.12255.
-/
public theorem_wanted mixedAdmissiblePairsRealizable_refuted : ¬ mixedAdmissiblePairsRealizable

end MathlibExt.Algebra.DescartesSignPatternRealizabilityAMR21Problem0012Wanted
