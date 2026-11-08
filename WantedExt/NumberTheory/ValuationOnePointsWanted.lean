/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Points of valuation 1 for a polynomial in two variables

Statements from Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for
a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82.

`ν_p(v) = 1` is written `p ∣ v ∧ ¬ p² ∣ v` and `ν_p(v) > 1` is written `p² ∣ v` (so `v = 0` has
valuation `> 1`). A polynomial `f ∈ ℤ[x, y]` is an `MvPolynomial (Fin 2) ℤ` evaluated at `![x, y]`,
with partial derivatives `f_x = pderiv 0 f`, `f_y = pderiv 1 f`; a point of `C_f(𝔽_p)` is a pair
`0 ≤ r, s < p` with `p ∣ f(r, s)`, and its lifts are `(r + kp, s + lp)`, `0 ≤ k, l < p`.

Section 3 onwards: the paper's random variables live on the uniform probability space
`(k, l) ∈ 𝔽_p²`, so an expectation or probability is a count over `range p ×ˢ range p` divided by
`p²`. Limits `p → ∞` run over primes, through the filter `atTop ⊓ 𝓟 {p | p.Prime}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- For a prime `p`, `g ∈ ℤ[x]` and `0 ≤ r < p` that is not a common root of `g` and `g'`
modulo `p`, at most one `k ∈ {0, …, p - 1}` has `ν_p(g(r + kp)) > 1`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 1
(`integers-2026-A82-prop-1`). -/
public theorem_wanted card_lift_padicVal_gt_one_le_one {p : ℕ} (hp : p.Prime) (g : Polynomial ℤ)
    {r : ℕ} (hr : r < p)
    (hroot : ¬ ((p : ℤ) ∣ g.eval (r : ℤ) ∧ (p : ℤ) ∣ (Polynomial.derivative g).eval (r : ℤ))) :
    ((Finset.range p).filter fun k : ℕ => (p : ℤ) ^ 2 ∣ g.eval ((r : ℤ) + k * p)).card ≤ 1

/-- For a non-zero `g ∈ ℤ[x]` of degree `d` with non-zero discriminant, for all sufficiently large primes `p`
at most `d` residues `0 ≤ x < p²` have `ν_p(g(x)) > 1`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Corollary 1
(`integers-2026-A82-cor-1`). -/
public theorem_wanted card_padicVal_gt_one_le_natDegree (g : Polynomial ℤ) (hg : g ≠ 0)
    (hdisc : g.discr ≠ 0) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      ((Finset.range (p ^ 2)).filter fun x : ℕ => (p : ℤ) ^ 2 ∣ g.eval (x : ℤ)).card ≤ g.natDegree

/-- For a prime `p`, `f ∈ ℤ[x, y]` and a point `(r, s)` of `C_f(𝔽_p)` with `f_x(r, s)` or
`f_y(r, s)` non-zero modulo `p`, exactly `p(p - 1)` of the lifts `(r + kp, s + lp)` have
`ν_p(f) = 1`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 2
(`integers-2026-A82-prop-2`). -/
public theorem_wanted card_lift_padicVal_eq_one {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hgrad : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f))) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      p * (p - 1)

/-- For a prime `p`, `f ∈ ℤ[x, y]` and points `(r₁, s₁)`, `(r₂, s₂)` of `C_f(𝔽_p)` whose
gradients `(f_x, f_y)` are linearly independent modulo `p` (the first two columns of the matrix
`A` with rows `(f_x, f_y, f/p)` at the two points), among the common lifts `(k, l) ∈ 𝔽_p²`:
`(p - 1)²` have `ν_p = 1` at both points, `p - 1` have `ν_p > 1` at the first and `ν_p = 1` at the
second, and exactly one has `ν_p > 1` at both.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 3
(`integers-2026-A82-prop-3`). -/
public theorem_wanted card_common_lift_padicVal_of_gradients_independent {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r₁ s₁ r₂ s₂ : ℕ} (hr₁ : r₁ < p) (hs₁ : s₁ < p) (hr₂ : r₂ < p)
    (hs₂ : s₂ < p) (h₁ : (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] f)
    (h₂ : (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] f)
    (hind : ¬ (p : ℤ) ∣
      MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f) -
        MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)) :
    let F₁ : ℕ × ℕ → ℤ := fun kl => MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f
    let F₂ : ℕ × ℕ → ℤ := fun kl => MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f
    let one : ℤ → Prop := fun v => (p : ℤ) ∣ v ∧ ¬ (p : ℤ) ^ 2 ∣ v
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ => one (F₁ kl) ∧ one (F₂ kl)).card =
        (p - 1) ^ 2 ∧
      ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ F₁ kl ∧ one (F₂ kl)).card = p - 1 ∧
      ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ F₁ kl ∧ (p : ℤ) ^ 2 ∣ F₂ kl).card = 1

/-- For a prime `p` and `f ∈ ℤ[x, y]` all of whose points on `C_f(𝔽_p)` are nonsingular (`f_x` or
`f_y` non-zero modulo `p`), the number `s` of residues `0 ≤ x, y < p²` with `ν_p(f(x, y)) = 1` is
`m p (p - 1)`, where `m = |C_f(𝔽_p)|`. The nonsingularity hypothesis is the one under which the
paper derives this from Proposition 2; without it the statement fails (`f = x² - y²`, `p = 3`:
`m = 5`, `s = 24 ≠ 30`).

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 2 (`integers-2026-A82-cor-2`). -/
public theorem_wanted card_padicVal_eq_one_mod_sq_eq {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ)
    (hns : ∀ r < p, ∀ s < p, (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f →
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f))) :
    ((Finset.range (p ^ 2) ×ˢ Finset.range (p ^ 2)).filter fun xy : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f).card =
      ((Finset.range p ×ˢ Finset.range p).filter fun rs : ℕ × ℕ =>
          (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f).card * (p * (p - 1))

/-- For a prime `p`, `f ∈ ℤ[x, y]` and a singular point `(r, s)` of `C_f(𝔽_p)`
(`f_x(r, s) ≡ f_y(r, s) ≡ 0 (mod p)`), the number of lifts `(r + kp, s + lp)`, `0 ≤ k, l < p`,
with `ν_p(f) = 1` is `0` if `f(r, s) ≡ 0 (mod p²)` and `p²` otherwise. Corrected reading: the
record (and the arXiv text) prints the two cases swapped; by the paper's eq. (7) every lift is
congruent to `f(r, s)` modulo `p²`. As printed it fails for `f = x² + y² + 3`, `p = 3`,
`(r, s) = (0, 0)`: `f(0, 0) = 3 ≢ 0 (mod 9)` and all `9` lifts have valuation `1`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 3 (`integers-2026-A82-cor-3`). -/
public theorem_wanted card_lift_padicVal_eq_one_of_singular {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hx : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f))
    (hy : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      if (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ), s] f then 0 else p ^ 2

/-- For a prime `p`, `f ∈ ℤ[x, y]` and two nonsingular points `(r₁, s₁)`, `(r₂, s₂)` of
`C_f(𝔽_p)` whose gradients `(f_x, f_y)` are linearly dependent modulo `p`, let `A` be the matrix
with rows `(f_x, f_y, f/p)` at the two points and `ρ` its rank modulo `p`. Among the common lifts
`(k, l) ∈ 𝔽_p²`, the number with `ν_p = 1` at both points is `p(p - 1)` if `ρ = 1` and `p(p - 2)`
if `ρ = 2`; with `ν_p > 1` at the first and `ν_p = 1` at the second, `0` if `ρ = 1` and `p` if
`ρ = 2`; with `ν_p > 1` at both, `p` if `ρ = 1` and `0` if `ρ = 2`. Here `ρ = 1` means that all
`2 × 2` minors of `A` vanish modulo `p`. Corrected hypothesis: the paper assumes that `f` has no
zero modulo `p²` with `f_x ≡ f_y ≡ 0 (mod p)` and that one column is non-zero; the counts need
both gradients non-zero (the paper's Case 2 uses it). As printed it fails for
`f = -x² + y² - x - 1`, `p = 3`, `(r₁, s₁) = (0, 1)`, `(r₂, s₂) = (1, 0)` (gradient `0` at
`(1, 0)`, `ρ = 2`): the counts are `(6, 3, 0)`, not `(3, 3, 0)`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Proposition 4 (`integers-2026-A82-prop-4`). -/
public theorem_wanted card_common_lift_padicVal_of_gradients_dependent {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r₁ s₁ r₂ s₂ : ℕ} (hr₁ : r₁ < p) (hs₁ : s₁ < p) (hr₂ : r₂ < p)
    (hs₂ : s₂ < p) (h₁ : (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] f)
    (h₂ : (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] f)
    (hns₁ : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f)))
    (hns₂ : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f)))
    (hdep : (p : ℤ) ∣
      MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f) -
        MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)) :
    let a₁ := MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f)
    let b₁ := MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f)
    let c₁ := MvPolynomial.eval ![(r₁ : ℤ), s₁] f / p
    let a₂ := MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)
    let b₂ := MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f)
    let c₂ := MvPolynomial.eval ![(r₂ : ℤ), s₂] f / p
    let rankOne : Prop := (p : ℤ) ∣ a₁ * c₂ - c₁ * a₂ ∧ (p : ℤ) ∣ b₁ * c₂ - c₁ * b₂
    let F₁ : ℕ × ℕ → ℤ := fun kl =>
      MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f
    let F₂ : ℕ × ℕ → ℤ := fun kl =>
      MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f
    let one : ℤ → Prop := fun v => (p : ℤ) ∣ v ∧ ¬ (p : ℤ) ^ 2 ∣ v
    let n₁ := ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      one (F₁ kl) ∧ one (F₂ kl)).card
    let n₂ := ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      (p : ℤ) ^ 2 ∣ F₁ kl ∧ one (F₂ kl)).card
    let n₃ := ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      (p : ℤ) ^ 2 ∣ F₁ kl ∧ (p : ℤ) ^ 2 ∣ F₂ kl).card
    (rankOne → n₁ = p * (p - 1) ∧ n₂ = 0 ∧ n₃ = p) ∧
      (¬ rankOne → n₁ = p * (p - 2) ∧ n₂ = p ∧ n₃ = 0)

/-- The points of `C_f(𝔽_p)`: pairs `0 ≤ r, s < p` with `p ∣ f(r, s)`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`C_f(𝔽_p)` and `m = |C_f(𝔽_p)|`). -/
public noncomputable def valuationCurvePoints (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Finset (ℕ × ℕ) := by
  classical exact
    (Finset.range p ×ˢ Finset.range p).filter fun rs : ℕ × ℕ =>
      (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f

/-- `|C_f(𝔽_p)| ≤ p²`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`C_f(𝔽_p)`). -/
public theorem valuationCurvePoints_card_le (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    (valuationCurvePoints f p).card ≤ p ^ 2 := by
  classical
  unfold valuationCurvePoints
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

/-- The row `(f_x(r, s), f_y(r, s), f(r, s)/p)` modulo `p` of the paper's matrix `B_k(P)`
(eq. (2)) at a point `(r, s)`; for points of `C_f(𝔽_p)` the division is exact.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, eq. (2). -/
public noncomputable def valuationRow (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) (rs : ℕ × ℕ) :
    Fin 3 → ZMod p :=
  ![((MvPolynomial.eval ![(rs.1 : ℤ), rs.2] (MvPolynomial.pderiv 0 f) : ℤ) : ZMod p),
    ((MvPolynomial.eval ![(rs.1 : ℤ), rs.2] (MvPolynomial.pderiv 1 f) : ℤ) : ZMod p),
    ((MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f / p : ℤ) : ZMod p)]

/-- The element-wise distinct (injective) `k`-tuples of points of `C_f(𝔽_p)`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`m_k(f, p)`) and Section 3 (sums over `l₁ ≠ l₂ ≠ ⋯ ≠ l_k`). -/
public noncomputable def valuationDistinctTuples (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ) :
    Finset (Fin k → ℕ × ℕ) := by
  classical exact
    (Fintype.piFinset fun _ : Fin k => valuationCurvePoints f p).filter Function.Injective

/-- `m_k(f, p)`: the number of element-wise distinct `k`-tuples `P` of points of `C_f(𝔽_p)` whose
matrix `B_k(P)` (rows `valuationRow`) has rank `2` with its first two columns linearly
independent (the `k × 2` submatrix has rank `2`); ranks are over `ZMod p`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`m_k(f, p)` after eq. (2)). -/
public noncomputable def valuationRankTwoTupleCount (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ) :
    ℕ := by
  classical exact
    ((valuationDistinctTuples f p k).filter fun P =>
      (Matrix.of fun i j => valuationRow f p (P i) j).rank = 2 ∧
        (Matrix.of fun i (j : Fin 2) => valuationRow f p (P i) j.castSucc).rank = 2).card

/-- `m_1(f, p) = 0`: a single row has rank at most `1`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 ("For `k = 1`, we
observe that `m_k(f, p) = 0` trivially"). -/
public theorem valuationRankTwoTupleCount_one (f : MvPolynomial (Fin 2) ℤ) (p : ℕ)
    [Fact p.Prime] : valuationRankTwoTupleCount f p 1 = 0 := by
  classical
  unfold valuationRankTwoTupleCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro P - ⟨h, -⟩
  have := Matrix.rank_le_height (Matrix.of fun i j => valuationRow f p (P i) j)
  omega

/-- `o_k(f, p)`: the number of element-wise distinct `k`-tuples `P` of points of `C_f(𝔽_p)` whose
matrix `B_k(P)` has rank `1` with at least one of its first two columns non-zero.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of
`o_k(f, p)` before Proposition 6). -/
public noncomputable def valuationRankOneTupleCount (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ) :
    ℕ := by
  classical exact
    ((valuationDistinctTuples f p k).filter fun P =>
      (Matrix.of fun i j => valuationRow f p (P i) j).rank = 1 ∧
        (Matrix.of fun i (j : Fin 2) => valuationRow f p (P i) j.castSucc) ≠ 0).card

/-- For a tuple `P` of points, the number of `(k, l) ∈ 𝔽_p²` at which every translate
`(r_i + kp, s_i + lp)` has `ν_p(f) > 1`; divided by `p²` it is `E[Y_{l₁} ⋯ Y_{l_k}]`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of the
indicator random variables `Y_{x,y}`). -/
public noncomputable def valuationCommonLiftCount (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ)
    (P : Fin k → ℕ × ℕ) : ℕ := by
  classical exact
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ => ∀ i,
      (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![((P i).1 : ℤ) + kl.1 * p, ((P i).2 : ℤ) + kl.2 * p] f).card

/-- At most `p²` common lifts.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of the
indicator random variables `Y_{x,y}`). -/
public theorem valuationCommonLiftCount_le (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ)
    (P : Fin k → ℕ × ℕ) : valuationCommonLiftCount f p k P ≤ p ^ 2 := by
  classical
  unfold valuationCommonLiftCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

/-- The random variable `X(k, l)` of eq. (1): the number of points `(x, y)` of the square
`{kp, …, kp + p - 1} × {lp, …, lp + p - 1}` with `ν_p(f(x, y)) > 1`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, eq. (1). -/
public noncomputable def valuationSquareCount (f : MvPolynomial (Fin 2) ℤ) (p k l : ℕ) : ℕ := by
  classical exact
    ((Finset.range p ×ˢ Finset.range p).filter fun xy : ℕ × ℕ =>
      (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![((k * p + xy.1 : ℕ) : ℤ), ((l * p + xy.2 : ℕ) : ℤ)] f).card

/-- `X(k, l) ≤ p²`.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, eq. (1). -/
public theorem valuationSquareCount_le (f : MvPolynomial (Fin 2) ℤ) (p k l : ℕ) :
    valuationSquareCount f p k l ≤ p ^ 2 := by
  classical
  unfold valuationSquareCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

/-- The paper's Conjecture 1 for `f`: for every `k ≥ 2`, `m_k(f, p)/p² → 1` as `p → ∞` through
the primes.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, Conjecture 1,
eq. (3). -/
public def ValuationConjectureOne (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ k ≥ 2, Filter.Tendsto (fun p : ℕ => (valuationRankTwoTupleCount f p k : ℝ) / (p : ℝ) ^ 2)
    (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1)

/-- For a prime `p`, `f ∈ ℤ[x, y]` with no point of `C_f(𝔽_p)` at which `f_x ≡ f_y ≡ 0 (mod p)`,
and `k ≥ 1`: `∑_{l₁ ≠ ⋯ ≠ l_k} E[Y_{l₁} ⋯ Y_{l_k}] = m_k(f, p)/p² + o_k(f, p)/p` (eq. (15)),
the sum over element-wise distinct `k`-tuples of points and `E[⋯]` the common-lift count over
`p²`. The hypothesis is the paper's standing assumption of Section 3 at this `p` (its proof
uses it to rule out rank `0`).

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 6, eq. (15)
(`integers-2026-A82-prop-6`). -/
public theorem_wanted sum_expectation_distinct_tuples_eq {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ)
    (hns : ∀ r < p, ∀ s < p, (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f →
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)))
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ P ∈ valuationDistinctTuples f p k, (valuationCommonLiftCount f p k P : ℝ) / (p : ℝ) ^ 2 =
      (valuationRankTwoTupleCount f p k : ℝ) / (p : ℝ) ^ 2 +
        (valuationRankOneTupleCount f p k : ℝ) / p

/-- For `f ∈ ℤ[x, y]` such that, for all sufficiently large primes `p`, `f`, `f_x`, `f_y` have no
common zero modulo `p`, with `|C_f(𝔽_p)|/p → 1`, assuming Conjecture 1 for `f`: for every
`k ≥ 1`, `∑_{l₁ ≠ ⋯ ≠ l_k} E[Y_{l₁} ⋯ Y_{l_k}] → 1` as `p → ∞` through the primes. The paper's
proof takes `|C_f(𝔽_p)|/p → 1` from the Hasse–Weil bounds, which need an irreducibility
hypothesis the paper does not state; it is assumed directly here.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Corollary 5
(`integers-2026-A82-cor-5`), under the standing assumption of Section 3. -/
public theorem_wanted tendsto_sum_expectation_distinct_tuples (f : MvPolynomial (Fin 2) ℤ)
    (hsing : ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ x y : ℤ,
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![x, y] f ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 1 f)))
    (hcurve : Filter.Tendsto (fun p : ℕ => ((valuationCurvePoints f p).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1))
    (hconj : ValuationConjectureOne f) {k : ℕ} (hk : 1 ≤ k) :
    Filter.Tendsto (fun p : ℕ =>
        ∑ P ∈ valuationDistinctTuples f p k, (valuationCommonLiftCount f p k P : ℝ) / (p : ℝ) ^ 2)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1)

/-- **Poisson limit for points of valuation `> 1`.** For `f ∈ ℤ[x, y]` such that, for all
sufficiently large primes `p`, `f`, `f_x`, `f_y` have no common zero modulo `p`, with
`|C_f(𝔽_p)|/p → 1` (the Hasse–Weil input of the paper's proof, assumed directly as for
`tendsto_sum_expectation_distinct_tuples`), assuming Conjecture 1 for `f`: the number `X(k, l)`
of points of valuation `> 1` in a uniformly random `p × p` square converges in distribution to a
Poisson variable with parameter `1`, i.e. for every
`j ≥ 0`, `P(X = j) = #{(k, l) ∈ 𝔽_p² : X(k, l) = j}/p² → e^{-1}/j!` as `p → ∞` through the
primes (for `ℕ`-valued variables, pointwise convergence of the mass functions is convergence in
distribution).

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Theorem 1
(`integers-2026-A82-thm-1`). -/
public theorem_wanted tendsto_valuationSquareCount_poisson (f : MvPolynomial (Fin 2) ℤ)
    (hsing : ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ x y : ℤ,
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![x, y] f ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 1 f)))
    (hcurve : Filter.Tendsto (fun p : ℕ => ((valuationCurvePoints f p).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1))
    (hconj : ValuationConjectureOne f) (j : ℕ) :
    Filter.Tendsto (fun p : ℕ =>
        (((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          valuationSquareCount f p kl.1 kl.2 = j).card : ℝ) / (p : ℝ) ^ 2)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (nhds (Real.exp (-1) / (j.factorial : ℝ)))

end

end MetaMathlibExt
