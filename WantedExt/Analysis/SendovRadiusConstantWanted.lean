/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.SendovRadiusConstantWanted

/-!
# Sendov radius constant
-/

/-- **Admissible radius in Sendov's problem.** A real number $R$ is an admissible radius if
$R > 0$ and, for every integer $n \ge 2$ and every complex polynomial $f$ of degree $n$ whose
zeros all lie in the closed unit disk $|z| \le 1$, every zero $\lambda$ of $f$ has a critical
point within distance $R$, that is, a zero $c$ of the derivative $f'$ with
$|c - \lambda| \le R$. -/
def IsAdmissibleRadius (R : ℝ) : Prop :=
  0 < R ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ f : Polynomial ℂ, f.natDegree = n →
        (∀ z : ℂ, f.eval z = 0 → ‖z‖ ≤ 1) →
          ∀ lambda0 : ℂ, f.eval lambda0 = 0 →
            ∃ c : ℂ, f.derivative.eval c = 0 ∧ ‖c - lambda0‖ ≤ R

/-- **Enlarging an admissible radius.** If $R$ is an admissible radius and $R \le S$, then $S$ is
an admissible radius. -/
theorem IsAdmissibleRadius.mono {R S : ℝ} (hR : IsAdmissibleRadius R) (hRS : R ≤ S) :
    IsAdmissibleRadius S := by
  refine ⟨lt_of_lt_of_le hR.1 hRS, ?_⟩
  intro n hn f hdeg hroots lambda0 hlambda0
  obtain ⟨c, hc, hdist⟩ := hR.2 n hn f hdeg hroots lambda0 hlambda0
  exact ⟨c, hc, hdist.trans hRS⟩

/-- **The Sendov radius.** The Sendov radius is the infimum, as a real number, of the set of
admissible radii in Sendov's problem.

By the convention for infima of real numbers, it would be $0$ if no radius were admissible. -/
noncomputable def sendovRadius : ℝ :=
  sInf {R : ℝ | IsAdmissibleRadius R}

/-- **The admissible radii are bounded below.** The set of admissible radii is bounded below.

Zero is a lower bound, since every admissible radius is positive. -/
theorem bddBelow_admissibleRadii : BddBelow {R : ℝ | IsAdmissibleRadius R} :=
  ⟨0, fun _ hR ↦ le_of_lt hR.1⟩

/-- **Admissible radii bound the Sendov radius.** If $R$ is an admissible radius, then the Sendov
radius is at most $R$. -/
theorem sendovRadius_le_of_isAdmissibleRadius {R : ℝ} (hR : IsAdmissibleRadius R) :
    sendovRadius ≤ R := by
  rw [sendovRadius]
  exact csInf_le bddBelow_admissibleRadii hR

/-- **Sendov's conjecture.** Sendov's conjecture is the proposition that the Sendov radius is at
most $1$. -/
def sendovConjecture : Prop :=
  sendovRadius ≤ 1

/-- **Lower bound one for the Sendov radius.** This is the proposition that the Sendov radius is at
least $1$.

The polynomials $z^n - 1$ with $n \ge 2$ give this lower bound. -/
def lowerBoundOne : Prop :=
  1 ≤ sendovRadius

/-- **Upper bound two for the Sendov radius.** This is the proposition that the Sendov radius is at
most $2$.

The geometric bound from the Gauss–Lucas theorem gives this upper bound. -/
def upperBoundTwo : Prop :=
  sendovRadius ≤ 2

/--
**Sendov's conjecture holds.** Sendov's conjecture is true: the Sendov radius is at most $1$.

Sendov's conjecture was resolved in 2026 by Lech Mazur's computer-assisted proof.

Source: Lech Mazur, A Computer-Assisted Proof of Sendov's Conjecture,
ProofAtlas, August 5, 2026,
https://www.proofatlas.ai/papers/sendov-conjecture/SENDOV_CONJECTURE_PROOF_AUGUST_5_2026.pdf;
teorth/sendov, Sendov's conjecture in Lean, commit 1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d,
https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean.
Moved from `OpenConjectures/Analysis/SendovRadiusConstant`.
-/
public theorem_wanted sendovConjecture_holds : sendovConjecture

end MathlibExt.Analysis.SendovRadiusConstantWanted
