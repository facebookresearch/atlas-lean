/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conductor-aspect Dirichlet subconvexity exponent
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import MathlibExt.NumberTheory.PowerFree

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletSubconvexity

/-- **Central-value exponents on a set of levels.** Let $S$ be a set of natural numbers and
$\theta$ a real number. Then $\theta$ is a central-value exponent on $S$ if $\theta \ge 0$ and for
every $\varepsilon > 0$ there are a real number $C > 0$ and a natural number $Q$ such that for
every positive $q \in S$ with $q \ge Q$ and every primitive Dirichlet character $\chi$ modulo $q$,
the analytically continued Dirichlet $L$-function satisfies
$|L(1/2, \chi)| \le C q^{\theta + \varepsilon}$.

The constants $C$ and $Q$ may depend on $\varepsilon$, but not on the level or the character. -/
def IsCentralValueExponentOn (levels : Set ℕ) (θ : ℝ) : Prop :=
  0 ≤ θ ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ hq : 0 < q, q ∈ levels →
        letI : NeZero q := ⟨hq.ne'⟩
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ‖χ.LFunction (1 / 2 : ℂ)‖ ≤ C * Real.rpow (q : ℝ) (θ + ε)

/-- **Admissible exponents for Dirichlet central values.** A real number $\theta$ is an admissible
conductor-aspect exponent for primitive Dirichlet characters if it is a central-value exponent on
the set of all natural numbers: $\theta \ge 0$, and for every $\varepsilon > 0$ there are a real
number $C > 0$ and a natural number $Q$ such that for every positive integer $q \ge Q$ and every
primitive Dirichlet character $\chi$ modulo $q$, the analytically continued Dirichlet
$L$-function satisfies $|L(1/2, \chi)| \le C q^{\theta + \varepsilon}$. -/
def IsDirichletSubconvexityExponent (θ : ℝ) : Prop :=
  IsCentralValueExponentOn Set.univ θ

/-- **The conductor-aspect Dirichlet subconvexity exponent.** The infimum, taken in the extended
real numbers, of the set of all real $\theta$ that are admissible conductor-aspect exponents for
primitive Dirichlet characters. If no real number is admissible, this infimum is $+\infty$. -/
noncomputable def dirichletSubconvexityExponent : EReal :=
  sInf ((fun θ : ℝ => (θ : EReal)) '' {θ | IsDirichletSubconvexityExponent θ})

/-- **The Dirichlet subconvexity exponent is nonnegative.** The conductor-aspect Dirichlet
subconvexity exponent, an extended real number, is at least $0$. This holds by construction:
every admissible exponent is nonnegative, and if no real exponent is admissible, the exponent is
the infimum of the empty set, which is $+\infty$. -/
theorem dirichletSubconvexityExponent_nonneg :
    (0 : EReal) ≤ dirichletSubconvexityExponent := by
  apply le_sInf
  rintro _ ⟨θ, hθ, rfl⟩
  exact EReal.coe_nonneg.mpr hθ.1

/-- **Admissible exponents bound the Dirichlet subconvexity exponent.** If a real number $\theta$
is an admissible conductor-aspect exponent for primitive Dirichlet characters, then the
conductor-aspect Dirichlet subconvexity exponent is at most $\theta$, as extended real numbers. -/
theorem dirichletSubconvexityExponent_le_of_admissible {θ : ℝ}
    (hθ : IsDirichletSubconvexityExponent θ) :
    dirichletSubconvexityExponent ≤ (θ : EReal) := by
  exact sInf_le ⟨θ, hθ, rfl⟩

end MathlibExt.NumberTheory.DirichletSubconvexity
