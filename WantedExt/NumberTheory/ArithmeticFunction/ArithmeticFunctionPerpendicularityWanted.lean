/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.RearickLogarithm

/-!
# Perpendicularities of arithmetical functions

Statements from Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33.

Arithmetical functions are real-valued (`ArithmeticFunction ℝ`, whose multiplication is the
Dirichlet convolution and whose unit `1` is the paper's `δ`). `U` is the unit group, `U₁` the units
with `f 1 = 1`, `U_M` the multiplicative functions (Mathlib's `IsMultiplicative`) and `U_A` the
antimultiplicative functions (`IsAntimultiplicative`). The paper's real power `f^{(α)} = E(α Lf)`
(Rearick) is pinned by `L(f^{(α)}) = α L(f)`, with `L` the MathlibExt `rearickLog`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Antimultiplicative arithmetical functions.** Let $R$ be a type with a zero and a one. An
arithmetical function $f$ with values in $R$ is antimultiplicative if $f(1) = 1$ and $f(p^k) = 0$
for every prime $p$ and every integer $k \ge 1$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
def IsAntimultiplicative {R : Type*} [Zero R] [One R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ p k : ℕ, p.Prime → 0 < k → f (p ^ k) = 0

/-- **The Dirichlet identity is antimultiplicative.** For every semiring $R$, the identity
$\delta$ of Dirichlet convolution on arithmetical functions with values in $R$, given by
$\delta(1) = 1$ and $\delta(n) = 0$ for $n \ne 1$, is antimultiplicative.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
theorem isAntimultiplicative_one {R : Type*} [Semiring R] :
    IsAntimultiplicative (1 : ArithmeticFunction R) := by
  refine ⟨ArithmeticFunction.one_one, fun p k hp hk => ?_⟩
  exact ArithmeticFunction.one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne'

/-- **Antimultiplicative functions vanish at primes.** Let $R$ be a type with a zero and a one, and
let $f$ be an antimultiplicative arithmetical function with values in $R$. Then $f(p) = 0$ for
every prime $p$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
theorem IsAntimultiplicative.apply_prime {R : Type*} [Zero R] [One R] {f : ArithmeticFunction R}
    (hf : IsAntimultiplicative f) {p : ℕ} (hp : p.Prime) : f p = 0 := by
  simpa using hf.2 p 1 hp one_pos

/-- **Multiplicative and antimultiplicative units form subgroups.** Let $U$ be the group of units
of the ring of real arithmetical functions under Dirichlet convolution. The units $f$ with
$f(1) = 1$, the multiplicative units and the antimultiplicative units form subgroups $U_1$, $U_M$
and $U_A$ of $U$, respectively. Moreover $U_M \le U_1$, $U_A \le U_1$ and
$U_M \cap U_A = \{\delta\}$, where $\delta$ is the Dirichlet identity.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 1 (`integers-2025-A33-prop-1`). -/
public theorem_wanted dirichletUnits_multiplicative_antimultiplicative_subgroups :
    ∃ U₁ UM UA : Subgroup (ArithmeticFunction ℝ)ˣ,
      (∀ u, u ∈ U₁ ↔ (u : ArithmeticFunction ℝ) 1 = 1) ∧
      (∀ u, u ∈ UM ↔ (u : ArithmeticFunction ℝ).IsMultiplicative) ∧
      (∀ u, u ∈ UA ↔ IsAntimultiplicative (u : ArithmeticFunction ℝ)) ∧
      UM ≤ U₁ ∧ UA ≤ U₁ ∧ UM ⊓ UA = ⊥

/-- **Unique splitting into multiplicative and antimultiplicative parts.** Every real
arithmetical function $f$ with $f(1) = 1$ can be written in exactly one way as a Dirichlet
convolution $f = g * h$ of a multiplicative real arithmetical function $g$ and an
antimultiplicative real arithmetical function $h$.

In the source, writing $U_1$, $U_M$ and $U_A$ for the real arithmetical functions $f$ with
$f(1) = 1$, the multiplicative ones and the antimultiplicative ones, this is written
$U_1 = U_M \oplus U_A$.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 2 (`integers-2025-A33-prop-2`). -/
public theorem_wanted existsUnique_multiplicative_mul_antimultiplicative
    (f : ArithmeticFunction ℝ) (hf : f 1 = 1) :
    ∃! gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ,
      gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = f

/-- **Rearick's real power and its vector space laws.** Let $L$ denote the Rearick logarithm and
$*$ the Dirichlet convolution. There is a map $(\alpha, f) \mapsto f^{(\alpha)}$, sending a real
number $\alpha$ and a real arithmetical function $f$ to a real arithmetical function, such that:
for every real $\alpha$ and every real arithmetical function $f$ with $f(1) = 1$, we have
$f^{(\alpha)}(1) = 1$ and $L(f^{(\alpha)}) = \alpha L(f)$; and for all real arithmetical functions
$f$, $g$ with $f(1) = g(1) = 1$ and all real $\alpha$, $\beta$, we have
$(f^{(\alpha)})^{(\beta)} = f^{(\alpha\beta)}$, $f^{(\alpha+\beta)} = f^{(\alpha)} * f^{(\beta)}$,
$(f * g)^{(\alpha)} = f^{(\alpha)} * g^{(\alpha)}$ and $f^{(1)} = f$.

In the source this is the statement that the real arithmetical functions $f$ with $f(1) = 1$ form
a real vector space, with Dirichlet convolution as addition and the real power as scalar
multiplication.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Theorem 1 (`integers-2025-A33-thm-1`). -/
public theorem_wanted dirichletRealPower_vectorSpace :
    ∃ pow : ℝ → ArithmeticFunction ℝ → ArithmeticFunction ℝ,
      (∀ (α : ℝ) (f : ArithmeticFunction ℝ), f 1 = 1 → pow α f 1 = 1 ∧
        ∀ (hp : 0 < pow α f 1) (hf : 0 < f 1),
          rearickLog (pow α f) hp = α • rearickLog f hf) ∧
      ∀ f g : ArithmeticFunction ℝ, f 1 = 1 → g 1 = 1 → ∀ α β : ℝ,
        pow β (pow α f) = pow (α * β) f ∧ pow (α + β) f = pow α f * pow β f ∧
          pow α (f * g) = pow α f * pow α g ∧ pow 1 f = f

/-- **Real powers preserve multiplicativity and antimultiplicativity.** Let $L$ denote the
Rearick logarithm. Let $f$ and $F$ be real arithmetical functions with $f(1) = F(1) = 1$, and let
$\alpha$ be a real number with $L(F) = \alpha L(f)$. If $f$ is multiplicative, then $F$ is
multiplicative, and if $f$ is antimultiplicative, then $F$ is antimultiplicative. Moreover, every
real arithmetical function $f$ with $f(1) = 1$ can be written in exactly one way as a Dirichlet
convolution $f = g * h$ with $g$ multiplicative and $h$ antimultiplicative.

In the source $F$ is Rearick's real power $f^{(\alpha)}$, and the theorem says that the
multiplicative and the antimultiplicative functions with $f(1) = 1$ form subspaces of the real
vector space of all real arithmetical functions $f$ with $f(1) = 1$, whose direct sum is that space.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Theorem 2 (`integers-2025-A33-thm-2`). -/
public theorem_wanted dirichletRealPower_multiplicative_antimultiplicative_subspaces :
    (∀ (f F : ArithmeticFunction ℝ) (α : ℝ), f 1 = 1 → F 1 = 1 →
        (∀ (hF : 0 < F 1) (hf : 0 < f 1), rearickLog F hF = α • rearickLog f hf) →
        (f.IsMultiplicative → F.IsMultiplicative) ∧
          (IsAntimultiplicative f → IsAntimultiplicative F)) ∧
      ∀ f : ArithmeticFunction ℝ, f 1 = 1 →
        ∃! gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ,
          gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = f

end

end MetaMathlibExt
