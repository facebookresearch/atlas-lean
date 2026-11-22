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

/-- An arithmetical function `f` is antimultiplicative if `f 1 = 1` and `f (p ^ k) = 0` for every
prime power `p ^ k` with `k > 0`.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
def IsAntimultiplicative {R : Type*} [Zero R] [One R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ p k : ℕ, p.Prime → 0 < k → f (p ^ k) = 0

/-- The Dirichlet identity `δ` is antimultiplicative.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
theorem isAntimultiplicative_one {R : Type*} [Semiring R] :
    IsAntimultiplicative (1 : ArithmeticFunction R) := by
  refine ⟨ArithmeticFunction.one_one, fun p k hp hk => ?_⟩
  exact ArithmeticFunction.one_apply_ne (Nat.one_lt_pow hk.ne' hp.one_lt).ne'

/-- An antimultiplicative function vanishes at every prime.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Section 2. -/
theorem IsAntimultiplicative.apply_prime {R : Type*} [Zero R] [One R] {f : ArithmeticFunction R}
    (hf : IsAntimultiplicative f) {p : ℕ} (hp : p.Prime) : f p = 0 := by
  simpa using hf.2 p 1 hp one_pos

/-- Proposition 1: in the unit group `U` of real arithmetical functions under Dirichlet
convolution, the units with `f 1 = 1`, the multiplicative units and the antimultiplicative units
form subgroups `U₁`, `U_M`, `U_A` with `U_M ≤ U₁`, `U_A ≤ U₁` and `U_M ∩ U_A = {δ}`.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 1 (`integers-2025-A33-prop-1`). -/
public theorem_wanted dirichletUnits_multiplicative_antimultiplicative_subgroups :
    ∃ U₁ UM UA : Subgroup (ArithmeticFunction ℝ)ˣ,
      (∀ u, u ∈ U₁ ↔ (u : ArithmeticFunction ℝ) 1 = 1) ∧
      (∀ u, u ∈ UM ↔ (u : ArithmeticFunction ℝ).IsMultiplicative) ∧
      (∀ u, u ∈ UA ↔ IsAntimultiplicative (u : ArithmeticFunction ℝ)) ∧
      UM ≤ U₁ ∧ UA ≤ U₁ ∧ UM ⊓ UA = ⊥

/-- Proposition 2: `U₁ = U_M ⊕ U_A`, i.e. every real arithmetical function `f` with `f 1 = 1`
is uniquely a Dirichlet convolution `g * h` of a multiplicative `g` and an antimultiplicative `h`.

Source: Pentti Haukkanen and Timo Tossavainen, *Some Perpendicularities of Arithmetical
Functions*, INTEGERS 25 (2025), Article A33, Proposition 2 (`integers-2025-A33-prop-2`). -/
public theorem_wanted existsUnique_multiplicative_mul_antimultiplicative
    (f : ArithmeticFunction ℝ) (hf : f 1 = 1) :
    ∃! gh : ArithmeticFunction ℝ × ArithmeticFunction ℝ,
      gh.1.IsMultiplicative ∧ IsAntimultiplicative gh.2 ∧ gh.1 * gh.2 = f

/-- Theorem 1: `U₁` is a real vector space with Dirichlet convolution as addition and the real
power `(α, f) ↦ f^{(α)}` as scalar multiplication. Stated as: there is a map `pow` that sends
`U₁` to `U₁`, is Rearick's real power (`L(f^{(α)}) = α L(f)`, equation (4)), and satisfies
`(f^{(α)})^{(β)} = f^{(αβ)}`, `f^{(α+β)} = f^{(α)} * f^{(β)}`, `(f * g)^{(α)} = f^{(α)} * g^{(α)}`
and `f^{(1)} = f` on `U₁`.

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

/-- Theorem 2: `U_M` and `U_A` are subspaces of `U₁` and `U₁ = U_M ⊕ U_A`. Stated as: the real
power `F = f^{(α)}` (pinned by `F 1 = 1` and `L(F) = α L(f)`) of a multiplicative function is
multiplicative and of an antimultiplicative function is antimultiplicative, and every `f ∈ U₁`
splits uniquely as `g * h` with `g ∈ U_M`, `h ∈ U_A`.

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
