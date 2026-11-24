/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Homotopy
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Uniform

/-!
# A literal sufficiently-fast composition-class criterion

This is only a property of the ACTUAL asymptotic homotopy class. It selects no
composition operation. Each uniform representative pair gets its own knots
and thresholds; no universal rate over all representatives is assumed.

The rates are continuous, increasing and proper, and dominate the thresholds
at the specified knots. The output family has the literal outer-reparametrized
formula. No condition assuming that this formula is already an asymptotic
morphism is passed as an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AsymptoticMorphism

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- Operational representative criterion for the printed reparametrized
composition. Existence/uniqueness is a separate source theorem, not a field. -/
def IsCompositionClass (z : HomotopyClasses A C)
    (φ : AsymptoticMorphism A B) (ψ : AsymptoticMorphism B C) : Prop :=
  ∀ (φu : AsymptoticMorphism A B) (ψu : AsymptoticMorphism B C),
    IsUniform φu → IsUniform ψu → Homotopic φu φ → Homotopic ψu ψ →
      ∃ τ ν : ℕ → AsymptoticTime,
        Monotone τ ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (τ n : ℝ)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (ν n : ℝ)) ∧
        ∀ r : AsymptoticTime → AsymptoticTime,
          Continuous r → Monotone r → Filter.Tendsto r Filter.atTop Filter.atTop →
          (∀ n : ℕ, ν n ≤ r (τ n)) →
          ∃ σ : AsymptoticMorphism A C,
            (∀ (t : AsymptoticTime) (a : A), σ t a = ψu (r t) (φu t a)) ∧
              mkClass σ = z

end AsymptoticMorphism
