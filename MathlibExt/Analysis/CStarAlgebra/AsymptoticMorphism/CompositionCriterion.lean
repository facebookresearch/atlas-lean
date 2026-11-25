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
# Rate criterion for a composition homotopy class

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), φ:A→B and ψ:B→C asymptotic star
morphisms, and z a homotopy class of asymptotic star morphisms A→C. For every uniform pair
φu,ψu homotopic to φ,ψ, require sequences τ,ν:ℕ→T with τ monotone and τ(n),ν(n)≥n+1. For every
continuous monotone r:T→T tending to infinity and satisfying r(τ(n))≥ν(n) for all n, the
family σ_t(a)=ψu_(r(t))(φu_t(a)) must be an asymptotic star morphism with homotopy class z.
Uniform means a continuous coefficient-to-orbit map into the bounded continuous function
algebra with its supremum norm. This criterion defines IsCompositionClass z φ ψ.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AsymptoticMorphism

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- **Composition-class predicate for reparametrized representatives.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), φ:A→B and ψ:B→C asymptotic star
morphisms, and z a homotopy class of asymptotic star morphisms A→C. For every uniform pair
φu,ψu homotopic to φ,ψ, require sequences τ,ν:ℕ→T with τ monotone and τ(n),ν(n)≥n+1. For every
continuous monotone r:T→T tending to infinity and satisfying r(τ(n))≥ν(n) for all n, the
family σ_t(a)=ψu_(r(t))(φu_t(a)) must be an asymptotic star morphism with homotopy class z.
Homotopy classes are defined using interval-valued asymptotic morphisms with supremum-norm
defect limits. Uniform representatives have continuous maps from the coefficient algebra into
C_b(T,target).
-/
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
