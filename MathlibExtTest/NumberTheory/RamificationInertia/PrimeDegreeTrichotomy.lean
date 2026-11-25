/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RamificationInertia.PrimeDegreeTrichotomy

@[expose] public section

open NumberField

-- Consumer with the original binders.
example (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hℓ : (Module.finrank K L).Prime)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p] :
    ((p.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = Module.finrank K L ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = Module.finrank K L) :=
  Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
    K L hℓ p hp P

-- The primality hypothesis matters at the arithmetic step: for the composite
-- degree `4`, the factorisation `2 * (2 * 1) = 4` satisfies `g * (e * f) = ℓ`
-- with none of the three trichotomy patterns for `ℓ = 4`.
example : ¬ ((2 = 4 ∧ (2 : ℕ) = 1 ∧ (1 : ℕ) = 1) ∨
    (2 = 1 ∧ (2 : ℕ) = 4 ∧ (1 : ℕ) = 1) ∨
    (2 = 1 ∧ (2 : ℕ) = 1 ∧ (1 : ℕ) = 4)) := by decide

universe u

-- The statement is universe-polymorphic: the same consumer works for number
-- fields in a higher universe.
example (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hℓ : (Module.finrank K L).Prime)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p] :
    ((p.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = Module.finrank K L ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = Module.finrank K L) :=
  Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
    K L hℓ p hp P
