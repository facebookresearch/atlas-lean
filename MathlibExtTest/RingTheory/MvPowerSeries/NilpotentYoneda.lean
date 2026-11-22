/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.NilpotentYoneda

@[expose] public section

open MvPowerSeries

universe u v

/-- Consumer with the original binders: rings and algebras live in the
same universe `u`, the index type is finite, and the conclusion is phrased
with the explicit nilpotency and membership hypotheses. -/
theorem exactSource
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C)
        (hJ : IsNilpotent J) (x : σ → C) (hx : ∀ s, x s ∈ J),
          t C J x = nilpotentEval J hJ x hx f :=
  MvPowerSeries.existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent
    t ht_nat

/-- Higher-universe consumer: the coefficient ring lives in `Type v`. -/
theorem exactSourceUniverse
    {R : Type v} [CommRing R] {σ : Type} [Finite σ]
    (t : ∀ (C : Type v) [CommRing C] [Algebra R C], Ideal C → (σ → C) → C)
    (ht_nat : ∀ (C C' : Type v) [CommRing C] [Algebra R C] [CommRing C']
      [Algebra R C'] (J : Ideal C) (J' : Ideal C'), IsNilpotent J →
      IsNilpotent J' → ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : σ → C, (∀ s, x s ∈ J) → t C' J' (φ ∘ x) = φ (t C J x)) :
    ∃! f : MvPowerSeries σ R,
      ∀ (C : Type v) [CommRing C] [Algebra R C] (J : Ideal C)
        (hJ : IsNilpotent J) (x : σ → C) (hx : ∀ s, x s ∈ J),
          t C J x = nilpotentEval J hJ x hx f :=
  MvPowerSeries.existsUnique_apply_eq_nilpotentEval_of_natural_of_isNilpotent
    t ht_nat

/-- Boundary example: the constant-coefficient hypothesis in
`nilpotentEval_mem` matters. At the zero point of the zero ideal, the
series `1` evaluates to `1`, which does not lie in the zero ideal. -/
example : nilpotentEval (R := ℚ) (σ := Fin 1) (⊥ : Ideal ℚ) ⟨1, pow_one _⟩
    (fun _ => 0) (fun s => by simp)
    ((1 : MvPolynomial (Fin 1) ℚ) : MvPowerSeries (Fin 1) ℚ) = 1 := by
  rw [nilpotentEval_coe (⊥ : Ideal ℚ) ⟨1, pow_one _⟩ (fun s => by simp)
    (1 : MvPolynomial (Fin 1) ℚ)]
  simp
