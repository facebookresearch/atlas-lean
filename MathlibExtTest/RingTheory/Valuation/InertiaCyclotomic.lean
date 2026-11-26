/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.InertiaCyclotomic

@[expose] public section

/-- Source-shaped consumer with the original binders. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
      σ μ = μ ^ (a : ZMod p).val :=
  ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hp hA a

/-- The conclusion at `μ = 1` is the fixed point forced by any such
inertia element. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (1 : AlgebraicClosure ℚ) = 1 := by
  obtain ⟨σ, hσ, h⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hp hA a
  exact ⟨σ, hσ, by rw [h 1 (one_pow p), one_pow]⟩

/-- Source-shaped consumer with the original binders for the prime-power
inertia character. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (k : ℕ) (a : (ZMod (p ^ k))ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ k = 1 →
      σ μ = μ ^ (a : ZMod (p ^ k)).val :=
  ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_prime_pow A hp hA k a

/-- Source-shaped consumer with the original binders for Kummer descent
along the inertia subgroup. -/
example (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (w : AlgebraicClosure ℚ)
    (hw : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ζ = ζ → σ w = w)
    (hx : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (w ^ p ^ N) = w ^ p ^ N) :
    ∃ w' : AlgebraicClosure ℚ, (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧
      w' ^ p ^ N = w ^ p ^ N :=
  ValuationSubring.exists_inertia_fixed_and_pow_eq_pow_of_isPrimitiveRoot
    p hp hp2 N P hP ζ hζ w hw hx

/-- Boundary case `w = 0`: the descended element may be taken to be `0`,
showing the descent conclusion is not vacuous at zero. -/
example (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N)) :
    ∃ w' : AlgebraicClosure ℚ, (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧
      w' ^ p ^ N = (0 : AlgebraicClosure ℚ) ^ p ^ N := by
  refine ValuationSubring.exists_inertia_fixed_and_pow_eq_pow_of_isPrimitiveRoot
    p hp hp2 N P hP ζ hζ 0 (fun σ _ _ => map_zero σ) (fun σ _ => ?_)
  rw [zero_pow (pow_pos hp.pos N).ne', map_zero]

/-- Consumer for the finite-level inertia dictionary: the center of `A` on the integers of a
finite Galois subextension contains `p`. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    ∃ Q : Ideal (NumberField.RingOfIntegers L), Q.IsMaximal ∧
      (p : NumberField.RingOfIntegers L) ∈ Q ∧
      (A.inertiaSubgroupIn ℚ).map (AlgEquiv.restrictNormalHom L) =
        Q.inertia (L ≃ₐ[ℚ] L) := by
  obtain ⟨Q, hQ, hpQ, -, -, hI⟩ :=
    ValuationSubring.exists_isMaximal_inertia_eq_map_restrictNormalHom A L hp hA
  exact ⟨Q, hQ, hpQ, hI⟩
