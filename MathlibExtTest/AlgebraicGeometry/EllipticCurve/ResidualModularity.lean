/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity

@[expose] public section

open WeierstrassCurve

open scoped WeierstrassCurve.Affine

/-- Importing the module adds no `DecidableEq` instance on `AlgebraicClosure ℚ`: the classical
instance the point API needs is local to the module, and importers choose their own (below,
with `open Classical in`). -/
example : True := by
  fail_if_success
    have : DecidableEq (AlgebraicClosure ℚ) := inferInstance
  trivial

/-- `apOfModel` at a prime `p` is the Frobenius trace `p + 1 - #W(𝔽_p)` of the reduction, from
the finite-field API `WeierstrassCurve.Affine.frobeniusTrace`. -/
example (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    W.apOfModel p = (p : ℤ) + 1 - Nat.card (W.reductionMod p).toAffine.Point := by
  rw [WeierstrassCurve.apOfModel, Affine.frobeniusTrace_eq, Nat.card_zmod]

open Classical in
/-- `ModRepIsIrreducible` says that the `n`-torsion is nontrivial and that its only
Galois-stable submodules are `⊥` and `⊤`. -/
example (W : WeierstrassCurve ℤ) (n : ℕ) :
    W.ModRepIsIrreducible n ↔
      Nontrivial (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n) ∧
      ∀ N : Submodule (ZMod n) (Submodule.torsionBy ℤ
          ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n),
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, σ • x ∈ N) →
          N = ⊥ ∨ N = ⊤ :=
  Affine.Point.galoisRepIsIrreducible_iff _ _

open Classical in
/-- Consumer with the original binders. -/
example (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (_hΔ : W.Δ ≠ 0) (_hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (_hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hp2M₀ : ¬ p ^ 2 ∣ M₀)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀)
    (hQ : ∀ M q : ℕ, Squarefree M → q.Prime → q ≠ p → q ∣ M → ¬ q ^ 2 ∣ M →
      ResidualGaloisRep.IsUnramifiedAt
        ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker) q →
      W.IsResiduallyModularOfLevel p M → W.IsResiduallyModularOfLevel p (M / q))
    (hSq : ∀ M q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ M → ¬ q ^ 3 ∣ M →
      W.IsResiduallyModularOfLevel p M → W.IsResiduallyModularOfLevel p (M / q))
    (hP : ∀ M : ℕ, W.IsResiduallyModularOfLevel p M →
      ((W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p) → p ∣ M → ¬ p ^ 2 ∣ M →
        W.IsResiduallyModularOfLevel p (M / p)) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → ¬ p ∣ M →
        W.IsResiduallyModularOfLevel p (M * p)))
    (hU : ∀ M q : ℕ, q.Prime → q ≠ p → ¬ q ∣ M →
      W.IsResiduallyModularOfLevel p M →
      ResidualGaloisRep.IsUnramifiedAt
        ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker) q) :
    ∃ N : ℕ, Squarefree N ∧
      (∀ q : ℕ, q.Prime → q ≠ p →
        (q ∣ N ↔ ¬ ResidualGaloisRep.IsUnramifiedAt
          ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker) q)) ∧
      (p ∣ N ↔ (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p)) ∧
      W.IsResiduallyModularOfLevel p N :=
  W.exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_of_not_cube_dvd_of_squarefree_step
    p _hp2 _hΔ _hW hcard₁ hker _hirr M₀ hres₀ hp2M₀ hM₀3 hQ hSq hP hU

/-- Boundary: the squarefree conclusion fails for `4`, showing that the
level-lowering hypotheses that remove squared prime factors are essential
to the form of the conclusion. -/
example : ¬ Squarefree 4 := by
  intro h
  exact (by norm_num : ¬ IsUnit (2 : ℕ)) (h (x := 2) (by norm_num))
