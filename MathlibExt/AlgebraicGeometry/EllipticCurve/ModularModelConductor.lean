/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FLTPrelim_Modularity.lean`,
`Definitions/Def_FLTPrelim_ModularRep.lean`,
`Definitions/Def_WeierstrassCurve_Mlc1RowStatement.lean`,
`Definitions/Def_WeierstrassCurve_ModularityLiftingConductor.lean`,
`Theorems/Thm_WeierstrassCurve_IsModularModelOfExactConductorLevel_
isModularModelOfConductorLevel.lean`,
`P2M/Sol/S_WeierstrassCurve_IsModularModelOfExactConductorLevel_
isModularModelOfConductorLevel.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj

@[expose] public section

open UpperHalfPlane

namespace CuspForm

/-- A normalized eigenform of weight `2` on `Γ₀ N`: its first
`q`-coefficient is `1` and its `q`-coefficients satisfy the Hecke
recurrences at primes inside and outside the level. -/
structure IsNormalizedEigenform {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop where
  /-- The first `q`-coefficient is `1`. -/
  qCoeff_one : ModularFormClass.qCoeff f 1 = 1
  /-- Multiplicativity of `q`-coefficients at coprime indices. -/
  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    ModularFormClass.qCoeff f (m * n)
      = ModularFormClass.qCoeff f m * ModularFormClass.qCoeff f n
  /-- The Hecke recurrence at a prime outside the level. -/
  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    ModularFormClass.qCoeff f (p ^ (r + 2))
      = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f (p ^ (r + 1))
        - p * ModularFormClass.qCoeff f (p ^ r)
  /-- The Hecke recurrence at a prime dividing the level. -/
  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    ModularFormClass.qCoeff f (p ^ (r + 2))
      = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f (p ^ (r + 1))

end CuspForm

namespace WeierstrassCurve

/-- Reduction of an integral Weierstrass curve modulo `p`. -/
def reductionMod (W : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  W.map (Int.castRingHom (ZMod p))

/-- The trace of Frobenius of the reduction of an integral Weierstrass
curve modulo a prime `p`: the Frobenius trace `p + 1 - #W(𝔽_p)` of the
reduction over the finite field `ZMod p`, where `#W(𝔽_p)` counts the
nonsingular points of the reduction, including the point at infinity. -/
noncomputable def apOfModel (W : WeierstrassCurve ℤ) (p : ℕ) [hp : Fact p.Prime] : ℤ :=
  (W.reductionMod p).toAffine.frobeniusTrace

theorem apOfModel_def (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    W.apOfModel p = (W.reductionMod p).toAffine.frobeniusTrace := rfl

/-- An integral Weierstrass curve has good reduction at `p` when `p`
does not divide its discriminant. -/
def IsGoodPrimeFor (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ W.Δ

/-- An integral Weierstrass curve is a modular model of level `N` when
some normalized eigenform of weight `2` on `Γ₀ N` has `q`-coefficients
agreeing with its Frobenius traces at good primes outside `N`. -/
def IsModularModelOfLevel (W : WeierstrassCurve ℤ) (N : ℕ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
    ∀ p : ℕ, ∀ hp : p.Prime, W.IsGoodPrimeFor p → ¬ p ∣ N →
      ModularFormClass.qCoeff f p = (W.apOfModel p (hp := ⟨hp⟩) : ℂ)

/-- An integral Weierstrass curve is a modular model of its exact
conductor level when it is a modular model of some squarefree level
`N` whose prime divisors are exactly the primes dividing the
discriminant. -/
def IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Squarefree N ∧
    (∀ q : ℕ, q.Prime → (q ∣ N ↔ (q : ℤ) ∣ W.Δ)) ∧
    W.IsModularModelOfLevel N

/-- An integral Weierstrass curve is a modular model of conductor level
when it is a modular model of some positive level `N` divisible by
every prime dividing the discriminant. -/
def IsModularModelOfConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N

/-- A modular model of exact conductor level is a modular model of
conductor level: the same level works, and a prime dividing the
discriminant divides the level by the exactness equivalence. -/
theorem IsModularModelOfExactConductorLevel.isModularModelOfConductorLevel
    {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfExactConductorLevel) :
    W.IsModularModelOfConductorLevel := by
  obtain ⟨N, hN, -, hiff, hmod⟩ := h
  exact ⟨N, hN, hmod, fun ℓ hℓ hdvd => (hiff ℓ hℓ).mpr hdvd⟩

end WeierstrassCurve
