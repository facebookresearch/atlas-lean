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

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj

@[expose] public section

namespace WeierstrassCurve

/-- **Modular model of level $N$.** An integral Weierstrass curve is a
modular model of level `N` when some normalized eigenform of weight `2`
on `Γ₀ N` has `q`-coefficients agreeing with its Frobenius traces at good
primes outside `N`. -/
def IsModularModelOfLevel (W : WeierstrassCurve ℤ) (N : ℕ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
    ∀ p : ℕ, ∀ hp : p.Prime, W.IsGoodPrimeFor p → ¬ p ∣ N →
      ModularFormClass.qCoeff f p = (W.apOfModel p (hp := ⟨hp⟩) : ℂ)

/-- **Modular model of exact conductor level.** An integral Weierstrass
curve is a modular model of its exact conductor level when it is a
modular model of some squarefree level `N` whose prime divisors are
exactly the primes dividing the discriminant. -/
def IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Squarefree N ∧
    (∀ q : ℕ, q.Prime → (q ∣ N ↔ (q : ℤ) ∣ W.Δ)) ∧
    W.IsModularModelOfLevel N

/-- **Modular model of conductor level.** An integral Weierstrass curve
is a modular model of conductor level when it is a modular model of some
positive level `N` divisible by every prime dividing the discriminant. -/
def IsModularModelOfConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N

/-- **Exact conductor level gives conductor level.** A modular model of
exact conductor level is a modular model of conductor level: the same
level works, and a prime dividing the discriminant divides the level by
the exactness equivalence. -/
theorem IsModularModelOfExactConductorLevel.isModularModelOfConductorLevel
    {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfExactConductorLevel) :
    W.IsModularModelOfConductorLevel := by
  obtain ⟨N, hN, -, hiff, hmod⟩ := h
  exact ⟨N, hN, hmod, fun ℓ hℓ hdvd => (hiff ℓ hℓ).mpr hdvd⟩

end WeierstrassCurve
