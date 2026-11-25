/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FLTPrelim_GaloisRep.lean`,
`Definitions/Def_FLTPrelim_Modularity.lean`,
`Definitions/Def_FLTPrelim_ModularRep.lean`,
`Definitions/Def_GaloisRep_Residual.lean`,
`Definitions/Def_EllipticCurve_FrobeniusTrace.lean`,
`Theorems/Thm_WeierstrassCurve_exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_
of_not_cube_dvd_of_squarefree_step.lean`
and
`P2M/Sol/S_WeierstrassCurve_exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_
of_not_cube_dvd_of_squarefree_step.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
The coefficient function `ModularFormClass.qCoeff`, the residual
representation type `ResidualGaloisRep`, the predicates
`ValuationSubring.LiesOverPrime` and `ValuationSubring.inertiaSubgroupIn`,
and `WeierstrassCurve.IsSemistableModel` are reused from existing files in
this repository, where they are definitionally the corresponding source
carriers.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import MathlibExt.AlgebraicGeometry.EllipticCurve.FreyCurve
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
public import MathlibExt.AlgebraicGeometry.EllipticCurve.PointGaloisAction
public import MathlibExt.FieldTheory.Galois.ResidualGaloisRep
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions

-- The point API needs decidable equality on `AlgebraicClosure ℚ`. Take it from classical
-- logic for this file only, so that importers do not inherit a global instance.
attribute [local instance] Classical.decEq

@[expose] public section

noncomputable section

open WeierstrassCurve

open scoped WeierstrassCurve.Affine

namespace CuspForm

/-- A cusp form is a normalized eigenform when its `q`-expansion
coefficients satisfy the usual multiplicativity and Hecke recurrences. -/
public structure IsNormalizedEigenform {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop where
  /-- The first coefficient is `1`. -/
  qCoeff_one : ModularFormClass.qCoeff f 1 = 1
  /-- Coefficients are multiplicative at coprime indices. -/
  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    ModularFormClass.qCoeff f (m * n) =
      ModularFormClass.qCoeff f m * ModularFormClass.qCoeff f n
  /-- The Hecke recurrence at prime powers away from the level. -/
  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    ModularFormClass.qCoeff f (p ^ (r + 2)) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f (p ^ (r + 1)) -
        p * ModularFormClass.qCoeff f (p ^ r)
  /-- The Hecke recurrence at prime powers dividing the level. -/
  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    ModularFormClass.qCoeff f (p ^ (r + 2)) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f (p ^ (r + 1))

end CuspForm

namespace WeierstrassCurve

/-- The reduction of an integral Weierstrass curve modulo `p`. -/
public def reductionMod (W : WeierstrassCurve ℤ) (p : ℕ) :
    WeierstrassCurve (ZMod p) :=
  W.map (Int.castRingHom (ZMod p))

/-- The trace of Frobenius of the reduction of an integral model at a prime `p`: the
Frobenius trace `p + 1 - #W(𝔽_p)` of the reduction over the finite field `ZMod p`. -/
public def apOfModel (W : WeierstrassCurve ℤ) (p : ℕ) [hp : Fact p.Prime] : ℤ :=
  (W.reductionMod p).toAffine.frobeniusTrace

/-- An integral model has good reduction at `p` when `p` does not divide
its discriminant. -/
public def IsGoodPrimeFor (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ W.Δ

/-- An integral Weierstrass curve is residually modular of level `M` at
`p` when a normalized eigenform of level `M` matches its traces of
Frobenius modulo a prime above `p` in the integral closure. -/
public def IsResiduallyModularOfLevel (W : WeierstrassCurve ℤ) (p M : ℕ) :
    Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ (hp := ⟨hℓ⟩) : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

/-- An integral Weierstrass curve is residually modular at `p` when it is
residually modular of some positive level. -/
public def IsResiduallyModular (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel p M

/-- The mod-`n` Galois representation of an integral Weierstrass curve is
irreducible when the representation on its `n`-torsion points is. -/
public def ModRepIsIrreducible (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ
    (W.map (Int.castRingHom ℚ)) n

end WeierstrassCurve

namespace ResidualGaloisRep

variable {k : Type*} [Field k]

/-- A residual representation is unramified at `q` when every inertia
element at every valuation subring lying over `q` acts trivially. -/
public def IsUnramifiedAt (ρ : ResidualGaloisRep k) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

end ResidualGaloisRep

/-- The residual Galois representation of a rational Weierstrass curve at
`p`, built from its `p`-torsion points. -/
public def WeierstrassCurve.residualGaloisRepOf (W : WeierstrassCurve ℚ)
    (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ
      (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ W p)) :
    ResidualGaloisRep (ZMod p) :=
  haveI hfin : Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero
      (hcard ▸ pow_ne_zero 2 (Fact.out (p := p.Prime)).pos.ne')
  { V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p
    finrank_eq := by
      have hp : p.Prime := Fact.out
      have h := Module.natCard_eq_pow_finrank (K := ZMod p)
        (V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p)
      rw [hcard, Nat.card_zmod] at h
      exact (Nat.pow_right_injective hp.two_le h).symm
    ρ := WeierstrassCurve.Affine.Point.galoisRepModuleEnd
      (K := AlgebraicClosure ℚ) ℚ W p
    factorsThroughFiniteLevel := hker }

namespace WeierstrassCurve

public theorem
    exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_of_not_cube_dvd_of_squarefree_step
    (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0)
    (_hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (_hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀) (hp2M₀ : ¬ p ^ 2 ∣ M₀)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀)
    (hQ : ∀ M q : ℕ, Squarefree M → q.Prime → q ≠ p → q ∣ M → ¬ q ^ 2 ∣ M →
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q →
      W.IsResiduallyModularOfLevel p M → W.IsResiduallyModularOfLevel p (M / q))
    (hSq : ∀ M q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ M → ¬ q ^ 3 ∣ M →
      W.IsResiduallyModularOfLevel p M → W.IsResiduallyModularOfLevel p (M / q))
    (hP : ∀ M : ℕ, W.IsResiduallyModularOfLevel p M →
      ((W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p) → p ∣ M → ¬ p ^ 2 ∣ M →
        W.IsResiduallyModularOfLevel p (M / p)) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → ¬ p ∣ M →
        W.IsResiduallyModularOfLevel p (M * p)))
    (hU : ∀ M q : ℕ, q.Prime → q ≠ p → ¬ q ∣ M → W.IsResiduallyModularOfLevel p M →
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q) :
    ∃ N : ℕ, Squarefree N ∧
      (∀ q : ℕ, q.Prime → q ≠ p →
        (q ∣ N ↔ ¬ ResidualGaloisRep.IsUnramifiedAt
          ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker) q)) ∧
      (p ∣ N ↔ (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p)) ∧
      W.IsResiduallyModularOfLevel p N := by
  classical
  have hp : p.Prime := Fact.out
  set ρbar := (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker with hρbar
  suffices H : ∀ M : ℕ, M ≠ 0 → ¬ p ^ 2 ∣ M → (∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M) →
      W.IsResiduallyModularOfLevel p M →
      ∃ N : ℕ, Squarefree N ∧
        (∀ q : ℕ, q.Prime → q ≠ p → (q ∣ N ↔ ¬ ρbar.IsUnramifiedAt q)) ∧
        (p ∣ N ↔ (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p)) ∧
        W.IsResiduallyModularOfLevel p N from
    H M₀ (NeZero.ne M₀) hp2M₀ hM₀3 hres₀
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro hM0 hp2M hM3 hresM
  by_cases hsq : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ^ 2 ∣ M
  · obtain ⟨q, hq, hqp, hq2⟩ := hsq
    have hqM : q ∣ M := (dvd_pow_self q two_ne_zero).trans hq2
    have hlt : M / q < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hq.one_lt
    have hMq0 : M / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hqM) hq.pos).ne'
    exact ih (M / q) hlt hMq0 (fun h => hp2M (h.trans (Nat.div_dvd_of_dvd hqM)))
      (fun r hr hrp h => hM3 r hr hrp (h.trans (Nat.div_dvd_of_dvd hqM)))
      (hSq M q hq hqp hq2 (hM3 q hq hqp) hresM)
  push Not at hsq
  have hMsqf : Squarefree M := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hq2
    rw [← pow_two] at hq2
    by_cases hqp : q = p
    · exact hp2M (hqp ▸ hq2)
    · exact hsq q hq hqp hq2
  by_cases hunr : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ M ∧ ρbar.IsUnramifiedAt q
  · obtain ⟨q, hq, hqp, hqM, hu⟩ := hunr
    have hlt : M / q < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hq.one_lt
    have hMq0 : M / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hqM) hq.pos).ne'
    exact ih (M / q) hlt hMq0 (fun h => hp2M (h.trans (Nat.div_dvd_of_dvd hqM)))
      (fun r hr hrp h => hM3 r hr hrp (h.trans (Nat.div_dvd_of_dvd hqM)))
      (hQ M q hMsqf hq hqp hqM (hsq q hq hqp) hu hresM)
  push Not at hunr
  by_cases hss : (W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p) ∧ p ∣ M
  · obtain ⟨hgs, hpM⟩ := hss
    have hlt : M / p < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hp.one_lt
    have hMp0 : M / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpM) hp.pos).ne'
    exact ih (M / p) hlt hMp0 (fun h => hp2M (h.trans (Nat.div_dvd_of_dvd hpM)))
      (fun r hr hrp h => hM3 r hr hrp (h.trans (Nat.div_dvd_of_dvd hpM)))
      ((hP M hresM).1 hgs hpM hp2M)
  have hqiff : ∀ q : ℕ, q.Prime → q ≠ p → (q ∣ M ↔ ¬ ρbar.IsUnramifiedAt q) := fun q hq hqp =>
    ⟨fun hqM => hunr q hq hqp hqM,
      fun hram => by_contra fun hqM => hram (hU M q hq hqp hqM hresM)⟩
  by_cases hcond : ¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p
  · by_cases hpM : p ∣ M
    · exact ⟨M, hMsqf, hqiff, ⟨fun _ => hcond, fun _ => hpM⟩, hresM⟩
    · refine ⟨M * p, ?_, fun q hq hqp => ?_, ⟨fun _ => hcond, fun _ => dvd_mul_left p M⟩,
        (hP M hresM).2 hcond hpM⟩
      · exact (Nat.squarefree_mul (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM))).2
          ⟨hMsqf, hp.squarefree⟩
      · rw [← hqiff q hq hqp]
        constructor
        · intro h
          exact ((Nat.Prime.dvd_mul hq).1 h).resolve_right fun h' =>
            hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h')
        · exact fun h => h.mul_right p
  · have hgs : W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p := by
      by_contra h
      exact hcond (not_and_or.1 h)
    have hpM : ¬ p ∣ M := fun h => hss ⟨hgs, h⟩
    exact ⟨M, hMsqf, hqiff,
      ⟨fun h => absurd h hpM, fun h => absurd hgs
        (fun hg => h.elim (fun h1 => h1 hg.1) (fun h2 => h2 hg.2))⟩, hresM⟩

end WeierstrassCurve

end
