/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq.lean`
and
`P2M/Sol/S_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq.lean`
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
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

set_option maxHeartbeats 4000000

universe u v

open Polynomial Module
open scoped DirectSum

noncomputable section

namespace Polynomial

/-- Two finite-dimensional `ℚ[X]`-modules killed by `X ^ n - 1` are
isomorphic as `ℚ[X]`-modules if, for every divisor `d` of `n`, the
`ℚ`-dimensions of their `cyclotomic d ℚ`-torsion submodules agree.

The modules are rational representations of a cyclic group of order `n`:
`X ^ n - 1` splits over `ℚ` as the product of the pairwise coprime
cyclotomic factors `Φ_d` for `d ∣ n`, so each module is the internal
direct sum of its `Φ_d`-torsion parts, and each part is a vector space
over the field `AdjoinRoot Φ_d`. -/
public theorem nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M]
    [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N]
    [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n)
    (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1))
    (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) := by
  classical
  have hprod : ∏ d ∈ n.divisors, cyclotomic d ℚ = (X : ℚ[X]) ^ n - 1 :=
    prod_cyclotomic_eq_X_pow_sub_one hn ℚ
  have hcop : (n.divisors : Set ℕ).Pairwise (Function.onFun IsCoprime fun d => cyclotomic d ℚ) :=
    fun i _ j _ hij => cyclotomic.isCoprime_rat hij
  have hMt : Module.IsTorsionBy ℚ[X] M (∏ d ∈ n.divisors, cyclotomic d ℚ) := by
    rw [hprod]; exact hM
  have hNt : Module.IsTorsionBy ℚ[X] N (∏ d ∈ n.divisors, cyclotomic d ℚ) := by
    rw [hprod]; exact hN
  let eM := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : n.divisors =>
      Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) (Submodule.torsionBy_isInternal hcop hMt)).symm
  let eN := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun d : n.divisors =>
      Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ)) (Submodule.torsionBy_isInternal hcop hNt)).symm
  have hcomp : ∀ (Φ : ℚ[X]), Irreducible Φ →
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] M Φ) =
        Module.finrank ℚ (Submodule.torsionBy ℚ[X] N Φ) →
      Nonempty (Submodule.torsionBy ℚ[X] M Φ ≃ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] N Φ) := by
    intro Φ hΦ hfin
    haveI : Fact (Irreducible Φ) := ⟨hΦ⟩
    letI : Module (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) :=
      inferInstanceAs (Module (ℚ[X] ⧸ Ideal.span {Φ}) (Submodule.torsionBy ℚ[X] M Φ))
    letI : Module (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) :=
      inferInstanceAs (Module (ℚ[X] ⧸ Ideal.span {Φ}) (Submodule.torsionBy ℚ[X] N Φ))
    have hmkM : ∀ (r : ℚ[X]) (x : Submodule.torsionBy ℚ[X] M Φ),
        (AdjoinRoot.mk Φ r) • x = r • x := fun _ _ => rfl
    have hmkN : ∀ (r : ℚ[X]) (x : Submodule.torsionBy ℚ[X] N Φ),
        (AdjoinRoot.mk Φ r) • x = r • x := fun _ _ => rfl
    haveI : IsScalarTower ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) := ⟨fun c k x => by
      obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective k
      rw [AdjoinRoot.smul_mk, hmkM, hmkM, smul_assoc]⟩
    haveI : IsScalarTower ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) := ⟨fun c k x => by
      obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective k
      rw [AdjoinRoot.smul_mk, hmkN, hmkN, smul_assoc]⟩
    haveI : Module.Finite ℚ (AdjoinRoot Φ) := (AdjoinRoot.powerBasis hΦ.ne_zero).finite
    haveI : Module.Finite ℚ (Submodule.torsionBy ℚ[X] M Φ) :=
      Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] M Φ).subtype.restrictScalars ℚ)
        Subtype.val_injective
    haveI : Module.Finite ℚ (Submodule.torsionBy ℚ[X] N Φ) :=
      Module.Finite.of_injective ((Submodule.torsionBy ℚ[X] N Φ).subtype.restrictScalars ℚ)
        Subtype.val_injective
    haveI : Module.Finite (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) :=
      Module.Finite.of_restrictScalars_finite ℚ (AdjoinRoot Φ) _
    haveI : Module.Finite (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) :=
      Module.Finite.of_restrictScalars_finite ℚ (AdjoinRoot Φ) _
    have hKpos : 0 < Module.finrank ℚ (AdjoinRoot Φ) := Module.finrank_pos
    have hdim : Module.finrank (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ) =
        Module.finrank (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ) := by
      have h1 := Module.finrank_mul_finrank ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] M Φ)
      have h2 := Module.finrank_mul_finrank ℚ (AdjoinRoot Φ) (Submodule.torsionBy ℚ[X] N Φ)
      rw [hfin, ← h2] at h1
      exact Nat.eq_of_mul_eq_mul_left hKpos h1
    let eK := LinearEquiv.ofFinrankEq (Submodule.torsionBy ℚ[X] M Φ)
      (Submodule.torsionBy ℚ[X] N Φ) hdim
    let f : Submodule.torsionBy ℚ[X] M Φ →ₗ[ℚ[X]] Submodule.torsionBy ℚ[X] N Φ :=
      { toFun := eK
        map_add' := fun x y => eK.map_add x y
        map_smul' := fun r x => by
          show eK (r • x) = r • eK x
          rw [← hmkM r x, eK.map_smul, hmkN] }
    exact ⟨LinearEquiv.ofBijective f eK.bijective⟩
  let ed := fun d : n.divisors => (hcomp (cyclotomic d ℚ)
    (cyclotomic.irreducible_rat (Nat.pos_of_mem_divisors d.2))
    (h d (Nat.dvd_of_mem_divisors d.2))).some
  exact ⟨eM ≪≫ₗ (DFinsupp.mapRange.linearEquiv ed) ≪≫ₗ eN.symm⟩

end Polynomial

end
