/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.CyclotomicTorsionEquiv

@[expose] public section

universe u v

open Polynomial Module

/-- Consumer with the original binders, including independent universes. -/
private theorem exactSource
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M]
    [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N]
    [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n)
    (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1))
    (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) :=
  Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq hn hM hN h

/-- Higher-universe consumer: the two modules may live in `Type 1` and
`Type 2`. -/
example
    {M : Type 1} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M]
    [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type 2} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N]
    [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n)
    (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1))
    (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) :=
  exactSource hn hM hN h

/-- Boundary case `n = 1`: a module killed by `X - 1` is compared with
itself, so the cyclotomic finrank hypothesis holds by reflexivity. -/
example
    {M : Type} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M]
    [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ 1 - 1)) :
    Nonempty (M ≃ₗ[ℚ[X]] M) :=
  exactSource Nat.one_pos hM hM (fun _ _ => rfl)
