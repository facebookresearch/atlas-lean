/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit.lean`
and
`P2M/Sol/S_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit.lean`
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

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.StandardEtale

@[expose] public section

open Polynomial

namespace AdjoinRootPowSub

variable {R : Type*} [CommRing R]

private noncomputable def kummerPair (n : ℕ) (u : R) (hn0 : n ≠ 0)
    (hn : IsUnit (n : R)) (hu : IsUnit u) : StandardEtalePair R where
  f := X ^ n - C u
  monic_f := monic_X_pow_sub_C u hn0
  g := 1
  cond := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨C (↑hn.unit⁻¹ * ↑hu.unit⁻¹ : R) * X, -C (↑hu.unit⁻¹ : R), 0, ?_⟩
    have h1 : ((m + 1 : ℕ) : R) * (↑hn.unit⁻¹ : R) = 1 := hn.mul_val_inv
    have h2 : u * (↑hu.unit⁻¹ : R) = 1 := hu.mul_val_inv
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero,
      Nat.add_sub_cancel]
    set a : R := ↑hn.unit⁻¹ with ha
    set b : R := ↑hu.unit⁻¹ with hb
    calc C ((m + 1 : ℕ) : R) * X ^ m * (C (a * b) * X)
          + (X ^ (m + 1) - C u) * -C b
        = C (((m + 1 : ℕ) : R) * a) * C b * X ^ (m + 1) - C b * X ^ (m + 1)
          + C (u * b) := by
          simp only [C_mul]; ring
      _ = 1 := by rw [h1, h2, C_1]; ring

private lemma kummerPair_f (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    (hu : IsUnit u) : (kummerPair n u hn0 hn hu).f = X ^ n - C u :=
  rfl

private lemma kummerPair_g (n : ℕ) (u : R) (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    (hu : IsUnit u) : (kummerPair n u hn0 hn hu).g = 1 :=
  rfl

private noncomputable def kummerPresentation (n : ℕ) (u : R) (hn0 : n ≠ 0)
    (hn : IsUnit (n : R)) (hu : IsUnit u) :
    StandardEtalePresentation R (AdjoinRoot (X ^ n - C u : R[X])) where
  __ := kummerPair n u hn0 hn hu
  x := AdjoinRoot.root (X ^ n - C u)
  hasMap := ⟨by rw [kummerPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
    by rw [kummerPair_g, map_one]; exact isUnit_one⟩
  lift_bijective := by
    set P := kummerPair n u hn0 hn hu with hP
    have hX : P.HasMap (AdjoinRoot.root (X ^ n - C u)) :=
      ⟨by rw [kummerPair_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
       by rw [kummerPair_g, map_one]; exact isUnit_one⟩
    let ψ : AdjoinRoot (X ^ n - C u : R[X]) →ₐ[R] P.Ring :=
      AdjoinRoot.liftAlgHom (X ^ n - C u) (Algebra.ofId R P.Ring) P.X
        (by have := P.hasMap_X.1; rwa [kummerPair_f] at this)
    have h1 : (P.lift _ hX).comp ψ = AlgHom.id R _ := by
      apply AdjoinRoot.algHom_ext
      calc (P.lift _ hX) (ψ (AdjoinRoot.root (X ^ n - C u)))
          = (P.lift _ hX) P.X :=
            congrArg _ (AdjoinRoot.liftAlgHom_root _ _ _ _)
        _ = AdjoinRoot.root (X ^ n - C u) := StandardEtalePair.lift_X _ _ _
    have h2 : ψ.comp (P.lift _ hX) = AlgHom.id R _ := by
      apply StandardEtalePair.hom_ext
      calc ψ ((P.lift _ hX) P.X) = ψ (AdjoinRoot.root (X ^ n - C u)) :=
            congrArg ψ (StandardEtalePair.lift_X _ _ _)
        _ = P.X := AdjoinRoot.liftAlgHom_root _ _ _ _
        _ = AlgHom.id R _ P.X := rfl
    exact (AlgEquiv.ofAlgHom (P.lift _ hX) ψ h1 h2).bijective

private theorem isStandardEtale (n : ℕ) (u : R) (hn0 : n ≠ 0)
    (hn : IsUnit (n : R)) (hu : IsUnit u) :
    Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u : R[X])) :=
  ⟨⟨kummerPresentation n u hn0 hn hu⟩⟩

end AdjoinRootPowSub

namespace AdjoinRoot

/-- Adjoining an `n`-th root of a unit `u` gives a finite étale algebra
when `n` is invertible in the base ring. -/
public theorem etale_and_finite_X_pow_sub_C_of_isUnit
    {R : Type*} [CommRing R] (n : ℕ) (u : R) (hn : IsUnit (n : R))
    (hu : IsUnit u) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C u : R[X])) ∧
      Module.Finite R (AdjoinRoot (X ^ n - C u : R[X])) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (AdjoinRoot (X ^ n - C u : R[X])) :=
      (algebraMap R (AdjoinRoot (X ^ n - C u : R[X]))).codomain_trivial
    refine ⟨?_, ?_⟩
    · exact Algebra.Etale.of_equiv
        ((AlgEquiv.ofBijective (Algebra.ofId R (AdjoinRoot (X ^ n - C u : R[X])))
          ⟨fun _ _ _ => Subsingleton.elim _ _,
           fun y => ⟨0, Subsingleton.elim _ _⟩⟩))
    · exact Module.Finite.of_surjective (Algebra.linearMap R _)
        (fun y => ⟨0, Subsingleton.elim _ _⟩)
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    haveI : Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u : R[X])) :=
      AdjoinRootPowSub.isStandardEtale n u hn0 hn hu
    exact ⟨inferInstance, (monic_X_pow_sub_C u hn0).finite_adjoinRoot⟩

end AdjoinRoot
