/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.lean` and
`P2M/Sol/S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebra homomorphisms from an étale algebra

Over an algebraically closed field, an étale algebra has as many algebra
homomorphisms to the base field as its rank.
-/

@[expose] public section

/-- Over an algebraically closed field, the number of algebra homomorphisms
from an étale algebra to the base field equals its rank. -/
theorem Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R := by
  classical
  obtain ⟨ι, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k R).mp ‹_›
  have : Fintype ι := Fintype.ofFinite ι
  have hLk : ∀ i, Nonempty (L i ≃ₐ[k] k) := fun i => by
    have := (hL i).1
    have : Algebra.IsIntegral k (L i) := Algebra.IsIntegral.of_finite k (L i)
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (L i))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm⟩
  let f : R ≃ₐ[k] (ι → k) := e.trans (AlgEquiv.piCongrRight fun i => (hLk i).some)
  have hrk : Module.finrank k R = Fintype.card ι := by
    rw [LinearEquiv.finrank_eq f.toLinearEquiv, Module.finrank_pi]
  have heval : Function.Bijective (fun i : ι => Pi.evalAlgHom k (fun _ => k) i) := by
    refine ⟨fun i j hij => ?_, fun φ => (AlgHom.eq_piEvalAlgHom φ).imp fun _ h => h.symm⟩
    have hthis := DFunLike.congr_fun hij (Pi.single i 1)
    simp only [Pi.evalAlgHom_apply, Pi.single_apply] at hthis
    by_contra hne; simp [ite_eq_right (Ne.symm hne)] at hthis
  have hcard : Nat.card (R →ₐ[k] k) = Fintype.card ι := by
    rw [Nat.card_congr (AlgEquiv.arrowCongr f AlgEquiv.refl),
      ← Nat.card_eq_fintype_card (α := ι),
      Nat.card_eq_of_bijective _ heval]
  rw [hrk, hcard]
