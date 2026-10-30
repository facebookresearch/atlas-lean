/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsAdicComplete_of_module_finite_free_span_natCast.lean` and
`P2M/Sol/S_IsAdicComplete_of_module_finite_free_span_natCast.lean`
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
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Adic completeness of finite free modules

If `𝓞` is adically complete at `(p)` and `R` is finite free over `𝓞`, then
`R` is adically complete at `(p)`: completeness transfers along linear
equivalences and finite products, and a finite free module is a finite
product of copies of `𝓞` via a chosen basis.
-/

@[expose] public section

universe u v

open AdicCompletion

/-- Adic completeness transfers along a linear equivalence. -/
private theorem isAdicComplete_of_linearEquiv {A : Type*} [CommRing A] {I : Ideal A}
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (AdicCompletion.of I N : N → AdicCompletion I N) =
      AdicCompletion.congr I e ∘ AdicCompletion.of I M ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, AdicCompletion.congr_apply, AdicCompletion.map_of,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

/-- A finite product of adically complete modules is adically complete. -/
private theorem isAdicComplete_pi_of_fintype {A : Type*} [CommRing A] {I : Ideal A}
    {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, IsAdicComplete I (M i)] :
    IsAdicComplete I (∀ i, M i) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [← AdicCompletion.of_bijective_iff]
  have h : (AdicCompletion.piEquivOfFintype I M : _ → _) ∘
      AdicCompletion.of I (∀ i, M i) = Pi.map fun i => AdicCompletion.of I (M i) := by
    funext x j
    simp [AdicCompletion.pi, AdicCompletion.map_of]
  have hb : Function.Bijective ((AdicCompletion.piEquivOfFintype I M : _ → _) ∘
      AdicCompletion.of I (∀ i, M i)) := by
    rw [h]
    exact Function.Bijective.piMap fun i => AdicCompletion.of_bijective I (M i)
  exact (Function.Bijective.of_comp_iff' (AdicCompletion.piEquivOfFintype I M).bijective _).1 hb

/-- If `𝓞` is adically complete at `(p)` and `R` is finite free over `𝓞`,
then `R` is adically complete at `(p)`. -/
theorem IsAdicComplete.of_module_finite_free_span_natCast
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R : Type v) [CommRing R] [Algebra 𝓞 R] [Module.Finite 𝓞 R] [Module.Free 𝓞 R] :
    IsAdicComplete (Ideal.span {(p : R)}) R := by
  classical
  have hmap : (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 R) = Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap, IsAdicComplete.map_algebraMap_iff]
  have : IsAdicComplete (Ideal.span {(p : 𝓞)}) (Module.Free.ChooseBasisIndex 𝓞 R → 𝓞) :=
    isAdicComplete_pi_of_fintype _
  exact isAdicComplete_of_linearEquiv (Module.Free.chooseBasis 𝓞 R).equivFun.symm
