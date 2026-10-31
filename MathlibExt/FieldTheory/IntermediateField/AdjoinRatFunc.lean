/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_
transcendental.lean`
and
`P2M/Sol/S_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_
transcendental.lean`
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

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Algebraic.Basic

@[expose] public section

universe u v

namespace IntermediateField

/-- Adjoining a single transcendental element gives the rational function
field, with the generator sent to `X`.

This is the one-generator case of Luroth's theorem and the basic
identification of simple transcendental extensions. It is used whenever a
transcendental element must be treated as an indeterminate: rational
parametrizations, function fields of curves, and transcendence-degree
arguments. -/
theorem exists_algEquiv_adjoin_simple_ratFunc_of_transcendental (K : Type u)
    [Field K] (L : Type v) [Field L] [Algebra K L] (x : L) (hx : Transcendental K x) :
    ∃ e : ↥(IntermediateField.adjoin K ({x} : Set L)) ≃ₐ[K] RatFunc K,
      e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ = RatFunc.X := by
  classical
  have hinj0 : Function.Injective (Polynomial.aeval (R := K) x) :=
    transcendental_iff_injective.mp hx
  have hφ : nonZeroDivisors (Polynomial K) ≤
      Submonoid.comap (Polynomial.aeval x : Polynomial K →ₐ[K] L)
        (nonZeroDivisors L) := by
    intro p hp
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hinj0 (h.trans (map_zero _).symm)))
  let ψ : RatFunc K →ₐ[K] L := RatFunc.liftAlgHom (Polynomial.aeval x) hφ
  have hψ : ∀ p q : Polynomial K,
      ψ (algebraMap _ (RatFunc K) p / algebraMap _ (RatFunc K) q) =
        Polynomial.aeval x p / Polynomial.aeval x q :=
    RatFunc.liftAlgHom_apply_div _ _
  have hmemA : ∀ p : Polynomial K,
      Polynomial.aeval x p ∈ IntermediateField.adjoin K ({x} : Set L) := fun p =>
    IntermediateField.algebra_adjoin_le_adjoin K _
      (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩)
  have hrange : ∀ r : RatFunc K,
      ψ r ∈ IntermediateField.adjoin K ({x} : Set L) := by
    intro r
    rw [← RatFunc.num_div_denom r, hψ]
    exact div_mem (hmemA _) (hmemA _)
  let f : RatFunc K →ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set L)) :=
    ψ.codRestrict (IntermediateField.adjoin K ({x} : Set L)).toSubalgebra hrange
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => (ψ : RatFunc K →+* L).injective
      (congrArg (fun z : ↥(IntermediateField.adjoin K ({x} : Set L)) => (z : L)) h),
      fun y => ?_⟩
    obtain ⟨r, hr, s, hs, hy⟩ := IntermediateField.mem_adjoin_iff_div.mp y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr hs
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hr
    obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).mp hs
    refine ⟨algebraMap _ (RatFunc K) p / algebraMap _ (RatFunc K) q, Subtype.ext ?_⟩
    change ψ _ = (y : L)
    rw [hψ, ← hy]
  refine ⟨(AlgEquiv.ofBijective f hf).symm, ?_⟩
  rw [AlgEquiv.symm_apply_eq, AlgEquiv.ofBijective_apply]
  apply Subtype.ext
  change x = ψ RatFunc.X
  rw [← RatFunc.algebraMap_X,
    ← div_one (algebraMap (Polynomial K) (RatFunc K) Polynomial.X),
    ← map_one (algebraMap (Polynomial K) (RatFunc K)), hψ, map_one, div_one,
    Polynomial.aeval_X]

end IntermediateField
