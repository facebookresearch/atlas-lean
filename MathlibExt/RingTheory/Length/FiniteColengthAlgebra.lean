/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.Length.FiniteColength
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Principal quotient lengths under finite-colength algebra inclusions

For an injective inclusion of a commutative ring in a domain, with actual
finite-length scalar cokernel, a nonzero base scalar has the same principal
quotient length before and after the inclusion. The target quotient uses
the genuine principal ideal and length over the original base ring.

The comparison follows from the actual scalar endomorphism on the target
and the two nested quotient filtrations. This is the local normalization
input for rational-function divisor orders; it retains independent ring
universes and does not assume a divisor pushforward identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v

namespace Algebra

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- Let `R`, `S` be commutative rings in independent universes, with `S` an
`R`-algebra domain and injective algebra map. Suppose the `R`-module quotient of `S`
by the image of `R` has finite composition length. For every nonzero `a ∈ R`,
`length_R(R/(a)) = length_R(S/(aS))`. Both sides use length over the original base
ring and the actual principal ideals. -/
theorem length_quotient_span_eq_of_finite_colength [IsDomain S]
    (hi : Function.Injective (algebraMap R S))
    (hfinite : IsFiniteLength R (S ⧸ (Algebra.linearMap R S).range))
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) =
      Module.length R (S ⧸ Ideal.span {algebraMap R S a}) := by
  let i : R →ₗ[R] S := Algebra.linearMap R S
  let N : Submodule R S := i.range
  let f : S →ₗ[R] S := LinearMap.lsmul R S a
  let T : Submodule R N := (N.map f).comap N.subtype
  let e : R ≃ₗ[R] N := LinearEquiv.ofInjective i hi
  have haS : algebraMap R S a ≠ 0 := by
    intro h
    apply ha
    apply hi
    simpa using h
  have hf : Function.Injective f := by
    intro x y h
    apply mul_left_cancel₀ haS
    simpa only [f, LinearMap.lsmul_apply, Algebra.smul_def] using h
  have hN : N.map f ≤ N := by
    rintro z ⟨x, ⟨r, rfl⟩, rfl⟩
    refine ⟨a * r, ?_⟩
    simp only [i, f, Algebra.linearMap_apply, LinearMap.lsmul_apply,
      Algebra.smul_def, map_mul]
  have hmap : Submodule.map e.toLinearMap (Ideal.span {a}) = T := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hr
      refine ⟨i q, ⟨q, rfl⟩, ?_⟩
      change f (i q) = i (a * q)
      simp only [i, f, Algebra.linearMap_apply, LinearMap.lsmul_apply,
        Algebra.smul_def, map_mul]
    · rintro ⟨x, ⟨r, rfl⟩, hr⟩
      refine ⟨a * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
      apply Subtype.ext
      change i (a * r) = (z : S)
      calc
        i (a * r) = f (i r) := by
          simp only [i, f, Algebra.linearMap_apply, LinearMap.lsmul_apply,
            Algebra.smul_def, map_mul]
        _ = (z : S) := hr
  have hleft : Module.length R (R ⧸ Ideal.span {a}) = Module.length R (N ⧸ T) :=
    (Submodule.Quotient.equiv (Ideal.span {a}) T e hmap).length_eq
  have hright : f.range = (Ideal.span {algebraMap R S a}).restrictScalars R := by
    ext z
    change (∃ x, f x = z) ↔ z ∈ Ideal.span {algebraMap R S a}
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simp only [f, LinearMap.lsmul_apply, Algebra.smul_def]
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa only [f, LinearMap.lsmul_apply, Algebra.smul_def] using hx.symm
  have hlength := Submodule.length_quotient_map_eq_of_finite_colength N hfinite f hf hN
  let eQ := Submodule.quotEquivOfEq f.range
    ((Ideal.span {algebraMap R S a}).restrictScalars R) hright
  let eS := Submodule.Quotient.restrictScalarsEquiv R
    (Ideal.span {algebraMap R S a})
  calc
    Module.length R (R ⧸ Ideal.span {a}) = Module.length R (N ⧸ T) := hleft
    _ = Module.length R (S ⧸ f.range) := hlength
    _ = Module.length R (S ⧸ Ideal.span {algebraMap R S a}) := (eQ.trans eS).length_eq

end Algebra
