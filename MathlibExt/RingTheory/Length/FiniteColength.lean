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

public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotient lengths and submodules of finite colength

An injective endomorphism preserving a submodule of finite colength has
quotient images of equal length on the ambient module and the submodule.
The proof uses the two genuine submodule filtrations through the image of
the smaller module, together with the canonical quotient isomorphisms.
Only the ambient quotient by the submodule must have finite length.

This supplies the local algebra comparison used for principal divisor
orders under finite birational normalization. Ring and module universes
remain independent, and no quotient-degree or divisor identity is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v

namespace Submodule

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Let `R` be a ring and `M` an `R`-module in an independent universe. For
submodules `A ⊆ B ⊆ M`, composition length satisfies
`length_R(M/A) = length_R(B/A) + length_R(M/B)`. The formula uses extended natural
lengths and requires no finite-length hypothesis. -/
theorem length_quotient_eq_add_of_le (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R (M ⧸ A) =
      Module.length R (B ⧸ A.comap B.subtype) + Module.length R (M ⧸ B) := by
  let U : Submodule R (M ⧸ A) := B.map A.mkQ
  have hlen : Module.length R (M ⧸ A) =
      Module.length R U + Module.length R ((M ⧸ A) ⧸ U) := by
    apply Module.length_eq_add_of_exact U.subtype U.mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    rw [LinearMap.exact_iff]
    simp
  let f : B →ₗ[R] M ⧸ A := A.mkQ.comp B.subtype
  have hker : LinearMap.ker f = A.comap B.subtype := by
    simp only [f, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range f = U := by
    simp only [f, U, LinearMap.range_comp, Submodule.range_subtype]
  have hleft : Module.length R (B ⧸ A.comap B.subtype) = Module.length R U := by
    let e₁ := (Submodule.quotEquivOfEq _ _ hker.symm).trans f.quotKerEquivRange
    let e₂ := LinearEquiv.ofEq (LinearMap.range f) U hrange
    exact (e₁.trans e₂).length_eq
  have hright : Module.length R ((M ⧸ A) ⧸ U) = Module.length R (M ⧸ B) :=
    (Submodule.quotientQuotientEquivQuotient A B hAB).length_eq
  rw [hleft, ← hright]
  exact hlen

/-- For a ring `R`, an `R`-module `M`, a submodule `N ⊆ M` and an injective
linear endomorphism `f`, there is a linear equivalence
`M/N ≃ range(f)/f(N)`, where `f(N)` is regarded as a submodule of `range(f)`.
No invariance or finite-colength assumption on `N` is needed for this equivalence. -/
def quotientRangeEquivOfInjective (N : Submodule R M) (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    (M ⧸ N) ≃ₗ[R] f.range ⧸ (N.map f).comap f.range.subtype := by
  let e : M ≃ₗ[R] f.range := LinearEquiv.ofInjective f hf
  refine Submodule.Quotient.equiv N _ e ?_
  ext z
  constructor
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, congrArg Subtype.val hxz⟩
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, Subtype.ext hxz⟩

/-- Let `R` be a ring, `M` an `R`-module and `N ⊆ M` a submodule such that
`M/N` has finite composition length. If a linear endomorphism `f` is injective and
`f(N) ⊆ N`, then `length_R(N/f(N)) = length_R(M/range(f))`, with the transported
image interpreted as a submodule of `N`. The two lengths themselves may be infinite. -/
theorem length_quotient_map_eq_of_finite_colength (N : Submodule R M)
    (hfinite : IsFiniteLength R (M ⧸ N)) (f : M →ₗ[R] M) (hf : Function.Injective f)
    (hN : N.map f ≤ N) :
    Module.length R (N ⧸ (N.map f).comap N.subtype) =
      Module.length R (M ⧸ f.range) := by
  have himage : N.map f ≤ f.range := by
    rintro z ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hleft := length_quotient_eq_add_of_le (N.map f) N hN
  have hright := length_quotient_eq_add_of_le (N.map f) f.range himage
  have htransport := (quotientRangeEquivOfInjective N f hf).length_eq
  have hc : Module.length R (M ⧸ N) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hfinite
  apply ENat.add_left_injective_of_ne_top hc
  calc
    Module.length R (N ⧸ (N.map f).comap N.subtype) + Module.length R (M ⧸ N) =
        Module.length R (M ⧸ N.map f) := hleft.symm
    _ = Module.length R (f.range ⧸ (N.map f).comap f.range.subtype) +
        Module.length R (M ⧸ f.range) := hright
    _ = Module.length R (M ⧸ N) + Module.length R (M ⧸ f.range) := by
      rw [← htransport]
    _ = Module.length R (M ⧸ f.range) + Module.length R (M ⧸ N) := add_comm _ _

end Submodule

namespace Submodule

variable {R : Type u} [CommRing R]

/-- Let R be a commutative ring and A an R-module in an independent universe.
An injective R-linear map i:R→A with finite-composition-length cokernel identifies
R/(a) and A/aA in length whenever multiplication by a on A is injective. The
quotient on A is by the actual range of scalar multiplication. No algebra,
domain, or fraction-field structure on A is required. -/
theorem length_quotient_span_eq_lsmul_of_finite_colength
    {A : Type v} [AddCommGroup A] [Module R A]
    (i : R →ₗ[R] A) (hi : Function.Injective i)
    (hfinite : IsFiniteLength R (A ⧸ i.range))
    (a : R) (hf : Function.Injective (LinearMap.lsmul R A a)) :
    Module.length R (R ⧸ Ideal.span {a}) =
      Module.length R (A ⧸ (LinearMap.lsmul R A a).range) := by
  let N : Submodule R A := i.range
  let f : A →ₗ[R] A := LinearMap.lsmul R A a
  let T : Submodule R N := (N.map f).comap N.subtype
  let e : R ≃ₗ[R] N := LinearEquiv.ofInjective i hi
  have hN : N.map f ≤ N := by
    rintro z ⟨x, ⟨r, rfl⟩, rfl⟩
    refine ⟨a * r, ?_⟩
    simpa only [smul_eq_mul, f, LinearMap.lsmul_apply] using i.map_smul a r
  have hmap : Submodule.map e.toLinearMap (Ideal.span {a}) = T := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hr
      refine ⟨i q, ⟨q, rfl⟩, ?_⟩
      change f (i q) = i (a * q)
      simpa only [smul_eq_mul, f, LinearMap.lsmul_apply] using (i.map_smul a q).symm
    · rintro ⟨x, ⟨r, rfl⟩, hr⟩
      refine ⟨a * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
      apply Subtype.ext
      change i (a * r) = (z : A)
      calc
        i (a * r) = f (i r) := by
          simpa only [smul_eq_mul, f, LinearMap.lsmul_apply] using i.map_smul a r
        _ = (z : A) := hr
  have hleft : Module.length R (R ⧸ Ideal.span {a}) = Module.length R (N ⧸ T) :=
    (Submodule.Quotient.equiv (Ideal.span {a}) T e hmap).length_eq
  exact hleft.trans (Submodule.length_quotient_map_eq_of_finite_colength N hfinite f hf hN)

end Submodule
