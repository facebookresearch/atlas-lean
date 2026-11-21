/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The tensor injectivity proof is adapted from
`StacksFrontier/RingTheory/Flat/RegularSequence.lean` in `AxiomMath/Stacks`
at commit c496df0d9beea9deaeabcea8492605f9a0a2313b, declaration
`rTensor_subtype_span_singleton_injective_of_isSMulRegular`.

The repository is distributed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The source file contains
no individual copyright or author notice.

Modification notice: retained the complete tensor injectivity proof,
placed it in an ATLAS namespace, and restricted imports to Mathlib.
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

@[expose] public noncomputable section

/-!
# Tensor injectivity for a principal ideal

If multiplication by `x` is injective on an `R`-module `M`, tensoring
the inclusion `xR ⊆ R` with `M` is injective. This proof uses Mathlib alone.
Its hypothesis is injectivity of multiplication by one scalar on `M`.

The full local criterion is recorded in
`WantedExt/RingTheory/MiracleFlatnessWanted.lean`. Its remaining proof
dependencies include the local criterion of flatness (Stacks 00ML) and
the numerical regular-sequence criterion for a Cohen–Macaulay local ring
(Stacks 02JN).

## References

* The Stacks Project, Tags 00R4, 00ML, and 07DY.
* The exact source file and revision are credited above.
-/

namespace MathlibExt.RingTheory.MiracleFlatness

open scoped TensorProduct

/-- If multiplication by `x` is injective on `M`, then tensoring the
inclusion `xR ⊆ R` with `M` is injective. -/
theorem rTensor_subtype_span_singleton_injective_of_isSMulRegular
    {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {x : R} (hx : IsSMulRegular M x) :
    Function.Injective ((Ideal.span {x} : Ideal R).subtype.rTensor M) := by
  set J : Ideal R := Ideal.span {x}
  set φ : R →ₗ[R] J :=
    LinearMap.toSpanSingleton R J ⟨x, Ideal.mem_span_singleton_self x⟩ with hφ
  have hsurj : Function.Surjective (φ.rTensor M) := by
    refine LinearMap.rTensor_surjective M fun ⟨y, hy⟩ ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact ⟨r, by
      ext
      simp [hφ, LinearMap.toSpanSingleton_apply, smul_eq_mul]⟩
  have key : (J.subtype ∘ₗ φ).rTensor M = x • LinearMap.id := by
    ext m
    simp [hφ, LinearMap.toSpanSingleton_apply,
      TensorProduct.smul_tmul', smul_eq_mul]
  have hreg : IsSMulRegular (R ⊗[R] M) x :=
    (LinearEquiv.isSMulRegular_congr' (TensorProduct.lid R M) x).mpr hx
  refine Function.Injective.of_comp_right ?_ hsurj
  rw [← LinearMap.coe_comp, ← LinearMap.rTensor_comp, key]
  exact fun a b h ↦ hreg (by simpa using h)

end MathlibExt.RingTheory.MiracleFlatness
