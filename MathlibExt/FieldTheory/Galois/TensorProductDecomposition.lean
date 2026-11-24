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

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Canonical finite-Galois self-tensor decomposition

For a finite Galois extension `L/F`, the canonical original tensor map
`x ⊗ y ↦ (σ ↦ x * σ(y))` is an `L`-algebra equivalence.
The generic construction and its proofs retain their existing public names.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace MilnorK

variable (F L : Type u) [Field F] [Field L] [Algebra F L]

/-- Canonical tensor coordinates: `x ⊗ y` has `σ`-coordinate
`x * σ(y)`.  The tensor product uses its left `L`-algebra structure. -/
noncomputable def finiteGaloisTensorToFunctions :
    letI := Algebra.TensorProduct.leftAlgebra
      (R := F) (S := L) (A := L) (B := L)
    L ⊗[F] L →ₐ[L] ((L ≃ₐ[F] L) → L) :=
  Algebra.TensorProduct.lift
    (AlgHom.pi (fun _ : L ≃ₐ[F] L => AlgHom.id L L))
    (AlgHom.pi (fun σ : L ≃ₐ[F] L => σ.toAlgHom))
    (fun _ _ => Commute.all _ _)

@[simp]
theorem finiteGaloisTensorToFunctions_tmul (x y : L) :
    finiteGaloisTensorToFunctions F L (x ⊗ₜ[F] y) =
      fun σ : L ≃ₐ[F] L => x * σ y := by
  funext σ
  rw [finiteGaloisTensorToFunctions, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The `σ`-coordinate of the canonical self-tensor map, regarded as an
`L`-linear functional. -/
private noncomputable def tensorCoordinateLinear
    (σ : L ≃ₐ[F] L) : Module.Dual L (L ⊗[F] L) :=
  (LinearMap.proj σ).comp (finiteGaloisTensorToFunctions F L).toLinearMap

/-- Restrict an `L`-linear tensor functional to `1 ⊗ L`. -/
private noncomputable def tensorDualRestrictRight :
    Module.Dual L (L ⊗[F] L) →ₗ[L] (L →ₗ[F] L) :=
  (LinearMap.applyₗ (1 : L)).comp
    (TensorProduct.AlgebraTensorModule.lcurry F L L L L L)

private theorem tensorDualRestrictRight_coordinate
    (σ : L ≃ₐ[F] L) :
    tensorDualRestrictRight F L (tensorCoordinateLinear F L σ) =
      σ.toAlgHom.toLinearMap := by
  ext y
  simp [tensorDualRestrictRight, tensorCoordinateLinear,
    finiteGaloisTensorToFunctions_tmul]

private theorem tensorCoordinateLinear_linearIndependent :
    LinearIndependent L (tensorCoordinateLinear F L) := by
  apply LinearIndependent.of_comp (tensorDualRestrictRight F L)
  simpa [Function.comp_def, tensorDualRestrictRight_coordinate] using
    ((linearIndependent_algHom_toLinearMap F L L).comp
      (fun σ : L ≃ₐ[F] L => σ.toAlgHom)
      AlgEquiv.coe_toAlgHom_injective)

variable [FiniteDimensional F L] [IsGalois F L]

/-- The canonical finite-Galois tensor-coordinate map is injective. -/
theorem finiteGaloisTensorToFunctions_injective :
    Function.Injective (finiteGaloisTensorToFunctions F L) := by
  have hspan : Submodule.span L
      (Set.range (tensorCoordinateLinear F L)) = ⊤ :=
    (tensorCoordinateLinear_linearIndependent F L).span_eq_top_of_card_eq_finrank
      (by
        rw [Subspace.dual_finrank_eq]
        simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
        exact (Nat.card_eq_fintype_card (α := L ≃ₐ[F] L)).symm.trans
          (IsGalois.card_aut_eq_finrank F L))
  apply (injective_iff_map_eq_zero (finiteGaloisTensorToFunctions F L)).mpr
  intro x hx
  apply (Module.forall_dual_apply_eq_zero_iff L x).mp
  intro φ
  have hmem : φ ∈ Submodule.span L
      (Set.range (tensorCoordinateLinear F L)) := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun f : Module.Dual L (L ⊗[F] L) => fun _ => f x = 0)
    ?_ ?_ ?_ ?_ hmem
  · rintro f ⟨σ, rfl⟩
    change finiteGaloisTensorToFunctions F L x σ = 0
    rw [hx]
    rfl
  · exact LinearMap.zero_apply _
  · intro f g _ _ hf hg
    change f x + g x = 0
    rw [hf, hg, add_zero]
  · intro c f _ hf
    simp [hf]

/-- The canonical finite-Galois tensor-coordinate map is surjective. -/
theorem finiteGaloisTensorToFunctions_surjective :
    Function.Surjective (finiteGaloisTensorToFunctions F L) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (finiteGaloisTensorToFunctions_injective F L)
  simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
    Module.finrank_fintype_fun_eq_card]
  exact (IsGalois.card_aut_eq_finrank F L).symm.trans
    (Nat.card_eq_fintype_card (α := L ≃ₐ[F] L))

/-- The canonical finite-Galois tensor-coordinate map is bijective. -/
theorem finiteGaloisTensorToFunctions_bijective :
    Function.Bijective (finiteGaloisTensorToFunctions F L) :=
  ⟨finiteGaloisTensorToFunctions_injective F L,
    finiteGaloisTensorToFunctions_surjective F L⟩

/-- The finite-Galois self-tensor decomposition as an `L`-algebra
equivalence. -/
noncomputable def finiteGaloisTensorProductEquiv :
    letI := Algebra.TensorProduct.leftAlgebra
      (R := F) (S := L) (A := L) (B := L)
    L ⊗[F] L ≃ₐ[L] ((L ≃ₐ[F] L) → L) :=
  AlgEquiv.ofBijective (finiteGaloisTensorToFunctions F L)
    (finiteGaloisTensorToFunctions_bijective F L)

@[simp]
theorem finiteGaloisTensorProductEquiv_apply (z : L ⊗[F] L) :
    finiteGaloisTensorProductEquiv F L z =
      finiteGaloisTensorToFunctions F L z :=
  rfl

@[simp]
theorem finiteGaloisTensorProductEquiv_tmul
    (x y : L) (σ : L ≃ₐ[F] L) :
    finiteGaloisTensorProductEquiv F L (x ⊗ₜ[F] y) σ =
      x * σ y :=
  congrFun (finiteGaloisTensorToFunctions_tmul F L x y) σ

end MilnorK
