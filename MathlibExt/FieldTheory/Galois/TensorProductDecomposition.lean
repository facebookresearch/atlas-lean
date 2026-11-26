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
# Finite-Galois self-tensor decomposition

Let L/F be a finite Galois field extension. With the left L-algebra structure,
Θ:L⊗_FL→L^(Aut_F L) sends x⊗y to (σ↦x*σ(y)). The map Θ is an L-algebra equivalence. Its
inverse gives the product decomposition indexed by all F-automorphisms of L.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace MilnorK

variable (F L : Type u) [Field F] [Field L] [Algebra F L]

/-- **Automorphism coordinates of a field self-tensor.**

Let L/F be any extension of fields. With the left L-scalar action,
finiteGaloisTensorToFunctions:L⊗_FL→L^(Aut_F L) is the algebra homomorphism x⊗y↦(σ↦xσ(y));
finiteness and Galoisness are needed for its equivalence property.
-/
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

/-- **One automorphism coordinate as a tensor functional.**

For a field extension L/F and σ∈Aut_F L, tensorCoordinateLinear σ:L⊗_FL→L is the L-linear
functional x⊗y↦xσ(y).
-/
private noncomputable def tensorCoordinateLinear
    (σ : L ≃ₐ[F] L) : Module.Dual L (L ⊗[F] L) :=
  (LinearMap.proj σ).comp (finiteGaloisTensorToFunctions F L).toLinearMap

/-- **Restriction of a tensor functional to the right factor.**

For a field extension L/F and an L-linear φ:L⊗_FL→L, tensorDualRestrictRight φ:L→L is F-linear
with value y↦φ(1⊗y).
-/
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

/-- **Injectivity of the finite-Galois coordinate map.**

Let L/F be a finite Galois field extension. With the left L-algebra structure,
Θ:L⊗_FL→L^(Aut_F L) sends x⊗y to (σ↦x*σ(y)). The map finiteGaloisTensorToFunctions F L is
injective.
-/
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

/-- **Surjectivity of the finite-Galois coordinate map.**

Let L/F be a finite Galois field extension. With the left L-algebra structure,
Θ:L⊗_FL→L^(Aut_F L) sends x⊗y to (σ↦x*σ(y)). The map finiteGaloisTensorToFunctions F L is
surjective.
-/
theorem finiteGaloisTensorToFunctions_surjective :
    Function.Surjective (finiteGaloisTensorToFunctions F L) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (finiteGaloisTensorToFunctions_injective F L)
  simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
    Module.finrank_fintype_fun_eq_card]
  exact (IsGalois.card_aut_eq_finrank F L).symm.trans
    (Nat.card_eq_fintype_card (α := L ≃ₐ[F] L))

/-- **Bijectivity of the finite-Galois coordinate map.**

Let L/F be a finite Galois field extension. With the left L-algebra structure,
Θ:L⊗_FL→L^(Aut_F L) sends x⊗y to (σ↦x*σ(y)). The map finiteGaloisTensorToFunctions F L is
bijective.
-/
theorem finiteGaloisTensorToFunctions_bijective :
    Function.Bijective (finiteGaloisTensorToFunctions F L) :=
  ⟨finiteGaloisTensorToFunctions_injective F L,
    finiteGaloisTensorToFunctions_surjective F L⟩

/-- **Algebra equivalence of a finite-Galois self-tensor.**

Let L/F be a finite Galois field extension. With the left L-algebra structure,
Θ:L⊗_FL→L^(Aut_F L) sends x⊗y to (σ↦x*σ(y)). The L-algebra equivalence
finiteGaloisTensorProductEquiv F L is Θ.
-/
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
