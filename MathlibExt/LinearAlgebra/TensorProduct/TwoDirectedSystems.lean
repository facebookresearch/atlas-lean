/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.TensorProduct.DirectedSystem

/-!
# Tensor products of directed module systems

A tensor that vanishes after both factors are mapped to their direct
limits vanishes after a common later transition.
The compatibility constructors abbreviate the `Diagonal` API.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Module Module.DirectLimit

namespace TensorProduct

variable {R ι : Type*} [CommRing R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]
section Vanishing
variable {G H : ι → Type*}
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
variable [DirectedSystem G (f · · ·)] [DirectedSystem H (g · · ·)]

/-- Vanishing after mapping two stagewise factors to their direct limits is
detected after one common enlargement. -/
theorem exists_eq_zero_of_map_to_two_directLimits_tensor_eq_zero
    {i : ι} (x : G i ⊗[R] H i)
    (hx : TensorProduct.map
      (Module.DirectLimit.of R ι G f i)
      (Module.DirectLimit.of R ι H g i) x = 0) :
    ∃ j : ι, ∃ hij : i ≤ j,
      TensorProduct.map (f i j hij) (g i j hij) x = 0 := by
  exact exists_eq_zero_of_map_to_directLimit_diagonal_eq_zero f g x hx

end Vanishing

variable {G : ι → Type*}
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- The diagonal tensor-product transition attached to two directed module
systems. -/
noncomputable abbrev directedTensorTransition
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    (i j : ι) (hij : i ≤ j) :
    G i ⊗[R] H i →ₗ[R] G j ⊗[R] H j :=
  diagonalTransition f g i j hij

/-- Tensoring two directed systems stagewise again gives a directed
system. -/
instance directedTensorSystem
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    DirectedSystem (fun i => G i ⊗[R] H i)
      (directedTensorTransition f g · · ·) :=
  diagonalDirectedSystem f g

/-- The canonical map from the direct limit of the stagewise tensor
products to the tensor product of the two direct limits. -/
noncomputable abbrev diagonalDirectLimitToTensor
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    : Module.DirectLimit (fun i => G i ⊗[R] H i)
        (directedTensorTransition f g) →ₗ[R]
      Module.DirectLimit G f ⊗[R] Module.DirectLimit H g :=
  diagonalToTensor f g

omit [IsDirectedOrder ι] [DirectedSystem G (f · · ·)] in
theorem diagonalDirectLimitToTensor_of
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    (i : ι) (x : G i ⊗[R] H i) :
    diagonalDirectLimitToTensor f g
        (Module.DirectLimit.of R ι _ (directedTensorTransition f g) i x) =
      TensorProduct.map
        (Module.DirectLimit.of R ι G f i)
        (Module.DirectLimit.of R ι H g i) x := by
  exact diagonalToTensor_of f g i x

/-- The canonical diagonal direct-limit map is bijective.  Thus filtered
direct limits commute with a stagewise binary tensor product even when both
factors vary over the same directed index. -/
theorem diagonalDirectLimitToTensor_bijective
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    Function.Bijective (diagonalDirectLimitToTensor f g) := by
  exact (directLimitDiagonal f g).bijective

/-- The direct limit of the stagewise tensor products is canonically
linearly equivalent to the tensor product of the two direct limits. -/
noncomputable abbrev diagonalDirectLimitEquivTensor
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    Module.DirectLimit (fun i => G i ⊗[R] H i)
        (directedTensorTransition f g) ≃ₗ[R]
      Module.DirectLimit G f ⊗[R] Module.DirectLimit H g :=
  directLimitDiagonal f g

theorem diagonalDirectLimitEquivTensor_apply_of
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)]
    (i : ι) (x : G i ⊗[R] H i) :
    diagonalDirectLimitEquivTensor f g
        (Module.DirectLimit.of R ι _ (directedTensorTransition f g) i x) =
      TensorProduct.map
        (Module.DirectLimit.of R ι G f i)
        (Module.DirectLimit.of R ι H g i) x :=
  directLimitDiagonal_of f g i x


end TensorProduct
