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
# Tensoring two directed module systems

Let R be a commutative ring, I an upward-directed preorder and G_i,H_i directed systems of
R-modules with transitions f,g. Then colim_i(G_i⊗H_i)≃(colim G)⊗(colim H). A tensor killed in
the two limits is killed by a simultaneous later transition.
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

/-- **Vanishing in two module limits is detected at a later stage.**

Let R be a commutative ring and G,H directed module systems over an upward-directed preorder
I. If x∈G_i⊗H_i maps to zero under the two stage maps to their limits, then some j≥i satisfies
(f_ij⊗g_ij)(x)=0.
-/
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

/-- **Tensor transition for two module systems.**

Let R be a commutative ring and G,H R-module systems with transitions f_ij,g_ij over a
preorder I. The map directedTensorTransition f g i j is f_ij⊗g_ij:G_i⊗H_i→G_j⊗H_j.
-/
noncomputable abbrev directedTensorTransition
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    (i j : ι) (hij : i ≤ j) :
    G i ⊗[R] H i →ₗ[R] G j ⊗[R] H j :=
  diagonalTransition f g i j hij

/-- **Simultaneous tensoring gives a directed system.**

For directed R-module systems G,H over an upward-directed preorder and R commutative, the
stages G_i⊗H_i and transitions f_ij⊗g_ij form a directed system.
-/
instance directedTensorSystem
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    DirectedSystem (fun i => G i ⊗[R] H i)
      (directedTensorTransition f g · · ·) :=
  diagonalDirectedSystem f g

/-- **Forward map from the limit of tensor stages.**

Let G,H be R-module systems over an upward-directed preorder, R commutative, with stage maps
a_i,b_i to the limits. The map diagonalDirectLimitToTensor sends the class of z∈G_i⊗H_i to
(a_i⊗b_i)(z).
-/
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

/-- **Bijectivity of the two-system tensor comparison.**

Let R be a commutative ring and G,H directed R-module systems over an upward-directed
preorder. The canonical map colim_i(G_i⊗H_i)→(colim G)⊗(colim H) is bijective.
-/
theorem diagonalDirectLimitToTensor_bijective
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    Function.Bijective (diagonalDirectLimitToTensor f g) := by
  exact (directLimitDiagonal f g).bijective

/-- **Linear equivalence of diagonal and factor tensor limits.**

Let R be a commutative ring and G,H directed R-module systems over an upward-directed
preorder. The equivalence diagonalDirectLimitEquivTensor:colim_i(G_i⊗H_i)≃ₗ[R](colim G)⊗(colim
H) has the canonical stage-map forward formula.
-/
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
