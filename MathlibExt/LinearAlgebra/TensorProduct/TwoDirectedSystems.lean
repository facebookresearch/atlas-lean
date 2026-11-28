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
# Stagewise tensor products of two systems on one directed preorder

Let R be commutative and ι a preorder with decidable equality. For module families G,H and
linear transition maps f,g, the simultaneous tensor transition is f_{ij}⊗g_{ij}. The
direct-limit relations give a canonical map colim_i(G_i⊗_RH_i)→(colim_iG_i)⊗_R(colim_iH_i),
characterized by sending a stage tensor through the two factor injections.

If ι is directed and both families satisfy the directed-system identity and composition laws,
this map is a linear equivalence. A stage tensor that vanishes after the two injections vanishes
after one common transition i≤j. The common index is retained throughout; no injectivity or
flatness of transition maps is assumed.
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

/-- Let R be commutative and ι a directed preorder with decidable equality. Let (G,f),(H,g) be
directed systems of R-modules on ι. If x∈G_i⊗_RH_i maps to zero in (colim G)⊗_R(colim H), then
there are j≥i such that (f_{ij}⊗g_{ij})(x)=0. Both factors are enlarged to the same later index. -/
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

/-- Let R be commutative, ι a preorder, G,H module families and f_{ij}:G_i→G_j, g_{ij}:H_i→H_j
linear maps for i≤j. This transition G_i⊗_RH_i→G_j⊗_RH_j is f_{ij}⊗g_{ij}, taking x⊗y to
f_{ij}(x)⊗g_{ij}(y). -/
noncomputable abbrev directedTensorTransition
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    (i j : ι) (hij : i ≤ j) :
    G i ⊗[R] H i →ₗ[R] G j ⊗[R] H j :=
  diagonalTransition f g i j hij

/-- For R-module directed systems (G,f),(H,g) over one preorder ι, the family i↦G_i⊗_RH_i with
transitions f_{ij}⊗g_{ij} is a directed system. The identity and composition laws follow by
tensoring the two factor laws. -/
instance directedTensorSystem
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    DirectedSystem (fun i => G i ⊗[R] H i)
      (directedTensorTransition f g · · ·) :=
  diagonalDirectedSystem f g

/-- Let R be commutative and ι a preorder with decidable equality. For R-module families G,H with
linear transition data f,g, this canonical map from the limit module presented by simultaneous
tensor transitions to (colim G)⊗_R(colim H) sends the class of x∈G_i⊗H_i to (ι_i^G⊗ι_i^H)(x).
Its construction uses the direct-limit relations. -/
noncomputable abbrev diagonalDirectLimitToTensor
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    : Module.DirectLimit (fun i => G i ⊗[R] H i)
        (directedTensorTransition f g) →ₗ[R]
      Module.DirectLimit G f ⊗[R] Module.DirectLimit H g :=
  diagonalToTensor f g

omit [IsDirectedOrder ι] [DirectedSystem G (f · · ·)] in
/-- For R-module families G,H over a preorder with decidable equality, transition data f,g, index i
and x∈G_i⊗_RH_i, the forward comparison satisfies e(ι_i^{G⊗H}(x))=(ι_i^G⊗ι_i^H)(x). This stage
formula requires neither directedness of the order nor the directed-system laws. -/
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

/-- Let R be commutative, ι a directed preorder with decidable equality and (G,f),(H,g) directed
R-module systems on ι. The canonical map colim_i(G_i⊗_RH_i)→(colim_iG_i)⊗_R(colim_iH_i) is
bijective. The same directed index controls both factor transitions. -/
theorem diagonalDirectLimitToTensor_bijective
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    Function.Bijective (diagonalDirectLimitToTensor f g) := by
  exact (directLimitDiagonal f g).bijective

/-- For two directed R-module systems (G,f),(H,g) over one directed preorder ι with decidable
equality, this is the R-linear equivalence colim_i(G_i⊗_RH_i)≅(colim_iG_i)⊗_R(colim_iH_i). Its
forward map is the canonical simultaneous stage-injection comparison. -/
noncomputable abbrev diagonalDirectLimitEquivTensor
    {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (g : ∀ i j, i ≤ j → H i →ₗ[R] H j)
    [DirectedSystem H (g · · ·)] :
    Module.DirectLimit (fun i => G i ⊗[R] H i)
        (directedTensorTransition f g) ≃ₗ[R]
      Module.DirectLimit G f ⊗[R] Module.DirectLimit H g :=
  directLimitDiagonal f g

/-- For directed R-module systems G,H over the same directed preorder with decidable equality, index
i and x∈G_i⊗_RH_i, the equivalence satisfies e(ι_i^{G⊗H}(x))=(ι_i^G⊗ι_i^H)(x). It identifies the
full stage tensor, not only decomposable generators. -/
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
