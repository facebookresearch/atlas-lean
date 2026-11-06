/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Pi
public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverInstances
public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOver

/-!
# Finite-place completion tensor product maps

For a number field extension `L / K` and a finite place `v` of `K`, this file
provides the canonical `v.adicCompletion K`-algebra maps from the tensor product
`v.adicCompletion K ⊗[K] L` to each `w.val.adicCompletion L` and to the product.

## ATLAS source correspondence

This is the map-construction stage for ATLAS NumberTheoryI N265, Theorem 13.5.
At atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the exact source statement is
indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879):
the canonical
map `L ⊗[K] K_v → ∏_{w ∣ v} L_w`, `ℓ ⊗ x ↦ (ℓx)_w`, is an isomorphism of
finite étale `K_v`-algebras. The primary formal map is
[`GlobalFields.canonicalMap_finite` in `v1/Atlas/NumberTheoryI/code/GlobalFields.lean`,
lines 726--738](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L726-L738);
its component completion embeddings are defined at
[lines 693--713](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L693-L713).

The declarations here map to that source as follows:

* `v.placesOver L` is the dependent index type
  `{w : HeightOneSpectrum (𝓞 L) // w ∣ v}` used by the source product.
* The scoped `LiesOver` instance extracts the proof carried by each `w`.
  The scoped completion algebra and scalar-tower instances use the canonical
  `adicCompletionMap v w.val`; this is the chosen map `K_v → L_w`
  corresponding to source `completionEmbedding_finite v w.val w.property`.
* `completionTensorProductComponent v w` is the source component
  `L ⊗[K] K_v → L_w`, written after the standard symmetry as
  `K_v ⊗[K] L → L_w`: it multiplies the images of `x : K_v` and `y : L`.
* `completionTensorProductMap` packages those components with `AlgHom.pi`, so
  its codomain is exactly the dependent product over all `w ∣ v`.
  The `_tmul`, `_apply`, and `_pi_eval` theorems expose the source formula and
  show that evaluation at `w` recovers the selected component.

Changing the tensor-factor order uses only the canonical commutativity
equivalence and does not alter the map. This module constructs the N265
morphism; injectivity, surjectivity, finite étaleness, and the final
`AlgEquiv` are deliberately left to later stages.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

open scoped NumberField
open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)} (w : v.placesOver L)

/-- Lying-over instance from places-over membership. -/
scoped instance : w.val.asIdeal.LiesOver v.asIdeal :=
  w.property

/-- Algebra from the base completion to the place completion. -/
noncomputable scoped instance : Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
  let _ : w.val.asIdeal.LiesOver v.asIdeal := w.property
  (adicCompletionMap v w.val).toAlgebra

/-- Scalar tower over the base field through the base completion. -/
scoped instance : IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) := by
  let _ : w.val.asIdeal.LiesOver v.asIdeal := w.property
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [RingHom.algebraMap_toAlgebra]
  exact (adicCompletionMap_algebraMap v w.val x).symm

end IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField
open TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

/-- **Component at a place of the completion tensor product map.** Let $L/K$ be an extension of
number fields, let $v$ be a finite place of $K$, given as a height-one prime of the ring of
integers $\mathcal{O}_K$, let $K_v$ be the completion of $K$ at $v$, and let $w$ be a finite place
of $L$ lying over $v$, with completion $L_w$. Let $\iota_w : K_v \to L_w$ be the continuous ring
homomorphism extending $K \to L$. This is the $K_v$-algebra homomorphism
$K_v \otimes_K L \to L_w$ sending $x \otimes y$ to $\iota_w(x)\, y$, where $y \in L$ is viewed in
$L_w$. -/
noncomputable def completionTensorProductComponent (w : v.placesOver L) :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] w.val.adicCompletion L :=
  Algebra.TensorProduct.lift (Algebra.algHom _ _ _) (Algebra.algHom K L _)
    (fun _ _ => mul_comm _ _)

/-- **The completion tensor product map.** Let $L/K$ be an extension of number fields, let $v$ be a
finite place of $K$, given as a height-one prime of the ring of integers $\mathcal{O}_K$, and let
$K_v$ be the completion of $K$ at $v$. For each finite place $w$ of $L$ lying over $v$, let $L_w$
be the completion of $L$ at $w$ and $\iota_w : K_v \to L_w$ the continuous ring homomorphism
extending $K \to L$. This is the $K_v$-algebra homomorphism
$K_v \otimes_K L \to \prod_{w \mid v} L_w$ sending $x \otimes y$ to $(\iota_w(x)\, y)_w$, where
$y \in L$ is viewed in each $L_w$ and the product runs over the finite places of $L$ lying over
$v$. -/
noncomputable def completionTensorProductMap :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ((w : v.placesOver L) → w.val.adicCompletion L) :=
  AlgHom.pi (fun w => completionTensorProductComponent v w)

@[simp]
theorem completionTensorProductComponent_tmul (w : v.placesOver L)
    (x : v.adicCompletion K) (y : L) :
    completionTensorProductComponent v w (x ⊗ₜ[K] y) =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.val.adicCompletion L) x * Algebra.algHom K L _ y :=
  rfl

@[simp]
theorem completionTensorProductMap_apply (t : v.adicCompletion K ⊗[K] L)
    (w : v.placesOver L) :
    completionTensorProductMap v t w = completionTensorProductComponent v w t :=
  rfl

@[simp]
theorem completionTensorProductMap_tmul (x : v.adicCompletion K) (y : L)
    (w : v.placesOver L) :
    completionTensorProductMap v (x ⊗ₜ[K] y) w =
      Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.val.adicCompletion L) x * Algebra.algHom K L _ y :=
  rfl

theorem completionTensorProductMap_pi_eval (w : v.placesOver L) :
    (Pi.evalAlgHom (v.adicCompletion K)
          (fun w : v.placesOver L => w.val.adicCompletion L) w).comp
      (completionTensorProductMap (K := K) (L := L) v) =
      completionTensorProductComponent v w := by
  ext t
  rfl


end IsDedekindDomain.HeightOneSpectrum
