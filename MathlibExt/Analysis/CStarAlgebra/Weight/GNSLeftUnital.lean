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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftRepresentation
public import Mathlib.Algebra.Algebra.Hom

/-!
# Unitality of the weight GNS representation

For a unital complex C-star algebra `A` and extended positive weight `φ`, the completed left
action satisfies `π(1)=I`, since it fixes every vector of the dense range `Λ(n_φ)`.

Thus left multiplication defines a unital complex star homomorphism `A → B(H_φ)` with
`π(a)Λ(x)=Λ(a*x)`. This includes a zero algebra or zero GNS space and does not require the
weight of `1` to be finite.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **Identity operator from the unit coefficient.** Let `A` be a unital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x : φ(x* x) < ∞}`, and let `Λ : n_φ → H_φ` be its dense GNS
map. `gnsLeftMul φ (1 : A)=1` on `H_φ`; the weight may be infinite at `1`. -/
theorem Weight.gnsLeftMul_one (φ : Weight A) : φ.gnsLeftMul (1 : A) = 1 := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
      change φ.gnsLeftMul 1 (φ.toGNS x) = φ.toGNS x
      rw [φ.gnsLeftMul_toGNS]
      apply congrArg φ.toGNS
      apply φ.preGNSLinearEquiv.injective
      apply Subtype.ext
      rw [φ.preGNSLeftMul_originalValue]
      exact one_mul _

/-- **Unital star representation of the weight algebra.** Let `A` be a unital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x : φ(x* x) < ∞}`, and let `Λ : n_φ → H_φ` be its
dense GNS map. `gnsLeftStarAlgHom φ : A →⋆ₐ[ℂ] B(H_φ)` sends `a` to completed left
multiplication, with `π(1)=I` and `π(a)Λ(x)=Λ(a*x)`. -/
def Weight.gnsLeftStarAlgHom (φ : Weight A) : A →⋆ₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) where
  toAlgHom := AlgHom.mk'
    { toFun := φ.gnsLeftRepresentation
      map_zero' := map_zero φ.gnsLeftRepresentation
      map_one' := by
        change φ.gnsLeftMul (1 : A) = 1
        exact φ.gnsLeftMul_one
      map_add' a b := map_add φ.gnsLeftRepresentation a b
      map_mul' a b := map_mul φ.gnsLeftRepresentation a b }
    (fun c a => map_smul φ.gnsLeftRepresentation c a)
  map_star' a := map_star φ.gnsLeftRepresentation a

/-- **Underlying GNS operator of the unital representation.** Let `A` be a unital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x : φ(x* x) < ∞}`, and let `Λ : n_φ → H_φ` be its
dense GNS map. for every `a : A`, `gnsLeftStarAlgHom φ a = gnsLeftRepresentation φ a`, the
completed left operator. -/
theorem Weight.gnsLeftStarAlgHom_apply (φ : Weight A) (a : A) :
    φ.gnsLeftStarAlgHom a = φ.gnsLeftRepresentation a :=
  rfl

/-- **Unital GNS representation on finite square vectors.** Let `A` be a unital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x : φ(x* x) < ∞}`, and let `Λ : n_φ → H_φ` be its
dense GNS map. for `a : A` and `x ∈ n_φ`, `gnsLeftStarAlgHom φ a (Λ x)=Λ(a*x)`. -/
theorem Weight.gnsLeftStarAlgHom_gnsMap (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    φ.gnsLeftStarAlgHom a (φ.gnsMap x) = φ.gnsMap (φ.finiteSquareLeftMul a x) :=
  φ.gnsLeftRepresentation_gnsMap a x

end

end CStarAlgebra.ScalarWeight
