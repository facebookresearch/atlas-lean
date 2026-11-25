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

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreGNSNorm
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Hilbert completion of the weight square domain

For a nonunital complex C-star algebra and extended positive weight `φ`, equip `n_φ = {x : φ(x*
x) < ∞}` with the seminorm `‖x‖_φ = √((φ(x* x)).toReal)` and its complex polarization. The
uniform completion of this seminormed space is the Hilbert space `H_φ`.

The complex-linear map `Λ : n_φ → H_φ` has dense range, `‖Λ(x)‖²=(φ(x* x)).toReal`, and
preserves the polarized pairing. If `φ` is faithful on positive elements, `Λ` is injective. A
general weight may have a nonzero null space; continuity for the ambient norm on `A` is not part
of these assertions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **GNS Hilbert completion of a positive weight.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `GNS φ` is the uniform completion of `PreGNS φ`, the type copy of `n_φ` equipped with
seminorm `√q(x)` and the polarized pairing. -/
def Weight.GNS (φ : Weight A) : Type u := UniformSpace.Completion φ.PreGNS

/-- **Norm on the GNS completion.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. the
completion `H_φ` is a normed additive commutative group with `‖Λ(x)‖=√q(x)`; null vectors of
the domain become zero in the completion. -/
instance Weight.gnsNormedAddCommGroup (φ : Weight A) : NormedAddCommGroup φ.GNS :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion φ.PreGNS))

/-- **Complex normed space structure of the GNS completion.** Let `A` be a nonunital complex
C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real
homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x*
x)).toReal` for `x ∈ n_φ`. the complex action on `n_φ` extends to `H_φ` and satisfies `‖c •
ξ‖=‖c‖*‖ξ‖` for `c : ℂ` and `ξ ∈ H_φ`. -/
instance Weight.gnsNormedSpace (φ : Weight A) : NormedSpace ℂ φ.GNS :=
  inferInstanceAs (NormedSpace ℂ (UniformSpace.Completion φ.PreGNS))

/-- **Inner product on the GNS completion.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. the polarization of `q` extends to the complex inner product on `H_φ`; for domain
vectors its value is `finiteSquarePolarInner φ x y`. -/
instance Weight.gnsInnerProductSpace (φ : Weight A) : InnerProductSpace ℂ φ.GNS :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion φ.PreGNS))

/-- **Completeness of the weight Hilbert space.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. the normed inner-product space `H_φ = Completion (PreGNS φ)` is complete, including the
case of a zero or degenerate weight. -/
instance Weight.gnsCompleteSpace (φ : Weight A) : CompleteSpace φ.GNS :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion φ.PreGNS))

/-- **Isometric map from the weight seminormed domain.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. `toGNS φ : PreGNS φ →ₗᵢ[ℂ] H_φ` is the complex-linear completion map for the
seminorm `√q`; for a degenerate weight, preservation of seminorm does not imply injectivity. -/
def Weight.toGNS (φ : Weight A) : φ.PreGNS →ₗᵢ[ℂ] φ.GNS :=
  UniformSpace.Completion.toComplₗᵢ

/-- **Completion value of a pre-GNS vector.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `toGNS φ x` is the image of `x : PreGNS φ` under the completion inclusion. -/
@[simp]
theorem Weight.toGNS_apply (φ : Weight A) (x : φ.PreGNS) :
    φ.toGNS x = (x : UniformSpace.Completion φ.PreGNS) :=
  rfl

/-- **Preservation of the pre-GNS seminorm.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. for `x : PreGNS φ`, `‖toGNS φ x‖=‖x‖`, where the domain norm is the weight seminorm, not
the subspace norm inherited from `A`. -/
theorem Weight.toGNS_norm (φ : Weight A) (x : φ.PreGNS) : ‖φ.toGNS x‖ = ‖x‖ := by
  change ‖(x : UniformSpace.Completion φ.PreGNS)‖ = ‖x‖
  exact UniformSpace.Completion.norm_coe x

/-- **Preservation of the pre-GNS pairing.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `⟨toGNS φ x,toGNS φ y⟩=⟨x,y⟩` for `x,y : PreGNS φ`, with the complex inner product
linear in its second argument. -/
theorem Weight.toGNS_inner (φ : Weight A) (x y : φ.PreGNS) :
    ⟪φ.toGNS x, φ.toGNS y⟫_ℂ = ⟪x, y⟫_ℂ := by
  change ⟪(x : UniformSpace.Completion φ.PreGNS), (y : UniformSpace.Completion φ.PreGNS)⟫_ℂ = ⟪x, y⟫_ℂ
  exact UniformSpace.Completion.inner_coe x y

/-- **Density of the pre-GNS inclusion.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. the
range of `toGNS φ : PreGNS φ → H_φ` is norm-dense in the Hilbert completion. -/
theorem Weight.toGNS_denseRange (φ : Weight A) : DenseRange φ.toGNS := by
  change DenseRange ((↑) : φ.PreGNS → UniformSpace.Completion φ.PreGNS)
  exact UniformSpace.Completion.denseRange_coe

/-- **Faithful weight gives an injective completion inclusion.** Let `A` be a nonunital complex
C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real
homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x*
x)).toReal` for `x ∈ n_φ`. if `φ(a)=0` implies `a=0` for every positive `a : A`, then `toGNS
φ` is injective. -/
theorem Weight.toGNS_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective φ.toGNS := by
  let : NormedAddCommGroup φ.PreGNS := φ.faithfulPreGNSNormedAddCommGroup hφ
  exact φ.toGNS.injective

/-- **GNS map of finite square elements.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. the
complex-linear map `Λ : n_φ → H_φ` is `toGNS φ` after identifying `n_φ` with its
weight-seminormed type copy `PreGNS φ`. -/
def Weight.gnsMap (φ : Weight A) : φ.finiteSquareSubmodule →ₗ[ℂ] φ.GNS :=
  φ.toGNS.toLinearMap.comp φ.preGNSLinearEquiv.symm.toLinearMap

/-- **GNS map through the seminormed type copy.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. for `x ∈ n_φ`, `gnsMap φ x = toGNS φ ((preGNSLinearEquiv φ).symm x)`; the inverse linear
equivalence equips the same element with its weight seminorm. -/
@[simp]
theorem Weight.gnsMap_apply (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.gnsMap x = φ.toGNS (φ.preGNSLinearEquiv.symm x) :=
  rfl

/-- **Weight square as a GNS norm square.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. for every `x ∈ n_φ`, `‖Λ(x)‖²=q(x)=(φ(x* x)).toReal`. -/
theorem Weight.gnsMap_norm_sq (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    ‖φ.gnsMap x‖ ^ 2 = φ.finiteSquareValue x := by
  rw [φ.gnsMap_apply, φ.toGNS_norm, φ.preGNS_norm_sq, LinearEquiv.apply_symm_apply]

/-- **Polarized weight pairing on GNS vectors.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. for `x,y ∈ n_φ`, `⟨Λ(x),Λ(y)⟩=finiteSquarePolarInner φ x y`, with the
convention linear in the second argument. -/
theorem Weight.gnsMap_inner (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    ⟪φ.gnsMap x, φ.gnsMap y⟫_ℂ = φ.finiteSquarePolarInner x y := by
  rw [φ.gnsMap_apply, φ.gnsMap_apply, φ.toGNS_inner, φ.preGNS_inner,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **Density of finite square GNS vectors.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. the image `Λ(n_φ)` is norm-dense in `H_φ`, regardless of whether `n_φ` is
dense in the ambient algebra `A`. -/
theorem Weight.gnsMap_denseRange (φ : Weight A) : DenseRange φ.gnsMap := by
  have hrange : Set.range φ.gnsMap = Set.range φ.toGNS := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ.preGNSLinearEquiv.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨φ.preGNSLinearEquiv x, ?_⟩
      rw [φ.gnsMap_apply, LinearEquiv.symm_apply_apply]
  change Dense (Set.range φ.gnsMap)
  rw [hrange]
  exact φ.toGNS_denseRange

/-- **Injectivity of the GNS map for a faithful weight.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. if `φ(a)=0 → a=0` for every positive `a : A`, then `Λ :
n_φ → H_φ` is injective. -/
theorem Weight.gnsMap_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective φ.gnsMap :=
  (φ.toGNS_injective hφ).comp φ.preGNSLinearEquiv.symm.injective

end

end CStarAlgebra.ScalarWeight
