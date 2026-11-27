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

public import MathlibExt.Analysis.VonNeumannAlgebra.MultiplicationPredual
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSFaithfulDomain
public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftUnital

/-!
# Injective GNS representation of a faithful semifinite weight

Let `φ` be a faithful extended positive weight on a concrete von Neumann algebra whose
finite-positive span is ultraweakly dense. Its bounded GNS left representation `π : M → B(H_φ)`
is injective.

If `π(a)=0`, then `a` annihilates the finite square domain. Its ultraweak density and continuity
of fixed multiplication give `a=0`. Normality of the weight is not needed for this injectivity
result.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Zero GNS coefficient operator forces zero algebra element.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]`
be an extended positive weight: additive, homogeneous for finite nonnegative real scalars,
and zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map
into the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`.
Assume the complex span of finite-weight positive elements is ultraweakly dense in `M`,
and `φ(a)=0 → a=0` for positive `a`. for `a ∈ M`, `π(a)=φ.gnsLeftStarAlgHom a=0` implies
`a=0`. Normality of `φ` is not assumed. -/
theorem Weight.gnsLeftStarAlgHom_eq_zero_implies (M : VonNeumannAlgebra H) (φ : Weight M)
    (hsem : VonNeumannAlgebra.IsSemifiniteWeight M φ)
    (hfaith : VonNeumannAlgebra.IsFaithfulWeight M φ) (a : M)
    (ha : φ.gnsLeftStarAlgHom a = 0) : a = 0 := by
  have hann : ∀ x : φ.finiteSquareSubmodule, a * (x : M) = 0 := by
    intro x
    have hmap : φ.gnsMap (φ.finiteSquareLeftMul a x) = φ.gnsMap 0 := by
      rw [map_zero]
      calc
        φ.gnsMap (φ.finiteSquareLeftMul a x) = φ.gnsLeftStarAlgHom a (φ.gnsMap x) :=
          (φ.gnsLeftStarAlgHom_gnsMap a x).symm
        _ = 0 := by rw [ha]; rfl
    have hzero : φ.finiteSquareLeftMul a x = 0 := φ.gnsMap_injective hfaith hmap
    have hvalue := congrArg (fun y : φ.finiteSquareSubmodule => (y : M)) hzero
    change a * (x : M) = 0 at hvalue
    exact hvalue
  let f : VonNeumannAlgebra.Ultraweak M → VonNeumannAlgebra.Ultraweak M :=
    fun z => (VonNeumannAlgebra.ultraweakLinearEquiv M).symm
      (a * VonNeumannAlgebra.ultraweakLinearEquiv M z)
  have hcontinuous : Continuous f := VonNeumannAlgebra.ultraweak_left_mul_continuous M a
  have hclosed : IsClosed {z | f z = 0} := isClosed_eq hcontinuous continuous_const
  have hdense := VonNeumannAlgebra.weightFiniteSquareUltraweakDense M φ hsem
  have hsubset :
      (φ.finiteSquareSubmodule.map (VonNeumannAlgebra.ultraweakLinearEquiv M).symm.toLinearMap :
        Set (VonNeumannAlgebra.Ultraweak M)) ⊆ {z | f z = 0} := by
    change (VonNeumannAlgebra.ultraweakLinearEquiv M).symm '' (φ.finiteSquareSubmodule : Set M) ⊆ _
    rintro z ⟨x, hx, rfl⟩
    have hxzero : a * x = 0 := hann ⟨x, hx⟩
    change (VonNeumannAlgebra.ultraweakLinearEquiv M).symm
      (a * VonNeumannAlgebra.ultraweakLinearEquiv M
        ((VonNeumannAlgebra.ultraweakLinearEquiv M).symm x)) = 0
    rw [LinearEquiv.apply_symm_apply, hxzero, map_zero]
  have hall : ∀ z, f z = 0 := fun z => (closure_minimal hsubset hclosed) (hdense z)
  have hone := hall ((VonNeumannAlgebra.ultraweakLinearEquiv M).symm (1 : M))
  have horiginal := congrArg (VonNeumannAlgebra.ultraweakLinearEquiv M) hone
  change a * VonNeumannAlgebra.ultraweakLinearEquiv M
    ((VonNeumannAlgebra.ultraweakLinearEquiv M).symm (1 : M)) =
      VonNeumannAlgebra.ultraweakLinearEquiv M (0 : VonNeumannAlgebra.Ultraweak M) at horiginal
  rw [LinearEquiv.apply_symm_apply, mul_one, map_zero] at horiginal
  exact horiginal

/-- **Faithful semifinite weight gives an injective GNS star map.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]`
be an extended positive weight: additive, homogeneous for finite nonnegative real scalars,
and zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map
into the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`.
Assume the complex span of finite-weight positive elements is ultraweakly dense in `M`,
and `φ(a)=0 → a=0` for positive `a`. the unital star homomorphism `π=φ.gnsLeftStarAlgHom :
M → B(H_φ)` is injective. -/
theorem Weight.gnsLeftStarAlgHom_injective (M : VonNeumannAlgebra H) (φ : Weight M)
    (hsem : VonNeumannAlgebra.IsSemifiniteWeight M φ)
    (hfaith : VonNeumannAlgebra.IsFaithfulWeight M φ) : Function.Injective φ.gnsLeftStarAlgHom := by
  intro a b hab
  have hzero : φ.gnsLeftStarAlgHom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (φ.gnsLeftStarAlgHom_eq_zero_implies M hsem hfaith (a - b) hzero)

end

end CStarAlgebra.ScalarWeight
