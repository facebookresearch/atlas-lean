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
# The actual source-faithful semifinite GNS coefficient map is injective

A zero coefficient operator annihilates the actual dense-domain map.
Original weight faithfulness makes that map injective, hence original
left multiplication annihilates the literal finite-square domain.
Source semifiniteness supplies that domain's actual ultraweak density,
and proved fixed-left ultraweak continuity extends the annihilation to
the original algebra. Original multiplication by one gives zero coefficient.

These proofs supply the actual representation-injectivity prerequisite
for the faithful normal-range constructor. No source existence, range or
normality output and no extra density/model certificate is selected.
Representation normality, full scalar extension and Tomita/modular/polar
objects remain separate; original source theorem proofs stay wholly open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A zero actual source-faithful semifinite coefficient operator has zero original coefficient. -/
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

/-- Source semifiniteness and original weight faithfulness make the computed coefficient map injective. -/
theorem Weight.gnsLeftStarAlgHom_injective (M : VonNeumannAlgebra H) (φ : Weight M)
    (hsem : VonNeumannAlgebra.IsSemifiniteWeight M φ)
    (hfaith : VonNeumannAlgebra.IsFaithfulWeight M φ) : Function.Injective φ.gnsLeftStarAlgHom := by
  intro a b hab
  have hzero : φ.gnsLeftStarAlgHom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (φ.gnsLeftStarAlgHom_eq_zero_implies M hsem hfaith (a - b) hzero)

end

end CStarAlgebra.ScalarWeight
