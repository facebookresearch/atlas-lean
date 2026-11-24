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
# The literal completed weight GNS carrier

The original weight-induced pre-GNS seminorm and inner product have their
stock uniform completion. The complete normed Hilbert carrier and dense
canonical map are constructed from those actual structures. Original
norms and pairing values are preserved on the dense domain.

The map from the original finite-square submodule is complex linear. Its
ambient norm is not used to claim continuity of an unbounded weight map.
The original positive-weight faithfulness law makes the canonical map
injective. No source existence output, Hilbert model, chosen scalar
extension or positive-inner certificate is supplied.

This completion does not construct the faithful normal left representation,
full scalar extension or any Tomita/modular/polar object.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The literal uniform completion of the actual weight pre-GNS type copy. -/
def Weight.GNS (φ : Weight A) : Type u := UniformSpace.Completion φ.PreGNS

/-- The completed carrier has the stock norm from the actual weight seminorm. -/
instance Weight.gnsNormedAddCommGroup (φ : Weight A) : NormedAddCommGroup φ.GNS :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion φ.PreGNS))

/-- The original complex scalar action extends to the actual completed carrier. -/
instance Weight.gnsNormedSpace (φ : Weight A) : NormedSpace ℂ φ.GNS :=
  inferInstanceAs (NormedSpace ℂ (UniformSpace.Completion φ.PreGNS))

/-- The actual weight inner product extends through the stock uniform completion. -/
instance Weight.gnsInnerProductSpace (φ : Weight A) : InnerProductSpace ℂ φ.GNS :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion φ.PreGNS))

/-- The literal weight completion is complete by its stock construction. -/
instance Weight.gnsCompleteSpace (φ : Weight A) : CompleteSpace φ.GNS :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion φ.PreGNS))

/-- The canonical original pre-GNS map is the stock completion linear isometry. -/
def Weight.toGNS (φ : Weight A) : φ.PreGNS →ₗᵢ[ℂ] φ.GNS :=
  UniformSpace.Completion.toComplₗᵢ

/-- The canonical map retains the literal stock completion value. -/
@[simp]
theorem Weight.toGNS_apply (φ : Weight A) (x : φ.PreGNS) :
    φ.toGNS x = (x : UniformSpace.Completion φ.PreGNS) :=
  rfl

/-- The canonical dense-domain map preserves the original weight-induced norm. -/
theorem Weight.toGNS_norm (φ : Weight A) (x : φ.PreGNS) : ‖φ.toGNS x‖ = ‖x‖ := by
  change ‖(x : UniformSpace.Completion φ.PreGNS)‖ = ‖x‖
  exact UniformSpace.Completion.norm_coe x

/-- The actual completion map preserves the original weight inner product. -/
theorem Weight.toGNS_inner (φ : Weight A) (x y : φ.PreGNS) :
    ⟪φ.toGNS x, φ.toGNS y⟫_ℂ = ⟪x, y⟫_ℂ := by
  change ⟪(x : UniformSpace.Completion φ.PreGNS), (y : UniformSpace.Completion φ.PreGNS)⟫_ℂ = ⟪x, y⟫_ℂ
  exact UniformSpace.Completion.inner_coe x y

/-- The literal canonical pre-GNS completion map has dense range. -/
theorem Weight.toGNS_denseRange (φ : Weight A) : DenseRange φ.toGNS := by
  change DenseRange ((↑) : φ.PreGNS → UniformSpace.Completion φ.PreGNS)
  exact UniformSpace.Completion.denseRange_coe

/-- Original positive-weight faithfulness makes the canonical dense map injective. -/
theorem Weight.toGNS_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective φ.toGNS := by
  let : NormedAddCommGroup φ.PreGNS := φ.faithfulPreGNSNormedAddCommGroup hφ
  exact φ.toGNS.injective

/-- The exact original finite-square domain maps linearly to the completed weight carrier. -/
def Weight.gnsMap (φ : Weight A) : φ.finiteSquareSubmodule →ₗ[ℂ] φ.GNS :=
  φ.toGNS.toLinearMap.comp φ.preGNSLinearEquiv.symm.toLinearMap

/-- The original-domain map is the canonical completion after the literal type-copy identity. -/
@[simp]
theorem Weight.gnsMap_apply (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.gnsMap x = φ.toGNS (φ.preGNSLinearEquiv.symm x) :=
  rfl

/-- The norm square of the original-domain image is its original finite square weight value. -/
theorem Weight.gnsMap_norm_sq (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    ‖φ.gnsMap x‖ ^ 2 = φ.finiteSquareValue x := by
  rw [φ.gnsMap_apply, φ.toGNS_norm, φ.preGNS_norm_sq, LinearEquiv.apply_symm_apply]

/-- Completed original-domain inner products retain the actual scalar-weight polarization. -/
theorem Weight.gnsMap_inner (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    ⟪φ.gnsMap x, φ.gnsMap y⟫_ℂ = φ.finiteSquarePolarInner x y := by
  rw [φ.gnsMap_apply, φ.gnsMap_apply, φ.toGNS_inner, φ.preGNS_inner,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The map of the exact original finite-square domain is dense in its literal completion. -/
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

/-- The original-domain GNS map is injective under exactly the original source faithfulness law. -/
theorem Weight.gnsMap_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective φ.gnsMap :=
  (φ.toGNS_injective hφ).comp φ.preGNSLinearEquiv.symm.injective

end

end CStarAlgebra.ScalarWeight
