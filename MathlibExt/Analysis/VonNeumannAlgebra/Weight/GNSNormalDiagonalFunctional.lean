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

public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveOrderNormalMembership
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSCoefficientOrderNormal

/-!
# The actual GNS diagonal coefficient of a normal weight is a normal functional

Normality of the original scalar weight makes its existing positive GNS
diagonal coefficient preserve original bounded positive-family LUBs. The
strict membership criterion applies to that same bounded map and gives a
member of the existing canonical normal-functional space. No normal member,
GNS model, family, limit or norm certificate is supplied as an input.
Faithfulness, semifiniteness and representation normality remain separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct the actual normal-functional member of the original normal-weight GNS diagonal coefficient. -/
def normalWeightGNSDiagonalFunctional (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x : φ.finiteSquareSubmodule) : normalFunctionalSpace M := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let ψ := φ.gnsDiagonalPositiveFunctional x
  have hmember : ψ.toContinuousLinearMap ∈ normalFunctionalSpace M := by
    apply positiveFunctional_mem_normalFunctionalSpace_of_positiveLUBs M ψ
    intro I _preorder _directed _nonempty a s hmono hbound hLUB
    exact gnsDiagonalPositiveFunctional_preserves_boundedPositiveIsLUB M φ hφ x a s
      hmono hbound hLUB
  exact ⟨ψ.toContinuousLinearMap, hmember⟩

/-- Coercion of the actual normal diagonal member is the same original GNS representation coefficient. -/
@[simp]
theorem normalWeightGNSDiagonalFunctional_coe (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x : φ.finiteSquareSubmodule) :
    (normalWeightGNSDiagonalFunctional M φ hφ x : StrongDual ℂ M) =
      MathlibExt.Analysis.CStarAlgebra.representationCoefficient
        φ.gnsLeftStarAlgHom (φ.gnsMap x) (φ.gnsMap x) :=
  rfl

/-- The actual normal diagonal member has its original completed GNS vector value. -/
theorem normalWeightGNSDiagonalFunctional_apply (M : VonNeumannAlgebra H) (φ : Weight M)
    (hφ : IsNormalWeight M φ) (x : φ.finiteSquareSubmodule) (a : M) :
    (normalWeightGNSDiagonalFunctional M φ hφ x : StrongDual ℂ M) a =
      inner ℂ (φ.gnsMap x) ((φ.gnsLeftStarAlgHom a) (φ.gnsMap x)) := by
  rw [normalWeightGNSDiagonalFunctional_coe,
    MathlibExt.Analysis.CStarAlgebra.representationCoefficient_apply]

end

end VonNeumannAlgebra
