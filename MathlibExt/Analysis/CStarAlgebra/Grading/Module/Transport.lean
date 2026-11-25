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


public import MathlibExt.Analysis.CStarAlgebra.Grading.Module
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary

/-!
# Transport a C-star-module grading along a unitary

A unitary equivalence transports the grading generator by conjugation.  The
transported generator retains involutivity, right-action covariance and
coefficient-inner covariance, and the same unitary is graded by construction.
-/

@[expose] public section

noncomputable section

open scoped RightActions

namespace CStarModuleGrading

universe uB uE uF

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
variable {γ : CStarGrading B}

/-- **Transport of a module grading.** Let `B` be a graded nonunital complex C*-algebra with an order on
its opposite algebra, let `E,F` be complete right Hilbert `B`-modules, let `G` be a compatible
grading generator on `E`, and let `U : E → F` be a unitary module equivalence. The conjugate
generator `U G U⁻¹` defines a compatible grading on `F` over the same coefficient grading. -/
def transport
    (δ : CStarModuleGrading γ E)
    (U : CStarModule.UnitaryEquiv B E F) :
    CStarModuleGrading γ F where
  generator :=
    ((U.toLinearIsometryEquiv.toContinuousLinearEquiv.symm.trans δ.generator).trans
      U.toLinearIsometryEquiv.toContinuousLinearEquiv)
  generator_involutive := by
    intro y
    change U (δ.generator (U.symm
      (U (δ.generator (U.symm y))))) = y
    rw [U.symm_apply_apply, δ.generator_involutive, U.apply_symm_apply]
  generator_right_smul := by
    intro y b
    change U (δ.generator (U.symm (y <• b))) =
      U (δ.generator (U.symm y)) <• γ.generatorAut b
    have hsymm : U.symm (y <• b) = U.symm y <• b := by
      change U.symm.toAdjointable (y <• b) =
        U.symm.toAdjointable y <• b
      exact U.symm.toAdjointable.map_right_smul y b
    have hforward :
        U (δ.generator (U.symm y) <• γ.generatorAut b) =
          U (δ.generator (U.symm y)) <• γ.generatorAut b := by
      change U.toAdjointable
          (δ.generator (U.symm y) <• γ.generatorAut b) =
        U.toAdjointable (δ.generator (U.symm y)) <• γ.generatorAut b
      exact U.toAdjointable.map_right_smul
        (δ.generator (U.symm y)) (γ.generatorAut b)
    calc
      U (δ.generator (U.symm (y <• b))) =
          U (δ.generator (U.symm y <• b)) := by rw [hsymm]
      _ = U (δ.generator (U.symm y) <• γ.generatorAut b) := by
        rw [δ.generator_right_smul]
      _ = U (δ.generator (U.symm y)) <• γ.generatorAut b := hforward
  generator_rightInner := by
    intro x y
    change CStarModule.rightInner (B := B)
        (U (δ.generator (U.symm x)))
        (U (δ.generator (U.symm y))) =
      γ.generatorAut (CStarModule.rightInner (B := B) x y)
    rw [U.rightInner_map_map, δ.generator_rightInner,
      U.symm.rightInner_map_map]

@[simp]
theorem transport_generator_apply
    (δ : CStarModuleGrading γ E)
    (U : CStarModule.UnitaryEquiv B E F) (y : F) :
    (transport δ U).generator y = U (δ.generator (U.symm y)) :=
  rfl

/-- **Transporting unitary is graded.** Let `B` be a graded nonunital complex C*-algebra with an order
on its opposite algebra, let `E,F` be complete right Hilbert `B`-modules, let `G` be a compatible
grading generator on `E`, and let `U : E → F` be a unitary module equivalence. The equivalence `U`
is graded from the original module grading on `E` to its conjugate grading on `F`. -/
theorem isGradedUnitaryEquiv_transport
    (δ : CStarModuleGrading γ E)
    (U : CStarModule.UnitaryEquiv B E F) :
    IsGradedUnitaryEquiv δ (transport δ U) U := by
  intro x
  change U (δ.generator x) = U (δ.generator (U.symm (U x)))
  rw [U.symm_apply_apply]

/-- **Inverse transporting unitary is graded.** Let `B` be a graded nonunital complex C*-algebra with an
order on its opposite algebra, let `E,F` be complete right Hilbert `B`-modules, let `G` be a
compatible grading generator on `E`, and let `U : E → F` be a unitary module equivalence. The
inverse `U⁻¹` is graded from the conjugate grading on `F` back to the original grading on `E`. -/
theorem isGradedUnitaryEquiv_transport_symm
    (δ : CStarModuleGrading γ E)
    (U : CStarModule.UnitaryEquiv B E F) :
    IsGradedUnitaryEquiv (transport δ U) δ U.symm :=
  symm_isGradedUnitaryEquiv δ (transport δ U) U
    (isGradedUnitaryEquiv_transport δ U)

end CStarModuleGrading
