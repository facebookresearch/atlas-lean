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

public import MathlibExt.Topology.Algebra.PontryaginDual.Evaluation
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.Pullback
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CrossedProductTensorNormal
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.TensorCharacterAction

/-!
# The actual nested tensor double crossed product and original-group second dual action

Use the first normal dual action and the same regular crossed-product
construction with an explicit genuine regular Haar measure on the full
compact-open character group. The Hilbert carrier is the literal nested
completed tensor, retaining both original Haar choices.

The original-group second dual action is the actual second character action
pulled back along canonical evaluation. The construction is valid for general
locally compact topological groups. The later source duality theorems retain
their abelian-group hypothesis.

No Fourier normalization, bidual isomorphism or topological-product L2 comparison
is asserted here. Their normalized source comparisons remain separate proof
obligations; no data is chosen from their open existence statements.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped TensorProduct CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
variable (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]

/-- The second regular construction uses the actual first dual action and explicit dual Haar measure. -/
def doubleCrossedProductTensor (α : NormalAction G M) :
    VonNeumannAlgebra
      (UniformSpace.Completion
        (UniformSpace.Completion (H ⊗[ℂ] Lp ℂ 2 μ) ⊗[ℂ] Lp ℂ 2 ν)) :=
  crossedProductTensor ν (tensorCharacterNormalAction μ α)

/-- The actual second dual action restricted along the original canonical evaluation homomorphism. -/
def doubleDualTensorNormalAction (α : NormalAction G M) :
    NormalAction G (doubleCrossedProductTensor μ ν α) :=
  comp (tensorCharacterNormalAction ν (tensorCharacterNormalAction μ α))
    (PontryaginDual.evaluation G)

/-- The actual original-group second dual action fixes every nested first-product coefficient. -/
@[simp]
theorem doubleDualTensorNormalAction_fix_coefficient (α : NormalAction G M) (g : G)
    (x : crossedProductTensor μ α) :
    doubleDualTensorNormalAction μ ν α g
      (crossedProductTensorCoefficient ν (tensorCharacterNormalAction μ α) x) =
        crossedProductTensorCoefficient ν (tensorCharacterNormalAction μ α) x := by
  change tensorCharacterNormalAction ν (tensorCharacterNormalAction μ α)
    (PontryaginDual.evaluation G g)
      (crossedProductTensorCoefficient ν (tensorCharacterNormalAction μ α) x) = _
  exact tensorCharacterNormalAction_fix_coefficient ν (tensorCharacterNormalAction μ α)
    (PontryaginDual.evaluation G g) x

/-- The actual original-group second dual action scales the second Haar unitary by positive χ(g). -/
@[simp]
theorem doubleDualTensorNormalAction_scale_group (α : NormalAction G M) (g : G)
    (χ : PontryaginDual G) :
    doubleDualTensorNormalAction μ ν α g
      ((crossedProductTensorGroupUnitary ν (tensorCharacterNormalAction μ α) χ).val :
        doubleCrossedProductTensor μ ν α) =
          ((χ g : Circle) : ℂ) •
            ((crossedProductTensorGroupUnitary ν (tensorCharacterNormalAction μ α) χ).val :
              doubleCrossedProductTensor μ ν α) := by
  change tensorCharacterNormalAction ν (tensorCharacterNormalAction μ α)
    (PontryaginDual.evaluation G g)
      ((crossedProductTensorGroupUnitary ν (tensorCharacterNormalAction μ α) χ).val :
        doubleCrossedProductTensor μ ν α) = _
  simpa only [PontryaginDual.evaluation_apply] using
    tensorCharacterNormalAction_scale_group ν (tensorCharacterNormalAction μ α)
      (PontryaginDual.evaluation G g) χ

end

end VonNeumannAlgebra.NormalAction
