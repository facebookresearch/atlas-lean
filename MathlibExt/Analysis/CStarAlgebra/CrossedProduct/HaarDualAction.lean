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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CharacterContinuity
public import MathlibExt.Topology.Algebra.PontryaginDual.Pairing

/-!
# The actual full locally compact dual action and second crossed-product carrier

The compact-open continuous-character group acts on the same original full
Haar maximal completion by the computed raw character automorphisms. Every
orbit is point-norm continuous by the strict compact-support/dense estimate.
The second crossed product uses the same existing full completion constructor
for that actual action and an original dual Haar measure.

The canonical group-to-bidual evaluation map can pull the second dual action
back to the original group without selecting a Pontryagin-duality equivalence.
No Takai isomorphism, stability result, Fourier model or norm certificate is
used to construct this action or carrier. Nonunital and zero coefficients,
all locally compact group/dual data and the original Haar convention remain.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped CStarAlgebra

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

attribute [local instance] fullCovariantCompletionCStarAlgebra

/-- The actual original compact-open dual action on the full Haar crossed product. -/
def fullHaarDualAction :
    PointNormCStarAction (PontryaginDual G) (FullCovariantCompletion mu alpha) where
  toMonoidHom :=
    { toFun := completedCharacterEquiv mu alpha
      map_one' := by
        apply StarAlgEquiv.ext
        intro x
        exact DFunLike.congr_fun (completedCharacterHom_one mu alpha) x
      map_mul' := fun chi eta => by
        apply StarAlgEquiv.ext
        intro x
        exact DFunLike.congr_fun (completedCharacterHom_mul mu alpha chi eta) x }
  continuous_orbit := continuous_completedCharacterEquiv_orbit mu alpha

omit [mu.Regular] in
/-- On the dense original core, the actual dual action has exactly the printed scalar character formula. -/
@[simp]
theorem fullHaarDualAction_apply (chi : PontryaginDual G) (f : Carrier mu alpha) :
    fullHaarDualAction mu alpha chi (toFullCovariantCompletion mu alpha f) =
      toFullCovariantCompletion mu alpha (characterModulation mu alpha chi f) :=
  completedCharacterEquiv_apply mu alpha chi f

section Double

variable [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
variable (muDual : Measure (PontryaginDual G)) [muDual.IsHaarMeasure] [muDual.Regular]

/-- The actual second full Haar crossed product of the original full carrier by its computed dual action. -/
abbrev DoubleFullHaarCrossedProduct : Type (max uG uA) :=
  FullCovariantCompletion muDual (fullHaarDualAction mu alpha)

/-- The second carrier retains its actual inherited nonunital C-star dictionary. -/
@[instance_reducible]
def doubleFullHaarCrossedProductCStarAlgebra :
    NonUnitalCStarAlgebra (DoubleFullHaarCrossedProduct mu alpha muDual) :=
  fullCovariantCompletionCStarAlgebra muDual (fullHaarDualAction mu alpha)

attribute [local instance] doubleFullHaarCrossedProductCStarAlgebra

/-- The original second crossed-product core has its existing actual dense completed map. -/
def toDoubleFullHaarCrossedProduct :
    Carrier muDual (fullHaarDualAction mu alpha) →⋆ₙₐ[ℂ] DoubleFullHaarCrossedProduct mu alpha muDual :=
  toFullCovariantCompletion muDual (fullHaarDualAction mu alpha)

/-- The computed second dual action is pulled back along actual original group evaluation. -/
def doubleDualHaarAction :
    PointNormCStarAction G (DoubleFullHaarCrossedProduct mu alpha muDual) :=
  (fullHaarDualAction muDual (fullHaarDualAction mu alpha)).restrict (PontryaginDual.evaluation G)

omit [mu.Regular] [muDual.Regular] in
/-- On the original dense second core, the pulled-back dual action is the actual evaluation character. -/
@[simp]
theorem doubleDualHaarAction_apply (g : G) (f : Carrier muDual (fullHaarDualAction mu alpha)) :
    doubleDualHaarAction mu alpha muDual g (toDoubleFullHaarCrossedProduct mu alpha muDual f) =
      toDoubleFullHaarCrossedProduct mu alpha muDual
        (characterModulation muDual (fullHaarDualAction mu alpha) (PontryaginDual.evaluation G g) f) := by
  simpa only [doubleDualHaarAction, PointNormCStarAction.restrict_apply,
    toDoubleFullHaarCrossedProduct] using
    fullHaarDualAction_apply muDual (fullHaarDualAction mu alpha) (PontryaginDual.evaluation G g) f

end Double
end HaarTwistedCore
