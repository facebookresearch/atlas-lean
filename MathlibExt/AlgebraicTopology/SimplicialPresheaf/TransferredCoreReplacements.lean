/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ConstantEvaluationQuillen
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.DerivedZeroProjection
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant

/-!
# Scalar replacements transferred from the actual original model

Evaluating the chosen `Q(const K)` transfers its actual counit to a scalar
trivial fibration. Evaluating the chosen `R C` gives a Kan target; when C is
original local-fibrant, its evaluated unit is a scalar trivial cofibration.
The target construction still takes the whole original presheaf C. No equality
with independently chosen scalar factors or dependence on its bare core is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.TransferredCoreReplacements

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- Evaluate the same actual Q applied to the literal constant extension. -/
def qReplacement (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) :
    SSet.{u} ⥤ SSet.{u} :=
  ConstantEvaluation.constant ⋙ localQ S ⋙ ConstantEvaluation.evaluation z

/-- The transferred source counit is the evaluated original first-factor leg. -/
def qCounit (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) :
    qReplacement S z ⟶ 𝟭 SSet.{u} :=
  Functor.whiskerLeft ConstantEvaluation.constant
    (Functor.whiskerRight (localQCounit S) (ConstantEvaluation.evaluation z))

/-- Source objects are the original Q objects evaluated at the same site value. -/
theorem qReplacement_obj (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u}) :
    (qReplacement S z).obj K =
      ((localQ S).obj (ConstantEvaluation.constant.obj K)).obj (op z) := rfl

/-- The counit component is exactly the original Q counit component at that value. -/
theorem qCounit_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u}) :
    (qCounit S z).app K = ((localQCounit S).app (ConstantEvaluation.constant.obj K)).app
      (op z) := rfl

/-- Every transferred source object is cofibrant in the scalar Kan–Quillen model. -/
theorem qReplacement_isCofibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    (z : D) (K : SSet.{u}) : IsCofibrant ((qReplacement S z).obj K) :=
  inferInstance

/-- The proved right-Quillen evaluation transfers the actual Q counit to a trivial fibration. -/
theorem qCounit_trivialFibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (K : SSet.{u}) :
    trivialFibrations SSet.{u} ((qCounit S z).app K) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  have hq : trivialFibrations (SimplicialPresheaf.{u} D)
      ((localQCounit S).app (ConstantEvaluation.constant.obj K)) := by
    rw [d.trivialFibrations_eq]
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
    have hb := localQCounit_baseTrivialFibration S (ConstantEvaluation.constant.obj K)
    rw [(data D).trivialFibrations_eq] at hb
    exact hb
  exact ConstantEvaluation.evaluation_trivialFibration S hz _ hq

/-- The transferred target retains the whole original C before evaluating its chosen R. -/
def rReplacement (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) :
    SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  localR S ⋙ ConstantEvaluation.evaluation z

/-- The target unit is evaluation of the same original Smith second-factor leg. -/
def rUnit (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) :
    ConstantEvaluation.evaluation z ⟶ rReplacement S z :=
  Functor.whiskerRight (localRUnit S) (ConstantEvaluation.evaluation z)

/-- The target object is the actual original R object evaluated at the same site value. -/
theorem rReplacement_obj (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C : SimplicialPresheaf.{u} D) :
    (rReplacement S z).obj C = ((localR S).obj C).obj (op z) := rfl

/-- The target unit component is exactly the original R unit at that value. -/
theorem rUnit_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C : SimplicialPresheaf.{u} D) :
    (rUnit S z).app C = ((localRUnit S).app C).app (op z) := rfl

/-- The transferred target is Kan by the genuine global fibrancy of the chosen R object. -/
theorem rReplacement_isKan (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (C : SimplicialPresheaf.{u} D) :
    SSet.KanComplex ((rReplacement S z).obj C) := by
  change IsFibrant (((localR S).obj C).obj (op z))
  exact ConstantEvaluation.evaluation_isFibrant S hz _ (localR_isOriginalLocalFibrant S C)

/-- At an original local-fibrant C, the evaluated R unit is a scalar trivial cofibration. -/
theorem rUnit_trivialCofibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    (z : D) (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    trivialCofibrations SSet.{u} ((rUnit S z).app C) := by
  let η := (localRUnit S).app C
  have hη := localRUnit_localTrivialCofibration S C
  let _ : Mono η := hη.1
  have hm : Mono (η.app (op z)) := inferInstance
  have hw := (originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant S η hC
    (localR_isOriginalLocalFibrant S C)).mp hη.2
  change cofibrations SSet.{u} (η.app (op z)) ∧
    SSet.realizationWeakEquivalences (η.app (op z))
  refine ⟨?_, hw (op z)⟩
  simpa only [SSet.modelCategoryQuillen.cofibrations_eq, monomorphisms.iff] using hm

/-- The scalar mapping object uses precisely these transferred source and target objects. -/
def mappingModel (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) : SSet.{u} :=
  (ihom ((qReplacement S z).obj K)).obj ((rReplacement S z).obj C)

/-- The comparison into the transferred scalar mapping object is the already proved gamma. -/
def comparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    ((localDerivedEnd S).obj (op (ConstantEvaluation.constant.obj K))).obj C ⟶
      mappingModel S z K C :=
  DerivedZeroProjection.gamma S z K C

/-- No map transport is introduced in relating the comparison to the literal projection. -/
theorem comparison_eq_gamma (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    comparison S z K C = DerivedZeroProjection.gamma S z K C := rfl

/-- Source naturality uses the exact transferred source functor action. -/
theorem comparison_source (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    {K L : SSet.{u}} (k : K ⟶ L) (C : SimplicialPresheaf.{u} D) :
    localDerivedPrecomp S (ConstantEvaluation.constant.map k) C ≫ comparison S z K C =
      comparison S z L C ≫ (pre ((qReplacement S z).map k)).app ((rReplacement S z).obj C) :=
  DerivedZeroProjection.gamma_source S z k C

/-- Target naturality uses the exact transferred target functor action. -/
theorem comparison_target (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    localDerivedPostcomp S (ConstantEvaluation.constant.obj K) f ≫ comparison S z K C' =
      comparison S z K C ≫ (ihom ((qReplacement S z).obj K)).map ((rReplacement S z).map f) :=
  DerivedZeroProjection.gamma_target S z K f

/-- The actual comparison to this transferred scalar mapping model is weak. -/
theorem comparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (comparison S z K C) :=
  DerivedZeroProjection.gamma_weak S hz K C

end SimplicialPresheaf.TransferredCoreReplacements
