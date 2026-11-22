/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ConstantEvaluation
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalDerivedMapping

/-!
# The actual derived projection at a terminal site object

Use the same original Smith choices `localQ S` and `localR S`. Projection
from the actual end out of `Q(const K)` into `R C` is weak at a terminal site
object. It factors through precomposition by the ordinary constant/evaluation
counit and the raw constant-source enriched isomorphism. This does not identify
the evaluated replacements with independent scalar replacement choices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.DerivedZeroProjection

variable {D : Type w} [Category.{v} D]

/-- The actual ordinary constant/evaluation counit at the terminal site object. -/
def counit {z : D} (hz : IsTerminal z) (X : SimplicialPresheaf.{u} D) :
    ConstantEvaluation.constant.obj (X.obj (op z)) ⟶ X :=
  (ConstantEvaluation.adjunction hz).counit.app X

/-- Each counit component uses the original operator to the terminal object. -/
theorem counit_app {z : D} (hz : IsTerminal z) (X : SimplicialPresheaf.{u} D)
    (a : Dᵒᵖ) : (counit hz X).app a = X.map (hz.from a.unop).op := by
  unfold counit
  rw [← Adjunction.homEquiv_symm_id]
  change (((ConstantEvaluation.adjunction hz).homEquiv (X.obj (op z)) X).symm
    (𝟙 (X.obj (op z)))).app a = _
  exact (ConstantEvaluation.adjunction_homEquiv_symm_app hz (X.obj (op z)) X (𝟙 _) a).trans
    (Category.id_comp _)

/-- At the terminal object the same counit component is the identity. -/
theorem counit_terminal {z : D} (hz : IsTerminal z) (X : SimplicialPresheaf.{u} D) :
    (counit hz X).app (op z) = 𝟙 (X.obj (op z)) := by
  rw [counit_app]
  have h : hz.from z = 𝟙 z := hz.hom_ext _ _
  rw [h, op_id, X.map_id]

variable [Small.{u} D] [LocallySmall.{u} D] {I : Type i} [Small.{u} I]

/-- The literal end projection uses the same actual original Q and R objects. -/
def gamma (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    ((localDerivedEnd S).obj (op (ConstantEvaluation.constant.obj K))).obj C ⟶
      (ihom (((localQ S).obj (ConstantEvaluation.constant.obj K)).obj (op z))).obj
        (((localR S).obj C).obj (op z)) :=
  innerHomπ ((localQ S).obj (ConstantEvaluation.constant.obj K)) ((localR S).obj C) (op z)

/-- The derived comparison is exactly the original end projection, without a transport. -/
theorem gamma_eq_projection (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    gamma S z K C =
      innerHomπ ((localQ S).obj (ConstantEvaluation.constant.obj K)) ((localR S).obj C)
        (op z) := rfl

/-- Scalar-source naturality uses the original constant map and the actual Q map. -/
theorem gamma_source (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    {K L : SSet.{u}} (k : K ⟶ L) (C : SimplicialPresheaf.{u} D) :
    localDerivedPrecomp S (ConstantEvaluation.constant.map k) C ≫ gamma S z K C =
      gamma S z L C ≫
        (pre (((localQ S).map (ConstantEvaluation.constant.map k)).app (op z))).app
          (((localR S).obj C).obj (op z)) :=
  innerHomPre_π _ _ _

/-- Target naturality uses the actual R map, followed by its scalar Hom action. -/
theorem gamma_target (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    localDerivedPostcomp S (ConstantEvaluation.constant.obj K) f ≫ gamma S z K C' =
      gamma S z K C ≫
        (ihom (((localQ S).obj (ConstantEvaluation.constant.obj K)).obj (op z))).map
          (((localR S).map f).app (op z)) :=
  innerHomPost_π _ _ _

/-- Every original site operator of the same Q replacement of a constant scalar is weak. -/
theorem qConstant_map_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    {a b : Dᵒᵖ} (g : a ⟶ b) :
    SSet.realizationWeakEquivalences
      (((localQ S).obj (ConstantEvaluation.constant.obj K)).map g) := by
  let q := (localQCounit S).app (ConstantEvaluation.constant.obj K)
  have hq : objectwiseKanWeakEquivalences D q := by
    have hb := (localQCounit_baseTrivialFibration S (ConstantEvaluation.constant.obj K)).2
    change (data D).model.categoryWithWeakEquivalences.weakEquivalences q at hb
    rwa [(data D).weakEquivalences_eq] at hb
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ (hq b)
  have hn := q.naturality g
  change ((localQ S).obj (ConstantEvaluation.constant.obj K)).map g ≫ q.app b =
    q.app a ≫ 𝟙 K at hn
  have hn' : ((localQ S).obj (ConstantEvaluation.constant.obj K)).map g ≫ q.app b =
      q.app a := hn.trans (Category.comp_id (q.app a))
  exact hn'.symm ▸ hq a

/-- The ordinary counit into Q of a constant scalar is a baseline weak equivalence. -/
theorem counit_qConstant_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (K : SSet.{u}) :
    weakEquivalences (SimplicialPresheaf.{u} D)
      (counit hz ((localQ S).obj (ConstantEvaluation.constant.obj K))) := by
  change (data D).model.categoryWithWeakEquivalences.weakEquivalences _
  rw [(data D).weakEquivalences_eq]
  intro a
  rw [counit_app]
  exact qConstant_map_weak S K (hz.from a.unop).op

/-- The literal derived projection factors through the ordinary counit and the raw iso. -/
theorem gamma_factorization (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    gamma S z K C =
      innerHomPre (counit hz ((localQ S).obj (ConstantEvaluation.constant.obj K)))
        ((localR S).obj C) ≫
      (ConstantEvaluation.iso hz
        (((localQ S).obj (ConstantEvaluation.constant.obj K)).obj (op z))
        ((localR S).obj C)).hom := by
  rw [gamma_eq_projection, ConstantEvaluation.iso_hom, innerHomPre_π, counit_terminal]
  simp only [pre_id, NatTrans.id_app, Category.comp_id]
  rfl

/-- The derived projection is weak for arbitrary K and C with the actual chosen replacements. -/
theorem gamma_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (gamma S z K C) := by
  rw [gamma_factorization S hz K C]
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (innerHomPre_weak_of_weakEquivalence _ ((localR S).obj C)
      (counit_qConstant_weak S hz K) (localR_isOriginalLocalFibrant S C).1)
    (SSet.realizationWeakEquivalences.of_isIso _)

end SimplicialPresheaf.DerivedZeroProjection
