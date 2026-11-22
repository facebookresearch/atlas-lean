/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.TransferredCoreReplacements
import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacements
import MathlibExt.AlgebraicTopology.ModelCategory.InternalHomSourceWeakEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductBrown
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Natural spans to independently fixed scalar replacements

The scalar conventions contain actual replacement functors and natural maps,
with their usual class and fibrancy properties. The common source is the
literal pullback of the two Q counits. The common target is the same fixed
scalar R applied to the literal pushout of the two R units. All comparison
legs are prescribed precomposition or postcomposition maps; no reverse weak
map, equality of factors, or universal-property certificate is selected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalCategory MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.ScalarCoreReplacementSpans

/-- Independently fixed scalar replacement functions and their genuine natural legs. -/
structure ScalarConventions where
  /-- The chosen scalar Q functor. -/
  Q : SSet.{u} ⥤ SSet.{u}
  /-- Its actual natural counit. -/
  q : Q ⟶ 𝟭 SSet.{u}
  /-- Every actual counit component is a scalar trivial fibration. -/
  q_trivialFibration (K : SSet.{u}) : trivialFibrations SSet.{u} (q.app K)
  /-- The independently chosen scalar R functor. -/
  R : SSet.{u} ⥤ SSet.{u}
  /-- Its actual natural unit. -/
  r : 𝟭 SSet.{u} ⟶ R
  /-- Every actual unit component is a scalar trivial cofibration. -/
  r_trivialCofibration (K : SSet.{u}) : trivialCofibrations SSet.{u} (r.app K)
  /-- Every chosen scalar R object is genuinely fibrant. -/
  R_isFibrant (K : SSet.{u}) : IsFibrant (R.obj K)

namespace ScalarConventions

/-- Reuse the given complete scalar factor records without changing any factor functions. -/
def ofFactorizations
    (qData : FunctorialFactorizationData (cofibrations SSet.{u}) (trivialFibrations SSet.{u}))
    (rData : FunctorialFactorizationData (trivialCofibrations SSet.{u}) (fibrations SSet.{u})) :
    ScalarConventions.{u} where
  Q := GivenFactorizationReplacements.initialReplacement qData _ initialIsInitial
  q := GivenFactorizationReplacements.initialProjection qData _ initialIsInitial
  q_trivialFibration K := qData.hp (Arrow.mk (initial.to K))
  R := GivenFactorizationReplacements.terminalReplacement rData _ terminalIsTerminal
  r := GivenFactorizationReplacements.terminalUnit rData _ terminalIsTerminal
  r_trivialCofibration K := rData.hi (Arrow.mk (terminal.from K))
  R_isFibrant K := GivenFactorizationReplacements.terminalReplacement_isFibrant
    SSet.modelCategoryQuillen.modelCategory rData _ terminalIsTerminal K

/-- The existing selected boundary and horn factor records give one scalar convention. -/
def standard : ScalarConventions.{u} :=
  ofFactorizations (functorialFactorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u}))
    (functorialFactorizationData (trivialCofibrations SSet.{u}) (fibrations SSet.{u}))

end ScalarConventions

private theorem scalarPre_weak {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) (Z : SSet.{u}) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences ((pre f).app Z) := by
  let _ : IsFibrant Z := hZ
  exact (weakEquivalence_iff _).mp
    (weakEquivalence_pre_app_of_cofibrant f ((weakEquivalence_iff f).mpr hf))

private theorem scalarPost_weak (A : SSet.{u}) {Y Z : SSet.{u}} (g : Y ⟶ Z)
    (hg : SSet.realizationWeakEquivalences g) (hY : IsFibrant Y) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences ((ihom A).map g) := by
  let _ : IsFibrant Y := hY
  let _ : IsFibrant Z := hZ
  let _ : WeakEquivalence g := (weakEquivalence_iff g).mpr hg
  exact (weakEquivalence_iff _).mp
    ((IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
      (C := SSet.{u})).ihom_weakEquivalence_of_fibrant A g)

variable {D : Type w} [Category.{v} D]

/-- Raw scalar Hom with its original contravariant and covariant functor actions. -/
def mapping (Q : SSet.{u} ⥤ SSet.{u}) (R : SimplicialPresheaf.{u} D ⥤ SSet.{u}) :
    SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  Q.op ⋙ MonoidalClosed.internalHom ⋙
    (Functor.whiskeringLeft (SimplicialPresheaf.{u} D) SSet.{u} SSet.{u}).obj R

/-- Precomposition by a natural source projection, with both variances retained. -/
def preLeg {P Q : SSet.{u} ⥤ SSet.{u}} (p : P ⟶ Q)
    (R : SimplicialPresheaf.{u} D ⥤ SSet.{u}) : mapping Q R ⟶ mapping P R :=
  Functor.whiskerRight (Functor.whiskerRight (NatTrans.op p) MonoidalClosed.internalHom)
    ((Functor.whiskeringLeft (SimplicialPresheaf.{u} D) SSet.{u} SSet.{u}).obj R)

/-- Postcomposition by a natural target inclusion, with both variances retained. -/
def postLeg (Q : SSet.{u} ⥤ SSet.{u})
    {R T : SimplicialPresheaf.{u} D ⥤ SSet.{u}} (r : R ⟶ T) : mapping Q R ⟶ mapping Q T :=
  Functor.whiskerLeft (Q.op ⋙ MonoidalClosed.internalHom)
    ((Functor.whiskeringLeft (SimplicialPresheaf.{u} D) SSet.{u} SSet.{u}).map r)

/-- A source leg is exactly precomposition by its actual scalar projection. -/
theorem preLeg_app {P Q : SSet.{u} ⥤ SSet.{u}} (p : P ⟶ Q)
    (R : SimplicialPresheaf.{u} D ⥤ SSet.{u}) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((preLeg p R).app (op K)).app C = (pre (p.app K)).app (R.obj C) := rfl

/-- A target leg is exactly postcomposition by its actual scalar inclusion. -/
theorem postLeg_app (Q : SSet.{u} ⥤ SSet.{u})
    {R T : SimplicialPresheaf.{u} D ⥤ SSet.{u}} (r : R ⟶ T)
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((postLeg Q r).app (op K)).app C = (ihom (Q.obj K)).map (r.app C) := rfl

variable [Small.{u} D] [LocallySmall.{u} D] {I : Type i} [Small.{u} I]

/-- The common scalar source is the literal pullback of the two actual Q counits. -/
def commonSource (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj K := pullback ((TransferredCoreReplacements.qCounit S z).app K) (e.q.app K)
  map {K L} k := pullback.map _ _ _ _
    ((TransferredCoreReplacements.qReplacement S z).map k) (e.Q.map k) k
    ((TransferredCoreReplacements.qCounit S z).naturality k).symm (e.q.naturality k).symm
  map_id K := by
    apply pullback.hom_ext <;> simp
  map_comp k l := by
    apply pullback.hom_ext <;> simp [Category.assoc]

/-- The prescribed left source projection. -/
def sourceLeft (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : commonSource S z e ⟶ TransferredCoreReplacements.qReplacement S z where
  app K := pullback.fst _ _
  naturality K L k := by
    dsimp only [commonSource]
    simp only [pullback.lift_fst]

/-- The prescribed right source projection. -/
def sourceRight (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : commonSource S z e ⟶ e.Q where
  app K := pullback.snd _ _
  naturality K L k := by
    dsimp only [commonSource]
    simp only [pullback.lift_snd]

/-- Both source projections preserve the same actual map to K. -/
theorem commonSource_square (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) :
    (sourceLeft S z e).app K ≫ (TransferredCoreReplacements.qCounit S z).app K =
      (sourceRight S z e).app K ≫ e.q.app K := pullback.condition

/-- The left projection is a pullback of the independently fixed scalar trivial fibration. -/
theorem sourceLeft_trivialFibration (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) :
    trivialFibrations SSet.{u} ((sourceLeft S z e).app K) :=
  (trivialFibrations SSet.{u}).pullback_fst _ _ (e.q_trivialFibration K)

/-- The right projection is a pullback of the transferred scalar trivial fibration. -/
theorem sourceRight_trivialFibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e : ScalarConventions.{u}) (K : SSet.{u}) :
    trivialFibrations SSet.{u} ((sourceRight S z e).app K) :=
  (trivialFibrations SSet.{u}).pullback_snd _ _
    (TransferredCoreReplacements.qCounit_trivialFibration S hz K)

/-- The independently fixed scalar R acts on the actual evaluated C. -/
def fixedTarget (z : D) (e : ScalarConventions.{u}) : SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  ConstantEvaluation.evaluation z ⋙ e.R

/-- The scalar unit is applied to the same actual evaluated C. -/
def fixedUnit (z : D) (e : ScalarConventions.{u}) :
    ConstantEvaluation.evaluation z ⟶ fixedTarget z e :=
  Functor.whiskerLeft (ConstantEvaluation.evaluation z) e.r

/-- The target pushout uses the two prescribed units from the same evaluated C. -/
def targetPushout (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : SimplicialPresheaf.{u} D ⥤ SSet.{u} where
  obj C := pushout ((TransferredCoreReplacements.rUnit S z).app C) ((fixedUnit z e).app C)
  map {C C'} f := pushout.map _ _ _ _
    ((TransferredCoreReplacements.rReplacement S z).map f) ((fixedTarget z e).map f)
    ((ConstantEvaluation.evaluation z).map f)
    ((TransferredCoreReplacements.rUnit S z).naturality f).symm
    ((fixedUnit z e).naturality f).symm
  map_id C := by
    apply pushout.hom_ext <;> simp
  map_comp f g := by
    apply pushout.hom_ext <;> simp [Category.assoc]

/-- Apply the same independently fixed scalar R to that actual pushout. -/
def commonTarget (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  targetPushout S z e ⋙ e.R

/-- The prescribed inclusion from the transferred target into the actual pushout. -/
def targetInclusionLeft (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : TransferredCoreReplacements.rReplacement S z ⟶ targetPushout S z e where
  app C := pushout.inl _ _
  naturality C C' f := by
    dsimp only [targetPushout]
    simp only [pushout.inl_desc]

/-- The prescribed inclusion from the fixed scalar target into the actual pushout. -/
def targetInclusionRight (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : fixedTarget z e ⟶ targetPushout S z e where
  app C := pushout.inr _ _
  naturality C C' f := by
    dsimp only [targetPushout]
    simp only [pushout.inr_desc]

/-- The same scalar replacement unit on the entire target-pushout functor. -/
def targetReplacementUnit (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : targetPushout S z e ⟶ commonTarget S z e :=
  Functor.whiskerLeft (targetPushout S z e) e.r

/-- The actual left target inclusion followed by the same scalar replacement unit. -/
def targetLeft (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : TransferredCoreReplacements.rReplacement S z ⟶ commonTarget S z e :=
  targetInclusionLeft S z e ≫ targetReplacementUnit S z e

/-- The actual right target inclusion followed by the same scalar replacement unit. -/
def targetRight (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : fixedTarget z e ⟶ commonTarget S z e :=
  targetInclusionRight S z e ≫ targetReplacementUnit S z e

/-- Both target legs extend the same actual map from the evaluated C. -/
theorem commonTarget_square (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (C : SimplicialPresheaf.{u} D) :
    (TransferredCoreReplacements.rUnit S z).app C ≫ (targetLeft S z e).app C =
      (fixedUnit z e).app C ≫ (targetRight S z e).app C := by
  exact pushout.condition_assoc
    (f := (TransferredCoreReplacements.rUnit S z).app C) (g := (fixedUnit z e).app C)
    (e.r.app ((targetPushout S z e).obj C))

/-- The left target leg is trivial-cofibrational by cobase change of the fixed scalar unit. -/
theorem targetLeft_trivialCofibration (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (C : SimplicialPresheaf.{u} D) :
    trivialCofibrations SSet.{u} ((targetLeft S z e).app C) :=
  (trivialCofibrations SSet.{u}).comp_mem _ _
    ((trivialCofibrations SSet.{u}).pushout_inl _ _ (e.r_trivialCofibration (C.obj (op z))))
    (e.r_trivialCofibration _)

/-- At a genuinely local-fibrant C, the right target leg is also trivial-cofibrational. -/
theorem targetRight_trivialCofibration (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    trivialCofibrations SSet.{u} ((targetRight S z e).app C) :=
  (trivialCofibrations SSet.{u}).comp_mem _ _
    ((trivialCofibrations SSet.{u}).pushout_inr _ _
      (TransferredCoreReplacements.rUnit_trivialCofibration S z C hC))
    (e.r_trivialCofibration _)

/-- The common target is genuinely fibrant by the same fixed scalar R convention. -/
theorem commonTarget_isFibrant (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (C : SimplicialPresheaf.{u} D) :
    IsFibrant ((commonTarget S z e).obj C) := e.R_isFibrant _

/-- The transferred scalar mapping presentation, with its original Q prime and R prime. -/
def transferredMapping (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) : SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  mapping (TransferredCoreReplacements.qReplacement S z)
    (TransferredCoreReplacements.rReplacement S z)

/-- The mapping presentation for the independently fixed scalar conventions. -/
def fixedMapping (z : D) (e : ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  mapping e.Q (fixedTarget z e)

/-- The transferred target with the actual common pullback source. -/
def transferredMiddle (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  mapping (commonSource S z e) (TransferredCoreReplacements.rReplacement S z)

/-- The fixed scalar target with the same actual common pullback source. -/
def fixedMiddle (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  mapping (commonSource S z e) (fixedTarget z e)

/-- The common mapping presentation uses the actual P and replaced pushout T. -/
def commonMapping (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  mapping (commonSource S z e) (commonTarget S z e)

/-- The first leg precomposes the transferred mapping object by the actual left projection. -/
def transferredPre (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : transferredMapping S z ⟶ transferredMiddle S z e :=
  preLeg (sourceLeft S z e) (TransferredCoreReplacements.rReplacement S z)

/-- The fixed-side first leg precomposes by the actual right projection. -/
def fixedPre (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : fixedMapping z e ⟶ fixedMiddle S z e :=
  preLeg (sourceRight S z e) (fixedTarget z e)

/-- The transferred-side second leg postcomposes by its actual inclusion into T. -/
def transferredPost (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : transferredMiddle S z e ⟶ commonMapping S z e :=
  postLeg (commonSource S z e) (targetLeft S z e)

/-- The fixed-side second leg postcomposes by its actual inclusion into the same T. -/
def fixedPost (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : fixedMiddle S z e ⟶ commonMapping S z e :=
  postLeg (commonSource S z e) (targetRight S z e)

/-- The transferred endpoint is exactly the earlier transferred mapping model. -/
theorem transferredMapping_obj (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((transferredMapping S z).obj (op K)).obj C =
      TransferredCoreReplacements.mappingModel S z K C := rfl

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The fixed endpoint retains exactly the independently chosen scalar Q and R objects. -/
theorem fixedMapping_obj (z : D) (e : ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    ((fixedMapping z e).obj (op K)).obj C = (ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z))) := rfl

/-- The transferred source leg is the prescribed raw precomposition map. -/
theorem transferredPre_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((transferredPre S z e).app (op K)).app C =
      (pre ((sourceLeft S z e).app K)).app ((TransferredCoreReplacements.rReplacement S z).obj C) := rfl

/-- The fixed source leg is the prescribed raw precomposition map. -/
theorem fixedPre_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((fixedPre S z e).app (op K)).app C =
      (pre ((sourceRight S z e).app K)).app (e.R.obj (C.obj (op z))) := rfl

/-- The transferred target leg is the prescribed raw postcomposition map. -/
theorem transferredPost_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((transferredPost S z e).app (op K)).app C =
      (ihom ((commonSource S z e).obj K)).map ((targetLeft S z e).app C) := rfl

/-- The fixed target leg is the prescribed raw postcomposition map. -/
theorem fixedPost_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    ((fixedPost S z e).app (op K)).app C =
      (ihom ((commonSource S z e).obj K)).map ((targetRight S z e).app C) := rfl

/-- The named transferredPre square for contravariant scalar-source maps. -/
theorem transferredPre_source_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) {K L : SSet.{u}} (k : K ⟶ L)
    (C : SimplicialPresheaf.{u} D) :
    ((transferredMapping S z).map k.op).app C ≫ ((transferredPre S z e).app (op K)).app C =
      ((transferredPre S z e).app (op L)).app C ≫ ((transferredMiddle S z e).map k.op).app C := by
  exact congrArg (fun t => t.app C) ((transferredPre S z e).naturality k.op)

/-- The named transferredPre square for covariant original-target maps. -/
theorem transferredPre_target_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    ((transferredMapping S z).obj (op K)).map f ≫ ((transferredPre S z e).app (op K)).app C' =
      ((transferredPre S z e).app (op K)).app C ≫ ((transferredMiddle S z e).obj (op K)).map f :=
  ((transferredPre S z e).app (op K)).naturality f

/-- The named fixedPre square for contravariant scalar-source maps. -/
theorem fixedPre_source_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) {K L : SSet.{u}} (k : K ⟶ L)
    (C : SimplicialPresheaf.{u} D) :
    ((fixedMapping z e).map k.op).app C ≫ ((fixedPre S z e).app (op K)).app C =
      ((fixedPre S z e).app (op L)).app C ≫ ((fixedMiddle S z e).map k.op).app C := by
  exact congrArg (fun t => t.app C) ((fixedPre S z e).naturality k.op)

/-- The named fixedPre square for covariant original-target maps. -/
theorem fixedPre_target_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    ((fixedMapping z e).obj (op K)).map f ≫ ((fixedPre S z e).app (op K)).app C' =
      ((fixedPre S z e).app (op K)).app C ≫ ((fixedMiddle S z e).obj (op K)).map f :=
  ((fixedPre S z e).app (op K)).naturality f

/-- The named transferredPost square for contravariant scalar-source maps. -/
theorem transferredPost_source_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) {K L : SSet.{u}} (k : K ⟶ L)
    (C : SimplicialPresheaf.{u} D) :
    ((transferredMiddle S z e).map k.op).app C ≫ ((transferredPost S z e).app (op K)).app C =
      ((transferredPost S z e).app (op L)).app C ≫ ((commonMapping S z e).map k.op).app C := by
  exact congrArg (fun t => t.app C) ((transferredPost S z e).naturality k.op)

/-- The named transferredPost square for covariant original-target maps. -/
theorem transferredPost_target_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    ((transferredMiddle S z e).obj (op K)).map f ≫ ((transferredPost S z e).app (op K)).app C' =
      ((transferredPost S z e).app (op K)).app C ≫ ((commonMapping S z e).obj (op K)).map f :=
  ((transferredPost S z e).app (op K)).naturality f

/-- The named fixedPost square for contravariant scalar-source maps. -/
theorem fixedPost_source_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) {K L : SSet.{u}} (k : K ⟶ L)
    (C : SimplicialPresheaf.{u} D) :
    ((fixedMiddle S z e).map k.op).app C ≫ ((fixedPost S z e).app (op K)).app C =
      ((fixedPost S z e).app (op L)).app C ≫ ((commonMapping S z e).map k.op).app C := by
  exact congrArg (fun t => t.app C) ((fixedPost S z e).naturality k.op)

/-- The named fixedPost square for covariant original-target maps. -/
theorem fixedPost_target_natural (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) {C C' : SimplicialPresheaf.{u} D} (f : C ⟶ C') :
    ((fixedMiddle S z e).obj (op K)).map f ≫ ((fixedPost S z e).app (op K)).app C' =
      ((fixedPost S z e).app (op K)).app C ≫ ((commonMapping S z e).obj (op K)).map f :=
  ((fixedPost S z e).app (op K)).naturality f

/-- The first transferred leg is weak by the existing scalar source Brown theorem. -/
theorem transferredPre_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e : ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (((transferredPre S z e).app (op K)).app C) := by
  rw [transferredPre_app]
  have hR : IsFibrant ((TransferredCoreReplacements.rReplacement S z).obj C) := by
    change SSet.KanComplex _
    exact TransferredCoreReplacements.rReplacement_isKan S hz C
  exact scalarPre_weak _ (sourceLeft_trivialFibration S z e K).2 _ hR

/-- The fixed precomposition leg is weak with the independently chosen fibrant target. -/
theorem fixedPre_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e : ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (((fixedPre S z e).app (op K)).app C) := by
  rw [fixedPre_app]
  exact scalarPre_weak _ (sourceRight_trivialFibration S hz e K).2 _
    (e.R_isFibrant (C.obj (op z)))

/-- The transferred postcomposition leg is weak between its genuine fibrant endpoints. -/
theorem transferredPost_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e : ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (((transferredPost S z e).app (op K)).app C) := by
  rw [transferredPost_app]
  have hR : IsFibrant ((TransferredCoreReplacements.rReplacement S z).obj C) := by
    change SSet.KanComplex _
    exact TransferredCoreReplacements.rReplacement_isKan S hz C
  exact scalarPost_weak _ _ (targetLeft_trivialCofibration S z e C).2 hR
    (commonTarget_isFibrant S z e C)

/-- The fixed postcomposition leg is weak at an actually original local-fibrant C. -/
theorem fixedPost_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C) :
    SSet.realizationWeakEquivalences (((fixedPost S z e).app (op K)).app C) := by
  rw [fixedPost_app]
  exact scalarPost_weak _ _ (targetRight_trivialCofibration S z e C hC).2
    (e.R_isFibrant (C.obj (op z))) (commonTarget_isFibrant S z e C)

/-- Compose the two actual transferred-side natural legs. -/
def transferredToCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : transferredMapping S z ⟶ commonMapping S z e :=
  transferredPre S z e ≫ transferredPost S z e

/-- Compose the two actual fixed-side natural legs, pointing into the same common object. -/
def fixedToCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarConventions.{u}) : fixedMapping z e ⟶ commonMapping S z e :=
  fixedPre S z e ≫ fixedPost S z e

/-- The transferred side of the natural comparison cospan is weak. -/
theorem transferredToCommon_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e : ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (((transferredToCommon S z e).app (op K)).app C) :=
  SSet.realizationWeakEquivalences.comp_mem _ _ (transferredPre_weak S hz e K C)
    (transferredPost_weak S hz e K C)

/-- The fixed side is weak at a genuine original local-fibrant C, with no reverse map selected. -/
theorem fixedToCommon_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e : ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    SSet.realizationWeakEquivalences (((fixedToCommon S z e).app (op K)).app C) :=
  SSet.realizationWeakEquivalences.comp_mem _ _ (fixedPre_weak S hz e K C)
    (fixedPost_weak S z e K C hC)

end SimplicialPresheaf.ScalarCoreReplacementSpans
