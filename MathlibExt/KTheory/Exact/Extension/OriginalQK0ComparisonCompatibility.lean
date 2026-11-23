/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.BasedSplitExactQLoopComparison
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagGroupNaturality
public import MathlibExt.KTheory.Waldhausen.K0.Exact
public import MathlibExt.CategoryTheory.ExactCategory.Zero
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellNormalized
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjective
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsRealizedConull
public import MathlibExt.KTheory.Ring.K0.ProjectiveUniverseEquivalence
public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The original comparison and canonical K₀, using the existing Q/S evaluator

The two positive-generator spans are calibrated by actual degenerate
Stage-one grids. The numerator and denominator paths are the original
zero-row lifts, preceded by the original stabilization to the diagonal
pair. Contractibility of the actual localized total compares this path
with the same kappa-then-r0 contraction trace.

No Q-arrow label functor or K₀ quotient is introduced. The existing Q/S
component equivalence, exact/Waldhausen dictionary and projective resizing
are consumed directly.

Weibel, *The K-book*, Exercise IV.7.8 (printed p. 332), is the primary
source for the original generator and canonical component-map comparison.
The explicit all-pair paths and fixed-ring universe dictionary retain that
source comparison, using the already proved Q/S and resizing APIs.


-/

@[expose] public section

universe u v

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite Algebra
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.Waldhausen.SConstruction SimplexCategory
open AlgebraicKTheory.QuillenQSZigzagGroupNaturality.Internal
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial ZeroObject

namespace AlgebraicKTheory.OriginalQK0Comparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

attribute [local instance] ExactCategory.waldhausenCategory

/-- The literal mono-forward/epi-reversed loop of the two parallel zero-to-A spans. -/
def generatorLoop (A : C) : BasedSplitExactQLoop.originalQLoops (C := C) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
      (nerve.edgeMk (ExtensionCategory.zeroMonoHom A)))).trans
    (TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
        (nerve.edgeMk (ExtensionCategory.zeroEpiHom A)))).symm

private def loopComponentsCast {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) :
    ZerothHomotopy (Path x x) → ZerothHomotopy (Path y y) := by
  cases h
  exact id

private theorem loopComponentsCast_mk {X : Type*} [TopologicalSpace X] {x y : X}
    (h : x = y) (p : Path x x) :
    loopComponentsCast h (ZerothHomotopy.mk p) =
      ZerothHomotopy.mk (p.cast h.symm h.symm) := by
  cases h
  rfl

private theorem originalZero_eq_NQBase :
    OriginalQZeroComparison.zeroQVertex (C := C) = NQReal.basepoint C :=
  (NQReal.basepoint_eq_realizedVertex C).symm

/-- The already-landed Q/S evaluator, transported only across its specified zero-point equality. -/
def canonicalLoopComponentsK0 :
    ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := C)) → K0 C := by
  let qSpace : TopCat.{max u v} := SSet.toTop.obj (NQ C)
  let transfer : ∀ {x y : qSpace}, x = y →
      ZerothHomotopy (Path x x) → ZerothHomotopy (Path y y) :=
    fun {x y} h => by cases h; exact id
  have h : (OriginalQZeroComparison.zeroQVertex (C := C) : qSpace) =
      (NQReal.basepoint C : qSpace) := (NQReal.basepoint_eq_realizedVertex C).symm
  exact fun c => WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C (transfer h c))

/-- The public representative formula retains the same original loop and its values at every
time. -/
theorem canonicalLoopComponentsK0_mk (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk p) = WaldhausenKTheory.K0.toExact C
      (NQKSpacePiZeroEquivK0 C (ZerothHomotopy.mk
        (p.cast (NQReal.basepoint_eq_realizedVertex C)
            (NQReal.basepoint_eq_realizedVertex C)))) := by
  let qSpace : TopCat.{max u v} := SSet.toTop.obj (NQ C)
  have h : (OriginalQZeroComparison.zeroQVertex (C := C) : qSpace) =
      (NQReal.basepoint C : qSpace) := originalZero_eq_NQBase (C := C)
  exact congrArg (fun c : ZerothHomotopy (NQKSpace C) =>
      WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C c))
    (loopComponentsCast_mk (X := qSpace) h p)

private theorem qLeg_components_fundamental
    (c : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
        (quillenStageGridToNQPiZeroEquiv C c) =
      quillenStageGridToNQFundamentalMulEquiv C
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) c) := by
  let eQ := loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
  change eQ (eQ.symm
      (basedFundamentalGroupMap (quillenStageGridToNQWeaklyPointed (C := C)).hom
        (quillenStageGridToNQWeaklyPointed (C := C)).rootPath
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) c))) = _
  exact eQ.apply_symm_apply _

private theorem stageLeg_components_fundamental
    (c : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) (quillenStageGridToStagePiZeroEquiv C c) =
      quillenStageGridToStageFundamentalMulEquiv C
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) c) := by
  let eS := loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
    (stageWeakDiagonalReal.basepoint C)
  change eS (eS.symm
      (basedFundamentalGroupMap (quillenStageGridToStageWeaklyPointed (C := C)).hom
        (quillenStageGridToStageWeaklyPointed (C := C)).rootPath
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) c))) = _
  exact eS.apply_symm_apply _

private theorem qFacade_eq_fundamental (c : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 C c = Multiplicative.toAdd
      (NQRealizedFundamentalK0MulEquiv C
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) c)) := by
  let cG := (quillenStageGridToNQPiZeroEquiv C).symm c
  have hQ := qLeg_components_fundamental (C := C) cG
  rw [show quillenStageGridToNQPiZeroEquiv C cG = c from
    (quillenStageGridToNQPiZeroEquiv C).apply_symm_apply c] at hQ
  have hS := stageLeg_components_fundamental (C := C) cG
  change Multiplicative.toAdd (stageWeakDiagonalRealizedFundamentalK0MulEquiv C
      (loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) (quillenStageGridToStagePiZeroEquiv C cG))) =
    Multiplicative.toAdd (stageWeakDiagonalRealizedFundamentalK0MulEquiv C
      (quillenStageGridToStageFundamentalMulEquiv C
        ((quillenStageGridToNQFundamentalMulEquiv C).symm
          (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) c))))
  rw [hS, hQ, MulEquiv.symm_apply_apply]

private def canonicalFundamentalHom : FundamentalGroup (NQReal C) (NQReal.basepoint C) →*
    Multiplicative (K0 C) :=
  (WaldhausenKTheory.K0.toExact C).toMultiplicative.comp
    (NQRealizedFundamentalK0MulEquiv C).toMonoidHom

private theorem canonicalLoopComponentsK0_mk_group
    (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk p) = Multiplicative.toAdd
      (canonicalFundamentalHom (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (p.cast (NQReal.basepoint_eq_realizedVertex C)
            (NQReal.basepoint_eq_realizedVertex C))))) := by
  let pN : LoopSpace (NQReal C) (NQReal.basepoint C) :=
    p.cast (NQReal.basepoint_eq_realizedVertex C) (NQReal.basepoint_eq_realizedVertex C)
  have h₁ := canonicalLoopComponentsK0_mk (C := C) p
  have h₂ := congrArg (WaldhausenKTheory.K0.toExact C)
    (qFacade_eq_fundamental (C := C) (ZerothHomotopy.mk pN))
  have h₃ := congrArg (fun g : FundamentalGroup (NQReal C) (NQReal.basepoint C) =>
      WaldhausenKTheory.K0.toExact C (Multiplicative.toAdd (NQRealizedFundamentalK0MulEquiv C g)))
    (loopComponentsEquivFundamentalGroup_mk (X := NQReal C) (x := NQReal.basepoint C) pN)
  exact h₁.trans (h₂.trans h₃)

/-- The existing evaluator is additive on actual concatenated loops; no group structure on
components is assumed. -/
theorem canonicalLoopComponentsK0_trans
    (p q : BasedSplitExactQLoop.originalQLoops (C := C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk (p.trans q)) =
      canonicalLoopComponentsK0 (ZerothHomotopy.mk p) +
        canonicalLoopComponentsK0 (ZerothHomotopy.mk q) := by
  let h := NQReal.basepoint_eq_realizedVertex C
  let pN : LoopSpace (NQReal C) (NQReal.basepoint C) := p.cast h h
  let qN : LoopSpace (NQReal C) (NQReal.basepoint C) := q.cast h h
  let rN : LoopSpace (NQReal C) (NQReal.basepoint C) := (p.trans q).cast h h
  let gp := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk pN)
  let gq := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk qN)
  have hp : rN = pN.trans qN := Path.cast_trans p q h h h
  have hg : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rN) = gq * gp := by
    apply End.ext
    exact (congrArg Path.Homotopic.Quotient.mk hp).trans
      (Path.Homotopic.Quotient.mk_trans pN qN)
  calc
    canonicalLoopComponentsK0 (ZerothHomotopy.mk (p.trans q)) =
        Multiplicative.toAdd (canonicalFundamentalHom (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk rN))) := canonicalLoopComponentsK0_mk_group (C := C) _
    _ = Multiplicative.toAdd (canonicalFundamentalHom (gq * gp)) :=
      congrArg (fun g => Multiplicative.toAdd (canonicalFundamentalHom g)) hg
    _ = Multiplicative.toAdd (canonicalFundamentalHom gq) +
        Multiplicative.toAdd (canonicalFundamentalHom gp) :=
      congrArg Multiplicative.toAdd ((canonicalFundamentalHom (C := C)).map_mul gq gp)
    _ = canonicalLoopComponentsK0 (ZerothHomotopy.mk q) +
        canonicalLoopComponentsK0 (ZerothHomotopy.mk p) :=
      congrArg₂ (· + ·) (canonicalLoopComponentsK0_mk_group (C := C) q).symm
        (canonicalLoopComponentsK0_mk_group (C := C) p).symm
    _ = _ := add_comm _ _

/-- Reversing the literal original loop negates its canonical K₀ value. -/
theorem canonicalLoopComponentsK0_symm (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk p.symm) =
      -canonicalLoopComponentsK0 (ZerothHomotopy.mk p) := by
  let h := NQReal.basepoint_eq_realizedVertex C
  let pN : LoopSpace (NQReal C) (NQReal.basepoint C) := p.cast h h
  let rN : LoopSpace (NQReal C) (NQReal.basepoint C) := p.symm.cast h h
  let gp := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk pN)
  have hp : rN = pN.symm := Path.cast_symm p h h
  have hg : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rN) = gp⁻¹ := by
    apply End.ext
    exact (congrArg Path.Homotopic.Quotient.mk hp).trans (Path.Homotopic.Quotient.mk_symm pN)
  calc
    canonicalLoopComponentsK0 (ZerothHomotopy.mk p.symm) =
        Multiplicative.toAdd (canonicalFundamentalHom (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk rN))) := canonicalLoopComponentsK0_mk_group (C := C) _
    _ = Multiplicative.toAdd (canonicalFundamentalHom (gp⁻¹)) :=
      congrArg (fun g => Multiplicative.toAdd (canonicalFundamentalHom g)) hg
    _ = -Multiplicative.toAdd (canonicalFundamentalHom gp) :=
      congrArg Multiplicative.toAdd (map_inv (canonicalFundamentalHom (C := C)) gp)
    _ = _ := congrArg Neg.neg (canonicalLoopComponentsK0_mk_group (C := C) p).symm

/-- The actual constant loop has canonical value zero. -/
theorem canonicalLoopComponentsK0_refl :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk
      (Path.refl (OriginalQZeroComparison.zeroQVertex (C := C)))) = 0 := by
  let p := Path.refl (OriginalQZeroComparison.zeroQVertex (C := C))
  let h := NQReal.basepoint_eq_realizedVertex C
  let pN : LoopSpace (NQReal C) (NQReal.basepoint C) := p.cast h h
  have hp : pN = Path.refl (NQReal.basepoint C) := by
    apply Path.ext
    funext t
    exact originalZero_eq_NQBase (C := C)
  have hg : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk pN) =
      (1 : FundamentalGroup (NQReal C) (NQReal.basepoint C)) := by
    apply End.ext
    exact congrArg Path.Homotopic.Quotient.mk hp
  have hv := congrArg (fun g : FundamentalGroup (NQReal C) (NQReal.basepoint C) =>
      Multiplicative.toAdd (canonicalFundamentalHom g)) hg
  exact (canonicalLoopComponentsK0_mk_group (C := C) p).trans
    (hv.trans (congrArg Multiplicative.toAdd (canonicalFundamentalHom (C := C)).map_one))

private def stageCut (top : Bool) : edgewiseQ.obj ⦋1⦌ ⟶ ⦋1⦌ :=
  if top then (SimplexCategory.σ 2 : ⦋3⦌ ⟶ ⦋2⦌) ≫ SimplexCategory.σ 1
  else (SimplexCategory.σ 0 : ⦋3⦌ ⟶ ⦋2⦌) ≫ SimplexCategory.σ 0

private def zeroWeakOne : StageWeakCategory C 1 :=
  ⟨⟨zeroDiagram C 1, isStage_zeroDiagram C 1⟩⟩

private def generatorWeakThree (A : C) (top : Bool) :
    StageWeakCategory C (edgewiseQ.obj ⦋1⦌).len :=
  (reindexStageWeak C (stageCut top)).obj (stageOneWeakObj C A)

private theorem weakOne_reindex_constant (A : C) (f : ⦋1⦌ ⟶ ⦋1⦌)
    (k : Fin 2) (hf : ∀ i : Fin 2, f.toOrderHom i = k) :
    (reindexStageWeak C f).obj (stageOneWeakObj C A) = zeroWeakOne (C := C) := by
  ext
  let F : Ar 1 ⥤ C := ((reindexStageWeak C f).obj (stageOneWeakObj C A)).obj.obj
  have hObj : ∀ J : Ar 1, F.obj J = (0 : C) := by
    intro J
    obtain ⟨i, j, h, rfl⟩ := Arrow.mk_surjective J
    have hj : (indexFunctor f).obj (Arrow.mk h) =
        _root_.CategoryTheory.Waldhausen.SConstruction.diag k := by
      apply Arrow.ext (hf i) (hf j)
      exact Subsingleton.elim _ _
    exact (congrArg ((stageOne C).obj A).obj.obj hj).trans (stageOne_obj_diag C A k)
  exact CategoryTheory.Functor.ext hObj (fun J K g =>
    ((hObj J).symm ▸ isZero_zero C).eq_of_src _ _)

private theorem generatorWeakThree_source (A : C) (top : Bool) :
    (edgewiseStageWeakReindex (C := C) (SimplexCategory.δ (1 : Fin 2))).obj
        (generatorWeakThree A top) = zeroWeakOne (C := C) := by
  have hf := reindexStageWeak_comp C
    (edgewiseQ.map (SimplexCategory.δ (1 : Fin 2))) (stageCut top)
  have he := CategoryTheory.Functor.congr_obj hf (stageOneWeakObj C A)
  exact he.symm.trans (weakOne_reindex_constant A _ (if top then 1 else 0)
    (by intro i; cases top <;> fin_cases i <;> rfl))

private theorem generatorWeakThree_target (A : C) (top : Bool) :
    (edgewiseStageWeakReindex (C := C) (SimplexCategory.δ (0 : Fin 2))).obj
        (generatorWeakThree A top) = stageOneWeakObj C A := by
  have hf : edgewiseQ.map (SimplexCategory.δ (0 : Fin 2)) ≫ stageCut top = 𝟙 ⦋1⦌ := by
    cases top <;> ext i <;> fin_cases i <;> rfl
  have he := CategoryTheory.Functor.congr_obj
    (reindexStageWeak_comp C (edgewiseQ.map (SimplexCategory.δ (0 : Fin 2))) (stageCut top))
    (stageOneWeakObj C A)
  have hMap := congrArg (fun f : ⦋1⦌ ⟶ ⦋1⦌ =>
      (reindexStageWeak C (a := ⦋1⦌) (b := ⦋1⦌) f).obj (stageOneWeakObj C A)) hf
  have hId := CategoryTheory.Functor.congr_obj (reindexStageWeak_id C ⦋1⦌) (stageOneWeakObj C A)
  exact he.symm.trans (hMap.trans hId)

private theorem ofGrid_reindex {a b : SimplexCategory} (f : a ⟶ b)
    (A : StageWeakCategory C (edgewiseQ.obj b).len) :
    (reindexQuillenStageGridLift (C := C) f).obj (QuillenStageGridLift.ofGrid A) =
      QuillenStageGridLift.ofGrid ((edgewiseStageWeakReindex (C := C) f).obj A) := by
  apply ObjectProperty.FullSubcategory.ext
  change ({
    left := (edgewiseStageWeakReindex (C := C) f).obj A
    right := (quillenQSimplexDiscreteReindex (C := C) f).obj
      (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A))
    hom := (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex (C := C) f)).app A ≫
      (edgewiseQuillenSimplexReindex (C := C) f).map (𝟙 _) ≫
      (eqToHom (quillenQSimplexDiscreteInclusion_reindex (C := C) f)).app _ } :
    QuillenStageGridAgreement C a) = _
  rw [Comma.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · apply Discrete.ext
    exact (CategoryTheory.Functor.congr_obj
      (edgewiseStageQuillenSimplexFunctor_reindex (C := C) f) A).symm
  · let V : QuillenQSimplex C a := (edgewiseStageQuillenSimplexFunctor C a).obj
        ((edgewiseStageWeakReindex (C := C) f).obj A)
    let U : QuillenQSimplex C a := (edgewiseQuillenSimplexReindex (C := C) f).obj
      ((edgewiseStageQuillenSimplexFunctor C b).obj A)
    let W : QuillenQSimplex C a := (quillenQSimplexDiscreteInclusion C a).obj
      ((quillenQSimplexDiscreteReindex (C := C) f).obj
        (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A)))
    let hVU : V = U := CategoryTheory.Functor.congr_obj
      (edgewiseStageQuillenSimplexFunctor_reindex (C := C) f) A
    let hUW : U = W := CategoryTheory.Functor.congr_obj
      (quillenQSimplexDiscreteInclusion_reindex (C := C) f)
      (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A))
    have hLeft : (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex (C := C) f)).app A =
        eqToHom hVU := eqToHom_app _ _
    have hRight : (eqToHom (quillenQSimplexDiscreteInclusion_reindex (C := C) f)).app
        (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A)) =
          eqToHom hUW := eqToHom_app _ _
    have hId := (edgewiseQuillenSimplexReindex (C := C) f).map_id
      ((edgewiseStageQuillenSimplexFunctor C b).obj A)
    have hComp : (eqToHom (edgewiseStageQuillenSimplexFunctor_reindex (C := C) f)).app A ≫
        (edgewiseQuillenSimplexReindex (C := C) f).map (𝟙 _) ≫
        (eqToHom (quillenQSimplexDiscreteInclusion_reindex (C := C) f)).app
          (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A)) =
          eqToHom (hVU.trans hUW) := by
      calc
        _ = eqToHom hVU ≫ (𝟙 U) ≫ eqToHom hUW :=
          (congrArg (fun l : V ⟶ U => l ≫
            (edgewiseQuillenSimplexReindex (C := C) f).map (𝟙 _) ≫
            (eqToHom (quillenQSimplexDiscreteInclusion_reindex (C := C) f)).app
              (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A))) hLeft).trans
            ((congrArg (fun m : U ⟶ U => eqToHom hVU ≫ m ≫
              (eqToHom (quillenQSimplexDiscreteInclusion_reindex (C := C) f)).app
                (Discrete.mk ((edgewiseStageQuillenSimplexFunctor C b).obj A))) hId).trans
              (congrArg (fun r : U ⟶ W => eqToHom hVU ≫ (𝟙 U) ≫ r) hRight))
        _ = eqToHom hVU ≫ eqToHom hUW :=
          congrArg (fun r : U ⟶ W => eqToHom hVU ≫ r) (Category.id_comp (eqToHom hUW))
        _ = _ := eqToHom_trans hVU hUW
    let T := QuillenStageGridLift.ofGrid (C := C) (a := a)
      ((edgewiseStageWeakReindex (C := C) f).obj A)
    have hTarget : T.obj.hom = 𝟙 V :=
      (QuillenStageGridLift.agreementIso_hom T).symm.trans
        (QuillenStageGridLift.ofGrid_agreementIso_hom (C := C) (a := a)
          ((edgewiseStageWeakReindex (C := C) f).obj A))
    exact hComp.heq.trans ((eqToHom_heq_id_dom V W (hVU.trans hUW)).trans hTarget.symm.heq)

private theorem gridIdentity_face (X : QuillenStageGridLift C ⦋1⦌) (i : Fin 2) :
    (quillenStageGridDiagonal C).δ i (ComposableArrows.mk₁ (𝟙 X)) =
      ComposableArrows.mk₀
          ((reindexQuillenStageGridLift (C := C) (SimplexCategory.δ i)).obj X) := by
  have h : ((nerve (QuillenStageGridLift C ⦋1⦌)).map (SimplexCategory.δ i).op)
      (ComposableArrows.mk₁ (𝟙 X)) = ComposableArrows.mk₀ X := by
    apply ComposableArrows.ext₀
    fin_cases i <;> rfl
  change (nerveMap (reindexQuillenStageGridLift (C := C) (SimplexCategory.δ i))).app _
    (((nerve (QuillenStageGridLift C ⦋1⦌)).map (SimplexCategory.δ i).op)
      (ComposableArrows.mk₁ (𝟙 X))) = _
  rw [h, nerveMap_app_mk₀]

private def generatorGridVertex (A : C) : (quillenStageGridDiagonal C) _⦋0⦌ :=
  ComposableArrows.mk₀ (QuillenStageGridLift.ofGrid (stageOneWeakObj C A))

private def generatorGridEdge (A : C) (top : Bool) : (quillenStageGridDiagonal C).Edge
    (quillenStageGridDiagonalZeroVertex (C := C)) (generatorGridVertex A) := by
  let B := generatorWeakThree (C := C) A top
  let X := QuillenStageGridLift.ofGrid (C := C) (a := ⦋1⦌) B
  refine SSet.Edge.mk (X := quillenStageGridDiagonal C) (ComposableArrows.mk₁ (𝟙 X)) ?_ ?_
  · have h₁ := gridIdentity_face (C := C) X (1 : Fin 2)
    have h₂ := ofGrid_reindex (C := C) (SimplexCategory.δ (1 : Fin 2)) B
    have h₃ := generatorWeakThree_source (C := C) A top
    exact h₁.trans (congrArg ComposableArrows.mk₀
      (h₂.trans (congrArg (QuillenStageGridLift.ofGrid (C := C) (a := ⦋0⦌)) h₃)))
  · have h₁ := gridIdentity_face (C := C) X (0 : Fin 2)
    have h₂ := ofGrid_reindex (C := C) (SimplexCategory.δ (0 : Fin 2)) B
    have h₃ := generatorWeakThree_target (C := C) A top
    exact h₁.trans (congrArg ComposableArrows.mk₀
      (h₂.trans (congrArg (QuillenStageGridLift.ofGrid (C := C) (a := ⦋0⦌)) h₃)))

private def generatorGridLoop (A : C) : quillenStageGridDiagonalKSpace C :=
  (TopCat.pathEquiv (SSet.realizedEdgePath (X := quillenStageGridDiagonal C)
      (generatorGridEdge A false))).trans
    (TopCat.pathEquiv (SSet.realizedEdgePath (X := quillenStageGridDiagonal C)
        (generatorGridEdge A true))).symm

private def zeroSpan (A : C) (top : Bool) : QuillenSpan (0 : C) A :=
  if top then ExtensionCategory.zeroEpiSpan A else ExtensionCategory.zeroMonoSpan A

private def zeroArrow (A : C) (top : Bool) : (⟨0⟩ : QuillenQ C) ⟶ ⟨A⟩ :=
  if top then ExtensionCategory.zeroEpiHom A else ExtensionCategory.zeroMonoHom A

private theorem generatorStage_source_value (A : C) (top : Bool) :
    edgewiseStageVertex (generatorWeakThree A top).obj (0 : Fin 2) = (0 : C) := by
  change ((stageOne C).obj A).obj.obj
    ((indexFunctor (stageCut top)).obj
      (interval (edgewiseLeftIndex ⦋1⦌ (0 : Fin 2)) (edgewiseRightIndex ⦋1⦌ (0 : Fin 2))
          (edgewiseStageVertex_le ⦋1⦌ (0 : Fin 2)))) = (0 : C)
  let k : Fin 2 := if top then 1 else 0
  have hj : (indexFunctor (stageCut top)).obj
      (interval (edgewiseLeftIndex ⦋1⦌ (0 : Fin 2)) (edgewiseRightIndex ⦋1⦌ (0 : Fin 2))
          (edgewiseStageVertex_le ⦋1⦌ (0 : Fin 2))) =
          _root_.CategoryTheory.Waldhausen.SConstruction.diag k := by
    cases top <;> apply Arrow.ext <;>
      rfl
  exact (congrArg ((stageOne C).obj A).obj.obj hj).trans (stageOne_obj_diag C A k)

private theorem generatorStage_target_value (A : C) (top : Bool) :
    edgewiseStageVertex (generatorWeakThree A top).obj (1 : Fin 2) = A := by
  change ((stageOne C).obj A).obj.obj
    ((indexFunctor (stageCut top)).obj
      (interval (edgewiseLeftIndex ⦋1⦌ (1 : Fin 2)) (edgewiseRightIndex ⦋1⦌ (1 : Fin 2))
          (edgewiseStageVertex_le ⦋1⦌ (1 : Fin 2)))) = A
  have hj : (indexFunctor (stageCut top)).obj
      (interval (edgewiseLeftIndex ⦋1⦌ (1 : Fin 2)) (edgewiseRightIndex ⦋1⦌ (1 : Fin 2))
          (edgewiseStageVertex_le ⦋1⦌ (1 : Fin 2))) =
      interval (0 : Fin 2) 1 (by decide) := by
    cases top <;> apply Arrow.ext <;>
      rfl
  exact (congrArg ((stageOne C).obj A).obj.obj hj).trans
    (stageOne_obj_interval_zero_one C A (by decide))

private theorem generatorStage_apex_value (A : C) (top : Bool) :
    (edgewiseStageShellSpanNormalized (generatorWeakThree A top).obj
      (0 : Fin 2) 1 (by decide)).apex = (zeroSpan A top).apex := by
  let B := (generatorWeakThree (C := C) A top).obj
  have h := edgewiseStageShellSpanNormalized_apex (C := C) B (0 : Fin 2) 1 (by decide)
  refine h.trans ?_
  change ((stageOne C).obj A).obj.obj
    ((indexFunctor (stageCut top)).obj (interval (0 : Fin 4) 2 (by decide))) = (zeroSpan A top).apex
  cases top
  · have hj : (indexFunctor (stageCut false)).obj (interval (0 : Fin 4) 2 (by decide)) =
      _root_.CategoryTheory.Waldhausen.SConstruction.diag (0 : Fin 2) := by
      apply Arrow.ext rfl rfl
      exact Subsingleton.elim _ _
    exact (congrArg ((stageOne C).obj A).obj.obj hj).trans (stageOne_obj_diag C A 0)
  · have hj : (indexFunctor (stageCut true)).obj (interval (0 : Fin 4) 2 (by decide)) =
        interval (0 : Fin 2) 1 (by decide) := by
      apply Arrow.ext rfl rfl
      exact Subsingleton.elim _ _
    exact (congrArg ((stageOne C).obj A).obj.obj hj).trans
      (stageOne_obj_interval_zero_one C A (by decide))

private theorem underlyingEqIso_hom {X Y : C} (h : X = Y) :
    (QuillenQ.underlyingIso (eqToIso h)).hom =
      eqToHom (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C)) h) := by
  cases h
  exact congrArg Iso.hom (QuillenQ.underlyingIso_refl X)

private theorem generatorStage_span_square (A : C) (top : Bool) :
    edgewiseStageShellClassNormalized (generatorWeakThree A top).obj
        (0 : Fin 2) 1 (by decide) ≫
      eqToHom (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C))
        (generatorStage_target_value A top)) =
    eqToHom (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C))
        (generatorStage_source_value A top)) ≫ zeroArrow A top := by
  let S := edgewiseStageShellSpanNormalized (generatorWeakThree A top).obj
    (0 : Fin 2) 1 (by decide)
  let T := zeroSpan A top
  let eX := eqToIso (generatorStage_source_value A top)
  let eY := eqToIso (generatorStage_target_value A top)
  have hSpan : ∃ eA : S.apex ≅ T.apex,
      eA.hom ≫ T.l = S.l ≫ eX.hom ∧ eA.hom ≫ T.r = S.r ≫ eY.hom := by
    cases top
    · let eA := eqToIso (generatorStage_apex_value A false)
      have hz : IsZero S.apex := (generatorStage_apex_value A false).symm ▸ isZero_zero C
      exact ⟨eA, (isZero_zero C).eq_of_tgt _ _, hz.eq_of_src _ _⟩
    · let D := edgewiseStageShellPacket (generatorWeakThree (C := C) A true).obj
        (0 : Fin 2) 1 (by decide)
      let E : ShortComplex C := ShortComplex.mk D.span.r D.flag.quotientπ
        D.flag.right_quotient_zero
      have hE : IsAdmissibleExact E := D.flag.apex_target_quotient_exact
      have hZero : D.flag.quotientObj = (0 : C) := by
        change ((stageOne C).obj A).obj.obj
          ((indexFunctor (stageCut true)).obj
            ((indexFunctor (edgewiseShell ⦋1⦌ (0 : Fin 2) 1 (by decide))).obj
              (interval (2 : Fin 4) 3 (by decide)))) = (0 : C)
        have hj : (indexFunctor (stageCut true)).obj
            ((indexFunctor (edgewiseShell ⦋1⦌ (0 : Fin 2) 1 (by decide))).obj
              (interval (2 : Fin 4) 3 (by decide))) =
                  _root_.CategoryTheory.Waldhausen.SConstruction.diag (1 : Fin 2) := by
          apply Arrow.ext rfl rfl
          exact Subsingleton.elim _ _
        exact (congrArg ((stageOne C).obj A).obj.obj hj).trans (stageOne_obj_diag C A 1)
      have hZeroE : IsZero E.X₃ := by
        change IsZero D.flag.quotientObj
        exact hZero.symm ▸ isZero_zero C
      let : IsIso D.span.r := isIso_f_of_isAdmissibleExact_of_isZero hE hZeroE
      let : IsIso S.r := by
        change IsIso (D.span.r ≫
          (eqToIso (edgewiseStageShellTargetEqVertex (generatorWeakThree A true).obj
            (0 : Fin 2) 1 (by decide))).hom)
        infer_instance
      let eA : S.apex ≅ T.apex := (asIso S.r).trans eY
      refine ⟨eA, (isZero_zero C).eq_of_tgt _ _, ?_⟩
      change (S.r ≫ eY.hom) ≫ (𝟙 A) = S.r ≫ eY.hom
      exact Category.comp_id _
  obtain ⟨eA, hl, hr⟩ := hSpan
  have hn := QuillenQ.mkHom_naturality_of_span_iso S T eX eY eA hl hr
  have hs : QuillenQ.mkHom S = edgewiseStageShellClassNormalized
      (generatorWeakThree A top).obj (0 : Fin 2) 1 (by decide) :=
    edgewiseStageShellSpanNormalized_mkHom (generatorWeakThree A top).obj
      (0 : Fin 2) 1 (by decide)
  have ht : QuillenQ.mkHom T = zeroArrow A top := by cases top <;> rfl
  have hx := underlyingEqIso_hom (generatorStage_source_value A top)
  have hy := underlyingEqIso_hom (generatorStage_target_value A top)
  exact (congrArg (fun f => f ≫ eqToHom (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C))
      (generatorStage_target_value A top))) hs.symm).trans
    ((congrArg (fun f => QuillenQ.mkHom S ≫ f) hy.symm).trans
      (hn.trans (congrArg₂ (fun f g => f ≫ g) hx ht)))

private theorem generatorGrid_q (A : C) (top : Bool) :
    (QuillenStageGridLift.ofGrid (generatorWeakThree A top)).q =
      ComposableArrows.mk₁ (zeroArrow A top) := by
  refine ComposableArrows.ext₁
    (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C)) (generatorStage_source_value A top))
    (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C)) (generatorStage_target_value A top)) ?_
  have h := generatorStage_span_square (C := C) A top
  have h' := congrArg (fun f => f ≫ eqToHom
    (congrArg (fun Z : C => (⟨Z⟩ : QuillenQ C)) (generatorStage_target_value A top)).symm) h
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using! h'

private theorem generatorGrid_Q_edge (A : C) (top : Bool) :
    ((generatorGridEdge A top).map (quillenStageGridToNQ (C := C))).edge =
      ComposableArrows.mk₁ (zeroArrow A top) := by
  let G := QuillenStageGridLift.ofGrid (C := C) (a := ⦋1⦌) (generatorWeakThree (C := C) A top)
  change (SSet.nerveDiscreteObjEquiv (QuillenQSimplex C ⦋1⦌) (op ⦋1⦌))
    ((nerveMap (quillenStageGridQProjection C ⦋1⦌)).app (op ⦋1⦌)
      (ComposableArrows.mk₁ (𝟙 G))) = _
  change G.q = _
  exact generatorGrid_q (C := C) A top

private theorem generatorGrid_stage_right (A : C) :
    (ComposableArrows.left
      ((generatorGridEdge A false).map (quillenStageGridToStageWeakDiagonal (C := C))).edge) =
      stageOneWeakObj C A := by
  have h : edgewiseRightInclusion.app ⦋1⦌ ≫ stageCut false = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  have hc := CategoryTheory.Functor.congr_obj
    (reindexStageWeak_comp C (edgewiseRightInclusion.app ⦋1⦌) (stageCut false))
    (stageOneWeakObj C A)
  have hMap := congrArg (fun f : ⦋1⦌ ⟶ ⦋1⦌ =>
    (reindexStageWeak C (a := ⦋1⦌) (b := ⦋1⦌) f).obj (stageOneWeakObj C A)) h
  have hId := CategoryTheory.Functor.congr_obj (reindexStageWeak_id C ⦋1⦌) (stageOneWeakObj C A)
  exact hc.symm.trans (hMap.trans hId)

private theorem generatorGrid_stage_left_zero (A : C) :
    (ComposableArrows.left
      ((generatorGridEdge A true).map (quillenStageGridToStageWeakDiagonal (C := C))).edge) =
      zeroWeakOne (C := C) := by
  have hc := CategoryTheory.Functor.congr_obj
    (reindexStageWeak_comp C (edgewiseRightInclusion.app ⦋1⦌) (stageCut true))
    (stageOneWeakObj C A)
  exact hc.symm.trans (weakOne_reindex_constant A _ (1 : Fin 2)
    (by intro i; fin_cases i <;> rfl))

private theorem weakOne_zero : stageOneWeakObj C (0 : C) = zeroWeakOne (C := C) := by
  ext
  let F : Ar 1 ⥤ C := (stageOneWeakObj C (0 : C)).obj.obj
  have hObj : ∀ J : Ar 1, F.obj J = (0 : C) := by
    intro J
    simp [F, stageOneWeakObj, stageOne, stageOneDiagramFunctor, stageOneDiagram,
      stageOneDiagramObj]
  refine CategoryTheory.Functor.ext hObj ?_
  intro J K f
  have hJ : IsZero (F.obj J) := (hObj J).symm ▸ isZero_zero C
  exact hJ.eq_of_src _ _

private theorem generatorGrid_stage_edge (A : C) (top : Bool) :
    ((generatorGridEdge A top).map (quillenStageGridToStageWeakDiagonal (C := C))).edge =
      ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C (if top then (0 : C) else A))) := by
  let B := generatorWeakThree (C := C) A top
  let G := QuillenStageGridLift.ofGrid (C := C) (a := ⦋1⦌) B
  let F := quillenStageGridProjection C ⦋1⦌ ⋙ reindexStageWeak C (edgewiseRightInclusion.app ⦋1⦌)
  have h : ((generatorGridEdge A top).map (quillenStageGridToStageWeakDiagonal (C := C))).edge =
      ComposableArrows.mk₁ (𝟙 (F.obj G)) := by
    let e := F.mapComposableArrowsObjMk₁Iso (𝟙 G)
    have he : (F.mapComposableArrows 1).obj (ComposableArrows.mk₁ (𝟙 G)) =
        ComposableArrows.mk₁ (F.map (𝟙 G)) :=
      CategoryTheory.Functor.ext_of_iso e
        (fun i => by fin_cases i <;> rfl) (fun i => by fin_cases i <;> rfl)
    exact he.trans (congrArg ComposableArrows.mk₁ (F.map_id G))
  have hObj : F.obj G = stageOneWeakObj C (if top then (0 : C) else A) := by
    cases top
    · simpa only [↓reduceIte] using! (generatorGrid_stage_right (C := C) A)
    · simpa only [↓reduceIte] using!
        (generatorGrid_stage_left_zero (C := C) A).trans (weakOne_zero (C := C)).symm
  exact h.trans (congrArg (fun W => ComposableArrows.mk₁ (𝟙 W)) hObj)

private theorem realizedEdge_hom_eq {K : SSet.{max u v}}
    {x y x' y' : K _⦋0⦌} (e : K.Edge x y) (e' : K.Edge x' y')
    (h : e.edge = e'.edge) : (SSet.realizedEdgePath (X := K) e).hom =
        (SSet.realizedEdgePath (X := K) e').hom :=
  congrArg (fun z : K _⦋1⦌ => SSet.stdSimplex.toTopObjIsoI.inv ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm z)) h

private theorem map_trans_value {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y z : X} {x' y' z' : Y} (f : X → Y)
    (p : Path x y) (q : Path y z) (p' : Path x' y') (q' : Path y' z')
    (hp : ∀ t : unitInterval, f (p t) = p' t)
    (hq : ∀ t : unitInterval, f (q t) = q' t) (t : unitInterval) :
    f ((p.trans q) t) = (p'.trans q') t := by
  rw [Path.trans_apply p q t, Path.trans_apply p' q' t]
  split_ifs
  · exact hp _
  · exact hq _

private theorem gridQ_path_value (A : C) (top : Bool) (t : unitInterval) :
    SSet.toTop.map (quillenStageGridToNQ (C := C))
      (TopCat.pathEquiv (SSet.realizedEdgePath (X := quillenStageGridDiagonal C)
          (generatorGridEdge A top)) t) =
      TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C) (nerve.edgeMk (zeroArrow A top))) t := by
  have h := SSet.realizedEdgePath_naturality_hom (quillenStageGridToNQ (C := C))
    (generatorGridEdge A top)
  have h' := ConcreteCategory.congr_hom h (TopCat.I.homeomorph.symm t)
  have he := realizedEdge_hom_eq.{u, v} (K := NQ C)
    ((generatorGridEdge A top).map (quillenStageGridToNQ (C := C)))
    (nerve.edgeMk (zeroArrow A top))
    ((generatorGrid_Q_edge A top).trans (nerve.edgeMk_edge (zeroArrow A top)).symm)
  exact h'.symm.trans (ConcreteCategory.congr_hom he (TopCat.I.homeomorph.symm t))

private theorem gridStage_path_value (A : C) (top : Bool) (t : unitInterval) :
    SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))
      (TopCat.pathEquiv (SSet.realizedEdgePath (X := quillenStageGridDiagonal C)
          (generatorGridEdge A top)) t) =
      stageWeakDiagonalObjectLoop C (if top then (0 : C) else A) t := by
  have h := SSet.realizedEdgePath_naturality_hom
    (quillenStageGridToStageWeakDiagonal (C := C)) (generatorGridEdge A top)
  have h' := ConcreteCategory.congr_hom h (TopCat.I.homeomorph.symm t)
  have he := realizedEdge_hom_eq.{u, v} (K := stageWeakDiagonal C)
    ((generatorGridEdge A top).map (quillenStageGridToStageWeakDiagonal (C := C)))
    (stageWeakDiagonalObjectEdge C (if top then (0 : C) else A))
    ((generatorGrid_stage_edge A top).trans
      (stageWeakDiagonalObjectEdge_edge C (if top then (0 : C) else A)).symm)
  exact h'.symm.trans (ConcreteCategory.congr_hom he (TopCat.I.homeomorph.symm t))

private theorem weakLoop_normalized {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (F : ContinuousMap.WeaklyPointed x y)
    (h : F.hom x = y) (hRoot : ∀ t, F.rootPath t = y) (p : Path x x) :
    (F.loopMap p).Homotopic ((p.map F.hom.continuous).cast h.symm h.symm) := by
  rcases F with ⟨f, r⟩
  change f x = y at h
  subst y
  have hr : r = Path.refl (f x) := by
    apply Path.ext
    funext t
    exact hRoot t
  change (r.symm.trans ((p.map f.continuous).trans r)).Homotopic (p.map f.continuous)
  rw [hr, Path.refl_symm]
  exact (Path.Homotopic.refl_trans _).trans (Path.Homotopic.trans_refl _)

private theorem generator_Q_loop (A : C) :
    (quillenStageGridToNQLoopMap (C := C) (generatorGridLoop A)).Homotopic
      ((generatorLoop A).cast (NQReal.basepoint_eq_realizedVertex C)
        (NQReal.basepoint_eq_realizedVertex C)) := by
  have h := weakLoop_normalized (quillenStageGridToNQWeaklyPointed (C := C))
    (quillenStageGridToNQ_map_basepoint (C := C)) (fun _ => rfl) (generatorGridLoop A)
  refine h.trans ?_
  have hp : ((generatorGridLoop A).map
      (SSet.toTop.map (quillenStageGridToNQ (C := C))).hom.continuous).cast
      (quillenStageGridToNQ_map_basepoint (C := C)).symm
      (quillenStageGridToNQ_map_basepoint (C := C)).symm =
      (generatorLoop A).cast (NQReal.basepoint_eq_realizedVertex C)
        (NQReal.basepoint_eq_realizedVertex C) := by
    let pm := TopCat.pathEquiv (SSet.realizedEdgePath
      (X := quillenStageGridDiagonal C) (generatorGridEdge A false))
    let pe := TopCat.pathEquiv (SSet.realizedEdgePath
      (X := quillenStageGridDiagonal C) (generatorGridEdge A true))
    let qm := TopCat.pathEquiv (SSet.realizedEdgePath
      (X := NQ C) (nerve.edgeMk (ExtensionCategory.zeroMonoHom A)))
    let qe := TopCat.pathEquiv (SSet.realizedEdgePath
      (X := NQ C) (nerve.edgeMk (ExtensionCategory.zeroEpiHom A)))
    apply Path.ext
    funext t
    change SSet.toTop.map (quillenStageGridToNQ (C := C)) ((pm.trans pe.symm) t) =
      (qm.trans qe.symm) t
    exact map_trans_value (SSet.toTop.map (quillenStageGridToNQ (C := C)))
      pm pe.symm qm qe.symm (gridQ_path_value A false)
      (fun (r : unitInterval) => gridQ_path_value A true (unitInterval.symm r)) t
  exact Path.Homotopic.Quotient.eq.mp (congrArg Path.Homotopic.Quotient.mk hp)

private theorem generator_stage_loop (A : C) :
    (quillenStageGridToStageLoopMap (C := C) (generatorGridLoop A)).Homotopic
      ((stageWeakDiagonalObjectLoop C A).trans (stageWeakDiagonalObjectLoop C (0 : C)).symm) := by
  have hPoint : (quillenStageGridToStageWeaklyPointed (C := C)).hom
      (quillenStageGridDiagonalReal.basepoint C) = stageWeakDiagonalReal.basepoint C := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := C)).trans
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm
  have hRoot : ∀ t, (quillenStageGridToStageWeaklyPointed (C := C)).rootPath t =
      stageWeakDiagonalReal.basepoint C := by
    intro t
    change (((quillenStageGridStageProjectionWeaklyPointed (C := C)).rootPath.map
      (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)).hom.continuous).trans
        (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)).rootPath) t = _
    rw [Path.trans_apply]
    split_ifs
    · exact outerEdgewiseStageDiagonalComparison_map_basepoint (C := C)
    · rfl
  have h := weakLoop_normalized (quillenStageGridToStageWeaklyPointed (C := C))
    hPoint hRoot (generatorGridLoop A)
  refine h.trans ?_
  have hp : ((generatorGridLoop A).map
      (quillenStageGridToStageWeaklyPointed (C := C)).hom.continuous).cast
      hPoint.symm hPoint.symm =
      (stageWeakDiagonalObjectLoop C A).trans (stageWeakDiagonalObjectLoop C (0 : C)).symm := by
    let pm := TopCat.pathEquiv (SSet.realizedEdgePath
      (X := quillenStageGridDiagonal C) (generatorGridEdge A false))
    let pe := TopCat.pathEquiv (SSet.realizedEdgePath
      (X := quillenStageGridDiagonal C) (generatorGridEdge A true))
    apply Path.ext
    funext t
    change (quillenStageGridToStageWeaklyPointed (C := C)).hom ((pm.trans pe.symm) t) = _
    have hHom := quillenStageGridToStageWeaklyPointed_hom (C := C)
    have hValue := map_trans_value (SSet.toTop.map
      (quillenStageGridToStageWeakDiagonal (C := C))) pm pe.symm
      (stageWeakDiagonalObjectLoop C A) (stageWeakDiagonalObjectLoop C (0 : C)).symm
      (gridStage_path_value A false) (fun (r : unitInterval) =>
          gridStage_path_value A true (unitInterval.symm r)) t
    exact (congrArg (fun f : C((quillenStageGridDiagonalReal C), (stageWeakDiagonalReal C)) =>
      f ((pm.trans pe.symm) t)) hHom).trans hValue
  exact Path.Homotopic.Quotient.eq.mp (congrArg Path.Homotopic.Quotient.mk hp)

private theorem stageObjectLoop_group_value (A : C) :
    stageWeakDiagonalRealizedFundamentalK0MulEquiv C
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (stageWeakDiagonalObjectLoop C A))) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk A) := by
  apply Multiplicative.toAdd.injective
  exact stageWeakDiagonalKSpacePiZeroEquivK0_objectLoop C A

private theorem stage_difference_loop_value (A : C) :
    stageWeakDiagonalKSpacePiZeroEquivK0 C
      (ZerothHomotopy.mk ((stageWeakDiagonalObjectLoop C A).trans
        (stageWeakDiagonalObjectLoop C (0 : C)).symm)) = WaldhausenKTheory.K0.mk A := by
  let p := stageWeakDiagonalObjectLoop C A
  let q := stageWeakDiagonalObjectLoop C (0 : C)
  let gp := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)
  let gq := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)
  let e := stageWeakDiagonalRealizedFundamentalK0MulEquiv C
  have hg : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.trans q.symm)) =
      gq⁻¹ * gp := by
    have hi : (gq⁻¹).asHom = (Path.Homotopic.Quotient.mk q).symm :=
      congrArg (fun g : FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) => g.asHom) (FundamentalGroup.inv_def (p := gq))
    have hm : (gq⁻¹ * gp).asHom = gp.asHom.trans (gq⁻¹).asHom :=
      congrArg (fun g : FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) => g.asHom)
        (FundamentalGroup.mul_def (p := gq⁻¹) (q := gp))
    have hm' := hm.trans (congrArg (fun r : Path.Homotopic.Quotient
        (stageWeakDiagonalReal.basepoint C) (stageWeakDiagonalReal.basepoint C) =>
        (Path.Homotopic.Quotient.mk p).trans r) hi)
    apply End.ext
    exact ((Path.Homotopic.Quotient.mk_trans p q.symm).trans
      (congrArg (fun r : Path.Homotopic.Quotient (stageWeakDiagonalReal.basepoint C)
        (stageWeakDiagonalReal.basepoint C) => (Path.Homotopic.Quotient.mk p).trans r)
        (Path.Homotopic.Quotient.mk_symm q))).trans hm'.symm
  have hr := congrArg (fun g : FundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C) => Multiplicative.toAdd (e g))
    (loopComponentsEquivFundamentalGroup_mk (X := stageWeakDiagonalReal C)
      (x := stageWeakDiagonalReal.basepoint C) (p.trans q.symm))
  calc
    stageWeakDiagonalKSpacePiZeroEquivK0 C (ZerothHomotopy.mk (p.trans q.symm)) =
        Multiplicative.toAdd (e (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (p.trans q.symm)))) := hr
    _ = Multiplicative.toAdd (e (gq⁻¹ * gp)) := congrArg (fun g => Multiplicative.toAdd (e g)) hg
    _ = -Multiplicative.toAdd (e gq) + Multiplicative.toAdd (e gp) := by
      rw [e.map_mul, map_inv]
      rfl
    _ = -(WaldhausenKTheory.K0.mk (0 : C)) + WaldhausenKTheory.K0.mk A :=
      congrArg₂ (fun a b => -a + b)
        (congrArg Multiplicative.toAdd (stageObjectLoop_group_value (C := C) (0 : C)))
        (congrArg Multiplicative.toAdd (stageObjectLoop_group_value (C := C) A))
    _ = _ := by rw [WaldhausenKTheory.K0.mk_zero]; exact zero_add _

/-- The actual two parallel Q spans give [A] under the already-landed Q/S evaluator. -/
theorem generatorLoop_canonical (A : C) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk (generatorLoop A)) = K0.mk A := by
  let cG := ZerothHomotopy.mk (generatorGridLoop (C := C) A)
  have hQ : quillenStageGridToNQPiZeroEquiv C cG =
      ZerothHomotopy.mk ((generatorLoop A).cast (NQReal.basepoint_eq_realizedVertex C)
        (NQReal.basepoint_eq_realizedVertex C)) := by
    change (quillenStageGridToNQWeaklyPointed (C := C)).loopComponentsMap cG = _
    exact (ContinuousMap.WeaklyPointed.loopComponentsMap_mk _ _).trans
      (zerothHomotopy_mk_eq_of_pathHomotopic (generator_Q_loop A))
  have hS : quillenStageGridToStagePiZeroEquiv C cG =
      ZerothHomotopy.mk ((stageWeakDiagonalObjectLoop C A).trans
        (stageWeakDiagonalObjectLoop C (0 : C)).symm) := by
    change (quillenStageGridToStageWeaklyPointed (C := C)).loopComponentsMap cG = _
    exact (ContinuousMap.WeaklyPointed.loopComponentsMap_mk _ _).trans
      (zerothHomotopy_mk_eq_of_pathHomotopic (generator_stage_loop A))
  have hFacade : NQKSpacePiZeroEquivK0 C (quillenStageGridToNQPiZeroEquiv C cG) =
      stageWeakDiagonalKSpacePiZeroEquivK0 C (quillenStageGridToStagePiZeroEquiv C cG) :=
    congrArg (fun c : ZerothHomotopy (quillenStageGridDiagonalKSpace C) =>
      stageWeakDiagonalKSpacePiZeroEquivK0 C (quillenStageGridToStagePiZeroEquiv C c))
      ((quillenStageGridToNQPiZeroEquiv C).symm_apply_apply cG)
  have hQValue := congrArg (fun c : ZerothHomotopy (NQKSpace C) =>
      WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C c)) hQ.symm
  have hSValue :=
      congrArg
      (fun c : ZerothHomotopy (LoopSpace (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C)) =>
      WaldhausenKTheory.K0.toExact C (stageWeakDiagonalKSpacePiZeroEquivK0 C c)) hS
  exact (canonicalLoopComponentsK0_mk (C := C) (generatorLoop A)).trans
    (hQValue.trans ((congrArg (WaldhausenKTheory.K0.toExact C) hFacade).trans
      (hSValue.trans ((congrArg (WaldhausenKTheory.K0.toExact C)
        (stage_difference_loop_value (C := C) A)).trans
          (WaldhausenKTheory.K0.toExact_mk (C := C) A)))))

private abbrev totalSpace : TopCat.{max u v} :=
  SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v})

private abbrev projectionNerve := nerveMapCommonHom.{u, max u v, 0}
  (ExtensionCategory.localizedTarget (C := C))

private abbrev projection : totalSpace (C := C) ⟶ NQReal C :=
    SSet.toTop.map (projectionNerve (C := C))

private def atDenominator (D : Core C) : ExtensionCategory C ⥤
    ExtensionCategory.localizedExtensions (C := C) :=
  (𝟭 (ExtensionCategory C)).prod' ((CategoryTheory.Functor.const (ExtensionCategory C)).obj D) ⋙
    MonoidalActionCategory.inclusion (Core C) (ExtensionCategory C × Core C)

private def zeroToTotal : SInverse (Core C) (Core C) ⥤
    ExtensionCategory.localizedExtensions (C := C) :=
  FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedForget (C := C) (0 : C)

private def pointPair (P D : Core C) : totalSpace (C := C) :=
  SSet.realizedVertex
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
      (ComposableArrows.mk₀
    ((atDenominator D).obj (FixedTargetExtension.zeroRow P).toExtension))

private theorem pointPair_map (P D : Core C) :
    projection (C := C) (pointPair P D) = OriginalQZeroComparison.zeroQVertex (C := C) := by
  have hv := SSet.realizedVertex_naturality (projectionNerve (C := C))
    (ComposableArrows.mk₀ ((atDenominator D).obj (FixedTargetExtension.zeroRow P).toExtension))
  have hz : (projectionNerve (C := C)).app (op ⦋0⦌)
      (ComposableArrows.mk₀ ((atDenominator D).obj (FixedTargetExtension.zeroRow P).toExtension)) =
      ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C) := ComposableArrows.ext₀ rfl
  exact hv.symm.trans (congrArg (fun x : (NQ C) _⦋0⦌ => SSet.realizedVertex (X := NQ C) x) hz)

private theorem atDenominator_target_map (D : Core C) {E F : ExtensionCategory C} (f : E ⟶ F) :
    (ExtensionCategory.localizedTarget (C := C)).map ((atDenominator D).map f) =
      (ExtensionCategory.target (C := C)).map f := by
  let L : ExtensionCategory C ⥤ QuillenQ C :=
    SInverse.inclusion (Core C) (ExtensionCategory C) ⋙ ExtensionCategory.localizedTarget (C := C)
  let T : ExtensionCategory C ⥤ QuillenQ C := ExtensionCategory.target (C := C)
  let hFunctor : L = T := ExtensionCategory.localizedTarget_inclusion (C := C)
  let A : QuillenQ C := T.obj E
  let B : QuillenQ C := T.obj F
  let qf : A ⟶ B := T.map f
  let α : A ⟶ A := eqToHom (CategoryTheory.Functor.congr_obj hFunctor E)
  let β : B ⟶ B := eqToHom (CategoryTheory.Functor.congr_obj hFunctor F).symm
  have hα : α = 𝟙 A := eqToHom_refl A _
  have hβ : β = 𝟙 B := eqToHom_refl B _
  have hCast : α ≫ qf ≫ β = qf :=
    (congrArg₂ (fun (a : A ⟶ A) (b : B ⟶ B) => a ≫ qf ≫ b) hα hβ).trans
      ((congrArg (fun k : A ⟶ B => 𝟙 A ≫ k)
        (@Category.comp_id (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A B qf)).trans
        (@Category.id_comp (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A B qf))
  have hp : L.map f = α ≫ qf ≫ β := CategoryTheory.Functor.congr_hom hFunctor f
  have h : (ExtensionCategory.localizedTarget (C := C)).map ((atDenominator D).map f) =
      L.map f := rfl
  exact h.trans (hp.trans hCast)

private def diagonalPair (D : Core C) : SInverse (Core C) (Core C) := ⟨(D, D)⟩

private def unitToDiagonal (D : Core C) :
    (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)) ⟶ diagonalPair D :=
  MonoidalActionCategory.Hom.mk
    { stabilizer := D
      hom := ((ρ_ D).hom, (ρ_ D).hom) }

private theorem stabilized_target_identity (D : Core C) :
    (ExtensionCategory.localizedTarget (C := C)).map
        ((zeroToTotal (C := C)).map (unitToDiagonal D)) =
      𝟙 (⟨0⟩ : QuillenQ C) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let A : QuillenQ C := ⟨0⟩
  let f := (FixedTargetExtension.zeroLocalizedFunctor (C := C)).map (unitToDiagonal D)
  let g := (FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).map f
  let φ := (zeroToTotal (C := C)).map (unitToDiagonal D)
  have hLift : p.IsHomLift (𝟙 A) φ := by
    change p.IsHomLift (𝟙 A)
      ((CategoryTheory.Functor.Fiber.fiberInclusion :
        FixedTargetExtension.localizedFiber (C := C) (0 : C) ⥤ _).map g)
    infer_instance
  let := hLift
  let α : A ⟶ A := eqToHom (CategoryTheory.IsHomLift.domain_eq p (𝟙 A) φ)
  let β : A ⟶ A := eqToHom (CategoryTheory.IsHomLift.codomain_eq p (𝟙 A) φ).symm
  have hα : α = 𝟙 A := eqToHom_refl A _
  have hβ : β = 𝟙 A := eqToHom_refl A _
  have h := CategoryTheory.IsHomLift.fac' p (𝟙 A) φ
  have hCast : α ≫ (𝟙 A) ≫ β = 𝟙 A :=
    (congrArg₂ (fun (a b : A ⟶ A) => a ≫ (𝟙 A) ≫ b) hα hβ).trans
      ((congrArg (fun k : A ⟶ A => 𝟙 A ≫ k)
        (@Category.comp_id (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A A (𝟙 A))).trans
        (@Category.id_comp (QuillenQ C) (inferInstance : Category.{max u v} (QuillenQ C))
          A A (𝟙 A)))
  exact h.trans hCast

private def stabilizationPath (D : Core C) :
    Path (OriginalQZeroComparison.zeroTotalVertex (C := C)) (pointPair D D) :=
  TopCat.pathEquiv (SSet.realizedEdgePath
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
      (nerve.edgeMk ((zeroToTotal (C := C)).map (unitToDiagonal D))))

private def numeratorPath (P D : Core C) : Path (pointPair (𝟙_ (Core C)) D) (pointPair P D) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v})) (nerve.edgeMk
      ((atDenominator D).map (ExtensionCategory.zeroMonoLift
          (AuxiliaryExtension.unitRow P.of)))))).trans
    (TopCat.pathEquiv (SSet.realizedEdgePath
        (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
        (nerve.edgeMk
      ((atDenominator D).map (ExtensionCategory.zeroEpiLift
          (AuxiliaryExtension.unitRow P.of)))))).symm

private def denominatorPath (D : Core C) : Path (pointPair D D) (pointPair (𝟙_ (Core C)) D) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v})) (nerve.edgeMk
      ((atDenominator D).map (ExtensionCategory.zeroEpiLift
          (AuxiliaryExtension.unitRow D.of)))))).trans
    (TopCat.pathEquiv (SSet.realizedEdgePath
        (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
        (nerve.edgeMk
      ((atDenominator D).map (ExtensionCategory.zeroMonoLift
          (AuxiliaryExtension.unitRow D.of)))))).symm

private def allPairTotalPath (a : SInverse (Core C) (Core C)) :
    Path (OriginalQZeroComparison.zeroTotalVertex (C := C))
      (SSet.realizedVertex
          (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ ((zeroToTotal (C := C)).obj a))) :=
  (stabilizationPath a.of.2).trans ((denominatorPath a.of.2).trans (numeratorPath a.of.1 a.of.2))

private theorem projectedEdge_value {E F : ExtensionCategory.localizedExtensions (C := C)}
    (f : E ⟶ F) (t : unitInterval) :
    projection (C := C) (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
          (nerve.edgeMk f)) t) =
      TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
        (nerve.edgeMk ((ExtensionCategory.localizedTarget (C := C)).map f))) t := by
  have h := SSet.realizedEdgePath_naturality_hom (projectionNerve (C := C)) (nerve.edgeMk f)
  have ht := ConcreteCategory.congr_hom h (TopCat.I.homeomorph.symm t)
  have he : ((nerve.edgeMk f).map (projectionNerve (C := C))).edge =
      ComposableArrows.mk₁ ((ExtensionCategory.localizedTarget (C := C)).map f) := by
    change ((ExtensionCategory.localizedTarget (C := C)).mapComposableArrows 1).obj
      (ComposableArrows.mk₁ f) = _
    exact ComposableArrows.ext₁ rfl rfl (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
  have hp := realizedEdge_hom_eq.{u, v} (K := NQ C)
    ((nerve.edgeMk f).map (projectionNerve (C := C)))
    (nerve.edgeMk ((ExtensionCategory.localizedTarget (C := C)).map f))
    (he.trans (nerve.edgeMk_edge ((ExtensionCategory.localizedTarget (C := C)).map f)).symm)
  exact ht.symm.trans (ConcreteCategory.congr_hom hp (TopCat.I.homeomorph.symm t))

private theorem projectedEdge_eq_value {E F : ExtensionCategory.localizedExtensions (C := C)}
    (f : E ⟶ F) {x y : (NQ C) _⦋0⦌} (e : (NQ C).Edge x y)
    (he : ComposableArrows.mk₁ ((ExtensionCategory.localizedTarget (C := C)).map f) = e.edge)
    (t : unitInterval) :
    projection (C := C) (TopCat.pathEquiv (SSet.realizedEdgePath
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
        (nerve.edgeMk f)) t) = TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C) e) t := by
  have h := projectedEdge_value (C := C) f t
  have hp := realizedEdge_hom_eq.{u, v} (K := NQ C)
    (nerve.edgeMk ((ExtensionCategory.localizedTarget (C := C)).map f)) e
    ((nerve.edgeMk_edge ((ExtensionCategory.localizedTarget (C := C)).map f)).trans he)
  exact h.trans (ConcreteCategory.congr_hom hp (TopCat.I.homeomorph.symm t))

private theorem projected_mono_value (P D : Core C) (t : unitInterval) :
    projection (C := C) (TopCat.pathEquiv (SSet.realizedEdgePath
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
      (nerve.edgeMk ((atDenominator D).map
        (ExtensionCategory.zeroMonoLift (AuxiliaryExtension.unitRow P.of))))) t) =
      TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
        (nerve.edgeMk (ExtensionCategory.zeroMonoHom P.of))) t := by
  have h := (atDenominator_target_map D
    (ExtensionCategory.zeroMonoLift (AuxiliaryExtension.unitRow P.of))).trans
      (ExtensionCategory.zeroMonoLift_target (AuxiliaryExtension.unitRow P.of))
  exact projectedEdge_eq_value _ (nerve.edgeMk (ExtensionCategory.zeroMonoHom P.of))
    ((congrArg ComposableArrows.mk₁ h).trans (nerve.edgeMk_edge _).symm) t

private theorem projected_epi_value (P D : Core C) (t : unitInterval) :
    projection (C := C) (TopCat.pathEquiv (SSet.realizedEdgePath
      (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
      (nerve.edgeMk ((atDenominator D).map
        (ExtensionCategory.zeroEpiLift (AuxiliaryExtension.unitRow P.of))))) t) =
      TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
        (nerve.edgeMk (ExtensionCategory.zeroEpiHom P.of))) t := by
  have h := (atDenominator_target_map D
    (ExtensionCategory.zeroEpiLift (AuxiliaryExtension.unitRow P.of))).trans
      (ExtensionCategory.zeroEpiLift_target (AuxiliaryExtension.unitRow P.of))
  exact projectedEdge_eq_value _ (nerve.edgeMk (ExtensionCategory.zeroEpiHom P.of))
    ((congrArg ComposableArrows.mk₁ h).trans (nerve.edgeMk_edge _).symm) t

private theorem projected_numerator (P D : Core C) :
    ((numeratorPath P D).map (projection (C := C)).hom.continuous).cast
      (pointPair_map (𝟙_ (Core C)) D).symm (pointPair_map P D).symm = generatorLoop P.of := by
  let pm := TopCat.pathEquiv (SSet.realizedEdgePath
    (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
    (nerve.edgeMk ((atDenominator D).map
      (ExtensionCategory.zeroMonoLift (AuxiliaryExtension.unitRow P.of)))))
  let pe := TopCat.pathEquiv (SSet.realizedEdgePath
    (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
    (nerve.edgeMk ((atDenominator D).map
      (ExtensionCategory.zeroEpiLift (AuxiliaryExtension.unitRow P.of)))))
  let qm := TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
    (nerve.edgeMk (ExtensionCategory.zeroMonoHom P.of)))
  let qe := TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
    (nerve.edgeMk (ExtensionCategory.zeroEpiHom P.of)))
  apply Path.ext
  funext t
  change projection (C := C) ((pm.trans pe.symm) t) = (qm.trans qe.symm) t
  exact map_trans_value (projection (C := C)) pm pe.symm qm qe.symm
    (projected_mono_value P D) (fun (r : unitInterval) =>
        projected_epi_value P D (unitInterval.symm r)) t

private theorem projected_denominator (D : Core C) :
    ((denominatorPath D).map (projection (C := C)).hom.continuous).cast
      (pointPair_map D D).symm (pointPair_map (𝟙_ (Core C)) D).symm =
          (generatorLoop D.of).symm := by
  let pe := TopCat.pathEquiv (SSet.realizedEdgePath
    (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
    (nerve.edgeMk ((atDenominator D).map
      (ExtensionCategory.zeroEpiLift (AuxiliaryExtension.unitRow D.of)))))
  let pm := TopCat.pathEquiv (SSet.realizedEdgePath
    (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
    (nerve.edgeMk ((atDenominator D).map
      (ExtensionCategory.zeroMonoLift (AuxiliaryExtension.unitRow D.of)))))
  let qe := TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
    (nerve.edgeMk (ExtensionCategory.zeroEpiHom D.of)))
  let qm := TopCat.pathEquiv (SSet.realizedEdgePath (X := NQ C)
    (nerve.edgeMk (ExtensionCategory.zeroMonoHom D.of)))
  have hs : (generatorLoop D.of).symm = qe.trans qm.symm := by
    exact (Path.trans_symm qm qe.symm).trans
      (congrArg (fun q => q.trans qm.symm) (Path.symm_symm qe))
  apply Path.ext
  funext t
  change projection (C := C) ((pe.trans pm.symm) t) = (generatorLoop D.of).symm t
  exact (map_trans_value (projection (C := C)) pe pm.symm qe qm.symm
    (projected_epi_value D D) (fun (r : unitInterval) =>
        projected_mono_value D D (unitInterval.symm r)) t).trans
      (congrArg (fun q => q t) hs.symm)

private theorem projected_stabilization (D : Core C) :
    (((stabilizationPath D).map (projection (C := C)).hom.continuous).cast
      (OriginalQZeroComparison.zeroTotalVertex_map (C := C)).symm
          (pointPair_map D D).symm).Homotopic
        (Path.refl (OriginalQZeroComparison.zeroQVertex (C := C))) := by
  let K : SSet.{max u v} := NQ C
  let z : K _⦋0⦌ := nerveEquiv.symm (⟨0⟩ : QuillenQ C)
  let e : K.Edge z z := nerve.edgeMk (𝟙 (⟨0⟩ : QuillenQ C))
  let q : Path (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.zeroQVertex (C := C)) :=
    TopCat.pathEquiv (SSet.realizedEdgePath (X := K) e)
  have hq : ((stabilizationPath D).map (projection (C := C)).hom.continuous).cast
      (OriginalQZeroComparison.zeroTotalVertex_map (C := C)).symm (pointPair_map D D).symm = q := by
    apply Path.ext
    funext t
    exact projectedEdge_eq_value ((zeroToTotal (C := C)).map (unitToDiagonal D)) e
      ((congrArg ComposableArrows.mk₁ (stabilized_target_identity D)).trans
        (nerve.edgeMk_edge (𝟙 (⟨0⟩ : QuillenQ C))).symm) t
  let R := SSet.realizationFundamentalGroupoidFunctor K
  have hi : SSet.FundamentalGroupoid.homMk e = 𝟙 (SSet.FundamentalGroupoid.mk z) :=
    (congrArg SSet.FundamentalGroupoid.homMk (nerve.edgeMk_id (⟨0⟩ : QuillenQ C))).trans
      (SSet.FundamentalGroupoid.homMk_id z)
  have hMap : R.map (SSet.FundamentalGroupoid.homMk e) =
      𝟙 (R.obj (SSet.FundamentalGroupoid.mk z)) :=
    (congrArg R.map hi).trans (R.map_id (SSet.FundamentalGroupoid.mk z))
  have hEdge := SSet.realizationFundamentalGroupoidFunctor_map_homMk K e
  have hPath : Path.Homotopic.Quotient.mk q = Path.Homotopic.Quotient.mk
      (Path.refl (OriginalQZeroComparison.zeroQVertex (C := C))) := hEdge.symm.trans hMap
  have hClass := congrArg Path.Homotopic.Quotient.mk hq
  exact Path.Homotopic.Quotient.eq.mp (hClass.trans hPath)

private theorem totalPair_map (a : SInverse (Core C) (Core C)) :
    projection (C := C) (SSet.realizedVertex
        (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ ((zeroToTotal (C := C)).obj a))) =
      OriginalQZeroComparison.zeroQVertex (C := C) :=
  pointPair_map a.of.1 a.of.2

private theorem allPair_projection (a : SInverse (Core C) (Core C)) :
    (((allPairTotalPath a).map (projection (C := C)).hom.continuous).cast
      (OriginalQZeroComparison.zeroTotalVertex_map (C := C)).symm (totalPair_map a).symm).Homotopic
      ((generatorLoop a.of.2.of).symm.trans (generatorLoop a.of.1.of)) := by
  let D := a.of.2
  let P := a.of.1
  let ps := (stabilizationPath D).map (projection (C := C)).hom.continuous
  let pd := (denominatorPath D).map (projection (C := C)).hom.continuous
  let pp := (numeratorPath P D).map (projection (C := C)).hom.continuous
  have h : ((allPairTotalPath a).map (projection (C := C)).hom.continuous).cast
      (OriginalQZeroComparison.zeroTotalVertex_map (C := C)).symm (totalPair_map a).symm =
      (ps.cast (OriginalQZeroComparison.zeroTotalVertex_map (C := C)).symm
          (pointPair_map D D).symm).trans
        ((pd.cast (pointPair_map D D).symm (pointPair_map (𝟙_ (Core C)) D).symm).trans
          (pp.cast (pointPair_map (𝟙_ (Core C)) D).symm (pointPair_map P D).symm)) := by
    change (((stabilizationPath D).trans ((denominatorPath D).trans (numeratorPath P D))).map
      (projection (C := C)).hom.continuous).cast _ _ = _
    rw [Path.map_trans, Path.map_trans,
      Path.cast_trans ps (pd.trans pp)
        (OriginalQZeroComparison.zeroTotalVertex_map (C := C)).symm
        (pointPair_map D D).symm (pointPair_map P D).symm,
      Path.cast_trans pd pp (pointPair_map D D).symm
        (pointPair_map (𝟙_ (Core C)) D).symm (pointPair_map P D).symm]
  rw [h, projected_denominator, projected_numerator]
  exact ((projected_stabilization D).hcomp (Path.Homotopic.refl _)).trans
    (Path.Homotopic.refl_trans _)

private theorem comparisonVertex_path_const (a : SInverse (Core C) (Core C)) :
    TopCat.homotopyFiberPath (projection (C := C)) (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)
        (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a))) =
      ContinuousMap.const TopCat.I.{max u v} (OriginalQZeroComparison.zeroQVertex (C := C)) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let theta := FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)
  let c := (CategoryTheory.Functor.fiberToStructuredArrow (p := p) (⟨0⟩ : QuillenQ C)).obj
      (theta.obj a)
  have hc : c.hom = eqToHom (theta.obj a).property.symm :=
    CategoryTheory.Functor.fiberToStructuredArrow_obj_hom (⟨0⟩ : QuillenQ C) (theta.obj a)
  apply ContinuousMap.ext
  intro t
  have hv := OriginalQZeroComparison.completedCoreToZeroLeftCommaNerveMap_vertex a
  have hp := SSet.leftCommaHomotopyFiberComparison_vertex_path_const_of_hom_eqToHom.{u, 0, max u v}
    p (⟨0⟩ : QuillenQ C) c (theta.obj a).property.symm hc t
  change TopCat.homotopyFiberPath _ _
    (SSet.leftCommaHomotopyFiberComparison.{u, 0, max u v} p (⟨0⟩ : QuillenQ C)
      (SSet.toTop.map (OriginalQZeroComparison.completedCoreToZeroLeftCommaNerveMap (C := C))
        (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a)))) t = _
  rw [hv]
  exact hp

private theorem basedReturn_projectedPath {E B : TopCat.{max u v}} [ContractibleSpace E]
    (p : E ⟶ B) (e : E) (b : B) (he : p e = b) (contract : TopCat.BasedContraction E e)
    (z : TopCat.homotopyFiber p b) (e' : E) (he' : p e' = b)
    (hz : TopCat.homotopyFiberToTotal p b z = e')
    (hpath : TopCat.homotopyFiberPath p b z = ContinuousMap.const TopCat.I.{max u v} b)
    (lift : Path e e') :
    (TopCat.homotopyFiberToLoopsOfBasedContraction p e b he contract z).Homotopic
      ((lift.map p.hom.continuous).cast he.symm he'.symm) := by
  let trace : Path e e' := (contract.homotopy.evalAt e').symm
  let q : Path b b := (trace.map p.hom.continuous).cast he.symm he'.symm
  have hReturn : TopCat.homotopyFiberToLoopsOfBasedContraction p e b he contract z =
      q.trans (Path.refl b) := by
    apply Path.ext
    funext t
    rw [TopCat.homotopyFiberToLoopsOfBasedContraction_apply, Path.trans_apply]
    split_ifs
    · rw [hz]
      rfl
    · rw [hpath]
      rfl
  have hTrace : trace.Homotopic lift := SimplyConnectedSpace.paths_homotopic trace lift
  rw [hReturn]
  exact (Path.Homotopic.trans_refl q).trans ((hTrace.map p.hom).pathCast he.symm he'.symm)

/-- The SAME original comparison has the actual negative-denominator/positive-numerator loop
class. -/
theorem comparison_all_pairs_path (a : SInverse (Core C) (Core C)) :
    (BasedSplitExactQLoop.comparisonMap (C := C)
        (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ a))).Homotopic
      ((generatorLoop a.of.2.of).symm.trans (generatorLoop a.of.1.of)) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  let fiberUnit : FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
    OriginalQZeroComparison.zeroFiberUnit (C := C)
  let rawUnit : ExtensionCategory.localizedExtensions (C := C) := fiberUnit.val
  let v0 : K _⦋0⦌ := ComposableArrows.mk₀ rawUnit
  let p0 : SSet.toTop.obj K ⟶ NQReal C := SSet.toTop.map (projectionNerve (C := C))
  let e0 : SSet.toTop.obj K := SSet.realizedVertex (X := K) v0
  let b : NQReal C := OriginalQZeroComparison.zeroQVertex (C := C)
  let z : TopCat.homotopyFiber p0 b :=
    OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ a))
  let ea : SSet.toTop.obj K := SSet.realizedVertex (X := K)
    (ComposableArrows.mk₀ ((zeroToTotal (C := C)).obj a))
  let : ContractibleSpace (SSet.toTop.obj K) := LocalizedTotal.localizedTotal_contractible (C := C)
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    OriginalQZeroComparison.originalLocalizedTotalTerminalWeak (C := C)
  let contract : TopCat.BasedContraction (SSet.toTop.obj K) e0 :=
    SSet.basedContractionAtRealizedVertex K v0 hK
  have he : p0 e0 = b := OriginalQZeroComparison.zeroTotalVertex_map (C := C)
  have hz : TopCat.homotopyFiberToTotal p0 b z = ea :=
    OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_toTotal_vertex a
  have h := basedReturn_projectedPath.{u, v} p0 e0 b he contract z ea (totalPair_map a) hz
    (comparisonVertex_path_const a) (allPairTotalPath a)
  have hMap : OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C) =
      TopCat.homotopyFiberToLoopsOfRealizedConull K v0 p0 b he hK :=
    OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_eq_realizedConull (C := C)
  have hActual : BasedSplitExactQLoop.comparisonMap (C := C)
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ a)) =
      TopCat.homotopyFiberToLoopsOfBasedContraction p0 e0 b he contract z := by
    have hAtZ := congrArg (fun f : TopCat.homotopyFiber p0 b ⟶ TopCat.of (LoopSpace (NQReal C) b) =>
      f z) hMap
    apply Path.ext
    funext t
    have hReal := TopCat.homotopyFiberToLoopsOfRealizedConull_apply K v0 p0 b he hK z t
    have hBased := TopCat.homotopyFiberToLoopsOfBasedContraction_apply p0 e0 b he contract z t
    change OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C) z t = _
    exact (congrArg (fun q : LoopSpace (NQReal C) b => q t) hAtZ).trans
      (hReal.trans hBased.symm)
  exact (Path.Homotopic.Quotient.eq.mp (congrArg Path.Homotopic.Quotient.mk hActual)).trans
    (h.trans (allPair_projection a))

/-- The already-landed Q/S evaluator agrees with the actual original comparison on every pair. -/
theorem comparison_all_pairs (a : SInverse (Core C) (Core C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk
      (BasedSplitExactQLoop.comparisonMap (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a)))) =
      K0.mk a.of.1.of - K0.mk a.of.2.of := by
  have h := zerothHomotopy_mk_eq_of_pathHomotopic (comparison_all_pairs_path a)
  rw [h, canonicalLoopComponentsK0_trans, canonicalLoopComponentsK0_symm,
    generatorLoop_canonical, generatorLoop_canonical]
  abel

private def nativeDifference (a : SInverse (Core C) (Core C)) :
    GrothendieckAddGroup (Skeleton C) :=
  SInverseS.Pair.difference (CoreLocalizationComparison.toPairObj a)

private def differenceFundamental : SSet.FundamentalGroupoid
    (nerve (SInverse (Core C) (Core C))) ⥤ Discrete (GrothendieckAddGroup (Skeleton C)) := by
  letI : Groupoid (Discrete (GrothendieckAddGroup (Skeleton C))) := Groupoid.ofIsGroupoid
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let D : SInverse (Core C) (Core C) ⥤ Discrete (GrothendieckAddGroup (Skeleton C)) :=
    CoreLocalizationComparison.toPairFunctor (C := C) ⋙ SInverseS.differenceFunctor (C := C)
  exact SSet.FundamentalGroupoid.desc (X := K)
    (fun x : K _⦋0⦌ => D.obj (nerveEquiv x))
    (fun {x y} (e : K.Edge x y) => D.map (nerve.homEquiv e))
    (fun _ => Subsingleton.elim _ _)

omit [ExactCategory C] in
private theorem nativeDifference_of_joined (a b : SInverse (Core C) (Core C))
    (h : Joined (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ a))
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ b))) : nativeDifference a = nativeDifference b := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let a₀ : K _⦋0⦌ := ComposableArrows.mk₀ a
  let b₀ : K _⦋0⦌ := ComposableArrows.mk₀ b
  let R := SSet.realizationFundamentalGroupoidFunctor K
  let : R.IsEquivalence := SSet.realizationFundamentalGroupoidFunctor_isEquivalence K
  let eA : R.obj (SSet.FundamentalGroupoid.mk a₀) ≅
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex (X := K) a₀) :=
    eqToIso (SSet.realizationFundamentalGroupoidFunctor_obj_mk K a₀)
  let eB : R.obj (SSet.FundamentalGroupoid.mk b₀) ≅
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex (X := K) b₀) :=
    eqToIso (SSet.realizationFundamentalGroupoidFunctor_obj_mk K b₀)
  let topPath : _root_.FundamentalGroupoid.mk (SSet.realizedVertex (X := K) a₀) ⟶
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex (X := K) b₀) :=
    Path.Homotopic.Quotient.mk h.somePath
  let f : SSet.FundamentalGroupoid.mk a₀ ⟶ SSet.FundamentalGroupoid.mk b₀ :=
    R.preimage (eA.hom ≫ topPath ≫ eB.inv)
  let F := differenceFundamental (C := C)
  let : Groupoid (Discrete (GrothendieckAddGroup (Skeleton C))) := Groupoid.ofIsGroupoid
  let D : SInverse (Core C) (Core C) ⥤ Discrete (GrothendieckAddGroup (Skeleton C)) :=
    CoreLocalizationComparison.toPairFunctor (C := C) ⋙ SInverseS.differenceFunctor (C := C)
  let objectValues : K _⦋0⦌ → Discrete (GrothendieckAddGroup (Skeleton C)) :=
    fun x => D.obj (nerveEquiv x)
  let edgeValues : ∀ {x y : K _⦋0⦌}, K.Edge x y → (objectValues x ⟶ objectValues y) :=
    fun {x y} e => D.map (nerve.homEquiv e)
  let triangleLaw : ∀ {x₀ x₁ x₂ : K _⦋0⦌} {e₀₁ : K.Edge x₀ x₁}
      {e₁₂ : K.Edge x₁ x₂} {e₀₂ : K.Edge x₀ x₂},
      SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂ →
        edgeValues e₀₁ ≫ edgeValues e₁₂ = edgeValues e₀₂ :=
    fun _ => Subsingleton.elim _ _
  have hDescA : F.obj (SSet.FundamentalGroupoid.mk a₀) = objectValues a₀ := by
    change (SSet.FundamentalGroupoid.desc (X := K)
      objectValues edgeValues triangleLaw).obj (SSet.FundamentalGroupoid.mk a₀) = objectValues a₀
    exact SSet.FundamentalGroupoid.desc_obj_mk (X := K)
      (D := Discrete (GrothendieckAddGroup (Skeleton C))) objectValues edgeValues triangleLaw a₀
  have hDescB : F.obj (SSet.FundamentalGroupoid.mk b₀) = objectValues b₀ := by
    change (SSet.FundamentalGroupoid.desc (X := K)
      objectValues edgeValues triangleLaw).obj (SSet.FundamentalGroupoid.mk b₀) = objectValues b₀
    exact SSet.FundamentalGroupoid.desc_obj_mk (X := K)
      (D := Discrete (GrothendieckAddGroup (Skeleton C))) objectValues edgeValues triangleLaw b₀
  have hValueA : objectValues a₀ = Discrete.mk (nativeDifference a) := rfl
  have hValueB : objectValues b₀ = Discrete.mk (nativeDifference b) := rfl
  let dA : F.obj (SSet.FundamentalGroupoid.mk a₀) ≅ Discrete.mk (nativeDifference a) :=
    eqToIso (hDescA.trans hValueA)
  let dB : F.obj (SSet.FundamentalGroupoid.mk b₀) ≅ Discrete.mk (nativeDifference b) :=
    eqToIso (hDescB.trans hValueB)
  exact Discrete.eq_of_hom (dA.inv ≫ F.map f ≫ dB.hom)

omit [ExactCategory C] in
private theorem component_vertex (c : ZerothHomotopy
    (BasedSplitExactQLoop.completedCoreSpace (C := C))) :
    ∃ a : SInverse (Core C) (Core C),
      ZerothHomotopy.mk (SSet.realizedVertex
          (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ a)) = c := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  obtain ⟨q, hq⟩ := SSet.piZeroToZerothHomotopy_surjective K c
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective q
  obtain ⟨a, rfl⟩ := (nerveEquiv (C := SInverse (Core C) (Core C))).symm.surjective x
  exact ⟨a, (SSet.piZeroToZerothHomotopy_mk K (nerveEquiv.symm a)).symm.trans hq⟩

omit [ExactCategory C] in
/-- The ordinary completed-Core component's canonical positive-first Grothendieck difference. -/
def canonicalCoreComponentsGrothendieck :
    ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C)) →
      GrothendieckAddGroup (Skeleton C) := by
  let K : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let representatives : ∀ c : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C)),
      ∃ a : SInverse (Core C) (Core C),
        ZerothHomotopy.mk (SSet.realizedVertex (X := K) (ComposableArrows.mk₀ a)) = c := by
    intro c
    obtain ⟨q, hq⟩ := SSet.piZeroToZerothHomotopy_surjective K c
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective q
    obtain ⟨a, rfl⟩ := (nerveEquiv (C := SInverse (Core C) (Core C))).symm.surjective x
    exact ⟨a, (SSet.piZeroToZerothHomotopy_mk K (nerveEquiv.symm a)).symm.trans hq⟩
  exact fun c => SInverseS.Pair.difference
    (CoreLocalizationComparison.toPairObj (Classical.choose (representatives c)))

omit [ExactCategory C] in
/-- This canonical dictionary retains the original numerator and denominator of every native
pair. -/
theorem canonicalCoreComponentsGrothendieck_mk (a : SInverse (Core C) (Core C)) :
    canonicalCoreComponentsGrothendieck
      (ZerothHomotopy.mk (SSet.realizedVertex
          (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ a))) =
      SInverseS.Pair.difference (CoreLocalizationComparison.toPairObj a) := by
  let c :=
      ZerothHomotopy.mk (SSet.realizedVertex
        (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) (ComposableArrows.mk₀ a))
  have hc := Classical.choose_spec (component_vertex (C := C) c)
  have hj : Joined (SSet.realizedVertex
      (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) (ComposableArrows.mk₀
      (Classical.choose (component_vertex (C := C) c))))
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ a)) := Quotient.exact hc
  change nativeDifference (Classical.choose (component_vertex (C := C) c)) = nativeDifference a
  exact nativeDifference_of_joined _ _ hj

/-- The independently defined Grothendieck-to-exact-K₀ comparison on ALL ordinary components. -/
def canonicalCoreComponentsK0 :
    ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C)) → K0 C :=
  fun c => K0.grothendieckToK0 C (canonicalCoreComponentsGrothendieck c)

/-- The actual original comparison commutes with the already-landed Q/S and canonical K₀ maps on
ALL components. -/
theorem comparison_components_canonical :
    canonicalLoopComponentsK0 (C := C) ∘
      TopCat.zerothHomotopyMap (BasedSplitExactQLoop.comparisonMap (C := C)) =
        canonicalCoreComponentsK0 (C := C) := by
  funext c
  obtain ⟨a, ha⟩ := component_vertex (C := C) c
  let v : BasedSplitExactQLoop.completedCoreSpace (C := C) := SSet.realizedVertex
    (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) (ComposableArrows.mk₀ a)
  have hMap := TopCat.zerothHomotopyMap_mk (BasedSplitExactQLoop.comparisonMap (C := C)) v
  have hActual : canonicalLoopComponentsK0 (C := C)
      (TopCat.zerothHomotopyMap (BasedSplitExactQLoop.comparisonMap (C := C))
          (ZerothHomotopy.mk v)) =
        K0.mk a.of.1.of - K0.mk a.of.2.of :=
    (congrArg (canonicalLoopComponentsK0 (C := C)) hMap).trans (comparison_all_pairs a)
  have hCanonical : canonicalCoreComponentsK0 (C := C) (ZerothHomotopy.mk v) =
      K0.mk a.of.1.of - K0.mk a.of.2.of := by
    have h := congrArg (K0.grothendieckToK0 C) (canonicalCoreComponentsGrothendieck_mk a)
    exact h.trans (by
      simp only [SInverseS.Pair.difference, CoreLocalizationComparison.toPairObj,
        map_sub, K0.grothendieckToK0_of_toSkeleton])
  have hValue := hActual.trans hCanonical.symm
  exact (congrArg (fun d : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C)) =>
      canonicalLoopComponentsK0 (TopCat.zerothHomotopyMap
        (BasedSplitExactQLoop.comparisonMap (C := C)) d)) ha.symm).trans
    (hValue.trans (congrArg (canonicalCoreComponentsK0 (C := C)) ha))

/-- The zero pair is the SAME specified constant original loop, retaining the existing full-point
law. -/
theorem comparison_zero :
    BasedSplitExactQLoop.comparisonMap (C := C) (BasedSplitExactQLoop.completedCorePoint (C := C)) =
      BasedSplitExactQLoop.constantQLoop (C := C) :=
  BasedSplitExactQLoop.comparisonMap_point

section Projective

universe uRing vModule

variable (R : Type uRing) [Ring R]

/-- Every original projective pair maps to its usual difference in FIXED RingK₀, for independent
module universe. -/
theorem projective_comparison_all_pairs (P D : FGProjectiveCat.{max uRing vModule} R) :
    RingK0.projectiveUniverseEquiv.{uRing, vModule} R
      (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uRing vModule} R)
        (ZerothHomotopy.mk (BasedSplitExactQLoop.comparisonMap
          (C := FGProjectiveCat.{max uRing vModule} R)
            (SSet.realizedVertex
              (X := (nerve (SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
                (Core (FGProjectiveCat.{max uRing vModule} R))) :
                    SSet.{max (uRing + 1) (vModule + 1)}))
              (ComposableArrows.mk₀
              (⟨((⟨P⟩ : Core (FGProjectiveCat.{max uRing vModule} R)),
                  (⟨D⟩ : Core (FGProjectiveCat.{max uRing vModule} R)))⟩ :
                SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
                  (Core (FGProjectiveCat.{max uRing vModule} R)))))))) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{uRing, vModule} R P) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{uRing, vModule} R D) := by
  rw [comparison_all_pairs, map_sub, RingK0.projectiveUniverseEquiv_mk,
    RingK0.projectiveUniverseEquiv_mk]

/-- The actual original loop image agrees with the existing independent-size categorical Pair
dictionary. -/
theorem projective_comparison_component_dictionary
    (a : SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
      (Core (FGProjectiveCat.{max uRing vModule} R))) :
    RingK0.projectiveUniverseEquiv.{uRing, vModule} R
      (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uRing vModule} R)
        (ZerothHomotopy.mk (BasedSplitExactQLoop.comparisonMap
          (C := FGProjectiveCat.{max uRing vModule} R)
            (SSet.realizedVertex
              (X := (nerve (SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
                (Core (FGProjectiveCat.{max uRing vModule} R))) :
                    SSet.{max (uRing + 1) (vModule + 1)}))
              (ComposableArrows.mk₀ a))))) =
      RingK0.sInverseSComponentsUniverseEquiv.{uRing, vModule} R
        (CategoryTheory.ConnectedComponents.mk (CoreLocalizationComparison.toPairObj a)) := by
  rw [comparison_all_pairs, RingK0.sInverseSComponentsUniverseEquiv_mk,
    map_sub, RingK0.projectiveUniverseEquiv_mk, RingK0.projectiveUniverseEquiv_mk]
  rfl

end Projective

end AlgebraicKTheory.OriginalQK0Comparison

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal CategoryTheory.MonoidalCategory

namespace AlgebraicKTheory.OriginalQK0Comparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] MonoidalActionCategory.diagonalAction

omit [ExactCategory C] in
/-- Every original realized completed-Core component has an original pair-vertex representative. -/
public theorem canonicalCoreComponents_vertex_surjective
    (c : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C))) :
    ∃ a : SInverse (Core C) (Core C),
      ZerothHomotopy.mk (SSet.realizedVertex
        (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ a)) = c :=
  component_vertex c

private theorem originalCanonicalCoreK0VertexComputed (a : SInverse (Core C) (Core C)) :
    canonicalCoreComponentsK0 (C := C) (ZerothHomotopy.mk (SSet.realizedVertex
      (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
      (ComposableArrows.mk₀ a))) = K0.mk a.of.1.of - K0.mk a.of.2.of := by
  have h := congrArg (K0.grothendieckToK0 C) (canonicalCoreComponentsGrothendieck_mk a)
  exact h.trans (by
    simp only [SInverseS.Pair.difference, CoreLocalizationComparison.toPairObj,
      map_sub, K0.grothendieckToK0_of_toSkeleton])

/-- The existing canonical K0 evaluator retains the difference of both original pair coordinates. -/
public theorem canonicalCoreComponentsK0_mk (a : SInverse (Core C) (Core C)) :
    canonicalCoreComponentsK0 (C := C) (ZerothHomotopy.mk (SSet.realizedVertex
      (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
      (ComposableArrows.mk₀ a))) = K0.mk a.of.1.of - K0.mk a.of.2.of :=
  originalCanonicalCoreK0VertexComputed a

end AlgebraicKTheory.OriginalQK0Comparison

end


public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

universe uK0 vK0

namespace AlgebraicKTheory.OriginalQK0Comparison

variable {C : Type uK0} [Category.{vK0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] CategoryTheory.ExactCategory.waldhausenCategory

/-- The original Q-component evaluator agrees with its same canonical
fundamental-group evaluator on every class. -/
theorem canonicalQComponents_fundamental (c : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 C c = Multiplicative.toAdd
      (NQRealizedFundamentalK0MulEquiv C
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) c)) :=
  qFacade_eq_fundamental (C := C) c

end AlgebraicKTheory.OriginalQK0Comparison

end
