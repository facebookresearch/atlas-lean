/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiber
public import MathlibExt.KTheory.Exact.Quillen.QuillenUnderlyingCoreEquivalence
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalence

/-!
# Degree-zero connectedness of Quillen Stage-grid fibers

An isomorphism in the Quillen Q-construction between two underlying objects
forces those objects to be isomorphic.  The proof chooses spans representing
the isomorphism and its inverse.  Each composite is isomorphic to an identity
span, so regular epi/mono cancellation makes both legs of the first span
isomorphisms.  This uses no balancedness or abelian-category assumption.

The strengthened lift theorem shows that the chosen underlying isomorphism
reproduces the given Q-isomorphism exactly.  In degree zero this supplies the
compatibility needed to connect any two objects of the strict Stage-grid fiber.

This file proves only degree-zero fiber connectedness.  It makes no
positive-degree connectedness, contractibility, finality, weak-equivalence,
nerve/realization, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridFiberDegreeZeroWaldhausenCategory :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- Lift an isomorphism between the unique cross objects of two degree-one
weak Stages to an isomorphism of those weak Stages. -/
private noncomputable def degreeZeroGridIso
    (A B : StageWeakCategory C (edgewiseQ.obj ⦋0⦌).len)
    (e : edgewiseStageVertex A.obj (0 : Fin 1) ≅
      edgewiseStageVertex B.obj (0 : Fin 1)) : A ≅ B := by
  let hff : (stageOneEval C).FullyFaithful :=
    (stageOneEquivalence C).fullyFaithfulInverse
  let eStage : A.obj ≅ B.obj := hff.preimageIso e
  have hHom : stageWeak C 1 eStage.hom := by
    change ∀ a, IsWeakEquivalence ((eval C 1 a).map eStage.hom)
    intro a
    have hIso : IsIso ((eval C 1 a).map eStage.hom) :=
      ((eval C 1 a).mapIso eStage).isIso_hom
    exact hIso
  have hInv : stageWeak C 1 eStage.inv := by
    change ∀ a, IsWeakEquivalence ((eval C 1 a).map eStage.inv)
    intro a
    have hIso : IsIso ((eval C 1 a).map eStage.inv) :=
      ((eval C 1 a).mapIso eStage).isIso_inv
    exact hIso
  exact WideSubcategory.isoMk eStage hHom hInv

/-- The unique extracted Q-vertex of `degreeZeroGridIso` is the supplied
underlying isomorphism. -/
private theorem degreeZeroGridIso_vertexIso
    (A B : StageWeakCategory C (edgewiseQ.obj ⦋0⦌).len)
    (e : edgewiseStageVertex A.obj (0 : Fin 1) ≅
      edgewiseStageVertex B.obj (0 : Fin 1)) :
    edgewiseStageVertexIso (degreeZeroGridIso A B e).hom (0 : Fin 1) = e := by
  apply Iso.ext
  let hff : (stageOneEval C).FullyFaithful :=
    (stageOneEquivalence C).fullyFaithfulInverse
  change (stageOneEval C).map (hff.preimage e.hom) = e.hom
  exact hff.map_preimage e.hom

/-- A direct morphism between any two objects in one degree-zero strict
Stage-grid fiber. -/
private noncomputable def degreeZeroFiberHom
    (q : QuillenQSimplex C ⦋0⦌)
    (X Y : QuillenStageGridFiber q) : X ⟶ Y := by
  let hXq : X.1.q = q := congrArg Discrete.as X.2
  let hYq : Y.1.q = q := congrArg Discrete.as Y.2
  let hXY : X.1.q = Y.1.q := hXq.trans hYq.symm
  let dIso : Discrete.mk X.1.q ≅ Discrete.mk Y.1.q :=
    eqToIso (Discrete.ext hXY)
  let qIso : X.1.q ≅ Y.1.q :=
    (quillenQSimplexDiscreteInclusion C ⦋0⦌).mapIso dIso
  let eNat :
      (edgewiseStageQuillenSimplexFunctor C ⦋0⦌).obj X.1.grid ≅
        (edgewiseStageQuillenSimplexFunctor C ⦋0⦌).obj Y.1.grid :=
    X.1.agreementIso.trans (qIso.trans Y.1.agreementIso.symm)
  let eQ :
      (⟨edgewiseStageVertex X.1.grid.obj (0 : Fin 1)⟩ : QuillenQ C) ≅
        ⟨edgewiseStageVertex Y.1.grid.obj (0 : Fin 1)⟩ :=
    eNat.app 0
  let lift := Classical.choice (quillenQ_iso_lifts_to_underlying_iso_eq eQ)
  let eC := lift.1
  have heC := lift.2
  let gIso : X.1.grid ≅ Y.1.grid :=
    degreeZeroGridIso X.1.grid Y.1.grid eC
  let g : X.1.grid ⟶ Y.1.grid := gIso.hom
  have hMap :
      (edgewiseStageQuillenSimplexFunctor C ⦋0⦌).map g = eNat.hom := by
    change edgewiseStageQuillenSimplexMap g = eNat.hom
    apply ComposableArrows.hom_ext₀
    change (edgewiseStageQuillenSimplexMap g).app (0 : Fin 1) =
      eNat.hom.app (0 : Fin 1)
    rw [edgewiseStageQuillenSimplexMap_app]
    have hv := degreeZeroGridIso_vertexIso X.1.grid Y.1.grid eC
    have he := congrArg Iso.hom heC
    rw [hv, he]
    rfl
  have hW :
      (edgewiseStageQuillenSimplexFunctor C ⦋0⦌).map g ≫
          Y.1.obj.hom =
        X.1.obj.hom ≫
          (quillenQSimplexDiscreteInclusion C ⦋0⦌).map dIso.hom := by
    rw [hMap]
    have hIsoComp :
        eNat.hom ≫ Y.1.agreementIso.hom =
          X.1.agreementIso.hom ≫ qIso.hom := by
      change (X.1.agreementIso.hom ≫ qIso.hom ≫
          Y.1.agreementIso.inv) ≫ Y.1.agreementIso.hom =
        X.1.agreementIso.hom ≫ qIso.hom
      calc
        (X.1.agreementIso.hom ≫ qIso.hom ≫
            Y.1.agreementIso.inv) ≫ Y.1.agreementIso.hom =
          X.1.agreementIso.hom ≫
            ((qIso.hom ≫ Y.1.agreementIso.inv) ≫
              Y.1.agreementIso.hom) := Category.assoc _ _ _
        _ = X.1.agreementIso.hom ≫
            (qIso.hom ≫
              (Y.1.agreementIso.inv ≫ Y.1.agreementIso.hom)) :=
          congrArg (fun f ↦ X.1.agreementIso.hom ≫ f)
            (Category.assoc _ _ _)
        _ = X.1.agreementIso.hom ≫ (qIso.hom ≫ 𝟙 _) :=
          congrArg (fun f ↦
            X.1.agreementIso.hom ≫ (qIso.hom ≫ f))
            Y.1.agreementIso.inv_hom_id
        _ = X.1.agreementIso.hom ≫ qIso.hom := by
          rw [Category.comp_id]
    have hIsoComp' := hIsoComp
    simp only [QuillenStageGridLift.agreementIso_hom] at hIsoComp'
    change eNat.hom ≫ Y.1.obj.hom =
      X.1.obj.hom ≫ qIso.hom at hIsoComp'
    apply eq_of_heq
    exact heq_of_eq hIsoComp'
  let fComma : X.1.obj ⟶ Y.1.obj :=
    { left := g
      right := dIso.hom
      w := hW }
  let fLift : X.1 ⟶ Y.1 := ObjectProperty.homMk fComma
  refine ⟨fLift, ?_⟩
  apply IsHomLift.of_fac
    (quillenStageGridQProjection C ⦋0⦌)
    (𝟙 (Discrete.mk q)) fLift X.2 Y.2
  exact Subsingleton.elim _ _

set_option linter.style.haveILetI false in
/-- Every strict Stage-grid fiber in degree zero is connected.  This is a
degree-zero statement only. -/
theorem quillenStageGridFiber_degreeZero_isConnected
    (q : QuillenQSimplex C ⦋0⦌) :
    IsConnected (QuillenStageGridFiber q) := by
  letI : Nonempty (QuillenStageGridFiber q) :=
    quillenStageGridFiber_nonempty q
  apply zigzag_isConnected
  intro X Y
  exact Relation.ReflTransGen.single
    (Zag.of_hom (degreeZeroFiberHom q X Y))

end AlgebraicKTheory

end
