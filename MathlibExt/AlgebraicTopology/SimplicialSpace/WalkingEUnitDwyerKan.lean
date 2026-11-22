/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalExponentClosure
import MathlibExt.AlgebraicTopology.SimplicialSpace.CategoricalHomotopyPrism
import MathlibExt.AlgebraicTopology.SimplicialSet.WalkingEContraction
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# The original walking-E evaluation and section

The coefficient is the actual discrete-inner walking-groupoid E. The power
is the native Cartesian exponential. Its categorical homotopy is constructed
from the actual E-contraction by currying, and all mapping-fibre maps retain
their original prescribed vertices. Only original Reedy-fibrant Segal spaces
are caller inputs to the final Dwyer--Kan conclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner SimplicialSpace.Cartesian
open scoped SSet.modelCategoryQuillen

namespace SimplicialSpace.WalkingEUnit
open SegalHomotopy
attribute [local instance] ReedyModel.modelCategory

/-- The original walking-groupoid coefficient on the designated simplicial-space carrier. -/
def coherentSpace : SimplicialSpace.{u} := discreteInnerFunctor.obj SSet.coherentIso

/-- The SAME chosen Cartesian power, with no new carrier or replacement selection. -/
def powerSpace (W : SimplicialSpace.{u}) : SimplicialSpace.{u} :=
  (SegalExponentSupport.outerPower SSet.coherentIso).obj W

private theorem discretePreservesTerminal :
    PreservesLimit (Functor.empty.{0} SSet.{u}) discreteInnerFunctor := by
  dsimp only [discreteInnerFunctor, SSet.simplicialSpaceDiscrete]
  infer_instance
attribute [local instance] discretePreservesTerminal

/-- The actual terminal comparison identifies the coefficient functor's original unit. -/
def coherentUnitIso : discreteInnerFunctor.obj (𝟙_ SSet.{u}) ≅ (𝟙_ SimplicialSpace.{u}) :=
  CartesianMonoidalCategory.preservesTerminalIso discreteInnerFunctor

/-- The actual original E vertex is inserted from the chosen simplicial-space unit. -/
def coherentPoint (e : SSet.coherentIso.{u} _⦋0⦌) :
    (𝟙_ SimplicialSpace.{u}) ⟶ coherentSpace.{u} :=
  coherentUnitIso.inv ≫ discreteInnerFunctor.map ((SSet.unitHomEquiv SSet.coherentIso).symm e)

/-- Entire endpoint insertion into the SAME Cartesian coefficient tensor. -/
def spaceEndpoint (W : SimplicialSpace.{u}) (e : SSet.coherentIso.{u} _⦋0⦌) :
    W ⟶ coherentSpace.{u} ⊗ W := (λ_ W).inv ≫ (coherentPoint e ▷ W)

/-- Both Cartesian legs and the literal original raw endpoint are retained. -/
theorem spaceEndpoint_laws (W : SimplicialSpace.{u}) (e : SSet.coherentIso.{u} _⦋0⦌) :
    spaceEndpoint W e ≫ CartesianMonoidalCategory.fst coherentSpace W =
        toUnit W ≫ coherentPoint e ∧
    spaceEndpoint W e ≫ CartesianMonoidalCategory.snd coherentSpace W = 𝟙 W ∧
    (spaceEndpoint W e).hom = CategoricalHomotopyPrism.tensorEndpoint W e := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [spaceEndpoint, Category.assoc, whiskerRight_fst, leftUnitor_inv_fst_assoc]
  · simp only [spaceEndpoint, Category.assoc, whiskerRight_snd, leftUnitor_inv_snd]
  · apply NatTrans.ext
    funext m
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl

private theorem discreteConst_eq (e : SSet.coherentIso.{u} _⦋0⦌) :
    discreteInnerFunctor.map (SSet.const (X := SSet.coherentIso) e) =
      toUnit coherentSpace ≫ coherentPoint e := by
  dsimp +instances only [coherentSpace, coherentPoint]
  have hc : SSet.const (X := SSet.coherentIso) e =
      toUnit SSet.coherentIso ≫ (SSet.unitHomEquiv SSet.coherentIso).symm e := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have ht : discreteInnerFunctor.map (toUnit SSet.coherentIso) =
      toUnit (discreteInnerFunctor.obj SSet.coherentIso) ≫ coherentUnitIso.inv := by
    apply (cancel_mono coherentUnitIso.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact toUnit_unique _ _
  rw [hc, CategoryTheory.Functor.map_comp, ht, Category.assoc]

private theorem discreteLift (f g : SSet.coherentIso.{u} ⟶ SSet.coherentIso.{u}) :
    discreteInnerFunctor.map (CartesianMonoidalCategory.lift f g) =
      CartesianMonoidalCategory.lift (discreteInnerFunctor.map f) (discreteInnerFunctor.map g) ≫
        (SegalExponentRawAssembly.discreteTensorIso SSet.coherentIso SSet.coherentIso).hom := by
  apply (cancel_mono
    (SegalExponentRawAssembly.discreteTensorIso SSet.coherentIso SSet.coherentIso).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change discreteInnerFunctor.map (CartesianMonoidalCategory.lift f g) ≫
      CartesianMonoidalCategory.prodComparison discreteInnerFunctor SSet.coherentIso
          SSet.coherentIso =
    CartesianMonoidalCategory.lift (discreteInnerFunctor.map f) (discreteInnerFunctor.map g)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
      ← CategoryTheory.Functor.map_comp, lift_fst]
  · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
      ← CategoryTheory.Functor.map_comp, lift_snd]

/-- Lift the whole original E × E categorical conjunction through the actual D product
comparison. -/
def spaceContraction : coherentSpace.{u} ⊗ coherentSpace.{u} ⟶ coherentSpace.{u} :=
  (SegalExponentRawAssembly.discreteTensorIso SSet.coherentIso SSet.coherentIso).hom ≫
    discreteInnerFunctor.map SSet.CategoricalEContraction.contraction

/-- The lifted whole contraction has BOTH original endpoints and original zero stationarity. -/
theorem spaceContraction_endpoints :
    CartesianMonoidalCategory.lift (𝟙 coherentSpace.{u})
        (toUnit coherentSpace ≫ coherentPoint SSet.coherentIso.x₀) ≫ spaceContraction =
      toUnit coherentSpace ≫ coherentPoint SSet.coherentIso.x₀ ∧
    CartesianMonoidalCategory.lift (𝟙 coherentSpace.{u})
        (toUnit coherentSpace ≫ coherentPoint SSet.coherentIso.x₁) ≫ spaceContraction =
      𝟙 coherentSpace ∧
    CartesianMonoidalCategory.lift
        (toUnit coherentSpace ≫ coherentPoint SSet.coherentIso.x₀)
        (𝟙 coherentSpace.{u}) ≫ spaceContraction =
      toUnit coherentSpace ≫ coherentPoint SSet.coherentIso.x₀ := by
  have hz := congrArg discreteInnerFunctor.map SSet.CategoricalEContraction.contraction_zero.{u}
  have ho := congrArg discreteInnerFunctor.map SSet.CategoricalEContraction.contraction_one.{u}
  have hl := congrArg discreteInnerFunctor.map
      SSet.CategoricalEContraction.contraction_zero_left.{u}
  simp only [CategoryTheory.Functor.map_comp, discreteLift, CategoryTheory.Functor.map_id,
    discreteConst_eq, Category.assoc] at hz ho hl
  exact ⟨hz, ho, hl⟩

/-- The original constant-power map is the native curry of the actual second projection. -/
def constantPower (W : SimplicialSpace.{u}) : W ⟶ powerSpace W :=
  curry (CartesianMonoidalCategory.snd coherentSpace W)

/-- Evaluation at the original zero vertex uses the same native power and counit. -/
def zeroEvaluation (W : SimplicialSpace.{u}) : powerSpace W ⟶ W :=
  spaceEndpoint (powerSpace W) SSet.coherentIso.x₀ ≫ (ihom.ev coherentSpace).app W

/-- The actual constant-power map is natural on every original simplicial-space morphism. -/
theorem constantPower_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f ≫ constantPower V = constantPower W ≫
      (SegalExponentSupport.outerPower SSet.coherentIso).map f := by
  dsimp +instances only [constantPower, powerSpace, SegalExponentSupport.outerPower, coherentSpace]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_right, uncurry_curry]
  exact CartesianMonoidalCategory.whiskerLeft_snd _ _

private theorem endpoint_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    f ≫ spaceEndpoint V e = spaceEndpoint W e ≫ (coherentSpace ◁ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      (f ≫ spaceEndpoint V e) ≫ CartesianMonoidalCategory.fst coherentSpace V =
          (f ≫ toUnit V) ≫ coherentPoint e := by
        rw [Category.assoc, (spaceEndpoint_laws V e).1, ← Category.assoc]
      _ = toUnit W ≫ coherentPoint e :=
        congrArg (fun k : W ⟶ (𝟙_ SimplicialSpace) => k ≫ coherentPoint e)
          (toUnit_unique (f ≫ toUnit V) (toUnit W))
      _ = (spaceEndpoint W e ≫ (coherentSpace ◁ f)) ≫
          CartesianMonoidalCategory.fst coherentSpace V := by
        rw [Category.assoc, whiskerLeft_fst, (spaceEndpoint_laws W e).1]
  · calc
      (f ≫ spaceEndpoint V e) ≫ CartesianMonoidalCategory.snd coherentSpace V = f := by
        rw [Category.assoc, (spaceEndpoint_laws V e).2.1, Category.comp_id]
      _ = (spaceEndpoint W e ≫ (coherentSpace ◁ f)) ≫
          CartesianMonoidalCategory.snd coherentSpace V := by
        rw [Category.assoc, whiskerLeft_snd, ← Category.assoc,
          (spaceEndpoint_laws W e).2.1, Category.id_comp]

/-- The SAME zero-evaluation map is natural on every original morphism and native power map. -/
theorem zeroEvaluation_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (SegalExponentSupport.outerPower SSet.coherentIso).map f ≫ zeroEvaluation V =
      zeroEvaluation W ≫ f := by
  have he : (coherentSpace ◁ (SegalExponentSupport.outerPower SSet.coherentIso).map f) ≫
      (ihom.ev coherentSpace).app V = (ihom.ev coherentSpace).app W ≫ f :=
    (ihom.ev coherentSpace).naturality f
  have hn := endpoint_naturality ((SegalExponentSupport.outerPower SSet.coherentIso).map f)
    SSet.coherentIso.x₀
  dsimp +instances only [zeroEvaluation, spaceEndpoint, coherentPoint, coherentSpace,
    powerSpace, SegalExponentSupport.outerPower] at he hn ⊢
  rw [← Category.assoc, hn, Category.assoc, he]
  simp only [Category.assoc]

/-- The SAME original constant map and zero evaluation satisfy the entire strict unit equation. -/
theorem constantPower_zeroEvaluation (W : SimplicialSpace.{u}) :
    constantPower W ≫ zeroEvaluation W = 𝟙 W := by
  have ht : (coherentSpace ◁ constantPower W) ≫ (ihom.ev coherentSpace).app W =
      CartesianMonoidalCategory.snd coherentSpace W := by
    dsimp +instances only [constantPower, powerSpace, SegalExponentSupport.outerPower,
        coherentSpace]
    rw [← uncurry_eq, uncurry_curry]
  have hn := endpoint_naturality (constantPower W) SSet.coherentIso.x₀
  have hs := (spaceEndpoint_laws W SSet.coherentIso.x₀).2.1
  dsimp +instances only [zeroEvaluation, constantPower, spaceEndpoint, coherentPoint,
    coherentSpace, powerSpace, SegalExponentSupport.outerPower] at ht hn hs ⊢
  rw [← Category.assoc, hn, Category.assoc, ht]
  exact hs

private theorem insertion_associator (W : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    (coherentSpace ◁ spaceEndpoint W e) ≫ (α_ coherentSpace coherentSpace W).inv =
      (CartesianMonoidalCategory.lift (𝟙 coherentSpace)
        (toUnit coherentSpace ≫ coherentPoint e)) ▷ W := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, associator_inv_fst_fst, whiskerLeft_fst,
        whiskerRight_fst_assoc, lift_fst, Category.comp_id]
    · simp only [Category.assoc, associator_inv_fst_snd, whiskerLeft_snd_assoc,
        (spaceEndpoint_laws W e).1, whiskerRight_fst_assoc, lift_snd]
      simpa only [Category.assoc] using
        congrArg (fun k : coherentSpace ⊗ W ⟶ (𝟙_ SimplicialSpace) => k ≫ coherentPoint e)
          (toUnit_unique (CartesianMonoidalCategory.snd coherentSpace W ≫ toUnit W)
            (CartesianMonoidalCategory.fst coherentSpace W ≫ toUnit coherentSpace))
  · simp only [Category.assoc, associator_inv_snd, whiskerLeft_snd_assoc,
      (spaceEndpoint_laws W e).2.1, whiskerRight_snd, Category.comp_id]

private theorem terminalWhisker (W : SimplicialSpace.{u}) :
    (toUnit coherentSpace ▷ W) =
      CartesianMonoidalCategory.snd coherentSpace W ≫ (λ_ W).inv := by
  apply CartesianMonoidalCategory.hom_ext
  · exact toUnit_unique _ _
  · simp only [whiskerRight_snd, Category.assoc, leftUnitor_inv_snd, Category.comp_id]

/-- The actual categorical E homotopy is the native transpose of the lifted conjunction. -/
def powerCategoricalHomotopy (W : SimplicialSpace.{u}) :
    (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj (powerSpace W).diagram ⟶
      (powerSpace W).diagram :=
  (curry ((α_ coherentSpace coherentSpace (powerSpace W)).inv ≫
    (spaceContraction ▷ powerSpace W) ≫ (ihom.ev coherentSpace).app W)).hom

/-- Both entire original raw endpoints are proved by native transposition and the actual E
contraction. -/
theorem powerCategoricalHomotopy_endpoints (W : SimplicialSpace.{u}) :
    CategoricalHomotopyPrism.tensorEndpoint (powerSpace W) SSet.coherentIso.x₀ ≫
        powerCategoricalHomotopy W = (zeroEvaluation W ≫ constantPower W).hom ∧
    CategoricalHomotopyPrism.tensorEndpoint (powerSpace W) SSet.coherentIso.x₁ ≫
        powerCategoricalHomotopy W = (𝟙 (powerSpace W) : powerSpace W ⟶ powerSpace W).hom := by
  have hz : spaceEndpoint (powerSpace W) SSet.coherentIso.x₀ ≫
      curry ((α_ coherentSpace coherentSpace (powerSpace W)).inv ≫
        (spaceContraction ▷ powerSpace W) ≫ (ihom.ev coherentSpace).app W) =
        zeroEvaluation W ≫ constantPower W := by
    have hi := insertion_associator (powerSpace W) SSet.coherentIso.x₀
    have hc := spaceContraction_endpoints.{u}.1
    have ht := terminalWhisker (powerSpace W)
    have hs := CartesianMonoidalCategory.whiskerLeft_snd coherentSpace (zeroEvaluation W)
    dsimp +instances only [zeroEvaluation, constantPower, spaceEndpoint, coherentPoint,
      coherentSpace, powerSpace, SegalExponentSupport.outerPower, spaceContraction] at hi hc ht hs ⊢
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry]
    rw [← Category.assoc, hi]
    rw [← Category.assoc, ← comp_whiskerRight, hc, comp_whiskerRight, ht]
    simpa only [Category.assoc] using hs.symm
  have ho : spaceEndpoint (powerSpace W) SSet.coherentIso.x₁ ≫
      curry ((α_ coherentSpace coherentSpace (powerSpace W)).inv ≫
        (spaceContraction ▷ powerSpace W) ≫ (ihom.ev coherentSpace).app W) =
        𝟙 (powerSpace W) := by
    have hi := insertion_associator (powerSpace W) SSet.coherentIso.x₁
    have hc := spaceContraction_endpoints.{u}.2.1
    dsimp +instances only [zeroEvaluation, constantPower, spaceEndpoint, coherentPoint,
      coherentSpace, powerSpace, SegalExponentSupport.outerPower, spaceContraction] at hi hc ⊢
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry,
      uncurry_id_eq_ev (discreteInnerFunctor.obj SSet.coherentIso) W]
    rw [← Category.assoc, hi, ← Category.assoc, ← comp_whiskerRight,
      hc, id_whiskerRight, Category.id_comp]
  constructor
  · have h := congrArg (fun k : powerSpace W ⟶ powerSpace W => k.hom) hz
    change (spaceEndpoint (powerSpace W) SSet.coherentIso.x₀).hom ≫
      powerCategoricalHomotopy W = (zeroEvaluation W ≫ constantPower W).hom at h
    rw [(spaceEndpoint_laws (powerSpace W) SSet.coherentIso.x₀).2.2] at h
    exact h
  · have h := congrArg (fun k : powerSpace W ⟶ powerSpace W => k.hom) ho
    change (spaceEndpoint (powerSpace W) SSet.coherentIso.x₁).hom ≫
      powerCategoricalHomotopy W = (𝟙 (powerSpace W) : powerSpace W ⟶ powerSpace W).hom at h
    rw [(spaceEndpoint_laws (powerSpace W) SSet.coherentIso.x₁).2.2] at h
    exact h

/-- Actual Reedy RF and Segal locality of the same power are derived from the proved discrete
exponent theorem. -/
theorem powerSpace_segal (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    segalSpaces (powerSpace W) := SegalExponentRawAssembly.outerPower_segal SSet.coherentIso W hW

private theorem endMap_weak {F : SimplicialSpace.{u}} (g : F ⟶ F) (hF : segalSpaces F)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj F.diagram ⟶ F.diagram)
    (h₀ : CategoricalHomotopyPrism.tensorEndpoint F SSet.coherentIso.x₀ ≫ H = g.hom)
    (h₁ : CategoricalHomotopyPrism.tensorEndpoint F SSet.coherentIso.x₁ ≫ H = (𝟙 F : F ⟶ F).hom)
    (z z' : (F.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map g (x := z) (y := z') rfl rfl) := by
  have hi : SSet.realizationWeakEquivalences
      (mappingFibre.map (𝟙 F) (x := z) (y := z') rfl rfl) := by
    rw [mappingFibre.map_id]
    exact SSet.realizationWeakEquivalences.id_mem _
  exact (CategoricalHomotopyPrism.mappingFibreWeak_iff g (𝟙 F) hF H h₀ h₁ z z').mpr hi

private theorem prescribedMap_weak {F : SimplicialSpace.{u}} (g : F ⟶ F)
    {z z' w w' : (F.diagram _⦋0⦌) _⦋0⦌}
    (hz : mappingVertexMap g z = w) (hz' : mappingVertexMap g z' = w')
    (hg : SSet.realizationWeakEquivalences (mappingFibre.map g (x := z) (y := z') rfl rfl)) :
    SSet.realizationWeakEquivalences (mappingFibre.map g hz hz') := by
  rw [mappingFibre.map_eq_comp_eqToHom]
  exact (SSet.realizationWeakEquivalences.postcomp_iff _ _
    (SSet.realizationWeakEquivalences.of_isIso _)).mpr hg

private theorem originalSection_weak {W F : SimplicialSpace.{u}} (j : W ⟶ F) (e : F ⟶ W)
    (hj : j ≫ e = 𝟙 W) (hF : segalSpaces F)
    (H : (SSet.simplicialSpaceTensor.obj SSet.coherentIso).obj F.diagram ⟶ F.diagram)
    (h₀ : CategoricalHomotopyPrism.tensorEndpoint F SSet.coherentIso.x₀ ≫ H = (e ≫ j).hom)
    (h₁ : CategoricalHomotopyPrism.tensorEndpoint F SSet.coherentIso.x₁ ≫ H = (𝟙 F : F ⟶ F).hom)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map j (x := x) (y := y) rfl rfl) := by
  have hx : mappingVertexMap e (mappingVertexMap j x) = x := by
    change mappingVertexMap (j ≫ e) x = x
    rw [hj]
    rfl
  have hy : mappingVertexMap e (mappingVertexMap j y) = y := by
    change mappingVertexMap (j ≫ e) y = y
    rw [hj]
    rfl
  let p := mappingFibre.map j (x := x) (y := y) rfl rfl
  let q := mappingFibre.map e hx hy
  have hpq : p ≫ q = 𝟙 (mappingFibre W x y) := by
    dsimp only [p, q]
    have hid (a : W ⟶ W) (ha : a = 𝟙 W)
        (hx : mappingVertexMap a x = x) (hy : mappingVertexMap a y = y) :
        mappingFibre.map a hx hy = 𝟙 (mappingFibre W x y) := by
      subst a
      rw [mappingFibre.map_id_eqToHom]
      exact eqToHom_refl (mappingFibre W x y) _
    exact (mappingFibre.map_comp j e rfl rfl hx hy).trans (hid (j ≫ e) hj _ _)
  have hqp : SSet.realizationWeakEquivalences (q ≫ p) := by
    dsimp only [p, q]
    rw [mappingFibre.map_comp]
    apply prescribedMap_weak
    exact endMap_weak (e ≫ j) hF H h₀ h₁ (mappingVertexMap j x) (mappingVertexMap j y)
  let retract : RetractArrow p (q ≫ p) :=
    { i := Arrow.homMk p (𝟙 _) (by
        change p ≫ (q ≫ p) = p ≫ (𝟙 _)
        rw [← Category.assoc, hpq, Category.id_comp, Category.comp_id])
      r := Arrow.homMk q (𝟙 _) (by
        change q ≫ p = (q ≫ p) ≫ (𝟙 _)
        rw [Category.comp_id])
      retract := by
        apply Arrow.hom_ext
        · change p ≫ q = 𝟙 _
          exact hpq
        · change (𝟙 _) ≫ (𝟙 _) = (𝟙 _)
          rw [Category.id_comp] }
  exact MorphismProperty.of_retract (P := SSet.realizationWeakEquivalences) retract hqp

/-- The original constant-power mapping-fibre map is FULL weak at EVERY original pair of
vertices. -/
theorem constantPower_mappingFibresWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map (constantPower W) (x := x)
        (y := y) rfl rfl) :=
  originalSection_weak (constantPower W) (zeroEvaluation W) (constantPower_zeroEvaluation W)
    (powerSpace_segal W hW) (powerCategoricalHomotopy W)
    (powerCategoricalHomotopy_endpoints W).1 (powerCategoricalHomotopy_endpoints W).2 x y

/-- Evaluation keeps arbitrary original power vertices and their canonical j(ez) targets. -/
theorem zeroEvaluation_mappingFibresWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (z z' : ((powerSpace W).diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (mappingFibre.map (zeroEvaluation W) (x := z) (y := z') rfl rfl) := by
  let q := mappingFibre.map (zeroEvaluation W) (x := z) (y := z') rfl rfl
  let p := mappingFibre.map (constantPower W)
    (x := mappingVertexMap (zeroEvaluation W) z)
        (y := mappingVertexMap (zeroEvaluation W) z') rfl rfl
  have hp : SSet.realizationWeakEquivalences p := constantPower_mappingFibresWeak W hW _ _
  have hqp : SSet.realizationWeakEquivalences (q ≫ p) := by
    dsimp only [q, p]
    rw [mappingFibre.map_comp]
    exact endMap_weak (zeroEvaluation W ≫ constantPower W) (powerSpace_segal W hW)
      (powerCategoricalHomotopy W) (powerCategoricalHomotopy_endpoints W).1
      (powerCategoricalHomotopy_endpoints W).2 z z'
  exact SSet.realizationWeakEquivalences.of_postcomp q p hp hqp

/-- The actual E-prism constructs the intrinsic natural Ho Iso on the original power. -/
def powerHoNatIso (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SegalHomotopy.map (zeroEvaluation W ≫ constantPower W)
        (powerSpace_segal W hW) (powerSpace_segal W hW) ≅
      SegalHomotopy.map (𝟙 (powerSpace W)) (powerSpace_segal W hW) (powerSpace_segal W hW) :=
  CategoricalHomotopyPrism.homotopyHoNatIso _ _ (powerSpace_segal W hW) (powerSpace_segal W hW)
    (powerCategoricalHomotopy W) (powerCategoricalHomotopy_endpoints W).1
    (powerCategoricalHomotopy_endpoints W).2

/-- Each original power object has the actual Ho(e)(z) witness and internally derived E3 point
Iso. -/
theorem constantPower_HoEssSurj (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.map (constantPower W) hW (powerSpace_segal W hW)).EssSurj := by
  have iso := powerHoNatIso W hW
  rw [SegalHomotopy.map_comp (zeroEvaluation W) (constantPower W)
    (powerSpace_segal W hW) hW (powerSpace_segal W hW),
    SegalHomotopy.map_id (powerSpace W) (powerSpace_segal W hW)] at iso
  refine { mem_essImage := fun z => ?_ }
  exact ⟨(SegalHomotopy.map (zeroEvaluation W) (powerSpace_segal W hW) hW).obj z, ⟨iso.app z⟩⟩

/-- The entire strict j ≫ e equation supplies actual original Ho object witnesses for evaluation. -/
theorem zeroEvaluation_HoEssSurj (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.map (zeroEvaluation W) (powerSpace_segal W hW) hW).EssSurj := by
  have heq : SegalHomotopy.map (constantPower W) hW (powerSpace_segal W hW) ⋙
      SegalHomotopy.map (zeroEvaluation W) (powerSpace_segal W hW) hW =
        𝟭 (SegalHomotopy.Object W hW) := by
    rw [← SegalHomotopy.map_comp, constantPower_zeroEvaluation, SegalHomotopy.map_id]
  refine { mem_essImage := fun x => ?_ }
  exact ⟨(SegalHomotopy.map (constantPower W) hW (powerSpace_segal W hW)).obj x,
    ⟨(eqToIso heq).app x⟩⟩

/-- FULL intrinsic DK of the canonical section uses actual MF weakness and native Ho essential
surjectivity. -/
theorem constantPower_intrinsicDK (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (∀ x y : (W.diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map (constantPower W) (x := x) (y := y) rfl rfl)) ∧
      (SegalHomotopy.map (constantPower W) hW (powerSpace_segal W hW)).EssSurj :=
  ⟨constantPower_mappingFibresWeak W hW, constantPower_HoEssSurj W hW⟩

/-- FULL intrinsic DK of canonical zero evaluation retains all original power vertices and Homs. -/
theorem zeroEvaluation_intrinsicDK (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (∀ z z' : ((powerSpace W).diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map (zeroEvaluation W) (x := z) (y := z') rfl rfl)) ∧
      (SegalHomotopy.map (zeroEvaluation W) (powerSpace_segal W hW) hW).EssSurj :=
  ⟨zeroEvaluation_mappingFibresWeak W hW, zeroEvaluation_HoEssSurj W hW⟩

/-- Evaluation at the original one vertex uses the same power and counit. -/
def oneEvaluation (W : SimplicialSpace.{u}) : powerSpace W ⟶ W :=
  spaceEndpoint (powerSpace W) SSet.coherentIso.x₁ ≫ (ihom.ev coherentSpace).app W

/-- The second original evaluation is natural on every native power map. -/
theorem oneEvaluation_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (SegalExponentSupport.outerPower SSet.coherentIso).map f ≫ oneEvaluation V =
      oneEvaluation W ≫ f := by
  have he : (coherentSpace ◁ (SegalExponentSupport.outerPower SSet.coherentIso).map f) ≫
      (ihom.ev coherentSpace).app V = (ihom.ev coherentSpace).app W ≫ f :=
    (ihom.ev coherentSpace).naturality f
  have hn := endpoint_naturality ((SegalExponentSupport.outerPower SSet.coherentIso).map f)
    SSet.coherentIso.x₁
  dsimp +instances only [oneEvaluation, spaceEndpoint, coherentPoint, coherentSpace,
    powerSpace, SegalExponentSupport.outerPower] at he hn ⊢
  rw [← Category.assoc, hn, Category.assoc, he]
  simp only [Category.assoc]

/-- The same constant section is a strict section of the second evaluation. -/
theorem constantPower_oneEvaluation (W : SimplicialSpace.{u}) :
    constantPower W ≫ oneEvaluation W = 𝟙 W := by
  have ht : (coherentSpace ◁ constantPower W) ≫ (ihom.ev coherentSpace).app W =
      CartesianMonoidalCategory.snd coherentSpace W := by
    dsimp +instances only [constantPower, powerSpace, SegalExponentSupport.outerPower,
        coherentSpace]
    rw [← uncurry_eq, uncurry_curry]
  have hn := endpoint_naturality (constantPower W) SSet.coherentIso.x₁
  have hs := (spaceEndpoint_laws W SSet.coherentIso.x₁).2.1
  dsimp +instances only [oneEvaluation, constantPower, spaceEndpoint, coherentPoint,
    coherentSpace, powerSpace, SegalExponentSupport.outerPower] at ht hn hs ⊢
  rw [← Category.assoc, hn, Category.assoc, ht]
  exact hs

private theorem evaluation_endpoints (W : SimplicialSpace.{u}) :
    CategoricalHomotopyPrism.tensorEndpoint (powerSpace W) SSet.coherentIso.x₀ ≫
        ((ihom.ev coherentSpace).app W).hom = (zeroEvaluation W).hom ∧
    CategoricalHomotopyPrism.tensorEndpoint (powerSpace W) SSet.coherentIso.x₁ ≫
        ((ihom.ev coherentSpace).app W).hom = (oneEvaluation W).hom := by
  constructor
  · rw [← (spaceEndpoint_laws (powerSpace W) SSet.coherentIso.x₀).2.2]
    rfl
  · rw [← (spaceEndpoint_laws (powerSpace W) SSet.coherentIso.x₁).2.2]
    rfl

/-- The actual counit homotopy gives full weakness at every original power vertex pair. -/
theorem oneEvaluation_mappingFibresWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (z z' : ((powerSpace W).diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (mappingFibre.map (oneEvaluation W) (x := z) (y := z') rfl rfl) :=
  (CategoricalHomotopyPrism.mappingFibreWeak_iff (zeroEvaluation W) (oneEvaluation W) hW
    ((ihom.ev coherentSpace).app W).hom (evaluation_endpoints W).1
    (evaluation_endpoints W).2 z z').mp (zeroEvaluation_mappingFibresWeak W hW z z')

/-- The same counit homotopy transports intrinsic Ho essential surjectivity to the second vertex. -/
theorem oneEvaluation_HoEssSurj (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.map (oneEvaluation W) (powerSpace_segal W hW) hW).EssSurj :=
  (CategoricalHomotopyPrism.homotopyHoEssSurj_iff (zeroEvaluation W) (oneEvaluation W)
    (powerSpace_segal W hW) hW ((ihom.ev coherentSpace).app W).hom
    (evaluation_endpoints W).1 (evaluation_endpoints W).2).mp (zeroEvaluation_HoEssSurj W hW)

/-- Full Rezk 13.9 at the second original evaluation retains every original mapping fibre and Ho. -/
theorem oneEvaluation_intrinsicDK (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (∀ z z' : ((powerSpace W).diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map (oneEvaluation W) (x := z) (y := z') rfl rfl)) ∧
      (SegalHomotopy.map (oneEvaluation W) (powerSpace_segal W hW) hW).EssSurj :=
  ⟨oneEvaluation_mappingFibresWeak W hW, oneEvaluation_HoEssSurj W hW⟩

end SimplicialSpace.WalkingEUnit
