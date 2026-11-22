/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- True outer powers retain the original Segal tests and scalar-end transposition.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalRowFibrations
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.SpineInnerAnodyne
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCartesianModel
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.IndexedFreeMappingData
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CartesianTensorHomIso
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian exponentials and Segal locality

Exponentiation by the discrete outer embedding of any simplicial set preserves Reedy fibrancy
and Segal locality. Natural mapping-end and arrow isomorphisms compare chosen Cartesian
exponentials with the representable-weighted raw exponentials, identifying the Segal
restrictions with product-spine scalar restrictions that are trivial Kan fibrations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite MonoidalCategory
    MonoidalClosed
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner SimplicialSpace.Cartesian
    SSet.modelCategoryQuillen

namespace SimplicialSpace.SegalExponentSupport
attribute [local instance] ReedyModel.modelCategory

/-- The original right product of a consecutive-edge spine inclusion with arbitrary K. -/
def spineProductMap (K : SSet.{u}) (n : ℕ) :
    (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u}) ⊗ K ⟶ (Δ[n] : SSet.{u}) ⊗ K :=
  (SSet.Rezk.spineSubcomplex.{u} n).ι ▷ K

private theorem originalSpineTests (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
      ((boxLeftDivisionFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app W) := by
  intro n hn
  change SSet.realizationWeakEquivalences
    ((innerHomFunctor.map
      (ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app W)
  exact hW.2 n hn

/-- The full chosen scalar mapping-end product-spine restriction has original boundary RLP. -/
theorem spineProduct_boundaryRLP (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (K : SSet.{u}) (n : ℕ) (hn : 2 ≤ n) :
    SSet.modelCategoryQuillen.I.rlp
      ((boxLeftDivisionFunctor.map (spineProductMap K n).op).app W) := by
  have hp : SSet.innerAnodyneExtensions (spineProductMap K n) :=
    (SSet.Rezk.innerAnodyneExtensions_spineSubcomplex_ι n hn).whiskerRight K
  exact leftRestriction_boundaryRLP_of_innerAnodyne W hW.1
    (originalSpineTests W hW) (spineProductMap K n) hp

/-- Every original product-spine test is FULL realization weak, not only a row-QC conclusion. -/
theorem spineProduct_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (K : SSet.{u}) (n : ℕ) (hn : 2 ≤ n) :
    SSet.realizationWeakEquivalences
      ((boxLeftDivisionFunctor.map (spineProductMap K n).op).app W) :=
  SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (spineProduct_boundaryRLP W hW K n hn)

/-- The same original full mapping-end restriction is an ACTUAL scalar TF. -/
theorem spineProduct_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (K : SSet.{u}) (n : ℕ) (hn : 2 ≤ n) :
    trivialFibrations SSet.{u}
      ((boxLeftDivisionFunctor.map (spineProductMap K n).op).app W) := by
  let a := spineProductMap K n
  have : Mono a := by
    change Mono ((tensorRight K).map (SSet.Rezk.spineSubcomplex.{u} n).ι)
    infer_instance
  have : Mono (SSet.simplicialSpaceDiscrete.map a) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [NatTrans.mono_iff_mono_app]
    intro k
    change Mono (a.app m)
    infer_instance
  let f := discreteInnerFunctor.map a
  have : Mono f := by dsimp only [f, discreteInnerFunctor]; infer_instance
  have hf : Cofibration f := (ReedyModel.cofibration_iff f).mpr inferInstance
  have hg : Fibration ((boxLeftDivisionFunctor.map a.op).app W) :=
    (HomotopicalAlgebra.fibration_iff _).mpr
      (ReedyModel.inner_precomp_fibration f W
        ((HomotopicalAlgebra.cofibration_iff f).mp hf) hW.1)
  have hw : SSet.realizationWeakEquivalences ((boxLeftDivisionFunctor.map a.op).app W) :=
    spineProduct_realizationWeak W hW K n hn
  exact (mem_trivialFibrations_iff _).mpr
    ⟨hg, (HomotopicalAlgebra.weakEquivalence_iff _).mpr hw⟩

/-- The genuine chosen Cartesian exponential by the ORIGINAL discrete outer K. -/
def outerPower (K : SSet.{u}) : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  ihom (discreteInnerFunctor.obj K)

/-- Actual Reedy RF of the whole true exponent is derived from the existing base Cartesian model. -/
theorem outerPower_reedyFibrant (K : SSet.{u}) (W : SimplicialSpace.{u})
    (hW : IsFibrant W) : IsFibrant ((outerPower K).obj W) := by
  let _ : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
    ReedyModel.cartesian_isClosedSymmetricMonoidalModelCategory
  let _ : IsCofibrant (discreteInnerFunctor.obj K) := ReedyModel.isCofibrant _
  let _ : Adjunction.IsQuillenAdjunction (ihom.adjunction (discreteInnerFunctor.obj K)) :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant _
  exact (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := ihom.adjunction (discreteInnerFunctor.obj K))) hW

end SimplicialSpace.SegalExponentSupport

namespace SimplicialSpace.SegalExponentRawAssembly
attribute [local instance] SimplicialPresheaf.hasEnd

/-- The whole actual fixed-u representable-weighted raw exponential, on the original designated
carrier. -/
def wrappedRawPower (A : SimplicialSpace.{u}) : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  forget ⋙ SimplicialPresheaf.exponentialFunctor A.diagram ⋙ ofSimplicialObject

/-- Native right-adjoint uniqueness compares the SAME true Cartesian power using the actual
adjunction. -/
def chosenPowerIso (A : SimplicialSpace.{u}) : ihom A ≅ wrappedRawPower A := by
  letI : forget.{u}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts forget
  let a := equivalenceSimplicialObject.{u}.toAdjunction
  exact (ihom.adjunction A).rightAdjointUniq
    ((a.comp ((SimplicialPresheaf.exponentialAdjunction A.diagram).comp
      a.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
        (Iso.compInverseIso (H := a.toEquivalence) (Functor.Monoidal.commTensorLeft forget A)))

/-- The forgetful whole functor round trip identifies the same raw exponential functor. -/
def chosenPowerRawIso (A : SimplicialSpace.{u}) :
    ihom A ⋙ forget ≅ forget ⋙ SimplicialPresheaf.exponentialFunctor A.diagram := by
  let E := SimplicialPresheaf.exponentialFunctor A.diagram
  exact Functor.isoWhiskerRight (chosenPowerIso A) forget ≪≫
    Functor.associator forget (E ⋙ ofSimplicialObject) forget ≪≫
    Functor.isoWhiskerLeft forget
      (Functor.associator E ofSimplicialObject forget ≪≫
        Functor.isoWhiskerLeft E (eqToIso ofSimplicialObject_comp_forget) ≪≫
        E.rightUnitor)

/-- Full target naturality of the same chosen-to-raw scalar transposition. -/
def powerScalarMappingNatIso (A B : SimplicialSpace.{u}) :
    ihom A ⋙ innerHomFunctor.obj (op B) ≅
      forget ⋙ SimplicialPresheaf.innerHomFunctor.obj (op (B.diagram ⊗ A.diagram)) :=
  Functor.isoWhiskerLeft (ihom A)
      (SimplicialPresheaf.IndexedFreeMapping.rawEndNatIso B).symm ≪≫
    (Functor.associator (ihom A) forget
      (SimplicialPresheaf.innerHomFunctor.obj (op B.diagram))).symm ≪≫
    Functor.isoWhiskerRight (chosenPowerRawIso A)
      (SimplicialPresheaf.innerHomFunctor.obj (op B.diagram)) ≪≫
    Functor.associator forget (SimplicialPresheaf.exponentialFunctor A.diagram)
      (SimplicialPresheaf.innerHomFunctor.obj (op B.diagram)) ≪≫
    Functor.isoWhiskerLeft forget
      (SimplicialPresheaf.cartesianTensorHomIso A.diagram B.diagram)

/-- The scalar comparison retains its actual three endpoint factors in both directions. -/
def powerScalarMappingIso (A B W : SimplicialSpace.{u}) :
    (innerHomFunctor.obj (op B)).obj ((ihom A).obj W) ≅
      SimplicialPresheaf.innerHom (B.diagram ⊗ A.diagram) W.diagram :=
  (SimplicialPresheaf.IndexedFreeMapping.rawEndIso B ((ihom A).obj W)).symm ≪≫
    (SimplicialPresheaf.innerHomFunctor.obj (op B.diagram)).mapIso
      ((chosenPowerRawIso A).app W) ≪≫
    (SimplicialPresheaf.cartesianTensorHomIso A.diagram B.diagram).app W.diagram

/-- Both actual point directions are the components of the whole target-natural scalar
comparison. -/
theorem powerScalarMappingIso_components (A B W : SimplicialSpace.{u}) :
    (powerScalarMappingIso A B W).hom = (powerScalarMappingNatIso A B).hom.app W ∧
      (powerScalarMappingIso A B W).inv = (powerScalarMappingNatIso A B).inv.app W := by
  change (((SimplicialPresheaf.IndexedFreeMapping.rawEndNatIso B).app
      ((ihom A).obj W)).symm ≪≫
    (SimplicialPresheaf.innerHomFunctor.obj (op B.diagram)).mapIso
      ((chosenPowerRawIso A).app W) ≪≫
    (SimplicialPresheaf.cartesianTensorHomIso A.diagram B.diagram).app W.diagram).hom =
      (powerScalarMappingNatIso A B).hom.app W ∧
    (((SimplicialPresheaf.IndexedFreeMapping.rawEndNatIso B).app
      ((ihom A).obj W)).symm ≪≫
    (SimplicialPresheaf.innerHomFunctor.obj (op B.diagram)).mapIso
      ((chosenPowerRawIso A).app W) ≪≫
    (SimplicialPresheaf.cartesianTensorHomIso A.diagram B.diagram).app W.diagram).inv =
      (powerScalarMappingNatIso A B).inv.app W
  unfold powerScalarMappingNatIso
  generalize hr : SimplicialPresheaf.IndexedFreeMapping.rawEndNatIso B = r
  generalize he : chosenPowerRawIso A = e
  generalize ht : SimplicialPresheaf.cartesianTensorHomIso A.diagram B.diagram = t
  constructor <;> simp [Category.assoc]
  all_goals
    dsimp only [Iso.trans, CategoryTheory.Functor.mapIso, Iso.app]
    rfl

/-- The entire original source Arrow is transposed through actual native adjunctions and scalar
ends. -/
def powerPrecompRawArrowIso (A : SimplicialSpace.{u})
    {B B' : SimplicialSpace.{u}} (b : B' ⟶ B) (W : SimplicialSpace.{u}) :
    Arrow.mk ((innerHomFunctor.map b.op).app ((ihom A).obj W)) ≅
      Arrow.mk (SimplicialPresheaf.innerHomPre (b.hom ▷ A.diagram) W.diagram) := by
  let E₀ := (Arrow.isoMk'
    (SimplicialPresheaf.innerHomPre b.hom ((ihom A).obj W).diagram)
    ((innerHomFunctor.map b.op).app ((ihom A).obj W))
    (SimplicialPresheaf.IndexedFreeMapping.rawEndIso B ((ihom A).obj W))
    (SimplicialPresheaf.IndexedFreeMapping.rawEndIso B' ((ihom A).obj W))
    ((SimplicialPresheaf.IndexedFreeMapping.rawEnd_naturality.1 b ((ihom A).obj W)).1).symm).symm
  let e := (chosenPowerRawIso A).app W
  let E₁ := Arrow.isoMk'
    (SimplicialPresheaf.innerHomPre b.hom ((ihom A).obj W).diagram)
    (SimplicialPresheaf.innerHomPre b.hom
      ((SimplicialPresheaf.exponentialFunctor A.diagram).obj W.diagram))
    ((SimplicialPresheaf.innerHomFunctor.obj (op B.diagram)).mapIso e)
    ((SimplicialPresheaf.innerHomFunctor.obj (op B'.diagram)).mapIso e)
    (by
      change SimplicialPresheaf.innerHomPost B.diagram e.hom ≫
          SimplicialPresheaf.innerHomPre b.hom _ =
        SimplicialPresheaf.innerHomPre b.hom _ ≫
          SimplicialPresheaf.innerHomPost B'.diagram e.hom
      exact (SimplicialPresheaf.innerHom_exchange b.hom e.hom).symm)
  exact E₀ ≪≫ E₁ ≪≫
    SimplicialPresheaf.cartesianTensorHomArrowIso A.diagram b.hom W.diagram

/-- All four source Arrow legs use the same scalar characteristic isomorphisms. -/
theorem powerPrecompRawArrowIso_legs (A : SimplicialSpace.{u})
    {B B' : SimplicialSpace.{u}} (b : B' ⟶ B) (W : SimplicialSpace.{u}) :
    (powerPrecompRawArrowIso A b W).hom.left = (powerScalarMappingIso A B W).hom ∧
    (powerPrecompRawArrowIso A b W).hom.right = (powerScalarMappingIso A B' W).hom ∧
    (powerPrecompRawArrowIso A b W).inv.left = (powerScalarMappingIso A B W).inv ∧
    (powerPrecompRawArrowIso A b W).inv.right = (powerScalarMappingIso A B' W).inv :=
  ⟨rfl, rfl, rfl, rfl⟩

end SimplicialSpace.SegalExponentRawAssembly

namespace SimplicialSpace.SegalExponentRawAssembly
attribute [local instance] ReedyModel.modelCategory

/-- Binary products are preserved by the actual constant-inner embedding and wrapping
equivalence. -/
theorem discreteInnerPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) discreteInnerFunctor.{u} := by
  dsimp only [discreteInnerFunctor, SSet.simplicialSpaceDiscrete]
  infer_instance
attribute [local instance] discreteInnerPreservesBinaryProducts

/-- The original discrete product comparison, from two wrapped factors to their original product. -/
def discreteTensorIso (B K : SSet.{u}) :
    discreteInnerFunctor.obj B ⊗ discreteInnerFunctor.obj K ≅
      discreteInnerFunctor.obj (B ⊗ K) :=
  (asIso (CartesianMonoidalCategory.prodComparison discreteInnerFunctor B K)).symm

/-- The entire original product-source Arrow comparison retains both endpoint isomorphisms. -/
def discreteTensorSourceArrowIso {B' B : SSet.{u}} (b : B' ⟶ B) (K : SSet.{u}) :
    Arrow.mk (discreteInnerFunctor.map b ▷ discreteInnerFunctor.obj K) ≅
      Arrow.mk (discreteInnerFunctor.map (b ▷ K)) :=
  Arrow.isoMk' _ _ (discreteTensorIso B' K) (discreteTensorIso B K) (by
    change inv (CartesianMonoidalCategory.prodComparison discreteInnerFunctor B' K) ≫
        discreteInnerFunctor.map (b ▷ K) =
      (discreteInnerFunctor.map b ▷ discreteInnerFunctor.obj K) ≫
        inv (CartesianMonoidalCategory.prodComparison discreteInnerFunctor B K)
    exact CartesianMonoidalCategory.prodComparison_inv_natural_whiskerRight
      discreteInnerFunctor b)

/-- The original endpoint transposition finishes with the actual discrete product comparison. -/
def outerPowerMappingIso (K B : SSet.{u}) (W : SimplicialSpace.{u}) :
    (innerHomFunctor.obj (op (discreteInnerFunctor.obj B))).obj
        ((SegalExponentSupport.outerPower K).obj W) ≅
      (boxLeftDivisionFunctor.obj (op (B ⊗ K))).obj W :=
  powerScalarMappingIso (discreteInnerFunctor.obj K) (discreteInnerFunctor.obj B) W ≪≫
    SimplicialPresheaf.IndexedFreeMapping.rawEndIso
      (discreteInnerFunctor.obj B ⊗ discreteInnerFunctor.obj K) W ≪≫
    (innerHomFunctor.flip.obj W).mapIso (discreteTensorIso B K).symm.op

/-- Full chosen power precomposition is the SAME original product-spine scalar restriction. -/
def outerPowerSpineArrowIso (K : SSet.{u}) (n : ℕ) (W : SimplicialSpace.{u}) :
    Arrow.mk ((innerHomFunctor.map
      (discreteInnerFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι).op).app
        ((SegalExponentSupport.outerPower K).obj W)) ≅
      Arrow.mk ((boxLeftDivisionFunctor.map
        (SegalExponentSupport.spineProductMap K n).op).app W) := by
  let A := discreteInnerFunctor.obj K
  let b := discreteInnerFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι
  let E := powerPrecompRawArrowIso A b W
  let R := Arrow.isoMk'
    (SimplicialPresheaf.innerHomPre (b ▷ A).hom W.diagram)
    ((innerHomFunctor.map (b ▷ A).op).app W)
    (SimplicialPresheaf.IndexedFreeMapping.rawEndIso
      (discreteInnerFunctor.obj (Δ[n] : SSet.{u}) ⊗ A) W)
    (SimplicialPresheaf.IndexedFreeMapping.rawEndIso
      (discreteInnerFunctor.obj (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u}) ⊗ A) W)
    ((SimplicialPresheaf.IndexedFreeMapping.rawEnd_naturality.1 (b ▷ A) W).1).symm
  let f := b ▷ A
  let g := discreteInnerFunctor.map (SegalExponentSupport.spineProductMap K n)
  let d := discreteTensorSourceArrowIso (SSet.Rezk.spineSubcomplex.{u} n).ι K
  let F := innerHomFunctor.flip.obj W
  let P := Arrow.isoMk'
    ((innerHomFunctor.map f.op).app W) ((innerHomFunctor.map g.op).app W)
    (F.mapIso ((Arrow.rightFunc.mapIso d).symm.op))
    (F.mapIso ((Arrow.leftFunc.mapIso d).symm.op)) (by
      change F.map d.inv.right.op ≫ F.map g.op =
        F.map f.op ≫ F.map d.inv.left.op
      have hd : d.inv.left ≫ f = g ≫ d.inv.right := Arrow.w d.inv
      have h := congrArg (fun k => F.map k.op) hd
      simpa only [op_comp, CategoryTheory.Functor.map_comp] using h.symm)
  exact E ≪≫ R ≪≫ P

/-- Both forward and both inverse spine-Arrow legs are the same original endpoint comparisons. -/
theorem outerPowerSpineArrowIso_legs (K : SSet.{u}) (n : ℕ) (W : SimplicialSpace.{u}) :
    (outerPowerSpineArrowIso K n W).hom.left =
      (outerPowerMappingIso K (Δ[n] : SSet.{u}) W).hom ∧
    (outerPowerSpineArrowIso K n W).hom.right =
      (outerPowerMappingIso K (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u}) W).hom ∧
    (outerPowerSpineArrowIso K n W).inv.left =
      (outerPowerMappingIso K (Δ[n] : SSet.{u}) W).inv ∧
    (outerPowerSpineArrowIso K n W).inv.right =
      (outerPowerMappingIso K (SSet.Rezk.spineSubcomplex.{u} n : SSet.{u}) W).inv := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Both whole original mapping-end squares, including the inverse endpoint directions. -/
theorem outerPowerSpineArrowIso_squares (K : SSet.{u}) (n : ℕ) (W : SimplicialSpace.{u}) :
    let p := (innerHomFunctor.map
      (discreteInnerFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι).op).app
        ((SegalExponentSupport.outerPower K).obj W)
    let q := (boxLeftDivisionFunctor.map
      (SegalExponentSupport.spineProductMap K n).op).app W
    let e := outerPowerSpineArrowIso K n W
    e.hom.left ≫ q = p ≫ e.hom.right ∧
      e.inv.left ≫ p = q ≫ e.inv.right :=
  ⟨Arrow.w _, Arrow.w _⟩

/-- Every true original outer-simplicial-set power of a RF Segal space is itself RF and Segal. -/
theorem outerPower_segal (K : SSet.{u}) (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    segalSpaces ((SegalExponentSupport.outerPower K).obj W) := by
  refine ⟨SegalExponentSupport.outerPower_reedyFibrant K W hW.1, ?_⟩
  intro n hn
  change SSet.realizationWeakEquivalences
    ((innerHomFunctor.map
      (discreteInnerFunctor.map (SSet.Rezk.spineSubcomplex.{u} n).ι).op).app
      ((SegalExponentSupport.outerPower K).obj W))
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (outerPowerSpineArrowIso K n W)).mpr
      (SegalExponentSupport.spineProduct_realizationWeak W hW K n hn)

end SimplicialSpace.SegalExponentRawAssembly
