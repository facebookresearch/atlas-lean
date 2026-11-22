/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidTransfer
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.Monoidal
import MathlibExt.CategoryTheory.Monoidal.Mod

/-!
# Monoidal transfer API

Integration of generating pushout-products, actual tensor Quillen functors,
the monoid axiom, and models constructed by free/forgetful transfer.
The hypotheses supply source structures, generating families and relative
source smallness; the target model and its tested consequences are outputs.
-/

noncomputable section
universe w u v uD vD
open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra
open CategoryTheory.SmallObject
open scoped MonoidalCategory CategoryTheory.MonObj

namespace MonoidalTransferAPI

section GeneratorTensor
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (G : HomotopicalAlgebra.CofibrantGenerationData C κ)
  (hII : PushoutProductLe G.I G.I (cofibrations C))
  (hJI : PushoutProductLe G.J G.I (trivialCofibrations C))

example {A B K L : C} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations C i) (hj : cofibrations C j) :
    cofibrations C ((Arrow.mk i □ Arrow.mk j).hom) := by
  let pp := G.pushoutProductAxiom_of_generatorProducts hII hJI
  exact pp.cofibration_pushoutProduct i j hi hj

example {A B K L : C} (i : A ⟶ B) (j : K ⟶ L)
    (hi : trivialCofibrations C i) (hj : cofibrations C j) :
    trivialCofibrations C ((Arrow.mk i □ Arrow.mk j).hom) := by
  let pp := G.pushoutProductAxiom_of_generatorProducts hII hJI
  exact pp.trivial_pushoutProduct_left i j hi hj

example (K : C) [IsCofibrant K] {A B : C} (f : A ⟶ B)
    (hf : cofibrations C f) : cofibrations C (K ◁ f) := by
  let pp := G.pushoutProductAxiom_of_generatorProducts hII hJI
  let q := pp.ihomAdjunction_isQuillenAdjunction K
  exact q.preservesCofibrations f hf

example (K : C) [IsCofibrant K] {A B : C} (f : A ⟶ B)
    (hf : trivialCofibrations C f) : trivialCofibrations C (f ▷ K) := by
  let pp := G.pushoutProductAxiom_of_generatorProducts hII hJI
  let q := pp.tensorRightIhomAdjunction_isQuillenAdjunction K
  exact q.preservesTrivialCofibrations f hf

example [IsCofibrant (𝟙_ C)]
    (d : MapFactorizationData (cofibrations C) (trivialFibrations C)
      (initial.to (𝟙_ C))) (X : C) [IsCofibrant X] :
    weakEquivalences C (d.p ▷ X) := by
  let pp := G.pushoutProductAxiom_of_generatorProducts hII hJI
  let witness := pp.unitAxiomWitnessOfUnitFactor d
  exact witness.tensor_weak X inferInstance
end GeneratorTensor

section MonoidAxiom
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C]
  [HomotopicalAlgebra.MonoidAxiom.{w} C]

example {A B : C} (f : A ⟶ B) (hf : trivialCofibrations C f) (X : C) :
    weakEquivalences C (f ▷ X) := by
  apply HomotopicalAlgebra.MonoidAxiom.cellularClosure_le_weakEquivalences
  exact ((HomotopicalAlgebra.tensorTrivialCofibrationsRight C).le_coproducts.trans
    ((HomotopicalAlgebra.tensorTrivialCofibrationsRight C).coproducts.{w}).le_pushouts).trans
      ((HomotopicalAlgebra.tensorTrivialCofibrationsRight C).coproducts.{w}).pushouts.le_transfiniteCompositions _
    (HomotopicalAlgebra.whiskerRight_mem_tensorTrivialCofibrationsRight C f hf X)
end MonoidAxiom

section MonoidTransfer
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} (Mon C)]
  [HomotopicalAlgebra.IsClosedSymmetricMonoidalModelCategory C]
  [HomotopicalAlgebra.MonoidAxiom.{w} C]
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (hSI : UniformRelativeSourceSmallness.{w}
    (HomotopicalAlgebra.MonoidTransfer.freeGenerators I))
  (hSJ : UniformRelativeSourceSmallness.{w}
    (HomotopicalAlgebra.MonoidTransfer.freeGenerators J))

example {A B : C} (f : A ⟶ B) (hf : cofibrations C f) :
    let t := HomotopicalAlgebra.MonoidTransfer.fullAssociativeUnitalAlgebraModelTransfer
      I J hI hJ hSI hSJ
    letI : ModelCategory (Mon C) := t.model
    cofibrations (Mon C) (HomotopicalAlgebra.MonoidTransfer.free.map f) := by
  let t := HomotopicalAlgebra.MonoidTransfer.fullAssociativeUnitalAlgebraModelTransfer
    I J hI hJ hSI hSJ
  letI : ModelCategory (Mon C) := t.model
  have q := HomotopicalAlgebra.MonoidTransfer.freeForget_isQuillenAdjunction
    I J hI hJ hSI hSJ
  exact q.preservesCofibrations f hf

example {A B : C} (f : A ⟶ B) (hf : trivialCofibrations C f) :
    let t := HomotopicalAlgebra.MonoidTransfer.fullAssociativeUnitalAlgebraModelTransfer
      I J hI hJ hSI hSJ
    letI : ModelCategory (Mon C) := t.model
    trivialCofibrations (Mon C) (HomotopicalAlgebra.MonoidTransfer.free.map f) := by
  let t := HomotopicalAlgebra.MonoidTransfer.fullAssociativeUnitalAlgebraModelTransfer
    I J hI hJ hSI hSJ
  letI : ModelCategory (Mon C) := t.model
  have q := HomotopicalAlgebra.MonoidTransfer.freeForget_isQuillenAdjunction
    I J hI hJ hSI hSJ
  exact q.preservesTrivialCofibrations f hf
end MonoidTransfer

section ModuleTransfer
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  [HomotopicalAlgebra.MonoidAxiom.{w} C]
  (A : Mon C) (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (hSI : UniformRelativeSourceSmallness.{w}
    (HomotopicalAlgebra.ModuleTransfer.leftGenerators A I))
  (hSJ : UniformRelativeSourceSmallness.{w}
    (HomotopicalAlgebra.ModuleTransfer.leftGenerators A J))

example {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    let t := HomotopicalAlgebra.ModuleTransfer.fullLeftModuleModelTransfer
      A I J hI hJ hSI hSJ
    letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) ((Mod.free A.X).map f) := by
  let t := HomotopicalAlgebra.ModuleTransfer.fullLeftModuleModelTransfer
    A I J hI hJ hSI hSJ
  letI : ModelCategory (Mod C A.X) := t.model
  have q : (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := by
    apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    · intro M N g hg
      exact t.fibrations_eq.le g hg
    · intro M N g hg
      exact t.trivialFibrations_eq.le g hg
  exact q.preservesCofibrations f hf
end ModuleTransfer

section ExternalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalLeftAction C D]
  (A B E : C) [MonObj A] [MonObj B] [MonObj E]

example (f : A ⟶ B) (g : B ⟶ E) [IsMonHom f] [IsMonHom g]
    {M N : Mod D E} (h : M ⟶ N) :
    (Mod.comap (D := D) (f ≫ g)).map h ≫ (Mod.comapCompIso f g).hom.app N =
      (Mod.comapCompIso f g).hom.app M ≫
        (Mod.comap g ⋙ Mod.comap f).map h := by
  exact (Mod.comapCompIso f g).hom.naturality h
end ExternalAction

section BalancedTensor
variable {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasCoequalizers C] (A : CommMon C)

example (M N : Mod C A.X)
    (s : Cofork (Mod.relativeTensorFirstMap A M N)
      (Mod.relativeTensorSecondMap A M N)) :
    (Mod.relativeTensorCofork A M N).π ≫
      (Mod.relativeTensorCoforkIsColimit A M N).desc s = s.π := by
  exact (Mod.relativeTensorCoforkIsColimit A M N).fac s WalkingParallelPair.one
end BalancedTensor

section CommutativeModuleTransfer
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  [HomotopicalAlgebra.IsClosedSymmetricMonoidalModelCategory C]
  [HomotopicalAlgebra.MonoidAxiom.{w} C] [IsCofibrant (𝟙_ C)]
  (A : CommMon C) (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hSI : UniformRelativeSourceSmallness.{w} (I.strictMap (Mod.free A.X)))
  (hSJ : UniformRelativeSourceSmallness.{w} (J.strictMap (Mod.free A.X)))
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)

example :
    letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
    letI : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A
    letI : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A
    let t := HomotopicalAlgebra.ModuleTransfer.Monoidal.fullCommutativeModuleModelTransfer
      A I J hSI hSJ hI hJ
    letI : ModelCategory (Mod C A.X) := t.transfer.model
    IsCofibrant (𝟙_ (Mod C A.X)) := by
  letI : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  letI : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A
  letI : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A
  let t := HomotopicalAlgebra.ModuleTransfer.Monoidal.fullCommutativeModuleModelTransfer
    A I J hSI hSJ hI hJ
  letI : ModelCategory (Mod C A.X) := t.transfer.model
  exact HomotopicalAlgebra.ModuleTransfer.Monoidal.moduleUnit_isCofibrant
    A I J hSI hSJ t.transfer

end CommutativeModuleTransfer

end MonoidalTransferAPI
