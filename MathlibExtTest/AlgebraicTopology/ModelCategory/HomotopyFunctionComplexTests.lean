/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFunctionComplex

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace HomotopicalAlgebra.HomotopyFunctionComplexTests

#check HomotopyFunctionComplexPrecompData
#check HomotopyFunctionComplexInvarianceData
#check HomotopyFunctionComplexData

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

section PacketSurface

variable (data data' : HomotopyFunctionComplexData (C := C))
variable (precomp : HomotopyFunctionComplexPrecompData (C := C))
variable (invariance : HomotopyFunctionComplexInvarianceData (C := C))
variable {X Y Z : C}

example : HomotopyFunctionComplexInvarianceData (C := C) :=
  data.toHomotopyFunctionComplexInvarianceData

example : HomotopyFunctionComplexPrecompData (C := C) :=
  invariance.toHomotopyFunctionComplexPrecompData

example : Cᵒᵖ ⥤ C ⥤ SSet.{v} := data.alternativeMappingObject

example : Cᵒᵖ ⥤ C ⥤ SSet.{v} := data.comparisonMappingObject

example :
    data.comparisonMappingObject ⟶ derivedMappingObject (C := C) :=
  data.comparisonToDerived

example :
    data.comparisonMappingObject ⟶ data.alternativeMappingObject :=
  data.comparisonToAlternative

example :
    SSet.realizationWeakEquivalences
      ((data.comparisonToDerived.app (.op X)).app Y) :=
  data.comparisonToDerived_weak (.op X) Y

example :
    SSet.realizationWeakEquivalences
      ((data.comparisonToAlternative.app (.op X)).app Y) :=
  data.comparisonToAlternative_weak (.op X) Y

example (f : X ⟶ Y) (hX : IsCofibrant X) (hY : IsCofibrant Y)
    (hf : weakEquivalences C f) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).map f.op).app Z) :=
  precomp.precompWeakOfWeakEquivalence f hX hY hf Z hZ

example (g : Y ⟶ Z) (hX : IsCofibrant X) (hY : IsFibrant Y)
    (hZ : IsFibrant Z) (hg : weakEquivalences C g) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor C).obj (.op X)).map g) :=
  invariance.postcompWeakOfWeakEquivalence X hX g hY hZ hg

/-- Raw precomposition invariance applies to the weak map produced by cofibrant replacement. -/
example (f : X ⟶ Y) (hf : weakEquivalences C f) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := C) f Z) := by
  have hQf : weakEquivalences C ((cofibrantReplacement (C := C)).map f) := by
    apply (weakEquivalences C).of_postcomp (W' := weakEquivalences C)
      ((cofibrantReplacement (C := C)).map f)
      ((cofibrantReplacementCounit (C := C)).app Y)
      WeakEquivalence.mem
    rw [(cofibrantReplacementCounit (C := C)).naturality]
    exact (weakEquivalences C).comp_mem _ _ WeakEquivalence.mem hf
  have h := data.precompWeakOfWeakEquivalence
    ((cofibrantReplacement (C := C)).map f)
    (by infer_instance) (by infer_instance) hQf
    ((fibrantReplacement (C := C)).obj Z) (by infer_instance)
  simpa [derivedMappingPrecomp, derivedMappingObject] using h

/-- Raw postcomposition invariance applies to the weak map produced by fibrant replacement. -/
example (g : Y ⟶ Z) (hg : weakEquivalences C g) :
    SSet.realizationWeakEquivalences
      (derivedMappingPostcomp (C := C) X g) := by
  have hRg : weakEquivalences C ((fibrantReplacement (C := C)).map g) := by
    apply (weakEquivalences C).of_precomp (W' := weakEquivalences C)
      ((fibrantReplacementUnit (C := C)).app Y)
      ((fibrantReplacement (C := C)).map g)
      WeakEquivalence.mem
    rw [← (fibrantReplacementUnit (C := C)).naturality]
    exact (weakEquivalences C).comp_mem _ _ hg WeakEquivalence.mem
  have h := data.postcompWeakOfWeakEquivalence
    ((cofibrantReplacement (C := C)).obj X) (by infer_instance)
    ((fibrantReplacement (C := C)).map g)
    (by infer_instance) (by infer_instance) hRg
  simpa [derivedMappingPostcomp, derivedMappingObject] using h

example (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∀ (T : C), IsFibrant T →
      SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := C) f T) :=
  data.weakEquivalence_iff_derivedMappingPrecomp f

example (f : X ⟶ Y) (T : C) :
    SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := C) f T) ↔
      SSet.realizationWeakEquivalences
        ((data.alternativeMappingObject.map f.op).app T) :=
  derivedMappingPrecomp_weak_iff_alternative data f T

example (g : Y ⟶ Z) (A : C) :
    SSet.realizationWeakEquivalences
        (derivedMappingPostcomp (C := C) A g) ↔
      SSet.realizationWeakEquivalences
        ((data.alternativeMappingObject.obj (.op A)).map g) :=
  derivedMappingPostcomp_weak_iff_alternative data A g

/-- Two explicit packets coexist; neither is selected by typeclass inference. -/
example :
    (Cᵒᵖ ⥤ C ⥤ SSet.{v}) × (Cᵒᵖ ⥤ C ⥤ SSet.{v}) :=
  ⟨data.alternativeMappingObject, data'.alternativeMappingObject⟩

example : HomotopyFunctionComplexInvarianceData (C := C) :=
  invariance

example : HomotopyFunctionComplexPrecompData (C := C) :=
  precomp

example : True := by
  fail_if_success
    let _ : HomotopyFunctionComplexPrecompData (C := C) := by
      infer_instance
  fail_if_success
    let _ : HomotopyFunctionComplexData (C := C) := by infer_instance
  trivial

end PacketSurface

section NondiscreteMappingSpace

/-- The mapping-space interface is genuinely simplicial: the standard 1-simplex has distinct
degree-one simplices. Locality consumes a morphism of whole simplicial sets, not a function on
vertices. -/
example : Nontrivial ((Δ[1] : SSet).obj (.op ⦋1⦌)) := by
  let edge := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
  let constant :=
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)
  refine ⟨⟨edge, constant, ?_⟩⟩
  intro h
  have h' := congrArg SSet.stdSimplex.objEquiv h
  have h'' := congrArg
    (fun q : ⦋1⦌ ⟶ ⦋1⦌ ↦ q.toOrderHom (1 : Fin 2)) h'
  simp [edge, constant] at h''

example {K L : SSet.{v}} (f : K ⟶ L)
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences f := hf

end NondiscreteMappingSpace

section UniverseOneZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [SimplicialCategory C₁]
variable [HasFunctorialFactorization (cofibrations C₁) (trivialFibrations C₁)]
variable [HasFunctorialFactorization (trivialCofibrations C₁) (fibrations C₁)]

example : Prop := HomotopyFunctionComplexPrecompData (C := C₁)

example : Prop := HomotopyFunctionComplexInvarianceData (C := C₁)

example : Type 1 := HomotopyFunctionComplexData (C := C₁)

end UniverseOneZero

section UniverseZero

variable {C₀ : Type} [Category C₀] [ModelCategory C₀]
variable [SimplicialCategory C₀]
variable [HasFunctorialFactorization (cofibrations C₀) (trivialFibrations C₀)]
variable [HasFunctorialFactorization (trivialCofibrations C₀) (fibrations C₀)]

example : Prop := HomotopyFunctionComplexPrecompData (C := C₀)

example : Prop := HomotopyFunctionComplexInvarianceData (C := C₀)

example : Type 1 := HomotopyFunctionComplexData (C := C₀)

end UniverseZero

/- The reviewed derived-mapping provider remains the sole owner of its eight
names. Comparison scaffolding stays private while the characteristic
presentation-independence theorems are public. -/

/-- error: Unknown identifier `derivedMapping_mixed_naturality` -/
#guard_msgs (error) in
#check derivedMapping_mixed_naturality

/-- error: Unknown identifier `cofibrantReplacementComparison` -/
#guard_msgs (error) in
#check cofibrantReplacementComparison

/-- error: Unknown identifier `fibrantReplacementComparison` -/
#guard_msgs (error) in
#check fibrantReplacementComparison

/-- error: Unknown identifier `derivedMappingObjectReplacementZigzag` -/
#guard_msgs (error) in
#check derivedMappingObjectReplacementZigzag

#check derivedMappingPrecomp_weak_iff_alternative
#check derivedMappingPostcomp_weak_iff_alternative
#check localEquivalences_replacement_independent

#print axioms derivedMappingPrecomp_weak_iff_alternative
#print axioms derivedMappingPostcomp_weak_iff_alternative
#print axioms localEquivalences_replacement_independent

end HomotopicalAlgebra.HomotopyFunctionComplexTests
