/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalCorePathObject
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalEquivalenceFibreWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyFunctor
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathObjectWeakDetection

/-!
# Complete-Segal intrinsic DK recognition in original outer degree zero

The accepted genuine scalar path-fibre theorem supplies the degree-zero conclusion.
No completion, all-level or noncomplete CSS recognition is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner

namespace SimplicialSpace

private theorem objectQuotientMap_bijective {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (hE : (SegalHomotopy.map f hW hV).EssSurj) :
    Function.Bijective (SegalHomotopy.objectQuotientMap f hW hV) := by
  let F := SegalHomotopy.map f hW hV
  let : F.IsEquivalence :=
    SegalHomotopy.map_isEquivalence_of_mappingFibreWeak_of_essSurj f hW hV hm hE
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro a b h
    obtain ⟨e⟩ := Quotient.eq.mp h
    exact Quotient.sound ⟨F.preimageIso e⟩
  · intro q
    refine Quotient.inductionOn q ?_
    intro a
    exact ⟨Quotient.mk _ (F.objPreimage a), Quotient.sound ⟨F.objObjPreimageIso a⟩⟩

/-- The original degree-zero component map is bijective under intrinsic DK
hypotheses at actual complete endpoints. The given essential-surjectivity
property belongs to the same intrinsic Ho functor, not a replacement category. -/
theorem completeSegalMap_piZero_bijective {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (hE : let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1
      let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
      (SegalHomotopy.map f hS hT).EssSurj) :
    Function.Bijective (SSet.mapπ₀ (f.hom.app (op ⦋0⦌))) := by
  let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1
  let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
  have hs := completeSegalObjectComponentClass_bijective W hW
  have ht := completeSegalObjectComponentClass_bijective V hV
  have hq := objectQuotientMap_bijective f hS hT hm hE
  constructor
  · intro c d h
    apply hs.1
    apply hq.1
    rw [SegalHomotopy.objectComponentClass_naturality f hS hT,
      SegalHomotopy.objectComponentClass_naturality f hS hT, h]
  · intro d
    obtain ⟨q, hq⟩ := hq.2 (SegalHomotopy.objectComponentClass V hT d)
    obtain ⟨c, hc⟩ := hs.2 q
    refine ⟨c, ht.1 ?_⟩
    rw [← SegalHomotopy.objectComponentClass_naturality f hS hT, hc, hq]

private theorem degreeZero_kanComplex (W : SimplicialSpace.{u}) (hS : segalSpaces W) :
    SSet.KanComplex (W.diagram _⦋0⦌) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let A := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[0] : SSet.{u}))
  have hK := ReedyModel.innerHom_kanComplex A W (ReedyModel.isCofibrant A) hS.1
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) at hK
  let : SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) := hK
  exact isFibrant_of_fibration (discreteYonedaIso W 0).inv

/-- Full mapping-fibre weakness and actual intrinsic Ho essential surjectivity
force full realization weakness of the SAME original outer-zero map between
complete Segal spaces. No original fibration or global-core weakness is assumed. -/
theorem completeSegalMap_degreeZero_weak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (hE : let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1
      let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
      (SegalHomotopy.map f hS hT).EssSurj) :
    SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)) := by
  let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1
  let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
  let : SSet.KanComplex (W.diagram _⦋0⦌) := degreeZero_kanComplex W hS
  let : SSet.KanComplex (V.diagram _⦋0⦌) := degreeZero_kanComplex V hT
  let P := completeSegalCorePathObject W hW
  let Q := completeSegalCorePathObject V hV
  let : P.IsVeryGood := (completeSegalCorePathObject_laws W hW).1
  let : Q.IsVeryGood := (completeSegalCorePathObject_laws V hV).1
  let a := SegalHomotopy.equivalenceMap f hS hT
  have ha := (completeSegalCorePathObject_laws W hW).2.2.2 V hV f
  apply SSet.realizationWeakEquivalence_of_goodPathObjectDiagonalFibres
    (f.hom.app (op ⦋0⦌)) P Q a ha.1 ha.2.1 ha.2.2
    (completeSegalMap_piZero_bijective f hW hV hm hE)
  intro x
  change SSet.realizationWeakEquivalences
    (SegalHomotopy.equivalenceFibreMap f hS hT (x := x) (y := x) rfl rfl)
  exact SegalHomotopy.equivalenceFibreMap_weak_of_mappingFibreWeak f hS hT hm x x

end SimplicialSpace
