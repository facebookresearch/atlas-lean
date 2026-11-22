/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidSimplexCategoricalCylinder
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The original full-J coefficient categorical contractions

For every original simplex operator, one reverse constant map supplies
two actual walking-E categorical homotopies.  The source vertex is carried
to its image under that operator.  The coefficient is the literal D(J),
and the cylinder uses the same E-first Cartesian tensor as the power
homotopy interface.  These are data and equations, with no model, weak,
Segal, completeness or Dwyer--Kan conclusion as an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialSpace.RezkCoefficientContractions
open WalkingEUnit

/-- The original coefficient is the literal discrete-inner full free-groupoid nerve. -/
def coefficient (n : SimplexCategory) : SimplicialSpace.{u} :=
  discreteInnerFunctor.obj (SSet.FreeGroupoidSimplex.J.{u}.obj n)

/-- Every original simplex operator acts through the same full-J functor and D. -/
def coefficientMap {n m : SimplexCategory} (δ : n ⟶ m) :
    coefficient.{u} n ⟶ coefficient.{u} m :=
  discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.J.{u}.map δ)

/-- The reverse is the actual constant map at the prescribed source vertex. -/
def reverseMap (n m : SimplexCategory) (v : Fin (n.len + 1)) :
    coefficient.{u} m ⟶ coefficient.{u} n :=
  discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} m n v)

/-- Both composites use the SAME reverse and the target vertex is exactly δ(v). -/
theorem reverseMap_composites {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) :
    coefficientMap.{u} δ ≫ reverseMap.{u} n m v =
      discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} n n v) ∧
    reverseMap.{u} n m v ≫ coefficientMap.{u} δ =
      discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} m m (δ v)) := by
  have h := SSet.FreeGroupoidSimplex.map_inverse_constants.{u} δ v
  constructor
  · exact (discreteInnerFunctor.map_comp _ _).symm.trans
      (congrArg discreteInnerFunctor.map h.1)
  · exact (discreteInnerFunctor.map_comp _ _).symm.trans
      (congrArg discreteInnerFunctor.map h.2)

/-- The E-first tensor maps to D of the actual chosen J × E product by its two projections. -/
def cylinderBridge (n : SimplexCategory) :
    coherentSpace.{u} ⊗ coefficient.{u} n ⟶
      discreteInnerFunctor.obj (SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯ SSet.coherentIso.{u}) := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) discreteInnerFunctor.{u} :=
    SegalExponentRawAssembly.discreteInnerPreservesBinaryProducts
  let h := isLimitOfHasBinaryProductOfPreservesLimit discreteInnerFunctor
    (SSet.FreeGroupoidSimplex.J.{u}.obj n) SSet.coherentIso.{u}
  exact BinaryFan.IsLimit.lift h
    (CartesianMonoidalCategory.snd coherentSpace (coefficient n))
    (CartesianMonoidalCategory.fst coherentSpace (coefficient n))

/-- Both bridge projections retain the actual tensor legs, in their original order. -/
theorem cylinderBridge_legs (n : SimplexCategory) :
    cylinderBridge.{u} n ≫ discreteInnerFunctor.map
        (prod.fst : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯ SSet.coherentIso.{u} ⟶
          SSet.FreeGroupoidSimplex.J.{u}.obj n) =
      CartesianMonoidalCategory.snd coherentSpace (coefficient n) ∧
    cylinderBridge.{u} n ≫ discreteInnerFunctor.map
        (prod.snd : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯ SSet.coherentIso.{u} ⟶
          SSet.coherentIso.{u}) =
      CartesianMonoidalCategory.fst coherentSpace (coefficient n) := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) discreteInnerFunctor.{u} :=
    SegalExponentRawAssembly.discreteInnerPreservesBinaryProducts
  dsimp only [cylinderBridge]
  exact ⟨BinaryFan.IsLimit.lift_fst _ _ _, BinaryFan.IsLimit.lift_snd _ _ _⟩

private theorem discreteConst_eq (K : SSet.{u}) (e : SSet.coherentIso.{u} _⦋0⦌) :
    discreteInnerFunctor.map (SSet.const (X := K) e) =
      CartesianMonoidalCategory.toUnit (discreteInnerFunctor.obj K) ≫ coherentPoint e := by
  have hc : SSet.const (X := K) e = CartesianMonoidalCategory.toUnit K ≫
      (SSet.unitHomEquiv SSet.coherentIso).symm e := by
    apply NatTrans.ext
    funext a
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have ht : discreteInnerFunctor.map (CartesianMonoidalCategory.toUnit K) =
      CartesianMonoidalCategory.toUnit (discreteInnerFunctor.obj K) ≫ coherentUnitIso.inv := by
    apply (cancel_mono coherentUnitIso.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact CartesianMonoidalCategory.toUnit_unique _ _
  rw [hc, CategoryTheory.Functor.map_comp, ht, Category.assoc]
  rfl

private theorem cylinderBridge_endpoint (n : SimplexCategory)
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    spaceEndpoint (coefficient.{u} n) e ≫ cylinderBridge n =
      discreteInnerFunctor.map (prod.lift (𝟙 (SSet.FreeGroupoidSimplex.J.{u}.obj n))
        (SSet.const (X := SSet.FreeGroupoidSimplex.J.{u}.obj n) e)) := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) discreteInnerFunctor.{u} :=
    SegalExponentRawAssembly.discreteInnerPreservesBinaryProducts
  apply BinaryFan.IsLimit.hom_ext
    (isLimitOfHasBinaryProductOfPreservesLimit discreteInnerFunctor
      (SSet.FreeGroupoidSimplex.J.{u}.obj n) SSet.coherentIso.{u})
  · change (spaceEndpoint (coefficient n) e ≫ cylinderBridge n) ≫
        discreteInnerFunctor.map (prod.fst : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯
          SSet.coherentIso.{u} ⟶ SSet.FreeGroupoidSimplex.J.{u}.obj n) =
      discreteInnerFunctor.map (prod.lift (𝟙 (SSet.FreeGroupoidSimplex.J.{u}.obj n))
        (SSet.const (X := SSet.FreeGroupoidSimplex.J.{u}.obj n) e)) ≫
          discreteInnerFunctor.map prod.fst
    erw [Category.assoc, (cylinderBridge_legs n).1, (spaceEndpoint_laws _ e).2.1,
      ← CategoryTheory.Functor.map_comp, prod.lift_fst, CategoryTheory.Functor.map_id]
    rfl
  · change (spaceEndpoint (coefficient n) e ≫ cylinderBridge n) ≫
        discreteInnerFunctor.map (prod.snd : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯
          SSet.coherentIso.{u} ⟶ SSet.coherentIso.{u}) =
      discreteInnerFunctor.map (prod.lift (𝟙 (SSet.FreeGroupoidSimplex.J.{u}.obj n))
        (SSet.const (X := SSet.FreeGroupoidSimplex.J.{u}.obj n) e)) ≫
          discreteInnerFunctor.map prod.snd
    erw [Category.assoc, (cylinderBridge_legs n).2, (spaceEndpoint_laws _ e).1,
      ← CategoryTheory.Functor.map_comp, prod.lift_snd, discreteConst_eq]
    rfl

private theorem scalarContraction_endpoint (n : SimplexCategory)
    (v : Fin (n.len + 1)) (e : SSet.coherentIso.{u} _⦋0⦌)
    (r : SSet.FreeGroupoidSimplex.J.{u}.obj n ⟶ SSet.FreeGroupoidSimplex.J.{u}.obj n)
    (he : prod.map (𝟙 (SSet.FreeGroupoidSimplex.J.{u}.obj n))
        (SSet.yonedaEquiv.symm e) ≫ SSet.FreeGroupoidSimplex.intervalContraction.{u} n v =
      (prod.fst : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶
        SSet.FreeGroupoidSimplex.J.{u}.obj n) ≫ r) :
    prod.lift (𝟙 (SSet.FreeGroupoidSimplex.J.{u}.obj n))
        (SSet.const (X := SSet.FreeGroupoidSimplex.J.{u}.obj n) e) ≫
      SSet.FreeGroupoidSimplex.intervalContraction.{u} n v = r := by
  let K := SSet.FreeGroupoidSimplex.J.{u}.obj n
  let t : K ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from K
  have hs : prod.lift (𝟙 K) t ≫ (prod.fst : K ⨯ (Δ[0] : SSet.{u}) ⟶ K) = 𝟙 K :=
    prod.lift_fst _ _
  have hc : t ≫ SSet.yonedaEquiv.symm e = SSet.const (X := K) e := by
    erw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  have hl : prod.lift (𝟙 K) t ≫
      prod.map (𝟙 K) (SSet.yonedaEquiv.symm e) =
        prod.lift (𝟙 K) (SSet.const (X := K) e) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
    · erw [Category.assoc, prod.map_snd, ← Category.assoc, prod.lift_snd, prod.lift_snd]
      exact hc
  calc
    prod.lift (𝟙 K) (SSet.const (X := K) e) ≫
        SSet.FreeGroupoidSimplex.intervalContraction n v =
      (prod.lift (𝟙 K) t ≫ prod.map (𝟙 K) (SSet.yonedaEquiv.symm e)) ≫
        SSet.FreeGroupoidSimplex.intervalContraction n v := by erw [hl]
    _ = (prod.lift (𝟙 K) t ≫ prod.fst) ≫ r := by erw [Category.assoc, he, ← Category.assoc]
    _ = r := by erw [hs, Category.id_comp]

/-- Lift the whole original interval contraction through D and the E-first bridge. -/
def coefficientContraction (n : SimplexCategory) (v : Fin (n.len + 1)) :
    coherentSpace.{u} ⊗ coefficient.{u} n ⟶ coefficient.{u} n :=
  cylinderBridge n ≫
    discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.intervalContraction.{u} n v)

/-- The same full coefficient contraction has both original walking-E endpoints. -/
theorem coefficientContraction_endpoints (n : SimplexCategory) (v : Fin (n.len + 1)) :
    spaceEndpoint (coefficient.{u} n) SSet.coherentIso.x₀ ≫ coefficientContraction n v =
      discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} n n v) ∧
    spaceEndpoint (coefficient.{u} n) SSet.coherentIso.x₁ ≫ coefficientContraction n v =
      𝟙 (coefficient.{u} n) := by
  have h0 := scalarContraction_endpoint.{u} n v SSet.coherentIso.x₀
    (SSet.FreeGroupoidSimplex.constantMap.{u} n n v)
    (SSet.FreeGroupoidSimplex.intervalContraction_zero.{u} n v)
  have h1 := scalarContraction_endpoint.{u} n v SSet.coherentIso.x₁ (𝟙 _)
    (by simpa only [Category.comp_id] using
      SSet.FreeGroupoidSimplex.intervalContraction_one.{u} n v)
  constructor
  · change spaceEndpoint (coefficient n) SSet.coherentIso.x₀ ≫
      (cylinderBridge n ≫ discreteInnerFunctor.map
        (SSet.FreeGroupoidSimplex.intervalContraction.{u} n v)) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ discreteInnerFunctor.map
        (SSet.FreeGroupoidSimplex.intervalContraction.{u} n v))
          (cylinderBridge_endpoint n SSet.coherentIso.x₀)).trans
        ((discreteInnerFunctor.map_comp _ _).symm.trans (congrArg discreteInnerFunctor.map h0)))
  · change spaceEndpoint (coefficient n) SSet.coherentIso.x₁ ≫
      (cylinderBridge n ≫ discreteInnerFunctor.map
        (SSet.FreeGroupoidSimplex.intervalContraction.{u} n v)) = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ discreteInnerFunctor.map
        (SSet.FreeGroupoidSimplex.intervalContraction.{u} n v))
          (cylinderBridge_endpoint n SSet.coherentIso.x₁)).trans
        ((discreteInnerFunctor.map_comp _ _).symm.trans
          ((congrArg discreteInnerFunctor.map h1).trans (discreteInnerFunctor.map_id _))))

/-- Every original operator preserves the full bridge and its two original projection legs. -/
theorem cylinderBridge_site {n m : SimplexCategory} (δ : n ⟶ m) :
    (coherentSpace.{u} ◁ coefficientMap.{u} δ) ≫ cylinderBridge m =
      cylinderBridge n ≫ discreteInnerFunctor.map
        (prod.map (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u})) := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) discreteInnerFunctor.{u} :=
    SegalExponentRawAssembly.discreteInnerPreservesBinaryProducts
  apply BinaryFan.IsLimit.hom_ext
    (isLimitOfHasBinaryProductOfPreservesLimit discreteInnerFunctor
      (SSet.FreeGroupoidSimplex.J.{u}.obj m) SSet.coherentIso.{u})
  · change ((coherentSpace.{u} ◁ coefficientMap.{u} δ) ≫ cylinderBridge m) ≫
        discreteInnerFunctor.map (prod.fst : SSet.FreeGroupoidSimplex.J.{u}.obj m ⨯
          SSet.coherentIso.{u} ⟶ SSet.FreeGroupoidSimplex.J.{u}.obj m) =
      (cylinderBridge n ≫ discreteInnerFunctor.map
        (prod.map (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u}))) ≫
          discreteInnerFunctor.map prod.fst
    have hm : discreteInnerFunctor.map
        (prod.map (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u})) ≫
        discreteInnerFunctor.map (prod.fst : SSet.FreeGroupoidSimplex.J.{u}.obj m ⨯
          SSet.coherentIso.{u} ⟶ SSet.FreeGroupoidSimplex.J.{u}.obj m) =
      discreteInnerFunctor.map (prod.fst : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯
          SSet.coherentIso.{u} ⟶ SSet.FreeGroupoidSimplex.J.{u}.obj n) ≫ coefficientMap δ :=
      (discreteInnerFunctor.map_comp _ _).symm.trans
        ((congrArg discreteInnerFunctor.map
          (prod.map_fst (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u}))).trans
            (discreteInnerFunctor.map_comp _ _))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (coherentSpace ◁ coefficientMap δ) ≫ f) (cylinderBridge_legs m).1).trans
        ((CartesianMonoidalCategory.whiskerLeft_snd coherentSpace (coefficientMap δ)).trans
          ((congrArg (fun f => f ≫ coefficientMap δ) (cylinderBridge_legs n).1.symm).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun f => cylinderBridge n ≫ f) hm.symm).trans
                (Category.assoc _ _ _).symm)))))
  · change ((coherentSpace.{u} ◁ coefficientMap.{u} δ) ≫ cylinderBridge m) ≫
        discreteInnerFunctor.map (prod.snd : SSet.FreeGroupoidSimplex.J.{u}.obj m ⨯
          SSet.coherentIso.{u} ⟶ SSet.coherentIso.{u}) =
      (cylinderBridge n ≫ discreteInnerFunctor.map
        (prod.map (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u}))) ≫
          discreteInnerFunctor.map prod.snd
    have hm : discreteInnerFunctor.map
        (prod.map (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u})) ≫
        discreteInnerFunctor.map (prod.snd : SSet.FreeGroupoidSimplex.J.{u}.obj m ⨯
          SSet.coherentIso.{u} ⟶ SSet.coherentIso.{u}) =
      discreteInnerFunctor.map (prod.snd : SSet.FreeGroupoidSimplex.J.{u}.obj n ⨯
          SSet.coherentIso.{u} ⟶ SSet.coherentIso.{u}) :=
      (discreteInnerFunctor.map_comp _ _).symm.trans
        (congrArg discreteInnerFunctor.map
          ((prod.map_snd (SSet.FreeGroupoidSimplex.J.{u}.map δ) (𝟙 SSet.coherentIso.{u})).trans
            (Category.comp_id _)))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => (coherentSpace ◁ coefficientMap δ) ≫ f) (cylinderBridge_legs m).2).trans
        ((CartesianMonoidalCategory.whiskerLeft_fst coherentSpace (coefficientMap δ)).trans
          ((cylinderBridge_legs n).2.symm.trans
            ((congrArg (fun f => cylinderBridge n ≫ f) hm.symm).trans
              (Category.assoc _ _ _).symm))))

/-- Site naturality uses v on the source and exactly δ(v) on the target. -/
theorem coefficientContraction_site {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) :
    (coherentSpace.{u} ◁ coefficientMap.{u} δ) ≫ coefficientContraction m (δ v) =
      coefficientContraction n v ≫ coefficientMap δ := by
  dsimp only [coefficientContraction, coefficientMap, coefficient]
  erw [← Category.assoc, cylinderBridge_site, Category.assoc,
    ← CategoryTheory.Functor.map_comp, SSet.FreeGroupoidSimplex.intervalContraction_site,
    CategoryTheory.Functor.map_comp, ← Category.assoc]

/-- The two homotopies for an original operator are constructed internally from the SAME reverse. -/
theorem operator_inverse_homotopies {n m : SimplexCategory} (δ : n ⟶ m)
    (v : Fin (n.len + 1)) :
    spaceEndpoint (coefficient.{u} n) SSet.coherentIso.x₀ ≫ coefficientContraction n v =
        coefficientMap δ ≫ reverseMap n m v ∧
    spaceEndpoint (coefficient.{u} n) SSet.coherentIso.x₁ ≫ coefficientContraction n v =
        𝟙 (coefficient n) ∧
    spaceEndpoint (coefficient.{u} m) SSet.coherentIso.x₀ ≫ coefficientContraction m (δ v) =
        reverseMap n m v ≫ coefficientMap δ ∧
    spaceEndpoint (coefficient.{u} m) SSet.coherentIso.x₁ ≫ coefficientContraction m (δ v) =
        𝟙 (coefficient m) := by
  have hn := coefficientContraction_endpoints.{u} n v
  have hm := coefficientContraction_endpoints.{u} m (δ v)
  have hr := reverseMap_composites.{u} δ v
  exact ⟨hn.1.trans hr.1.symm, hn.2, hm.1.trans hr.2.symm, hm.2⟩

end SimplicialSpace.RezkCoefficientContractions
