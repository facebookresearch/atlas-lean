/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.DegreeTwoHurewiczMap

/-!
# The literal unnormalized cycle of a pointed two-simplex

The standard normalization inclusion sends the original pointed normalized
two-generator to the original simplex generator minus its constant generator.
Both the inclusion and the unnormalized chain object are the original models.
No sphere calibration, Hurewicz inverse or homology-isomorphism premise is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- The original normalization inclusion has this exact positive pointed
generator formula. The constant subtraction makes it an unnormalized cycle. -/
theorem pointedTwoGenerator_fromNormalized_eq_sub_const
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    pointedTwoGenerator p ≫
        (X.fromNormalizedChainComplex
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f 2 =
      X.ιChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
          (yonedaEquiv (RelativeMorphism.map p)) -
        X.ιChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
          (yonedaEquiv (const x : Δ[2] ⟶ X)) := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  let A : SimplicialObject AddCommGrpCat.{u} :=
    ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X
  let s : X _⦋2⦌ := yonedaEquiv (RelativeMorphism.map p)
  let c : X _⦋2⦌ := yonedaEquiv (const x : Δ[2] ⟶ X)
  let z : R ⟶ (X.chainComplex R).X 2 :=
    X.ιChainComplex (R := R) s - X.ιChainComplex (R := R) c
  have hface (i : Fin 3) : X.δ i s = X.δ i c := by
    dsimp only [s, c]
    rw [← stdSimplex.yonedaEquiv_δ_comp, PtSimplex.δ_map,
      ← stdSimplex.yonedaEquiv_δ_comp, comp_const]
  have hvanish : AlgebraicTopology.DoldKan.HigherFacesVanish (X := A) (n := 1) 2 z := by
    intro j _hj
    change (X.ιChainComplex (R := R) s - X.ιChainComplex (R := R) c) ≫
      Sigma.map' (C := AddCommGrpCat.{u})
        (f := fun _ : X _⦋1⦌ => R) (g := fun _ : X _⦋2⦌ => R)
        (X.δ j.succ) (fun _ => 𝟙 R) = 0
    simp only [ιChainComplex, Preadditive.sub_comp, Sigma.ι_comp_map',
      Category.id_comp, hface, sub_self]
  have hfixed :
      z ≫ (AlgebraicTopology.DoldKan.PInfty (X := A)).f 2 = z := by
    rw [AlgebraicTopology.DoldKan.PInfty_f]
    exact hvanish.comp_P_eq_self
  have hproject : z ≫ (X.toNormalizedChainComplex R).f 2 = pointedTwoGenerator p := by
    dsimp only [z, s, c]
    simp only [Preadditive.sub_comp, ιChainComplex_toNormalizedChainComplex_f,
      ιNormalizedChainComplex_yonedaEquiv_const_eq_zero, sub_zero,
      pointedTwoGenerator]
  calc
    pointedTwoGenerator p ≫ (X.fromNormalizedChainComplex R).f 2 =
        (z ≫ (X.toNormalizedChainComplex R).f 2) ≫
          (X.fromNormalizedChainComplex R).f 2 := by rw [hproject]
    _ = z ≫ (AlgebraicTopology.DoldKan.PInfty (X := A)).f 2 := by
      rw [Category.assoc, toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
    _ = z := hfixed

/-- The exact corrected original two-generator is an actual unnormalized cycle. -/
theorem pointedTwoSubConstGenerator_cycle
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    (X.ιChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
          (yonedaEquiv (RelativeMorphism.map p)) -
        X.ιChainComplex
          (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
          (yonedaEquiv (const x : Δ[2] ⟶ X))) ≫
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).d 2 1 = 0 := by
  rw [← pointedTwoGenerator_fromNormalized_eq_sub_const p, Category.assoc,
    (X.fromNormalizedChainComplex
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).comm 2 1,
    ← Category.assoc, pointedTwoGenerator_cycle, zero_comp]

/-- The original normalized class, included in original unnormalized H₂,
is represented by the original simplex minus its original constant simplex. -/
theorem pointedTwoHomologyClass_fromNormalized_explicit
    {X : SSet.{u}} {x : X _⦋0⦌} (p : X.PtSimplex 2 x) :
    pointedTwoHomologyClass p ≫
        (X.normalizedHomologyIso (C := AddCommGrpCat.{u})
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom =
      (X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).liftCycles
        (X.ιChainComplex
            (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
            (yonedaEquiv (RelativeMorphism.map p)) -
          X.ιChainComplex
            (R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}))
            (yonedaEquiv (const x : Δ[2] ⟶ X)))
        1 (by simp) (pointedTwoSubConstGenerator_cycle p) ≫
          (X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).homologyπ 2 := by
  rw [normalizedHomologyIso_hom, pointedTwoHomologyClass, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  apply (cancel_mono ((X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 2)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    pointedTwoCycle_i, HomologicalComplex.liftCycles_i,
    pointedTwoGenerator_fromNormalized_eq_sub_const]

end SSet
