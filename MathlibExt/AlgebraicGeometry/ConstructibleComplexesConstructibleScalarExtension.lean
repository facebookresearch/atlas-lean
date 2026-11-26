/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Scalar extension of bounded constructible complexes

Derived field extension preserves bounded algebraic constructibility with the
same stratification. The proof transports local trivializations and cohomology
through scalar extension.

Sources: A. Dimca, *Sheaves in Topology*, Chapters 2–4; M. de Cataldo and
L. Migliorini, *The decomposition theorem, perverse sheaves and the topology
of algebraic maps*, arXiv:0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

private def scalarExtensionPullbackIso (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z W : TopCat.{0}) (f : Z ⟶ W) :
    scalarExtension k l W ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} l) f ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} k) f ⋙ scalarExtension k l Z := by
  let a := (Sheaf.adjunction (Opens.grothendieckTopology W)
    (ModuleCat.extendRestrictScalarsAdj (algebraMap k l))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} l) f)
  let b := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).comp
    (Sheaf.adjunction (Opens.grothendieckTopology Z)
      (ModuleCat.extendRestrictScalarsAdj (algebraMap k l)))
  exact a.leftAdjointUniq b

private def scalarExtensionConstantIso (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z : TopCat.{0}) :
    constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k) ⋙ scalarExtension k l Z ≅
      ModuleCat.extendScalars (algebraMap k l) ⋙
        constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} l) := by
  let a := (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} k)
    (isTerminalTop (α := Opens Z))).comp
      (Sheaf.adjunction (Opens.grothendieckTopology Z)
        (ModuleCat.extendRestrictScalarsAdj (algebraMap k l)))
  let b := (ModuleCat.extendRestrictScalarsAdj (algebraMap k l)).comp
    (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} l)
      (isTerminalTop (α := Opens Z)))
  exact a.leftAdjointUniq b

private theorem localSystem_of_iso (k : Type) [Field k] (Z : TopCat.{0})
    (F G : CoefficientSheaf k Z) (e : F ≅ G)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F) :
    ConstructibleComplexes.IsFiniteRankLocalSystem k Z G := by
  intro x
  obtain ⟨U, hx, V, hV, ⟨i⟩⟩ := hF x
  exact ⟨U, hx, V, hV, ⟨(TopCat.Sheaf.pullback (ModuleCat.{0} k)
    (openInclusion Z U)).mapIso e.symm ≪≫ i⟩⟩

private theorem scalarExtension_localSystem_local (k l : Type) [Field k] [Field l]
    [Algebra k l] (Z : TopCat.{0}) (F : CoefficientSheaf k Z)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F) :
    ConstructibleComplexes.IsFiniteRankLocalSystem l Z ((scalarExtension k l Z).obj F) := by
  intro x
  obtain ⟨U, hx, V, hV, ⟨e⟩⟩ := hF x
  let : FiniteDimensional k V := hV
  refine ⟨U, hx, (ModuleCat.extendScalars (algebraMap k l)).obj V, ?_, ⟨?_⟩⟩
  · let : Algebra k l := (algebraMap k l).toAlgebra
    exact Module.Finite.base_change k l V
  · exact (scalarExtensionPullbackIso k l (TopCat.of U) Z (openInclusion Z U)).app F ≪≫
      (scalarExtension k l (TopCat.of U)).mapIso e ≪≫
        (scalarExtensionConstantIso k l (TopCat.of U)).app V

private def scalarExtensionHomologyIso (k l : Type) [Field k] [Field l] [Algebra k l]
    (Z : TopCat.{0}) (K : CoefficientDerived k Z) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).obj ((derivedScalarExtension k l Z).obj K) ≅
      (scalarExtension k l Z).obj ((DerivedCategory.homologyFunctor _ j).obj K) := by
  let F := scalarExtension k l Z
  let M := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor _ j).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor _ j).mapIso (F.mapDerivedCategoryFactors.app M) ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫
    (M.sc j).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors _ j).app M).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor _ j).mapIso e)

/-- Derived field extension preserves the same algebraic stratification property. -/
public theorem constructible_scalarExtension (k l : Type) [Field k] [Field l]
    [Algebra k l] (X : ComplexScheme) [IsComplexVariety X]
    (K : CoefficientDerived k (space X))
    (hK : ConstructibleComplexes.boundedConstructible k X K) :
    ConstructibleComplexes.boundedConstructible l X
      ((derivedScalarExtension k l (space X)).obj K)
    := by
  obtain ⟨⟨a, b, hb⟩, S, hS⟩ := hK
  constructor
  · refine ⟨a, b, fun j hj ↦ ?_⟩
    exact ((scalarExtension k l (space X)).map_isZero (hb j hj)).of_iso
      (scalarExtensionHomologyIso k l (space X) K j)
  · refine ⟨S, fun a j ↦ ?_⟩
    let f := spaceMap (S.inclusion a)
    exact localSystem_of_iso l (space (S.stratum a)) _ _
      (((scalarExtensionPullbackIso k l (space (S.stratum a)) (space X) f).app _).symm ≪≫
        (TopCat.Sheaf.pullback (ModuleCat.{0} l) f).mapIso
          (scalarExtensionHomologyIso k l (space X) K j).symm)
      (scalarExtension_localSystem_local k l (space (S.stratum a)) _ (hS a j))

end WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted
