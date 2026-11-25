/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.GlobalSolidCoefficientLimits
import MathlibExt.Condensed.SolidTorsionFrobeniusModels

/-!
# Enhanced pullbacks and Frobenius go through the almost localization

The enhanced local pullback and the enhanced Frobenius are the raw DG-module extension followed by
the almost localization of the target model, on objects and on Hom complexes. The unit of an almost
localization is natural, also against identities, and has an almost-zero cone. Hypercompleteness
provides a replacement model of every hypercover diagram.
-/

namespace MathlibExtTest.AlmostLocalization

open CategoryTheory Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.Condensed
open GeometricDGModules LocalSolidCoefficientModels SolidTorsionFrobeniusModels
open GlobalSolidCoefficientLimits MathlibExt.CategoryTheory.CategoricalCoefficientLimits

section Pullback

variable {p : ℕ} [Fact p.Prime] {P Q : AffineUntilting p} {f : P ⟶ Q}
  {MP : LocalModel p P} {MQ : LocalModel p Q} (B : PullbackModel p f MP MQ)

/-- The enhanced pullback of an almost-local module is the almost localization of its raw
extension. -/
example (N : LocalCategory p MQ) :
    (B.localExtension p).obj N =
      MP.localization.functor.obj (B.extension.functor.obj ⟨N.obj, N.property.1⟩) := rfl

/-- On Hom complexes it is the raw extension followed by the localization. -/
example (M N : LocalCategory p MQ) :
    (B.localExtension p).map M N =
      B.extension.functor.map ⟨M.obj, M.property.1⟩ ⟨N.obj, N.property.1⟩ ≫
        (restrictCochains (coefficientMap p f)).map
          (MP.localization.functor.map (B.extension.functor.obj ⟨M.obj, M.property.1⟩)
            (B.extension.functor.obj ⟨N.obj, N.property.1⟩)) := rfl

end Pullback

section Frobenius

variable {p : ℕ} [Fact p.Prime] {P : AffineUntilting p} {π : Pseudouniformizer p P}
  {h : π.element ∣ (p : P.pair.plus)} {M : TorsionModel p P π} (F : FrobeniusModel p P π h M)

/-- The enhanced Frobenius of an almost-local module is the almost localization of its raw
extension. -/
example (N : TorsionCategory p P π M) :
    (F.localExtension p P π).obj N =
      M.localization.functor.obj (F.extension.functor.obj ⟨N.obj, N.property.1⟩) := rfl

end Frobenius

section Localization

variable {A : Type 1} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {G : Profinite.{0} → SolidAnalyticModules.GeometricDerived A} {M : CompactDGModel A G}
  {I : Ideal A} (L : AlmostLocalization A M I)

/-- The cone of the unit is almost zero on every component. -/
example (X : ModifiedModules A M) (x : M.objectsᵒᵖ) (n : ℤ) (a : A) (ha : a ∈ I)
    (z : ((HomologicalComplex.homologyFunctor (ModuleCat.{1} A) (ComplexShape.up ℤ) n).obj
      (CochainComplex.mappingCone (moduleComponent (L.unit X) x)))) :
    a • z = 0 :=
  L.almost_cone X x n a ha z

/-- Naturality of the unit against the identity: both sides are the unit. -/
example (X : ModifiedModules A M) :
    dgComp A (C := RightModule A M.objects) (X := X.obj) (Y := (L.functor.obj X).obj)
        (Z := (L.functor.obj X).obj)
        ((DGFunctor.homEquivDGCycles A X.obj (L.functor.obj X).obj (L.unit X)).val)
        (L.functor.dgMap 0 (dgId A X)) (zero_add 0) =
      dgComp A (C := RightModule A M.objects) (X := X.obj) (Y := X.obj)
        (Z := (L.functor.obj X).obj) (dgId A X)
        ((DGFunctor.homEquivDGCycles A X.obj (L.functor.obj X).obj (L.unit X)).val)
        (add_zero 0) :=
  L.unit_natural X X 0 (dgId A X)

end Localization

/-- Hypercompleteness provides a replacement model of every hypercover diagram. -/
example {p : ℕ} [Fact p.Prime] {G : LocalDiagram p} (M : GlobalModel p G) (hM : IsHypercomplete p M)
    (F : Sheaf (originalVTopology p) (Type 1))
    (H : MathlibExt.CategoryTheory.SheafHypercoverModels.Hypercover F) :
    Nonempty (DiagramModel.{2, 0, 0} (hypercoverDiagram p M H)) :=
  (hM F H).1

end MathlibExtTest.AlmostLocalization
