/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereNullHom
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerMaps
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison

/-!
# Original sphere representatives and the actual suspended Q-cofiber lift

Every literal level cube represents the same whole native free-sphere
morphism in the level homotopy category. A null cofiber image has a strict
representative by the actual free-source cofibrancy and fundamental lemma.
The original chosen I cone then supplies its suspended coefficient lift.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev S := OriginalISuspension.suspension (B := B) (I := Index)

/-- The original sphere coefficient gives the full native free source at each actual level. -/
def sphereSource (m n : ℕ) : PointedCGWH.SequentialSpectrum.{u, v} :=
  (EnrichedFunctorCat.Free.functor
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)).obj
      (PointedCGWH.SphereHom.sphere n)

/-- The original source free/evaluation adjunction proves cofibrancy of the full sphere diagram. -/
theorem sphereSource_isCofibrant (m n : ℕ) : IsCofibrant (sphereSource.{u, v} m n) := by
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  let _ : (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v})
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree
        PointedCGWH.sphereOne m)).IsQuillenAdjunction :=
    HomotopicalAlgebra.EnrichedProjective.Native.freeAtEvaluation_isQuillenAdjunction _
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := EnrichedFunctorCat.Free.adjunction _) inferInstance

/-- A literal null sphere coefficient has the source's actual suspended Q-cone lift. -/
theorem sphereSuspendedLift_of_null
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (g : sphereSource m n ⟶ Q.obj F.right)
    (hg : H.map (g ≫ inclusion F) =
      OrdinaryHoCofiberKernel.nullHom (sphereSource m n) (cofiber.obj F)) :
    ∃ k : H.obj (S.obj (sphereSource m n)) ⟶ H.obj (S.obj (Q.obj F.left)),
      k ≫ H.map (S.map (Q.map F.hom)) = H.map (S.map g) := by
  let _ : IsCofibrant (sphereSource.{u, v} m n) := sphereSource_isCofibrant m n
  have hNull : H.map (g ≫ inclusion F) = H.map
      (OrdinaryHoChosenPuppe.nullMap Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (sphereSource m n) (cofiber.obj F)) := by
    rw [OrdinaryHoChosenPuppe.actualNullMap_eq_chosen]
    exact hg
  exact OriginalFiberComparison.originalQCoefficientLift_of_null (B := B) F
    (sphereSource m n) g hNull

/-- The exact original level class produces its full source sphere map. -/
def levelSphereClass (m n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (x : PointedCGWH.piN n (X.level m)) : H.obj (sphereSource m n) ⟶ H.obj X :=
  freeSpherePiHomEquiv (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n X x

/-- A null original level image gives exactly the same whole coefficient null morphism. -/
theorem levelSphereClass_null_composite
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (x : PointedCGWH.piN n (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) m))
    (hx : PointedCGWH.piNMap n
        (PointedCGWH.SequentialSpectrum.levelMap (inclusion F) m) x =
      PointedCGWH.SphereHom.nullCube n (PointedCGWH.SequentialSpectrum.level (cofiber.obj F) m)) :
    levelSphereClass m n (Q.obj F.right) x ≫ H.map (inclusion F) =
      OrdinaryHoCofiberKernel.nullHom (sphereSource m n) (cofiber.obj F) := by
  have h := freeSpherePiHomEquiv_naturality (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
    n (inclusion F) x
  have hNull := freeSpherePiHomEquiv_null (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
    n (cofiber.obj F)
  exact h.symm.trans ((congrArg
    (freeSpherePiHomEquiv (B := B)
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)
      n (cofiber.obj F)) hx).trans hNull)

/-- The original fundamental lemma realizes the same null coefficient by a strict spectrum map. -/
theorem levelSphereClass_null_representative
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (x : PointedCGWH.piN n (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) m))
    (hx : PointedCGWH.piNMap n
        (PointedCGWH.SequentialSpectrum.levelMap (inclusion F) m) x =
      PointedCGWH.SphereHom.nullCube n (PointedCGWH.SequentialSpectrum.level (cofiber.obj F) m)) :
    ∃ g : sphereSource m n ⟶ Q.obj F.right,
      H.map g = levelSphereClass m n (Q.obj F.right) x ∧
      H.map (g ≫ inclusion F) =
        OrdinaryHoCofiberKernel.nullHom (sphereSource m n) (cofiber.obj F) := by
  let _ : IsCofibrant (sphereSource.{u, v} m n) := sphereSource_isCofibrant m n
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization H (sphereSource m n) (Q.obj F.right)
    (levelSphereClass m n (Q.obj F.right) x)
  refine ⟨g, hg, ?_⟩
  rw [H.map_comp, hg]
  exact levelSphereClass_null_composite F m n x hx

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
