/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SuspendedFreeSphere
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberSphereLift

/-!
# Original scalar images of suspended cofiber coefficient lifts

The original free-sphere Q counit and I-to-scalar suspension comparison
transport a proved coefficient lift to the actual scalar free source.
The whole map equation retains each original Q, source counit and target
comparison. This is a Hom lift, with the integer suspension comparison
still needed to turn it into a stable group preimage.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory
namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index)
private abbrev S := OriginalISuspension.suspension (B := B) (I := Index)
private abbrev T :=
  CategoryTheory.EnrichedFunctorCat.tensorLeft (A := Index) PointedCGWH.sphereOne

/-- The original I-suspended null coefficient is transported to actual scalar free-sphere Hom. -/
def suspendedCoefficientLift (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (k : H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left))) :
    H.obj ((CategoryTheory.EnrichedFunctorCat.Free.functor
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m)).obj
        (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n))) ⟶
      H.obj (T.obj (Q.obj F.left)) :=
  (originalSuspendedFreeSphereIso (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n).inv ≫
      k ≫ (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app F.left

/-- The original Q source counit gives the same suspended coefficient lift on the Q-free source. -/
def qSuspendedCoefficient (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (k : H.obj (S.obj (sphereSource m n)) ⟶ H.obj (S.obj (Q.obj F.left))) :
    H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left)) :=
  H.map (S.map (ε.app (sphereSource m n))) ≫ k

/-- The full map equation retains the original Q source counit and unchanged target. -/
theorem qSuspendedCoefficient_map
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (g : sphereSource m n ⟶ Q.obj F.right)
    (k : H.obj (S.obj (sphereSource m n)) ⟶ H.obj (S.obj (Q.obj F.left)))
    (hk : k ≫ H.map (S.map (Q.map F.hom)) = H.map (S.map g)) :
    qSuspendedCoefficient F m n k ≫ H.map (S.map (Q.map F.hom)) =
      H.map (S.map (ε.app (sphereSource m n) ≫ g)) := by
  rw [qSuspendedCoefficient, Category.assoc, hk, ← H.map_comp, ← S.map_comp]

/-- The transported lift retains the same original scalar suspension map equation. -/
theorem suspendedCoefficientLift_map
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (m n : ℕ)
    (g : sphereSource m n ⟶ Q.obj F.right)
    (k : H.obj (S.obj (Q.obj (sphereSource m n))) ⟶ H.obj (S.obj (Q.obj F.left)))
    (hk : k ≫ H.map (S.map (Q.map F.hom)) = H.map (S.map (ε.app (sphereSource m n) ≫ g))) :
    suspendedCoefficientLift F m n k ≫ H.map (T.map (Q.map F.hom)) =
      (originalSuspendedFreeSphereIso (B := B)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n).inv ≫
        H.map (S.map (ε.app (sphereSource m n) ≫ g)) ≫
          (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app F.right := by
  let e := ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := Index)
  have hn := ScalarSphereSuspension.originalISuspensionQIsoSphereQ_hom_naturality
    (B := B) F.hom
  let a := (originalSuspendedFreeSphereIso (B := B)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne m) n).inv
  change (a ≫ k ≫ e.hom.app F.left) ≫ H.map (T.map (Q.map F.hom)) =
    a ≫ H.map (S.map (ε.app (sphereSource m n) ≫ g)) ≫ e.hom.app F.right
  calc
    (a ≫ k ≫ e.hom.app F.left) ≫ H.map (T.map (Q.map F.hom)) =
        a ≫ k ≫ (e.hom.app F.left ≫ H.map (T.map (Q.map F.hom))) :=
      (Category.assoc a (k ≫ e.hom.app F.left)
        (H.map (T.map (Q.map F.hom)))).trans
        (congrArg (fun q => a ≫ q) (Category.assoc k (e.hom.app F.left)
          (H.map (T.map (Q.map F.hom)))))
    _ = a ≫ k ≫ (H.map (S.map (Q.map F.hom)) ≫ e.hom.app F.right) :=
      congrArg (fun q => a ≫ k ≫ q) hn.symm
    _ = a ≫ (k ≫ H.map (S.map (Q.map F.hom))) ≫ e.hom.app F.right :=
      congrArg (fun q => a ≫ q)
        (Category.assoc k (H.map (S.map (Q.map F.hom))) (e.hom.app F.right)).symm
    _ = a ≫ H.map (S.map (ε.app (sphereSource m n) ≫ g)) ≫ e.hom.app F.right :=
      congrArg (fun q => a ≫ q ≫ e.hom.app F.right) hk

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
