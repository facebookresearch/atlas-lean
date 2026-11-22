/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereHom
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoCofiberKernel
import MathlibExt.Topology.Category.PointedCGWH.Zero
import MathlibExt.Topology.Category.PointedCGWH.Colimits.ClosedSequential

/-!
# Constant cube classes and null sphere maps

The constant cube represents the null class in every homotopy degree and the group
identity in positive degrees. Its sphere-representation map is the morphism factoring
through the zero object in the homotopy category, and constant cube classes are
preserved by pointed maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.SphereHom
attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant
private abbrev H := toHomotopyCategory PointedCGWH.{u, v}
private abbrev Z : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point)

/-- The actual null cube class uses the original constant cube, including degree zero. -/
def nullCube (n : ℕ) (X : PointedCGWH.{u, v}) : PointedCGWH.piN n X :=
  HomotopyGroup.mk GenLoop.const

/-- In each positive degree the same constant cube is the original group identity. -/
theorem nullCube_eq_one (k : ℕ) (X : PointedCGWH.{u, v}) :
    nullCube (k + 1) X = (1 : (PointedCGWH.piNPositiveFunctor k).obj X) := by
  exact (HomotopyGroup.one_def).symm

/-- The same original pointed zero map sends the constant cube to the original constant cube. -/
theorem nullCube_map (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    PointedCGWH.piNMap n f (nullCube n X) = nullCube n Y := by
  let e := Equiv.cast (congrArg
    (fun y => HomotopyGroup.Pi n (CGWH.cgwhToTop.obj Y.right) y)
    (PointedCGWH.underlyingBasepoint_naturality f).symm)
  apply e.injective
  change Eq.mp (congrArg
      (fun y => HomotopyGroup.Pi n (CGWH.cgwhToTop.obj Y.right) y)
      (PointedCGWH.underlyingBasepoint_naturality f).symm)
      (PointedCGWH.piNMap n f (nullCube n X)) = _
  rw [PointedCGWH.piNMap_apply]
  have hconst {A : Type v} [TopologicalSpace A] {x y : A} (h : x = y) :
      Eq.mp (congrArg (fun a => HomotopyGroup.Pi n A a) h)
          (HomotopyGroup.mk (GenLoop.const : GenLoop (Fin n) A x)) =
        HomotopyGroup.mk (GenLoop.const : GenLoop (Fin n) A y) := by
    cases h
    rfl
  exact (hconst (PointedCGWH.underlyingBasepoint_naturality f).symm).symm

/-- Every actual localized map from a cofibrant source to the literal zero is unique. -/
private theorem zero_hom_subsingleton (K : PointedCGWH.{u, v}) [IsCofibrant K] :
    Subsingleton (H.obj K ⟶ H.obj Z.{u, v}) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := map_surjective_of_isLocalization H K Z a
  obtain ⟨b, rfl⟩ := map_surjective_of_isLocalization H K Z b
  apply H.congr_map
  apply Under.UnderMorphism.ext
  exact CGWH.point_isTerminal.hom_ext a.right b.right

/-- Sphere representation retains the original null class at every degree. -/
theorem spherePiHomEquiv_nullCube (n : ℕ) (X : PointedCGWH.{u, v}) :
    spherePiHomEquiv n X (nullCube n X) = OrdinaryHoCofiberKernel.nullHom (sphere n) X := by
  let f : Z.{u, v} ⟶ X := Under.mkIdInitial.to X
  have h := spherePiHomEquiv_naturality n f (nullCube n Z)
  rw [nullCube_map] at h
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  let _ : IsCofibrant (sphere.{u, v} n) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := powerAdjunction n)
      inferInstance
  let _ : Subsingleton (H.obj (sphere n) ⟶ H.obj Z) := zero_hom_subsingleton (sphere n)
  have hz : spherePiHomEquiv n Z (nullCube n Z) =
      OrdinaryHoCofiberKernel.nullHom (sphere n) Z := Subsingleton.elim _ _
  rw [hz, OrdinaryHoCofiberKernel.nullHom_postcomp_map] at h
  exact h

end PointedCGWH.SphereHom
