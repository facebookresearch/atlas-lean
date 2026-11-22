/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopShift.AtPoints
import MathlibExt.CategoryTheory.Functor.Iteration

/-!
# Actual loop powers at every physical loop point

The original native loop functor is iterated as a whole functor. Positive
homotopy shifts use the actual original group comparisons at every step.
Their forgetful comparisons retain those same group maps.

At an arbitrary point of a positive loop power, the original all-point
connecting equivalence removes its outer loop. The remaining shifts are
the original positive group shifts. Both functions and all pointed-map
naturalities are retained, including degree zero and the first loop power.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CGWH.modelCategory

namespace PointedCGWH.LoopPowerAtPoints

open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.NativeAllPointLoopShiftGeometry

/-- The complete original native loop is iterated without changing any object or map. -/
abbrev power (n : ℕ) : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  Functor.Iteration.iterate PointedCGWH.loop n

/-- Every successor map is the actual original native loop image of the previous whole map. -/
theorem power_succ_map (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (power (n + 1)).map f = PointedCGWH.loop.map ((power n).map f) := rfl

/-- The positive group functor forgets to its original literal-degree Type functor. -/
def positiveForgetComparison (k : ℕ) :
    piNPositiveFunctor.{u, v} k ⋙ forget GrpCat ≅ piNFunctor (k + 1) :=
  NatIso.ofComponents (fun _X =>
    { hom := ↾id
      inv := ↾id
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun f => by
    apply ConcreteCategory.hom_ext
    intro q
    exact piNPositiveMap_apply k f q)

/-- Every genuine positive group shift retains all original native loop group maps. -/
def positivePowerComparison : ∀ n k : ℕ,
    power.{u, v} n ⋙ piNPositiveFunctor k ≅ piNPositiveFunctor (k + n) :=
  Nat.rec (fun k => (piNPositiveFunctor k).leftUnitor)
    (fun n previous k =>
      Functor.associator (power n) PointedCGWH.loop (piNPositiveFunctor k) ≪≫
        Functor.isoWhiskerLeft (power n) (nativeLoopGroupShiftNatIso k) ≪≫
        previous (k + 1) ≪≫
        eqToIso (congrArg (fun j : ℕ => piNPositiveFunctor.{u, v} j)
          ((Nat.add_right_comm k 1 n).trans (Nat.add_assoc k n 1))))

/-- Every full original pointed input map is natural for the genuine forward group comparison. -/
theorem positivePowerComparison_hom_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (piNPositiveFunctor k).map ((power n).map f) ≫
        (positivePowerComparison n k).hom.app Y =
      (positivePowerComparison n k).hom.app X ≫ (piNPositiveFunctor (k + n)).map f :=
  (positivePowerComparison n k).hom.naturality f

/-- The same complete original pointed map is natural for the genuine inverse group comparison. -/
theorem positivePowerComparison_inv_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (piNPositiveFunctor (k + n)).map f ≫ (positivePowerComparison n k).inv.app Y =
      (positivePowerComparison n k).inv.app X ≫ (piNPositiveFunctor k).map ((power n).map f) :=
  (positivePowerComparison n k).inv.naturality f

/-- The input forgetful comparison keeps the original positive group at the actual loop power. -/
def positiveSourceForgetComparison (n k : ℕ) :
    (power.{u, v} n ⋙ piNPositiveFunctor k) ⋙ forget GrpCat ≅
      power n ⋙ piNFunctor (k + 1) :=
  Functor.associator (power n) (piNPositiveFunctor k) (forget GrpCat) ≪≫
    Functor.isoWhiskerLeft (power n) (positiveForgetComparison k)

/-- Both underlying Type shift maps are built from those same original genuine group maps. -/
def positiveTypeComparison (n k : ℕ) :
    power.{u, v} n ⋙ piNFunctor (k + 1) ≅ piNFunctor (k + n + 1) :=
  (positiveSourceForgetComparison n k).symm ≪≫
    Functor.isoWhiskerRight (positivePowerComparison n k) (forget GrpCat) ≪≫
      positiveForgetComparison (k + n)

/-- Every entire forward Type comparison retains the actual forward original group homomorphism. -/
theorem positiveTypeComparison_hom_app (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (positiveTypeComparison n k).hom.app X =
      (positiveSourceForgetComparison n k).inv.app X ≫
        (forget GrpCat).map ((positivePowerComparison n k).hom.app X) ≫
          (positiveForgetComparison (k + n)).hom.app X := rfl

/-- Every entire inverse Type comparison retains the same actual inverse group homomorphism. -/
theorem positiveTypeComparison_inv_app (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (positiveTypeComparison n k).inv.app X =
      (positiveForgetComparison (k + n)).inv.app X ≫
        (forget GrpCat).map ((positivePowerComparison n k).inv.app X) ≫
          (positiveSourceForgetComparison n k).hom.app X := by
  simp only [positiveTypeComparison, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.assoc]

/-- The arbitrary-point map is the actual iterated native loop map with its actual image point. -/
def pointMap (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : ((power (n + 1)).obj X).right) (q : ((power (n + 1)).obj Y).right)
    (h : ((power (n + 1)).map f).right p = q) :
    pointedAt ((power (n + 1)).obj X).right p ⟶
      pointedAt ((power (n + 1)).obj Y).right q :=
  loopAtMap ((power n).map f) p q h

/-- Repointing keeps the original whole native loop-power map. -/
theorem pointMap_right (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : ((power (n + 1)).obj X).right) (q : ((power (n + 1)).obj Y).right)
    (h : ((power (n + 1)).map f).right p = q) :
    (pointMap n f p q h).right = ((power (n + 1)).map f).right := rfl

/-- Every actual positive loop-power point has both all-degree original homotopy shift maps. -/
def allPointComparison (n k : ℕ) (X : PointedCGWH.{u, v})
    (p : ((power (n + 1)).obj X).right) :
    (piNFunctor k).obj (pointedAt ((power (n + 1)).obj X).right p) ≅
      (piNFunctor (k + n + 1)).obj X :=
  loopAtShiftIso ((power n).obj X) p k ≪≫ (positiveTypeComparison n k).app X

/-- The forward function uses the given point's original connecting map and original group maps. -/
theorem allPointComparison_hom_app (n k : ℕ) (X : PointedCGWH.{u, v})
    (p : ((power (n + 1)).obj X).right)
    (a : (piNFunctor k).obj (pointedAt ((power (n + 1)).obj X).right p)) :
    (allPointComparison n k X p).hom a =
      (positiveTypeComparison n k).hom.app X ((loopAtShiftIso ((power n).obj X) p k).hom a) :=
  rfl

/-- The inverse function uses the same original inverse group maps and inverse connecting map. -/
theorem allPointComparison_inv_app (n k : ℕ) (X : PointedCGWH.{u, v})
    (p : ((power (n + 1)).obj X).right) (a : (piNFunctor (k + n + 1)).obj X) :
    (allPointComparison n k X p).inv a =
      (loopAtShiftIso ((power n).obj X) p k).inv ((positiveTypeComparison n k).inv.app X a) :=
  rfl

/-- The complete all-point forward comparison is natural on every actual pointed input map. -/
theorem allPointComparison_hom_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : ((power (n + 1)).obj X).right) (q : ((power (n + 1)).obj Y).right)
    (h : ((power (n + 1)).map f).right p = q) :
    (piNFunctor k).map (pointMap n f p q h) ≫ (allPointComparison n k Y q).hom =
      (allPointComparison n k X p).hom ≫ (piNFunctor (k + n + 1)).map f := by
  have h₁ : CommSq ((piNFunctor k).map (pointMap n f p q h))
      (loopAtShiftIso ((power n).obj X) p k).hom
      (loopAtShiftIso ((power n).obj Y) q k).hom
      ((piNFunctor (k + 1)).map ((power n).map f)) :=
    ⟨loopAtShiftIso_hom_naturality ((power n).map f) p q h k⟩
  have h₂ : CommSq ((piNFunctor (k + 1)).map ((power n).map f))
      ((positiveTypeComparison n k).hom.app X) ((positiveTypeComparison n k).hom.app Y)
      ((piNFunctor (k + n + 1)).map f) :=
    ⟨(positiveTypeComparison n k).hom.naturality f⟩
  exact (h₁.vert_comp h₂).w

/-- Both complete inverse maps preserve the same original input arrow and its actual image point. -/
theorem allPointComparison_inv_naturality (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : ((power (n + 1)).obj X).right) (q : ((power (n + 1)).obj Y).right)
    (h : ((power (n + 1)).map f).right p = q) :
    (piNFunctor (k + n + 1)).map f ≫ (allPointComparison n k Y q).inv =
      (allPointComparison n k X p).inv ≫ (piNFunctor k).map (pointMap n f p q h) :=
  (CommSq.vert_inv (g := allPointComparison n k X p) (h := allPointComparison n k Y q)
    ⟨allPointComparison_hom_naturality n k f p q h⟩).w

end PointedCGWH.LoopPowerAtPoints
