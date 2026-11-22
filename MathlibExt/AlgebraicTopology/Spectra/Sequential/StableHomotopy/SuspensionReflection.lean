/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionCoefficientGeometry
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionUnit

/-!
# Original circle reflection on the suspension image

Reversing the entire original native loop reverses the appended cube
coordinate. The actual circle-reflection coefficient therefore acts as
inversion on the image of the original suspension map. All original
homotopy groups and actual group maps are retained, including degree one
in the source. No action on an arbitrary unstable double suspension class
is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped MonoidalClosed CGWH.limits unitInterval

namespace PointedCGWH.SuspensionReflectionGeometry

open PointedCGWH.SuspensionCoefficientGeometry
open PointedCGWH.DoubleLoopInterchangeGeometry
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.CubeColimitGeometry

/-- The entire native loop reversal reflects exactly the newly appended original cube coordinate. -/
theorem nativeLoopCube_reflection (k : ℕ) (A : PointedCGWH.{u, v})
    (p : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj (PointedCGWH.loop.obj A).right)
      (underlyingBasepoint (PointedCGWH.loop.obj A))) :
    nativeLoopCube k A (cubeMap (k + 1) (loopReflection A) p) =
      GenLoop.symmAt (Fin.last (k + 1)) (nativeLoopCube k A p) := by
  apply GenLoop.ext
  intro q
  have hc := nativeLoopCube_apply k A (cubeMap (k + 1) (loopReflection A) p) q
  have hc' : (nativeLoopCube k A (cubeMap (k + 1) (loopReflection A) p)).1 q =
      PointedCGWH.loopLanding A
        ((loopReflection A).right (p.1 (fun i => q i.castSucc))) (q (Fin.last (k + 1))) := by
    exact hc.trans (congrArg
      (fun x => PointedCGWH.loopLanding A x (q (Fin.last (k + 1))))
      (cubeMap_apply (k + 1) (loopReflection A) p (fun i => q i.castSucc)))
  change (nativeLoopCube k A (cubeMap (k + 1) (loopReflection A) p)).1 q = _
  rw [hc', loopReflection_landing_evaluation]
  change _ = (nativeLoopCube k A p).1
    (fun i => if i = Fin.last (k + 1) then σ (q (Fin.last (k + 1))) else q i)
  rw [nativeLoopCube_apply]
  have hi : (fun i : Fin (k + 1) =>
      if i.castSucc = Fin.last (k + 1) then σ (q (Fin.last (k + 1))) else q i.castSucc) =
      (fun i => q i.castSucc) := by
    funext i
    rw [ite_eq_right (Fin.castSucc_ne_last i)]
  rw [hi, ite_eq_left rfl]

/-- The complete actual loop-reflection function inverts every original positive loop group. -/
theorem loopReflection_piNMap_eq_inv (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj A)) :
    piNMap (k + 1) (loopReflection A) a = a⁻¹ := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  apply (loopMulEquiv k A).injective
  have hm := piNMap_mk (k + 1) (loopReflection A) p
  have hi : (HomotopyGroup.mk (nativeLoopCube k A p))⁻¹ =
      HomotopyGroup.mk (GenLoop.symmAt (Fin.last (k + 1)) (nativeLoopCube k A p)) :=
    HomotopyGroup.inv_spec
  calc
    _ = loopMulEquiv k A (HomotopyGroup.mk (cubeMap (k + 1) (loopReflection A) p)) :=
      congrArg (loopMulEquiv k A) hm
    _ = HomotopyGroup.mk (nativeLoopCube k A (cubeMap (k + 1) (loopReflection A) p)) :=
      loopMulEquiv_mk k A (cubeMap (k + 1) (loopReflection A) p)
    _ = HomotopyGroup.mk
        (GenLoop.symmAt (Fin.last (k + 1)) (nativeLoopCube k A p)) :=
      congrArg HomotopyGroup.mk (nativeLoopCube_reflection k A p)
    _ = (HomotopyGroup.mk (nativeLoopCube k A p))⁻¹ := hi.symm
    _ = (loopMulEquiv k A (HomotopyGroup.mk p))⁻¹ :=
      congrArg Inv.inv (loopMulEquiv_mk k A p).symm
    _ = _ := (map_inv (loopMulEquiv k A) (HomotopyGroup.mk p)).symm

/-- The actual positive group map is the same complete original loop-reversal function. -/
theorem loopReflection_piNPositiveMap_eq_inv (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.loop.obj A)) :
    (piNPositiveMap k (loopReflection A)).hom a = a⁻¹ := by
  rw [piNPositiveMap_apply]
  exact loopReflection_piNMap_eq_inv k A a

/-- The original space suspension group map is induced by the actual circle adjunction unit. -/
def spaceSuspensionGroupMap (k : ℕ) : piNPositiveFunctor.{u, v} k ⟶
    tensorLeft PointedCGWH.sphereOne ⋙ piNPositiveFunctor (k + 1) :=
  Functor.whiskerRight (ihom.coev PointedCGWH.sphereOne) (piNPositiveFunctor k) ≫
    (Functor.associator (tensorLeft PointedCGWH.sphereOne) (ihom PointedCGWH.sphereOne)
      (piNPositiveFunctor k)).hom ≫
      Functor.whiskerLeft (tensorLeft PointedCGWH.sphereOne) (nativeLoopGroupShiftNatIso k).hom

/-- Its full component retains the actual original coevaluation and native group shift. -/
theorem spaceSuspensionGroupMap_app (k : ℕ) (A : PointedCGWH.{u, v}) :
    (spaceSuspensionGroupMap k).app A =
      piNPositiveMap k ((ihom.coev PointedCGWH.sphereOne).app A) ≫
        (nativeLoopGroupShiftNatIso k).hom.app (PointedCGWH.sphereOne ⊗ A) := by
  change _ ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- The actual coevaluation carries circle reflection to reversal of the newly based loop. -/
theorem coev_circleReflection (A : PointedCGWH.{u, v}) :
    (ihom.coev PointedCGWH.sphereOne).app A ≫
        PointedCGWH.loop.map (circleReflection ▷ A) =
      (ihom.coev PointedCGWH.sphereOne).app A ≫
        loopReflection (PointedCGWH.sphereOne ⊗ A) := by
  have hp := MonoidalClosed.coev_app_comp_pre_app (X := A) circleReflection
  have hr := congrArg
    (fun f => (ihom.coev PointedCGWH.sphereOne).app A ≫ f)
    (loopReflection_eq_pre (PointedCGWH.sphereOne ⊗ A))
  exact hp.symm.trans hr.symm

/-- Reflection inverts exactly the full original suspension image, in every positive degree. -/
theorem spaceSuspensionGroupMap_reflection (k : ℕ) (A : PointedCGWH.{u, v})
    (a : piN (k + 1) A) :
    (piNPositiveMap (k + 1) (circleReflection ▷ A)).hom
        (((spaceSuspensionGroupMap k).app A).hom a) =
      (((spaceSuspensionGroupMap k).app A).hom a)⁻¹ := by
  let B := PointedCGWH.sphereOne ⊗ A
  let c := piNPositiveMap k ((ihom.coev PointedCGWH.sphereOne).app A)
  let s := (nativeLoopGroupShiftNatIso k).hom.app B
  let m := piNPositiveMap k (PointedCGWH.loop.map (circleReflection ▷ A))
  let r := piNPositiveMap k (loopReflection B)
  let j := piNPositiveMap (k + 1) (circleReflection ▷ A)
  have he : ((spaceSuspensionGroupMap k).app A).hom a = s.hom (c.hom a) :=
    congrArg (fun f => f.hom a) (spaceSuspensionGroupMap_app k A)
  have hn := (nativeLoopGroupShiftNatIso k).hom.naturality (circleReflection ▷ A)
  have hn' : s.hom (m.hom (c.hom a)) = j.hom (s.hom (c.hom a)) :=
    congrArg (fun f => f.hom (c.hom a)) hn
  have hc := (piNPositiveFunctor k).congr_map (coev_circleReflection A)
  rw [(piNPositiveFunctor k).map_comp, (piNPositiveFunctor k).map_comp] at hc
  have hc' : m.hom (c.hom a) = r.hom (c.hom a) := congrArg (fun f => f.hom a) hc
  have hi : r.hom (c.hom a) = (c.hom a)⁻¹ :=
    loopReflection_piNPositiveMap_eq_inv k B (c.hom a)
  calc
    _ = j.hom (s.hom (c.hom a)) := congrArg j.hom he
    _ = s.hom (m.hom (c.hom a)) := hn'.symm
    _ = s.hom ((c.hom a)⁻¹) := congrArg s.hom (hc'.trans hi)
    _ = (s.hom (c.hom a))⁻¹ := map_inv s.hom (c.hom a)
    _ = _ := congrArg Inv.inv he.symm

end PointedCGWH.SuspensionReflectionGeometry
