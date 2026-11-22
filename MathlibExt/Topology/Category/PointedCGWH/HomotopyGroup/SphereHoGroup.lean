/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereGroupHom
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereNullHom

/-!
# Original sphere-Hom multiplication and cube representatives

The actual all-degree sphere correspondence transports the existing cube
concatenation to the same localized Hom set. Its representative laws use
original transAt and symmAt, retaining the degree-one fundamental-group
convention. Null classes, group maps and target naturality keep the actual
sphere source and localized pointed target.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory
namespace PointedCGWH.SphereHom
private abbrev H := toHomotopyCategory PointedCGWH.{u, v}

/-- The original positive cube concatenation acts on the same actual represented sphere maps. -/
def sphereHomMul (k : ℕ) (X : PointedCGWH.{u, v})
    (a b : H.obj (sphere (k + 1)) ⟶ H.obj X) :
    H.obj (sphere (k + 1)) ⟶ H.obj X :=
  spherePiHomEquiv (k + 1) X
    ((spherePiHomEquiv (k + 1) X).symm a * (spherePiHomEquiv (k + 1) X).symm b)

/-- Multiplication uses the original cube transAt and loop concatenation. -/
theorem sphereHomMul_representatives (k : ℕ) (X : PointedCGWH.{u, v})
    (a b : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)) (i : Fin (k + 1)) :
    sphereHomMul k X
      (spherePiHomEquiv (k + 1) X (HomotopyGroup.mk a))
      (spherePiHomEquiv (k + 1) X (HomotopyGroup.mk b)) =
      spherePiHomEquiv (k + 1) X (HomotopyGroup.mk (GenLoop.transAt i b a)) := by
  rw [sphereHomMul, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg (spherePiHomEquiv (k + 1) X) (HomotopyGroup.mul_spec (i := i))

/-- The group on the actual sphere Hom set is induced by the original cube concatenation. -/
@[instance_reducible]
def sphereHomGroup (k : ℕ) (X : PointedCGWH.{u, v}) :
    Group (H.obj (sphere (k + 1)) ⟶ H.obj X) :=
  (spherePiHomEquiv (k + 1) X).symm.group

/-- The represented Hom multiplication is precisely the original cube-concatenation operation. -/
theorem sphereHomGroup_mul (k : ℕ) (X : PointedCGWH.{u, v})
    (a b : H.obj (sphere (k + 1)) ⟶ H.obj X) :
    @Mul.mul _ (sphereHomGroup k X).toMul a b = sphereHomMul k X a b := rfl

/-- Both actual sphere-Hom functions form the multiplicative original comparison. -/
def spherePiHomMulEquiv (k : ℕ) (X : PointedCGWH.{u, v}) :
    letI := sphereHomGroup k X
    PointedCGWH.piN (k + 1) X ≃* (H.obj (sphere (k + 1)) ⟶ H.obj X) :=
  letI := sphereHomGroup k X
  (spherePiHomEquiv (k + 1) X).symm.mulEquiv.symm

/-- Every original target map preserves the same sphere-Hom multiplication. -/
theorem sphereHomMul_naturality (k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (a b : H.obj (sphere (k + 1)) ⟶ H.obj X) :
    sphereHomMul k X a b ≫ H.map f =
      sphereHomMul k Y (a ≫ H.map f) (b ≫ H.map f) := by
  let x := (spherePiHomEquiv (k + 1) X).symm a
  let y := (spherePiHomEquiv (k + 1) X).symm b
  have hmap := (PointedCGWH.piNPositiveMap k f).hom.map_mul x y
  change spherePiHomEquiv (k + 1) X (x * y) ≫ H.map f = _
  rw [← spherePiHomEquiv_naturality]
  have hinv (z : H.obj (sphere (k + 1)) ⟶ H.obj X) :
      (spherePiHomEquiv (k + 1) Y).symm (z ≫ H.map f) =
        PointedCGWH.piNMap (k + 1) f ((spherePiHomEquiv (k + 1) X).symm z) := by
    apply (spherePiHomEquiv (k + 1) Y).injective
    rw [Equiv.apply_symm_apply, spherePiHomEquiv_naturality, Equiv.apply_symm_apply]
  rw [sphereHomMul, hinv a, hinv b]
  have hm : PointedCGWH.piNMap (k + 1) f (x * y) =
      PointedCGWH.piNMap (k + 1) f x * PointedCGWH.piNMap (k + 1) f y := by
    exact (PointedCGWH.piNPositiveMap_apply k f (x * y)).symm.trans
      (hmap.trans (congrArg₂ (fun a b => a * b)
        (PointedCGWH.piNPositiveMap_apply k f x)
        (PointedCGWH.piNPositiveMap_apply k f y)))
  exact congrArg (spherePiHomEquiv (k + 1) Y) hm

/-- The identity in the represented sphere group is the same original null map. -/
theorem sphereHomGroup_one (k : ℕ) (X : PointedCGWH.{u, v}) :
    @One.one _ (sphereHomGroup k X).toOne =
      OrdinaryHoCofiberKernel.nullHom (sphere (k + 1)) X := by
  change spherePiHomEquiv (k + 1) X (1 : PointedCGWH.piN (k + 1) X) = _
  exact (congrArg (spherePiHomEquiv (k + 1) X) (nullCube_eq_one k X).symm).trans
    (spherePiHomEquiv_nullCube (k + 1) X)

/-- Degree one retains the original fundamental-group multiplication convention. -/
def sphereOneHomFundamentalGroup (X : PointedCGWH.{u, v}) :
    letI := sphereHomGroup 0 X
    (H.obj (sphere 1) ⟶ H.obj X) ≃*
      FundamentalGroup (CGWH.cgwhToTop.obj X.right) (PointedCGWH.underlyingBasepoint X) :=
  letI := sphereHomGroup 0 X
  (spherePiHomMulEquiv 0 X).symm.trans (PointedCGWH.piNOneMulEquivFundamentalGroup X)

/-- The inverse is represented by the original cube-coordinate loop reversal. -/
theorem sphereHomGroup_inv_representative (k : ℕ) (X : PointedCGWH.{u, v})
    (a : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)) (i : Fin (k + 1)) :
    @Inv.inv _ (sphereHomGroup k X).toInv
        (spherePiHomEquiv (k + 1) X (HomotopyGroup.mk a)) =
      spherePiHomEquiv (k + 1) X (HomotopyGroup.mk (GenLoop.symmAt i a)) := by
  change spherePiHomEquiv (k + 1) X
    (((spherePiHomEquiv (k + 1) X).symm
      (spherePiHomEquiv (k + 1) X (HomotopyGroup.mk a)))⁻¹) = _
  rw [Equiv.symm_apply_apply]
  exact congrArg (spherePiHomEquiv (k + 1) X) (HomotopyGroup.inv_spec (i := i))

end PointedCGWH.SphereHom
