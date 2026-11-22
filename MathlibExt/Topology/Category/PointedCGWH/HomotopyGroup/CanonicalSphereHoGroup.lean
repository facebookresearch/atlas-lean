/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SphereHoGroup

/-!
# Native sphere-power Hom groups

The literal native finite one-sphere tensor powers carry their original
represented Hom groups through both actual sphere-source isomorphism
functions. Cube concatenation, reversal, null identity, degree-one
multiplication, and full target postcomposition retain those exact maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory
namespace PointedCGWH.SphereHom
private abbrev H := toHomotopyCategory PointedCGWH.{u, v}
/-- The literal original native finite one-sphere tensor power. -/
abbrev canonicalSphere (n : ℕ) : PointedCGWH.{u, v} :=
  TensorPower.tensorPowObj PointedCGWH.sphereOne n

/-- The canonical source change retains both actual original sphere-isomorphism maps. -/
def canonicalHomEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    (H.obj (sphere n) ⟶ H.obj X) ≃ (H.obj (canonicalSphere n) ⟶ H.obj X) :=
  (H.mapIso (sphereCanonicalIso n)).homCongr (Iso.refl _)

/-- The forward Hom function precomposes with the actual inverse sphere-source map. -/
theorem canonicalHomEquiv_apply (n : ℕ) (X : PointedCGWH.{u, v})
    (f : H.obj (sphere n) ⟶ H.obj X) :
    canonicalHomEquiv n X f = H.map (sphereCanonicalIso n).inv ≫ f := by
  simp [canonicalHomEquiv, Iso.homCongr]

/-- The inverse Hom function retains the original forward sphere-source map. -/
theorem canonicalHomEquiv_symm_apply (n : ℕ) (X : PointedCGWH.{u, v})
    (f : H.obj (canonicalSphere n) ⟶ H.obj X) :
    (canonicalHomEquiv n X).symm f = H.map (sphereCanonicalIso n).hom ≫ f := by
  simp [canonicalHomEquiv, Iso.homCongr]

/-- The same native cube concatenation gives a group on literal canonical-power Hom. -/
@[instance_reducible]
def canonicalSphereHomGroup (k : ℕ) (X : PointedCGWH.{u, v}) :
    Group (H.obj (canonicalSphere (k + 1)) ⟶ H.obj X) :=
  (canonicalSpherePiHomEquiv (k + 1) X).symm.group

/-- Canonical sphere classes preserve the original positive homotopy multiplication. -/
def canonicalSpherePiHomMulEquiv (k : ℕ) (X : PointedCGWH.{u, v}) :
    letI := canonicalSphereHomGroup k X
    PointedCGWH.piN (k + 1) X ≃* (H.obj (canonicalSphere (k + 1)) ⟶ H.obj X) :=
  letI := canonicalSphereHomGroup k X
  (canonicalSpherePiHomEquiv (k + 1) X).symm.mulEquiv.symm

/-- Canonical-power multiplication uses the original full cube concatenation. -/
theorem canonicalSphereHom_mul_representatives (k : ℕ) (X : PointedCGWH.{u, v})
    (a b : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)) (i : Fin (k + 1)) :
    @Mul.mul _ (canonicalSphereHomGroup k X).toMul
      (canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk a))
      (canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk b)) =
      canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk (GenLoop.transAt i b a)) := by
  change canonicalSpherePiHomEquiv (k + 1) X
    ((canonicalSpherePiHomEquiv (k + 1) X).symm
      (canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk a)) *
     (canonicalSpherePiHomEquiv (k + 1) X).symm
      (canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk b))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg (canonicalSpherePiHomEquiv (k + 1) X) (HomotopyGroup.mul_spec (i := i))

/-- Canonical-power inversion uses the original cube-coordinate loop reversal. -/
theorem canonicalSphereHom_inv_representative (k : ℕ) (X : PointedCGWH.{u, v})
    (a : GenLoop (Fin (k + 1)) (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)) (i : Fin (k + 1)) :
    @Inv.inv _ (canonicalSphereHomGroup k X).toInv
      (canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk a)) =
      canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk (GenLoop.symmAt i a)) := by
  change canonicalSpherePiHomEquiv (k + 1) X
    (((canonicalSpherePiHomEquiv (k + 1) X).symm
      (canonicalSpherePiHomEquiv (k + 1) X (HomotopyGroup.mk a)))⁻¹) = _
  rw [Equiv.symm_apply_apply]
  exact congrArg (canonicalSpherePiHomEquiv (k + 1) X) (HomotopyGroup.inv_spec (i := i))

/-- The canonical forward class is the original sphere class with its actual source inverse. -/
theorem canonicalSpherePiHomEquiv_apply (n : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN n X) :
    canonicalSpherePiHomEquiv n X x = canonicalHomEquiv n X (spherePiHomEquiv n X x) := rfl

/-- Actual canonical sphere classes retain every original target-map square. -/
theorem canonicalSpherePiHomEquiv_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (x : PointedCGWH.piN n X) :
    canonicalSpherePiHomEquiv n Y (PointedCGWH.piNMap n f x) =
      canonicalSpherePiHomEquiv n X x ≫ H.map f := by
  rw [canonicalSpherePiHomEquiv_apply, canonicalSpherePiHomEquiv_apply,
    spherePiHomEquiv_naturality, canonicalHomEquiv_apply, canonicalHomEquiv_apply,
    Category.assoc]

/-- The complete source-isomorphism correspondence is multiplicative on the canonical Hom set. -/
def canonicalHomMulEquiv (k : ℕ) (X : PointedCGWH.{u, v}) :
    letI := sphereHomGroup k X
    letI := canonicalSphereHomGroup k X
    (H.obj (sphere (k + 1)) ⟶ H.obj X) ≃*
      (H.obj (canonicalSphere (k + 1)) ⟶ H.obj X) :=
  letI := sphereHomGroup k X
  letI := canonicalSphereHomGroup k X
  (spherePiHomMulEquiv k X).symm.trans (canonicalSpherePiHomMulEquiv k X)

/-- The multiplicative source-change function retains the original inverse source map. -/
theorem canonicalHomMulEquiv_apply (k : ℕ) (X : PointedCGWH.{u, v})
    (f : H.obj (sphere (k + 1)) ⟶ H.obj X) :
    canonicalHomMulEquiv k X f = H.map (sphereCanonicalIso (k + 1)).inv ≫ f := by
  change canonicalSpherePiHomEquiv (k + 1) X ((spherePiHomEquiv (k + 1) X).symm f) = _
  rw [canonicalSpherePiHomEquiv_apply, Equiv.apply_symm_apply, canonicalHomEquiv_apply]

/-- Its multiplicative inverse retains the actual forward source map. -/
theorem canonicalHomMulEquiv_symm_apply (k : ℕ) (X : PointedCGWH.{u, v})
    (f : H.obj (canonicalSphere (k + 1)) ⟶ H.obj X) :
    letI := sphereHomGroup k X
    letI := canonicalSphereHomGroup k X
    (canonicalHomMulEquiv k X).symm f = H.map (sphereCanonicalIso (k + 1)).hom ≫ f := by
  let := sphereHomGroup k X
  let := canonicalSphereHomGroup k X
  apply (canonicalHomMulEquiv k X).injective
  have hleft := (canonicalHomMulEquiv k X).apply_symm_apply f
  have hright := canonicalHomMulEquiv_apply k X
    (H.map (sphereCanonicalIso (k + 1)).hom ≫ f)
  have hi : H.map (sphereCanonicalIso (k + 1)).inv ≫
      (H.map (sphereCanonicalIso (k + 1)).hom ≫ f) = f := by
    rw [← Category.assoc, ← H.map_comp, Iso.inv_hom_id, H.map_id, Category.id_comp]
  exact hleft.trans (hright.trans hi).symm

/-- The canonical sphere group identity is the original ordinary null map. -/
theorem canonicalSphereHomGroup_one (k : ℕ) (X : PointedCGWH.{u, v}) :
    @One.one _ (canonicalSphereHomGroup k X).toOne =
      OrdinaryHoCofiberKernel.nullHom (canonicalSphere (k + 1)) X := by
  change canonicalSpherePiHomEquiv (k + 1) X (1 : PointedCGWH.piN (k + 1) X) = _
  have h := (congrArg (spherePiHomEquiv (k + 1) X) (nullCube_eq_one k X).symm).trans
    (spherePiHomEquiv_nullCube (k + 1) X)
  rw [canonicalSpherePiHomEquiv_apply, canonicalHomEquiv_apply]
  exact (congrArg (fun q => H.map (sphereCanonicalIso (k + 1)).inv ≫ q) h).trans
    (OrdinaryHoCofiberKernel.precomp_nullHom (sphereCanonicalIso (k + 1)).inv)

/-- Degree one on literal native powers uses the original fundamental-group convention. -/
def canonicalSphereOneHomFundamentalGroup (X : PointedCGWH.{u, v}) :
    letI := canonicalSphereHomGroup 0 X
    (H.obj (canonicalSphere 1) ⟶ H.obj X) ≃*
      FundamentalGroup (CGWH.cgwhToTop.obj X.right) (PointedCGWH.underlyingBasepoint X) :=
  letI := canonicalSphereHomGroup 0 X
  (canonicalSpherePiHomMulEquiv 0 X).symm.trans (PointedCGWH.piNOneMulEquivFundamentalGroup X)

/-- The full target arrow induces the original canonical sphere-Hom group homomorphism. -/
def canonicalSphereHomPostcompose (k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    letI := canonicalSphereHomGroup k X
    letI := canonicalSphereHomGroup k Y
    (H.obj (canonicalSphere (k + 1)) ⟶ H.obj X) →*
      (H.obj (canonicalSphere (k + 1)) ⟶ H.obj Y) :=
  letI := canonicalSphereHomGroup k X
  letI := canonicalSphereHomGroup k Y
  (canonicalSpherePiHomMulEquiv k Y).toMonoidHom.comp
    ((PointedCGWH.piNPositiveMap k f).hom.comp
      (canonicalSpherePiHomMulEquiv k X).symm.toMonoidHom)

/-- Its entire function is the same original localized target postcomposition. -/
theorem canonicalSphereHomPostcompose_apply (k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (a : H.obj (canonicalSphere (k + 1)) ⟶ H.obj X) :
    canonicalSphereHomPostcompose k f a = a ≫ H.map f := by
  change canonicalSpherePiHomEquiv (k + 1) Y
    ((PointedCGWH.piNPositiveMap k f).hom ((canonicalSpherePiHomEquiv (k + 1) X).symm a)) = _
  rw [PointedCGWH.piNPositiveMap_apply, canonicalSpherePiHomEquiv_naturality,
    Equiv.apply_symm_apply]

end PointedCGWH.SphereHom
