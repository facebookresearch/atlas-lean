/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicLambdaConnections

/-!
# Scaling actual relative lambda-connections

The scalar is a section of the base structure sheaf. Both connection
operators are multiplied by its actual pullback; the parameter becomes
the product of the two base sections. The relative differential of the
scalar is zero. No analytic or algebraic scaling operator is supplied.

Source: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 4, printed pages 18–19.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section


namespace MathlibExt.AlgebraicGeometry.LambdaConnectionScaling

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open RelativeDifferentialForms RelativeDeRhamDifferential SheafTensorSections
open AlgebraicLambdaConnections LineBundleTaskContracts AlgebraicLineBundleFamilies

variable {Y T : Scheme.{0}} {pi : Y ⟶ T} {lambda : Γ(T, ⊤)} {D : Differential pi}

@[simp] theorem lambdaOnOpen_mul (a b : Γ(T, ⊤)) (U : Y.Opens) :
    lambdaOnOpen pi (a * b) U = lambdaOnOpen pi a U * lambdaOnOpen pi b U := map_mul _ _ _

@[simp] theorem lambdaOnOpen_one (U : Y.Opens) : lambdaOnOpen pi 1 U = 1 := map_one _

theorem lambdaOnOpen_restriction (a : Γ(T, ⊤)) (U V : Y.Opens) (h : V ≤ U) :
    (Y.presheaf.map (homOfLE h).op).hom (lambdaOnOpen pi a U) = lambdaOnOpen pi a V := by
  dsimp [lambdaOnOpen, Scheme.Hom.appLE]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

def scale (a : Γ(T, ⊤)) (N : LambdaConnection pi lambda D) :
    LambdaConnection pi (a * lambda) D where
  rank := N.rank
  object := N.object
  bundle := N.bundle
  nabla0 U := (lambdaOnOpen pi a U) • N.nabla0 U
  restriction0 U V h s := by
    change lambdaOnOpen pi a V • N.nabla0 V ((N.object.val.map (homOfLE h).op).hom s) =
      ((moduleTensor Y N.object (forms pi 1)).val.map (homOfLE h).op).hom
        (lambdaOnOpen pi a U • N.nabla0 U s)
    rw [N.restriction0, PresheafOfModules.map_smul]
    exact congrArg
      (fun b : Γ(Y, V) ↦ b •
        (((moduleTensor Y N.object (forms pi 1)).val.map (homOfLE h).op).hom (N.nabla0 U s)))
      (lambdaOnOpen_restriction a U V h).symm
  leibniz U b s := by
    change lambdaOnOpen pi a U • N.nabla0 U (b • s) = _
    rw [N.leibniz, smul_add, lambdaOnOpen_mul, mul_smul]
    congr 1
    exact smul_comm _ _ _
  nabla1 U := (lambdaOnOpen pi a U) • N.nabla1 U
  restriction1 U V h s := by
    change lambdaOnOpen pi a V •
      N.nabla1 V (((moduleTensor Y N.object (forms pi 1)).val.map (homOfLE h).op).hom s) =
      ((moduleTensor Y N.object (forms pi 2)).val.map (homOfLE h).op).hom
        (lambdaOnOpen pi a U • N.nabla1 U s)
    rw [N.restriction1, PresheafOfModules.map_smul]
    exact congrArg
      (fun b : Γ(Y, V) ↦ b •
        (((moduleTensor Y N.object (forms pi 2)).val.map (homOfLE h).op).hom (N.nabla1 U s)))
      (lambdaOnOpen_restriction a U V h).symm
  extension U s omega := by
    change lambdaOnOpen pi a U •
      N.nabla1 U (tensorSection Y N.object (forms pi 1) U s omega) =
      ((bundleWedge pi N.object).val.app (op U)).hom
        (tensorSection Y (moduleTensor Y N.object (forms pi 1)) (forms pi 1) U
          (lambdaOnOpen pi a U • N.nabla0 U s) omega) +
      lambdaOnOpen pi (a * lambda) U • tensorSection Y N.object (forms pi 2) U s (D.map U omega)
    rw [N.extension, smul_add, lambdaOnOpen_mul, mul_smul, tensorSection_smul_left, map_smul]
  leibniz1 U b s := by
    change lambdaOnOpen pi a U • N.nabla1 U (b • s) = _
    rw [N.leibniz1, smul_add, lambdaOnOpen_mul, mul_smul]
    congr 1
    exact smul_comm _ _ _
  baseLinear1 V U h b s := by
    change lambdaOnOpen pi a U • N.nabla1 U ((pi.appLE V U h).hom b • s) = _
    rw [N.baseLinear1]
    exact smul_comm _ _ _
  integrable U s := by
    change lambdaOnOpen pi a U • N.nabla1 U (lambdaOnOpen pi a U • N.nabla0 U s) = 0
    have hb : N.nabla1 U (lambdaOnOpen pi a U • N.nabla0 U s) =
        lambdaOnOpen pi a U • N.nabla1 U (N.nabla0 U s) :=
      N.baseLinear1 ⊤ U (by intro x hx; trivial) a (N.nabla0 U s)
    rw [hb, N.integrable, smul_zero, smul_zero]

@[simp] theorem scale_nabla0 (a : Γ(T, ⊤)) (N : LambdaConnection pi lambda D)
    (U : Y.Opens) (s : N.object.val.obj (op U)) :
    (scale a N).nabla0 U s = lambdaOnOpen pi a U • N.nabla0 U s := rfl

@[simp] theorem scale_nabla1 (a : Γ(T, ⊤)) (N : LambdaConnection pi lambda D)
    (U : Y.Opens) (s : (moduleTensor Y N.object (forms pi 1)).val.obj (op U)) :
    (scale a N).nabla1 U s = lambdaOnOpen pi a U • N.nabla1 U s := rfl

def scaleFunctor (a : Γ(T, ⊤)) :
    LambdaConnection pi lambda D ⥤ LambdaConnection pi (a * lambda) D where
  obj N := scale a N
  map f :=
    { map := f.map
      connection U s := by
        change ((tensorMap f.map (𝟙 (forms pi 1))).val.app (op U)).hom
          (lambdaOnOpen pi a U • _) = lambdaOnOpen pi a U • _
        rw [map_smul, f.connection]
        rfl }
  map_id _ := by apply LambdaConnection.Hom.ext; rfl
  map_comp _ _ := by apply LambdaConnection.Hom.ext; rfl

end MathlibExt.AlgebraicGeometry.LambdaConnectionScaling
