/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LambdaConnectionScaling
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Native section-normalized reindexing of relative lambda-connections

Base change uses the actual scheme-module pullback. Its action on sections
is the unit of the native pullback/pushforward adjunction. Tensor and form
comparisons are normalized on every pulled section and universal differential.
The new connection is fixed by its action on those actual generators.

Source: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 4 and Proposition 4.1. Ordinary pullback and
tensor comparisons are completed Mathlib/AxiomMath source integration:
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
AlgebraicGeometry/Modules/Sheaf.lean (Joël Riou, Andrew Yang), Apache 2.0;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Topology/Sheaves/Modules/Differentials and DeRham/DeRhamComplexBaseChange,
Apache 2.0. No generic pullback or de Rham theorem is re-requested.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section


namespace MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open AlgebraicLambdaConnections RelativeDifferentialForms RelativeDeRhamDifferential
open SheafTensorSections LineBundleTaskContracts AlgebraicLineBundleFamilies

variable {Y Y' T T' : Scheme.{0}}

/-! The section pullback and the tensor-pullback comparison now live in `SheafTensorSections`;
their names stay available here. -/
export SheafTensorSections (pullSection pullSection_zero pullSection_add TensorPullbackComparison)

structure RelativeSquare (pi : Y ⟶ T) (pi' : Y' ⟶ T') where
  total : Y' ⟶ Y
  base : T' ⟶ T
  commutes : total ≫ pi = pi' ≫ base
  cartesian : _root_.CategoryTheory.IsPullback total pi' pi base

variable {pi : Y ⟶ T} {pi' : Y' ⟶ T'}

def RelativeSquare.parameter (Q : RelativeSquare pi pi') (lambda : Γ(T, ⊤)) : Γ(T', ⊤) :=
  Q.base.appTop.hom lambda

structure FormBaseChange (Q : RelativeSquare pi pi')
    (C : TensorPullbackComparison Q.total) (D : Differential pi) (D' : Differential pi') where
  one : (Scheme.Modules.pullback Q.total).obj (forms pi 1) ≅ forms pi' 1
  two : (Scheme.Modules.pullback Q.total).obj (forms pi 2) ≅ forms pi' 2
  universal : ∀ (U : Y.Opens) (a : Γ(Y, U)),
    (one.hom.val.app (op (Q.total ⁻¹ᵁ U))).hom
      (pullSection Q.total (forms pi 1) U ((d0 pi).d a)) =
      (d0 pi').d ((Q.total.app U).hom a)
  wedge : (Scheme.Modules.pullback Q.total).map (RelativeDifferentialForms.wedge pi) ≫
      two.hom = (C.iso (forms pi 1) (forms pi 1)).hom ≫
        tensorMap one.hom one.hom ≫ RelativeDifferentialForms.wedge pi'
  differential : ∀ (U : Y.Opens) (s : (forms pi 1).val.obj (op U)),
    D'.map (Q.total ⁻¹ᵁ U)
      ((one.hom.val.app (op (Q.total ⁻¹ᵁ U))).hom (pullSection Q.total (forms pi 1) U s)) =
      (two.hom.val.app (op (Q.total ⁻¹ᵁ U))).hom
        (pullSection Q.total (forms pi 2) U (D.map U s))

def connectionTensorComparison (Q : RelativeSquare pi pi')
    (C : TensorPullbackComparison Q.total) {D : Differential pi} {D' : Differential pi'}
    (F : FormBaseChange Q C D D') (E : Y.Modules) (E' : Y'.Modules)
    (b : (Scheme.Modules.pullback Q.total).obj E ≅ E') (p : Fin 2) :
    (Scheme.Modules.pullback Q.total).obj (moduleTensor Y E (forms pi (p.val + 1))) ≅
      moduleTensor Y' E' (forms pi' (p.val + 1)) :=
  (C.iso E (forms pi (p.val + 1))) ≪≫ GeometricHiggsFamilies.tensorIso b
    (Fin.cases F.one (fun i ↦ Fin.cases F.two (fun j ↦ Fin.elim0 j) i) p)

structure PulledConnection (Q : RelativeSquare pi pi')
    (C : TensorPullbackComparison Q.total) {D : Differential pi} {D' : Differential pi'}
    (F : FormBaseChange Q C D D') {lambda : Γ(T, ⊤)}
    (N : LambdaConnection pi lambda D) where
  connection : LambdaConnection pi' (Q.parameter lambda) D'
  rank_eq : connection.rank = N.rank
  bundleIso : (Scheme.Modules.pullback Q.total).obj N.object ≅ connection.object
  operator0 : ∀ (U : Y.Opens) (s : N.object.val.obj (op U)),
    connection.nabla0 (Q.total ⁻¹ᵁ U)
      ((bundleIso.hom.val.app (op (Q.total ⁻¹ᵁ U))).hom (pullSection Q.total N.object U s)) =
      (((connectionTensorComparison Q C F N.object connection.object bundleIso 0).hom).val.app
        (op (Q.total ⁻¹ᵁ U))).hom
        (pullSection Q.total (moduleTensor Y N.object (forms pi 1)) U (N.nabla0 U s))
  operator1 : ∀ (U : Y.Opens) (s : (moduleTensor Y N.object (forms pi 1)).val.obj (op U)),
    connection.nabla1 (Q.total ⁻¹ᵁ U)
      ((((connectionTensorComparison Q C F N.object connection.object bundleIso 0).hom).val.app
        (op (Q.total ⁻¹ᵁ U))).hom
          (pullSection Q.total (moduleTensor Y N.object (forms pi 1)) U s)) =
      (((connectionTensorComparison Q C F N.object connection.object bundleIso 1).hom).val.app
        (op (Q.total ⁻¹ᵁ U))).hom
        (pullSection Q.total (moduleTensor Y N.object (forms pi 2)) U (N.nabla1 U s))

end MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing
