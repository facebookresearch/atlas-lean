/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogarithmicMapDerivations
public import MathlibExt.AlgebraicGeometry.RelativeContactGeometry
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicTopology.CechNerve

/-!
# Native affine charts of a map to an expanded target

All local algebras are actual affine schemes with etale arrows into the
given family. The coefficient map is scalar extension of I along the
literal source/base algebra map. Boundary coordinates generate the
actual inverse-image ideal. Node coordinates give the actual smooth
chart from A[w0,w1]/(w0*w1-t).
Source: Jun Li arXiv:math/0110113v1, Sections1.1--1.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiAffineMapCharts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open RelativeContactGeometry LogarithmicMapDerivations
open scoped TensorProduct Simplicial

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {C X : Scheme.{0}} (p : C ⟶ Spec (.of A)) (q : X ⟶ Spec (.of k))
  (f : C ⟶ X)

structure Chart where
  base : Type
  source : Type
  target : Type
  [baseRing : CommRing base]
  [sourceRing : CommRing source]
  [targetRing : CommRing target]
  [baseAlgebra : Algebra A base]
  [sourceAlgebra : Algebra A source]
  [targetAlgebra : Algebra k target]
  [sourceKAlgebra : Algebra k source]
  [baseSource : Algebra base source]
  [targetSource : Algebra target source]
  [baseSourceTower : IsScalarTower A base source]
  [sourceKTower : IsScalarTower k A source]
  [mapKTower : IsScalarTower k target source]
  sourceMap : Spec (.of source) ⟶ C
  targetMap : Spec (.of target) ⟶ X
  [baseEtale : Etale (Spec.algebraMap A base)]
  [sourceEtale : Etale sourceMap]
  [targetEtale : Etale targetMap]
  sourceOver : sourceMap ≫ p = Spec.algebraMap A source
  targetOver : targetMap ≫ q = Spec.algebraMap k target
  mapSquare : Spec.algebraMap target source ≫ targetMap = sourceMap ≫ f

attribute [instance] Chart.baseRing Chart.sourceRing Chart.targetRing
  Chart.baseAlgebra Chart.sourceAlgebra Chart.targetAlgebra Chart.sourceKAlgebra Chart.baseSource
  Chart.targetSource Chart.baseSourceTower Chart.sourceKTower Chart.mapKTower
  Chart.baseEtale Chart.sourceEtale Chart.targetEtale

variable {p q f} (a : Chart p q f)

abbrev sourceObject : C.Etale := Scheme.Etale.mk a.sourceMap

variable (I : Type) [AddCommGroup I] [Module A I]

abbrev sourceCoefficient := a.source ⊗[A] I
abbrev baseCoefficient := a.base ⊗[A] I

def baseSourceLinear : a.base →ₗ[A] a.source where
  toFun := algebraMap a.base a.source
  map_add' := map_add _
  map_smul' r x := by
    simp only [Algebra.smul_def, map_mul]
    rw [← IsScalarTower.algebraMap_apply A a.base a.source]
    rfl

def baseCoefficientMap : baseCoefficient a I →ₗ[A] sourceCoefficient a I :=
  TensorProduct.map (baseSourceLinear a) LinearMap.id

structure Ordinary (m : ℕ) where
  targetBase : Type
  [targetBaseRing : CommRing targetBase]
  [targetBaseAlgebra : Algebra targetBase a.target]
  targetProjection : X ⟶ Spec (.of targetBase)
  projection : a.targetMap ≫ targetProjection = Spec.algebraMap targetBase a.target
  smooth : Smooth (Spec.algebraMap targetBase a.target)
  parameter : Fin m → targetBase

attribute [instance] Ordinary.targetBaseRing Ordinary.targetBaseAlgebra

def Ordinary.targetParameter {m : ℕ} (o : Ordinary a m) (i : Fin m) : a.target :=
  algebraMap o.targetBase a.target (o.parameter i)

structure Boundary (J : X.IdealSheafData) (m : ℕ) where
  ordinary : Ordinary a m
  coordinate : a.target
  ideal : (J.comap a.targetMap).ideal ⟨⊤, isAffineOpen_top _⟩ =
    Ideal.span {((Scheme.ΓSpecIso (.of a.target)).inv.hom coordinate)}

structure Node (m : ℕ) where
  ordinaryBase : Type
  [ordinaryBaseRing : CommRing ordinaryBase]
  [ordinaryBaseAlgebra : Algebra ordinaryBase a.target]
  targetProjection : X ⟶ Spec (.of ordinaryBase)
  projection : a.targetMap ≫ targetProjection = Spec.algebraMap ordinaryBase a.target
  parameter : Fin m → ordinaryBase
  smoothing : ordinaryBase
  coordinate : Fin 2 → a.target
  equation : coordinate 0 * coordinate 1 = algebraMap ordinaryBase a.target smoothing
  chart : NodeRing ordinaryBase smoothing →+* a.target
  scalar : ∀ r, chart (nodeCoefficient ordinaryBase smoothing r) = algebraMap ordinaryBase a.target r
  generator : ∀ i, chart (nodeVariable ordinaryBase smoothing i) = coordinate i
  smooth : Smooth (Spec.map (CommRingCat.ofHom chart))

attribute [instance] Node.ordinaryBaseRing Node.ordinaryBaseAlgebra

def Node.targetParameter {m : ℕ} (n : Node a m) (i : Fin m) : a.target :=
  algebraMap n.ordinaryBase a.target (n.parameter i)

def ordinaryModule {m : ℕ} (o : Ordinary a m) : ModuleCat.{0} A := by
  let P := ordinary (k := k) (A := A) (B := a.target)
    (M := sourceCoefficient a I) (I := baseCoefficient a I)
    o.targetParameter (baseCoefficientMap a I)
  letI := @Submodule.addCommGroup A (a.target →ₗ[k] sourceCoefficient a I)
    inferInstance inferInstance inferInstance P
  exact ModuleCat.of A P

def boundaryModule {J : X.IdealSheafData} {m : ℕ} (b : Boundary a J m) : ModuleCat.{0} A := by
  let P := boundary (k := k) (A := A) (B := a.target)
    (M := sourceCoefficient a I) (I := baseCoefficient a I)
    b.coordinate b.ordinary.targetParameter (baseCoefficientMap a I)
  letI := @Submodule.addCommGroup A ((a.target →ₗ[k] sourceCoefficient a I) × sourceCoefficient a I)
    inferInstance inferInstance inferInstance P
  exact ModuleCat.of A P

def nodeModule {m : ℕ} (n : Node a m) : ModuleCat.{0} A := by
  let P := node (k := k) (A := A) (B := a.target)
    (M := sourceCoefficient a I) (I := baseCoefficient a I)
    n.coordinate n.targetParameter (baseCoefficientMap a I)
  letI := @Submodule.addCommGroup A
    ((a.target →ₗ[k] sourceCoefficient a I) × (Fin 2 → sourceCoefficient a I))
    inferInstance inferInstance inferInstance P
  exact ModuleCat.of A P

def coverArrow (U : C.Etale) : Arrow C.Etale :=
  Arrow.mk (show U ⟶ Scheme.Etale.mk (𝟙 C) from
    MorphismProperty.Over.homMk U.hom
      (show U.hom ≫ (𝟙 C) = U.hom from Category.comp_id _))

def nerve (U : C.Etale) : SimplicialObject C.Etale := (coverArrow U).cechNerve

end MathlibExt.AlgebraicGeometry.LiAffineMapCharts
