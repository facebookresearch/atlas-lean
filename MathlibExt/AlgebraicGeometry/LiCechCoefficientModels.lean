/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGeometricCechModels

/-!
# Every coefficient map in the actual Li Cech models

The maps on each local value are fixed by the literal tensor map on
regular derivatives and all retained boundary/node logarithms. The
whole cosimplicial coefficient functor is normalized on every chart
tuple. Its native functor laws retain coefficient identities/compositions.
Source: Jun Li arXiv:math/0110113v1, Lemma1.15 and the base-change
condition of Definition1.11/Theorem1.22.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiCechCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open LiAffineMapCharts LiCechChartModules
open scoped Simplicial TensorProduct

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {C X Z : Scheme.{0}} {p : C ⟶ Spec (.of A)} {q : X ⟶ Spec (.of k)} {f : C ⟶ X}
  (g : X ⟶ Z) {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))
  (a : Chart p q f) {I N : ModuleCat.{0} A} (u : I ⟶ N)

def coefficientMap : sourceCoefficient a I →ₗ[A] sourceCoefficient a N :=
  TensorProduct.map LinearMap.id u.hom

def Normalized (o : Mode g J t a) (h : value g J t I o ⟶ value g J t N o) : Prop :=
  (∀ (x : value g J t I o) (s : a.target),
    derivative g J t N o (h x) s = coefficientMap a u (derivative g J t I o x s)) ∧
  match o with
  | .ordinary _ _ _ _ => True
  | .boundary _ z pr pt hp h' => ∀ x : value g J t I (.boundary _ z pr pt hp h'),
      boundaryLog g J t N z pr pt hp h' (h x) = coefficientMap a u (boundaryLog g J t I z pr pt hp h' x)
  | .node z pr pure h' => ∀ (x : value g J t I (.node z pr pure h')) (i : Fin 2),
      nodeLog g J t N z pr pure h' (h x) i = coefficientMap a u (nodeLog g J t I z pr pure h' x i)

structure LocalMap (o : Mode g J t a) where
  map : value g J t I o ⟶ value g J t N o
  normalized : Normalized g J t a u o map

variable
  (L : LiGeometricCechModels.Cover (p := p) (q := q) (f := f))
  (G : LiGeometricCechModels.Geometry g J t L)

structure Model where
  functor : ModuleCat.{0} A ⥤ CosimplicialObject (ModuleCat.{0} A)
  localModel : ∀ I : ModuleCat.{0} A, LiGeometricCechModels.Model g J t L G I
  comparison : ∀ I : ModuleCat.{0} A, functor.obj I ≅ (localModel I).cochains
  coefficient : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N)
    (n : SimplexCategory) (a : Fin (n.len + 1) → Fin L.count),
      LocalMap g J t (G.chart n a) u (G.mode n a)
  normalized : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) (n : SimplexCategory)
    (a : Fin (n.len + 1) → Fin L.count) (x : (functor.obj I).obj n),
      ((localModel N).comparison n).hom ((comparison N).hom.app n ((functor.map u).app n x)) a =
        (coefficient u n a).map
          (((localModel I).comparison n).hom ((comparison I).hom.app n x) a)

def transport {I N : ModuleCat.{0} A} (u : I ⟶ N) (V : Model g J t L G) :
    (V.localModel I).cochains ⟶ (V.localModel N).cochains :=
  (V.comparison I).inv ≫ V.functor.map u ≫ (V.comparison N).hom

end MathlibExt.AlgebraicGeometry.LiCechCoefficientModels
