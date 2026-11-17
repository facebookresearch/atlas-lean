/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiCechCoefficientModels

/-!
# Full base Cech coefficients for one target shared by finite source components

The base covering has every actual curve-chart base and the identity
base chart. Its Cech tuples include mixed-component and empty-source
intersections. Their target-parameter coefficients are retained even
when there is no curve intersection. The source derivative and the
corresponding base parameter are identified on every actual curve tuple.

Consequently the degree-zero target parameters glue on the full base
Cech nerve to ONE base deformation. A product of separate component
complexes would not impose this condition. All tensor coefficients,
base restrictions and source maps are the actual native scheme maps.

Source: Jun Li math/0110113v1 (1.10)--(1.20), (1.23)--(1.25), with the
one shared target in the disconnected relative families of Section 3.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiSharedTargetCechModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Opposite
open LiAffineMapCharts LiCechChartModules
open scoped Simplicial TensorProduct

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {c : ℕ} {C : Fin c → Scheme.{0}} {p : ∀ v, C v ⟶ Spec (.of A)}
  {X Z : Scheme.{0}} {q : X ⟶ Spec (.of k)} {f : ∀ v, C v ⟶ X}
  (g : X ⟶ Z) {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))
  (L : ∀ v, LiGeometricCechModels.Cover (p := p v) (q := q) (f := f v))
  (G : ∀ v, LiGeometricCechModels.Geometry g J t (L v))
  (V : ∀ v, LiCechCoefficientModels.Model g J t (L v) (G v))

abbrev Label := Option (Σ v : Fin c, Fin (L v).count)

def baseChart : Label L → Scheme.{0}
  | none => Spec (.of A)
  | some a => Spec (.of ((L a.1).charts a.2).base)

def baseArrow : ∀ a : Label L, baseChart L a ⟶ Spec (.of A)
  | none => 𝟙 _
  | some a => Spec.algebraMap A ((L a.1).charts a.2).base

abbrev labelRing (a : Label L) := Γ(baseChart L a, ⊤)

instance labelAlgebra (a : Label L) : Algebra A (labelRing L a) :=
  ((baseArrow L a).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra

def sourceLabels (v : Fin c) {z : SimplexCategory}
    (a : Fin (z.len + 1) → Fin (L v).count) : Fin (z.len + 1) → Label L :=
  fun i => some ⟨v, a i⟩

def baseTuple (z : SimplexCategory) (a : Fin (z.len + 1) → Label L) : Scheme.{0} :=
  LiGeometricCechModels.tuplePullback (baseChart L) (baseArrow L) z a

abbrev baseRing (z : SimplexCategory) (a : Fin (z.len + 1) → Label L) := Γ(baseTuple L z a, ⊤)

instance baseAlgebra (z : SimplexCategory) (a : Fin (z.len + 1) → Label L) :
    Algebra A (baseRing L z a) :=
  ((WidePullback.base (fun i : Fin (z.len + 1) => baseArrow L (a i))).appTop.hom.comp
    (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra

def parentLift : Spec (.of A) ⟶ baseTuple L ⦋0⦌ (fun _ => none) :=
  WidePullback.lift (𝟙 _) (fun _ => 𝟙 _) (by intro i; simp [baseArrow])

structure ParentRestriction where
  algebra : baseRing L ⦋0⦌ (fun _ => none) →ₐ[A] A
  native : ∀ x, algebra x = (Scheme.ΓSpecIso (.of A)).hom.hom
    ((parentLift L).appTop.hom x)

def baseProjection {n z : SimplexCategory} (s : n ⟶ z)
    (a : Fin (z.len + 1) → Label L) : baseTuple L z a ⟶ baseTuple L n (a ∘ s.toOrderHom) :=
  LiGeometricCechModels.tupleProjection (baseChart L) (baseArrow L) s a

/-- A base restriction is fixed on every regular function by the native tuple projection. -/
structure BaseRestriction {n z : SimplexCategory} (s : n ⟶ z)
    (a : Fin (z.len + 1) → Label L) where
  algebra : baseRing L n (a ∘ s.toOrderHom) →ₐ[A] baseRing L z a
  native : ∀ x, algebra x = (baseProjection L s a).appTop.hom x

structure LabelRestriction (z : SimplexCategory) (a : Fin (z.len + 1) → Label L)
    (i : Fin (z.len + 1)) where
  algebra : labelRing L (a i) →ₐ[A] baseRing L z a
  native : ∀ x, algebra x =
    (WidePullback.π (fun j : Fin (z.len + 1) => baseArrow L (a j)) i).appTop.hom x

structure SourceLabelMap (v : Fin c) (i : Fin (L v).count) where
  algebra : ((L v).charts i).base →ₐ[A] labelRing L (some ⟨v, i⟩)
  native : ∀ x, algebra x = (Scheme.ΓSpecIso (.of ((L v).charts i).base)).inv.hom x

def sourceToBase (v : Fin c) (z : SimplexCategory)
    (a : Fin (z.len + 1) → Fin (L v).count) :
    Spec (.of ((G v).chart z a).source) ⟶ baseTuple L z (sourceLabels L v a) :=
  Spec.algebraMap ((G v).chart z a).base ((G v).chart z a).source ≫ ((G v).base z a).hom

structure SourceBaseMap (v : Fin c) (z : SimplexCategory)
    (a : Fin (z.len + 1) → Fin (L v).count) where
  algebra : baseRing L z (sourceLabels L v a) →ₐ[A] ((G v).chart z a).source
  native : ∀ x, algebra x = (Scheme.ΓSpecIso (.of ((G v).chart z a).source)).hom.hom
    ((sourceToBase g J t L G v z a).appTop.hom x)

variable (B : ∀ v z a, SourceBaseMap g J t L G v z a) (I : ModuleCat.{0} A)

abbrev baseCoefficient (z : SimplexCategory) (a : Fin (z.len + 1) → Label L) :=
  baseRing L z a ⊗[A] I

def embedSourceCoefficient (v : Fin c) (z : SimplexCategory)
    (a : Fin (z.len + 1) → Fin (L v).count) :
    baseCoefficient L I z (sourceLabels L v a) →ₗ[A] sourceCoefficient ((G v).chart z a) I :=
  TensorProduct.map (B v z a).algebra.toLinearMap LinearMap.id

abbrev rawTerm (z : SimplexCategory) :=
  ∀ v : Fin c, ((V v).localModel I).cochains.obj z

abbrev parameterTerm (z : SimplexCategory) :=
  ∀ a : Fin (z.len + 1) → Label L, Fin m → baseCoefficient L I z a

def matchingDifference (z : SimplexCategory) :
    (rawTerm g J t L G V I z × parameterTerm (m := m) L I z) →ₗ[A]
      (∀ (v : Fin c) (a : Fin (z.len + 1) → Fin (L v).count),
        Fin m → LiAffineMapCharts.sourceCoefficient ((G v).chart z a) I) where
  toFun x v a i :=
    derivative g J t I ((G v).mode z a)
      ((((V v).localModel I).comparison z).hom (x.1 v) a)
      (parameterValue t ((G v).chart z a) i) -
    embedSourceCoefficient g J t L G B I v z a (x.2 (sourceLabels L v a) i)
  map_add' x y := by
    funext v a i
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
    change derivative g J t I ((G v).mode z a)
      (((((V v).localModel I).comparison z).hom (x.1 v) a) +
        ((((V v).localModel I).comparison z).hom (y.1 v) a))
      (parameterValue t ((G v).chart z a) i) -
      (embedSourceCoefficient g J t L G B I v z a (x.2 (sourceLabels L v a) i) +
        embedSourceCoefficient g J t L G B I v z a (y.2 (sourceLabels L v a) i)) = _
    rw [map_add, LinearMap.add_apply]
    abel
  map_smul' r x := by
    funext v a i
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
      RingHom.id_apply, smul_sub]
    change derivative g J t I ((G v).mode z a)
      (r • ((((V v).localModel I).comparison z).hom (x.1 v) a))
      (parameterValue t ((G v).chart z a) i) - _ = _
    rw [map_smul, LinearMap.smul_apply]

def term (z : SimplexCategory) : ModuleCat.{0} A :=
  ModuleCat.of A (LinearMap.ker (matchingDifference g J t L G V B I z))

structure Model where
  cochains : CosimplicialObject (ModuleCat.{0} A)
  comparison : ∀ z : SimplexCategory, cochains.obj z ≅ term g J t L G V B I z
  restriction : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Label L),
    BaseRestriction L s a
  source : ∀ {n z : SimplexCategory} (s : n ⟶ z) (x : cochains.obj n) v,
    ((comparison z).hom (cochains.map s x)).val.1 v =
      ((V v).localModel I).cochains.map s (((comparison n).hom x).val.1 v)
  parameter : ∀ {n z : SimplexCategory} (s : n ⟶ z) (x : cochains.obj n)
    (a : Fin (z.len + 1) → Label L) i,
    ((comparison z).hom (cochains.map s x)).val.2 a i =
      TensorProduct.map (restriction s a).algebra.toLinearMap LinearMap.id
        (((comparison n).hom x).val.2 (a ∘ s.toOrderHom) i)

structure System where
  base : ∀ v z a, SourceBaseMap g J t L G v z a
  parent : ParentRestriction L
  affine : ∀ z a, IsAffine (baseTuple L z a)
  labels : ∀ z a i, LabelRestriction L z a i
  sourceLabel : ∀ v i, SourceLabelMap L v i
  functor : ModuleCat.{0} A ⥤ CosimplicialObject (ModuleCat.{0} A)
  model : ∀ I : ModuleCat.{0} A, Model g J t L G V base I
  comparison : ∀ I : ModuleCat.{0} A, functor.obj I ≅ (model I).cochains
  source : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) z (x : (functor.obj I).obj z) v,
    (((model N).comparison z).hom ((comparison N).hom.app z ((functor.map u).app z x))).val.1 v =
      (LiCechCoefficientModels.transport (g := g) (J := J) (t := t) (L := L v) (G := G v)
        (u := u) (V v)).app z
          ((((model I).comparison z).hom ((comparison I).hom.app z x)).val.1 v)
  parameter : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) z (x : (functor.obj I).obj z)
    (a : Fin (z.len + 1) → Label L) i,
    (((model N).comparison z).hom ((comparison N).hom.app z ((functor.map u).app z x))).val.2 a i =
      TensorProduct.map LinearMap.id u.hom
        ((((model I).comparison z).hom ((comparison I).hom.app z x)).val.2 a i)

def transport {I N : ModuleCat.{0} A} (u : I ⟶ N) (H : System g J t L G V) :
    (H.model I).cochains ⟶ (H.model N).cochains :=
  (H.comparison I).inv ≫ H.functor.map u ≫ (H.comparison N).hom

end MathlibExt.AlgebraicGeometry.LiSharedTargetCechModels
