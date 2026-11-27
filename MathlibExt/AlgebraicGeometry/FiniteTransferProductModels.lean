/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels

/-!
# Source-normalized external products of finite transfer cycles

Smooth products are identified with the actual scheme pullback over the
field. Every product map is fixed on both projections. The product of two
integral correspondence schemes may be reducible or nonreduced; its cycle
therefore sums all actual generic components with their local-ring lengths.

The categorical external-product construction retains all integral cycle
maps. Its functor laws and geometry are explicit construction dependencies.

References: Mazza--Voevodsky--Weibel, Lectures 1 and 2, especially
Definition 1.1, Construction 1.3 and Exercise 2.9;
Voevodsky, arXiv:math/0107109v1, §2 equations 2.1--2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteTransferProductModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry TopologicalSpace
open FiniteTransferCycleModels

variable {k : Type} [Field k]

/-- The product is the native pullback over Spec(k), with its actual structure map. -/
structure SmoothProductGeometry (U V W : SmoothScheme k) where
  iso : W.scheme.left ≅ productScheme U V
  base_eq : iso.hom ≫ pullback.fst U.scheme.hom V.scheme.hom ≫ U.scheme.hom = W.scheme.hom

def SmoothProductGeometry.fst {U V W : SmoothScheme k} (P : SmoothProductGeometry U V W) : W ⟶ U :=
  Over.homMk (P.iso.hom ≫ pullback.fst U.scheme.hom V.scheme.hom)
    (by simpa only [Category.assoc] using P.base_eq)

def SmoothProductGeometry.snd {U V W : SmoothScheme k} (P : SmoothProductGeometry U V W) : W ⟶ V :=
  Over.homMk (P.iso.hom ≫ pullback.snd U.scheme.hom V.scheme.hom) (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact P.base_eq)

/-- A product functor is fixed on every actual scheme coordinate. -/
structure SmoothProductSystem (k : Type) [Field k] where
  tensor : SmoothScheme k ⥤ SmoothScheme k ⥤ SmoothScheme k
  geometry : ∀ U V : SmoothScheme k, SmoothProductGeometry U V ((tensor.obj U).obj V)
  map_fst : ∀ (U U' V V' : SmoothScheme k) (f : U ⟶ U') (g : V ⟶ V'),
    (tensor.map f).app V ≫ (tensor.obj U').map g ≫ (geometry U' V').fst = (geometry U V).fst ≫ f
  map_snd : ∀ (U U' V V' : SmoothScheme k) (f : U ⟶ U') (g : V ⟶ V'),
    (tensor.map f).app V ≫ (tensor.obj U').map g ≫ (geometry U' V').snd = (geometry U V).snd ≫ g
  unit : SmoothScheme k
  unitIso : unit.scheme.left ≅ Spec (.of k)
  unit_base : unit.scheme.hom = unitIso.hom

def SmoothProductSystem.obj (P : SmoothProductSystem k) (U V : SmoothScheme k) : SmoothScheme k :=
  (P.tensor.obj U).obj V

def generatorBase {U X : SmoothScheme k} (g : Generator U X) : g.presentation.scheme ⟶ Spec (.of k) :=
  g.presentation.inclusion ≫ pullback.fst U.scheme.hom X.scheme.hom ≫ U.scheme.hom

def externalScheme {U X V Y : SmoothScheme k} (g : Generator U X) (h : Generator V Y) : Scheme.{0} :=
  pullback (generatorBase g) (generatorBase h)

/-- The four coordinates determine the actual closed product embedding. -/
structure ExternalProjection (P : SmoothProductSystem k)
    {U X V Y : SmoothScheme k} (g : Generator U X) (h : Generator V Y) where
  map : externalScheme g h ⟶ productScheme (P.obj U V) (P.obj X Y)
  firstSource : map ≫ pullback.fst (P.obj U V).scheme.hom (P.obj X Y).scheme.hom ≫
      (P.geometry U V).fst.left =
    pullback.fst (generatorBase g) (generatorBase h) ≫ g.presentation.inclusion ≫
      pullback.fst U.scheme.hom X.scheme.hom
  secondSource : map ≫ pullback.fst (P.obj U V).scheme.hom (P.obj X Y).scheme.hom ≫
      (P.geometry U V).snd.left =
    pullback.snd (generatorBase g) (generatorBase h) ≫ h.presentation.inclusion ≫
      pullback.fst V.scheme.hom Y.scheme.hom
  firstTarget : map ≫ pullback.snd (P.obj U V).scheme.hom (P.obj X Y).scheme.hom ≫
      (P.geometry X Y).fst.left =
    pullback.fst (generatorBase g) (generatorBase h) ≫ g.presentation.inclusion ≫
      pullback.snd U.scheme.hom X.scheme.hom
  secondTarget : map ≫ pullback.snd (P.obj U V).scheme.hom (P.obj X Y).scheme.hom ≫
      (P.geometry X Y).snd.left =
    pullback.snd (generatorBase g) (generatorBase h) ≫ h.presentation.inclusion ≫
      pullback.snd V.scheme.hom Y.scheme.hom
  [closed : IsClosedImmersion map]

attribute [instance] ExternalProjection.closed

/-- External-product multiplicities are the native lengths of the actual product local rings. -/
structure ExternalGeometry (P : SmoothProductSystem k)
    {U X V Y : SmoothScheme k} (g : Generator U X) (h : Generator V Y) where
  projection : ExternalProjection P g h
  noetherian : IsNoetherian (externalScheme g h)
  finiteLength : ∀ z : irreducibleComponents (externalScheme g h),
    Module.length ((externalScheme g h).presheaf.stalk z.2.1.genericPoint)
      ((externalScheme g h).presheaf.stalk z.2.1.genericPoint) ≠ ⊤
  image : ∀ _z : irreducibleComponents (externalScheme g h), Generator (P.obj U V) (P.obj X Y)
  image_eq : ∀ z : irreducibleComponents (externalScheme g h),
    ((image z).support : Set (productScheme (P.obj U V) (P.obj X Y))) =
      closure {projection.map z.2.1.genericPoint}

def ExternalGeometry.cycle {P : SmoothProductSystem k} {U X V Y : SmoothScheme k}
    {g : Generator U X} {h : Generator V Y} (D : ExternalGeometry P g h) :
    Cycles (P.obj U V) (P.obj X Y) := by
  letI := D.noetherian
  letI : Finite (irreducibleComponents (externalScheme g h)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents (externalScheme g h))
  exact ∑ z : irreducibleComponents (externalScheme g h),
    ((Module.length ((externalScheme g h).presheaf.stalk z.2.1.genericPoint)
      ((externalScheme g h).presheaf.stalk z.2.1.genericPoint)).toNat : ℤ) • generatorCycle (D.image z)

structure ExternalSystem (P : SmoothProductSystem k) where
  geometry : ∀ (U X V Y : SmoothScheme k) (g : Generator U X) (h : Generator V Y), ExternalGeometry P g h

def externalCycles {P : SmoothProductSystem k} (E : ExternalSystem P)
    {U X V Y : SmoothScheme k} (a : Cycles U X) (b : Cycles V Y) :
    Cycles (P.obj U V) (P.obj X Y) :=
  a.sum fun g n => b.sum fun h m => (n * m) • (E.geometry U X V Y g h).cycle

/-- The categorical tensor is normalized on all objects and every pair of integral cycle maps. -/
structure CorrespondenceProductModel (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] (P : SmoothProductSystem k) (E : ExternalSystem P) where
  tensor : CorrespondenceObject D G ⥤ CorrespondenceObject D G ⥤ CorrespondenceObject D G
  objects_eq : ∀ U V : CorrespondenceObject D G,
    (tensor.obj U).obj V = ⟨P.obj U.scheme V.scheme⟩
  maps_eq : ∀ (U X V Y : CorrespondenceObject D G) (a : U ⟶ X) (b : V ⟶ Y),
    eqToHom (objects_eq U V).symm ≫ (tensor.map a).app V ≫ (tensor.obj X).map b ≫
      eqToHom (objects_eq X Y) =
    (show (⟨P.obj U.scheme V.scheme⟩ : CorrespondenceObject D G) ⟶ ⟨P.obj X.scheme Y.scheme⟩ from
      externalCycles E (show Cycles U.scheme X.scheme from a) (show Cycles V.scheme Y.scheme from b))

end MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
