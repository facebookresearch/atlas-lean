/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
public import MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
public import MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage

/-!
# Deligne--Faltings structures on the actual small etale site

The site/category is Mathlib's X.Etale and X.smallEtaleTopology. Values
are actual line modules with actual sections on the etale schemes. The
reindexing, monoidal and composition diagrams use the actual scheme
pullback/tensor maps. Denominators are actual sheaf maps with local power
lifting; exponent may vary on the covering, as stalkwise Kummerness permits.

References: Borne--Vistoli, arXiv:1001.0466v2, §§3--5.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections

universe u

abbrev MonoidSheaf (X : Scheme.{u}) := EtaleMonoidInverseImage.MonoidSheaf X

/-- The actual local scheme below a small-etale object. -/
abbrev localScheme {X : Scheme.{u}} (U : X.Etale) := U.left

lemma mapIdentity {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale)
    (a : A.obj.obj (op U)) : A.obj.map (𝟙 (op U)) a = a := by
  exact ConcreteCategory.congr_hom (A.obj.map_id (op U)) a

lemma mapComposition {X : Scheme.{u}} (A : MonoidSheaf X)
    {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V) (a : A.obj.obj (op U)) :
    A.obj.map ((g ≫ f).op) a = A.obj.map g.op (A.obj.map f.op a) := by
  rw [op_comp, A.obj.map_comp]
  rfl

/-- A DF structure has native line/section charts and coherent etale reindexing.
The tensor-pullback comparison is characterized by all native local sections. -/
structure Structure {X : Scheme.{u}} (A : MonoidSheaf X) where
  chart : ∀ U : X.Etale, DeligneFaltingsChart U.left (A.obj.obj (op U))
  tensorPullback : ∀ {U V : X.Etale} (f : V ⟶ U), PullbackTensorData f.left
  reindex : ∀ {U V : X.Etale} (f : V ⟶ U) (a : A.obj.obj (op U)),
    (Scheme.Modules.pullback f.left).obj ((chart U).module a) ≅
      (chart V).module (A.obj.map f.op a)
  reindex_section : ∀ {U V : X.Etale} (f : V ⟶ U) (a : A.obj.obj (op U)),
    pullbackSection f.left ((chart U).sectionMap a) ≫ (reindex f a).hom =
      (chart V).sectionMap (A.obj.map f.op a)
  reindex_unit : ∀ {U V : X.Etale} (f : V ⟶ U),
    (reindex f 1).hom ≫ eqToHom
      (congrArg ((chart V).module) (map_one (A.obj.map f.op).hom)) ≫ (chart V).unit.hom =
    (Scheme.Modules.pullback f.left).map (chart U).unit.hom ≫
      SheafOfModules.pullbackObjUnitToUnit f.left.toRingCatSheafHom
  reindex_multiplication : ∀ {U V : X.Etale} (f : V ⟶ U)
    (a b : A.obj.obj (op U)),
    (Scheme.Modules.pullback f.left).map ((chart U).multiplication a b).hom ≫
      (reindex f (a*b)).hom =
    ((tensorPullback f).comparison ((chart U).module a) ((chart U).module b)).hom ≫
      tensorMap (reindex f a).hom (reindex f b).hom ≫
      ((chart V).multiplication (A.obj.map f.op a) (A.obj.map f.op b)).hom ≫
      eqToHom (congrArg ((chart V).module) (map_mul (A.obj.map f.op).hom a b).symm)
  identity : ∀ (U : X.Etale) (a : A.obj.obj (op U)),
    (reindex (𝟙 U) a).hom ≫
      eqToHom (congrArg ((chart U).module) (mapIdentity A U a)) =
        (Scheme.Modules.pullbackId U.left).hom.app ((chart U).module a)
  composition : ∀ {U V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
    (a : A.obj.obj (op U)),
    (reindex (g ≫ f) a).hom =
    (Scheme.Modules.pullbackComp g.left f.left).inv.app ((chart U).module a) ≫
      (Scheme.Modules.pullback g.left).map (reindex f a).hom ≫
      (reindex g (A.obj.map f.op a)).hom ≫
      eqToHom (congrArg ((chart W).module) (mapComposition A f g a).symm)

/-- Local power lifting is the actual sheaf version of Kummerness.
No uniform exponent across a parameter scheme is assumed. -/
def LocallyKummer {X : Scheme.{u}} {A B : MonoidSheaf X} (j : A ⟶ B) : Prop :=
  (∀ U : X.Etale, Function.Injective (j.hom.app (op U))) ∧
  ∀ (U : X.Etale) (b : B.obj.obj (op U)),
    ∃ (I : Type u) (V : I → X.Etale) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      ∀ i, ∃ n : ℕ, 0 < n ∧ ∃ a : A.obj.obj (op (V i)),
        j.hom.app (op (V i)) a = (B.obj.map (f i).op b) ^ n

/-- An actual denominator sheaf map; coherent chart witnesses are added
by the finite-presentation packet, not replaced by an arbitrary label. -/
structure DenominatorMap {X : Scheme.{u}} (A B : MonoidSheaf X) where
  map : A ⟶ B
  kummer : LocallyKummer map

end MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
