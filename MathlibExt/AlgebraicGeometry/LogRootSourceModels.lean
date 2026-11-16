/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels
public import MathlibExt.AlgebraicGeometry.InfiniteDenominatorRoots

/-!
# Native logarithmic sources of the finite and infinite root models

The small characteristic sheaf is compared to the entire original
characteristic presheaf, with only a universe lift. Each DF line is
identified through its actual trivialization torsor: lifts in the original
log monoid correspond to frames of that line, with alpha, multiplication,
units and every etale restriction fixed. Zero alpha values retain the
full frame torsor and its monoidal action.

The root realization uses the existing actual finite denominator models,
coherent tower and compatible-root infinite fibres. It does not choose
an unrelated fibred category called the root stack.

Source: Borne--Vistoli arXiv:1001.0466v2, Proposition3.9;
Talpo--Vistoli arXiv:1410.1164v2, Sections2--4 and Theorem5.24.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams KatoChartCoefficientModels
open DeligneFaltingsCategories DenominatorRootStacks InfiniteDenominatorRoots
open LineBundleTaskContracts

variable [InverseImageTheory.{0}]

def liftMonoids : CommMonCat.{0} ⥤ CommMonCat.{1} where
  obj P := .of (ULift.{1} P)
  map f := CommMonCat.ofHom
    { toFun x := ULift.up (f.hom x.down)
      map_one' := ULift.ext (map_one f.hom)
      map_mul' x y := ULift.ext (map_mul f.hom x.down y.down) }
  map_id P := by ext x; rfl
  map_comp f g := by ext x; rfl

def logCoefficient (D : RegularSectionComparisons) (X : LogScheme.{0}) (U : X.scheme.Etale)
    (m : (LogStructures.monoid X.scheme.smallEtaleTopology X.log).obj.obj (op U)) :
    Γ(U.left, ⊤) :=
  ULift.ringEquiv ((regularIso D X.scheme U).inv.hom
    ((LogStructures.alpha X.scheme.smallEtaleTopology X.log).hom.app (op U) m))

variable (X : LogScheme.{0}) (A : DeligneFaltingsSheaves.MonoidSheaf X.scheme)
  (e : A.obj ⋙ liftMonoids ≅ (LogStructures.characteristic X.scheme.smallEtaleTopology X.log).obj)

def LogLift (U : X.scheme.Etale) (a : A.obj.obj (op U)) :=
  {m : (LogStructures.monoid X.scheme.smallEtaleTopology X.log).obj.obj (op U) //
    (LogStructures.characteristicMap X.scheme.smallEtaleTopology X.log).hom.app (op U) m =
      (e.hom.app (op U)).hom (ULift.up a)}

variable (D : RegularSectionComparisons) (L : DeligneFaltingsSheaves.Structure A)

/-- The actual log-lift/frame torsor dictionary, on all coefficients and arrows. -/
structure FrameDictionary where
  frame : ∀ (U : X.scheme.Etale) (a : A.obj.obj (op U)),
    LogLift X A e U a ≃ ((L.chart U).module a ≅ CoherentCurveLinearSeries.structureModule U.left)
  section_normalization : ∀ (U : X.scheme.Etale) (a : A.obj.obj (op U)) (m : LogLift X A e U a),
    ((((L.chart U).sectionMap a ≫ (frame U a m).hom).val.app (op ⊤)).hom
      (1 : Γ(U.left, ⊤))) = logCoefficient D X U m.val
  unit : ∀ (U : X.scheme.Etale) (m : LogLift X A e U 1),
    m.val = 1 → frame U 1 m = (L.chart U).unit
  multiplication : ∀ (U : X.scheme.Etale) (a b : A.obj.obj (op U))
      (m : LogLift X A e U a) (n : LogLift X A e U b) (mn : LogLift X A e U (a * b)),
    mn.val = m.val * n.val →
      ((L.chart U).multiplication a b).hom ≫ (frame U (a * b) mn).hom =
        LineBundleTaskContracts.tensorMap (frame U a m).hom (frame U b n).hom ≫
          (tensorLeftUnit U.left (CoherentCurveLinearSeries.structureModule U.left)).hom
  restriction : ∀ {U V : X.scheme.Etale} (f : V ⟶ U) (a : A.obj.obj (op U))
      (m : LogLift X A e U a) (n : LogLift X A e V (A.obj.map f.op a)),
    n.val = (LogStructures.monoid X.scheme.smallEtaleTopology X.log).obj.map f.op m.val →
      (L.reindex f a).hom ≫ (frame V (A.obj.map f.op a) n).hom =
        (Scheme.Modules.pullback f.left).map (frame U a m).hom ≫
          SheafOfModules.pullbackObjUnitToUnit f.left.toRingCatSheafHom

/-- A source DF object is fixed by the original logarithmic characteristic
and its full unit/section frame torsors. -/
structure LogDFDictionary where
  characteristic : DeligneFaltingsSheaves.MonoidSheaf X.scheme
  df : DeligneFaltingsSheaves.Structure characteristic
  isDF : IsDeligneFaltings df
  fs : FiniteRootTowers.IsFineSaturated characteristic
  comparison : characteristic.obj ⋙ liftMonoids ≅
    (LogStructures.characteristic X.scheme.smallEtaleTopology X.log).obj
  frames : FrameDictionary X characteristic comparison D df

variable (I : NativeDFImages.{0})

/-- The actual root realization, using those same finite root families
and all normalized infinite projections and parameter maps. -/
structure RootRealization where
  dictionary : LogDFDictionary X D
  finite : FiniteModels I dictionary.df
  tower : GlobalTower I dictionary.df finite
  infinite : InfiniteModel I dictionary.df tower

end MathlibExt.AlgebraicGeometry.LogRootSourceModels
