/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.RightActionMapping
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.RightModule
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
public import MathlibExt.Topology.Category.CGWH.Limits
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Mapping objects for right sphere modules

Presents the mapping object of right sphere modules as the equalizer imposing compatibility with every pair action. Ordinary module morphisms correspond to tensor-unit points, and maps from arbitrary parameters correspond to compatible families, with explicit projection formulas.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite
open LawfulDayConvolutionMonoidalCategoryStruct
open scoped CategoryTheory.MonObj MonoidalClosed

namespace PointedCGWH.SymmetricRightModuleMapping

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => Operad.SmallFinBijGroupoid

/-- The symmetric right sphere modules whose mapping objects are constructed here. -/
abbrev Carrier := SymmetricRightModulePresentation.RightSphereModule.{u, v}

private theorem pointedSmallLimits : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := CGWH.limits.instHasLimitsOfSize
  let _ : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
    change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
    infer_instance
  exact hasLimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallLimits

/-- The exact actual right actions and underlying original diagrams. -/
abbrev mappingData (M N : Carrier.{u, v}) :
    Enriched.RightActionMapping.Data (V := PointedCGWH.{u, v})
      («I» := Operad.SmallFinBijGroupoid) where
  X := M.X.functor
  Y := N.X.functor
  coefficient := sphereSequence.{u, v}.functor.obj
  rightX := SymmetricRightModulePresentation.pairAction M
  rightY := SymmetricRightModulePresentation.pairAction N

/-- Actual existing native limits provide every whole original degree product. -/
instance mappingObjectProduct (M N : Carrier.{u, v}) :
    HasProduct (Enriched.RightActionMapping.objects (mappingData M N)) := by
  let _ : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := pointedSmallLimits
  infer_instance

/-- Actual existing native limits provide both complete original relation products. -/
instance mappingRelationProduct (M N : Carrier.{u, v}) :
    HasProduct (Enriched.RightActionMapping.relations (mappingData M N)) := by
  let _ : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := pointedSmallLimits
  infer_instance

/-- The two original full native mapping-space relation maps have their actual equalizer. -/
instance mappingEqualizer (M N : Carrier.{u, v}) :
    HasEqualizer (Enriched.RightActionMapping.leftMap (mappingData M N))
      (Enriched.RightActionMapping.rightMap (mappingData M N)) := by
  let _ : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := pointedSmallLimits
  infer_instance

/-- The original Day injection is natural under every full right-module underlying map. -/
theorem dayRight_map (M N : Carrier.{u, v}) (f : M.X ⟶ N.X) (n a : I) :
    (DayFunctor.η M.X sphereSequence.{u, v}).app (n, a) ≫
        (f ▷ sphereSequence.{u, v}).natTrans.app (n ⊗ a) =
      (f.natTrans.app n ▷ sphereSequence.{u, v}.functor.obj a) ≫
        (DayFunctor.η N.X sphereSequence.{u, v}).app (n, a) :=
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app
    I PointedCGWH.{u, v} f sphereSequence.{u, v} n a

/-- Every actual original module morphism intertwines the entire right coefficient action. -/
theorem pairAction_map {M N : Carrier.{u, v}} (f : M ⟶ N) (n a : I) :
    SymmetricRightModulePresentation.pairAction M n a ≫ f.hom.natTrans.app (n ⊗ a) =
      (f.hom.natTrans.app n ▷ sphereSequence.{u, v}.functor.obj a) ≫
        SymmetricRightModulePresentation.pairAction N n a := by
  let rM : M.X ⊗ sphereSequence.{u, v} ⟶ M.X :=
    ModObj.smul (M := mop sphereSequence.{u, v}) (X := M.X)
  let rN : N.X ⊗ sphereSequence.{u, v} ⟶ N.X :=
    ModObj.smul (M := mop sphereSequence.{u, v}) (X := N.X)
  let i := (DayFunctor.η M.X sphereSequence.{u, v}).app (n, a)
  have h : rM ≫ f.hom = (f.hom ▷ sphereSequence.{u, v}) ≫ rN :=
    IsModHom.smul_hom (A := mop sphereSequence.{u, v}) (f := f.hom)
  have hPoint := congrArg (fun z : M.X ⊗ sphereSequence.{u, v} ⟶ N.X =>
    i ≫ z.natTrans.app (n ⊗ a)) h
  change (i ≫ rM.natTrans.app (n ⊗ a)) ≫ f.hom.natTrans.app (n ⊗ a) =
    (f.hom.natTrans.app n ▷ sphereSequence.{u, v}.functor.obj a) ≫
      (DayFunctor.η N.X sphereSequence.{u, v}).app (n, a) ≫ rN.natTrans.app (n ⊗ a)
  exact (Category.assoc _ _ _).trans
    (hPoint.trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ rN.natTrans.app (n ⊗ a))
          (dayRight_map M N f.hom n a)).trans (Category.assoc _ _ _))))

/-- Every actual module map defines exactly the whole original compatible transformation. -/
def toCompatibleHom {M N : Carrier.{u, v}} (f : M ⟶ N) :
    Enriched.RightActionMapping.CompatibleHom (mappingData M N) :=
  ⟨f.hom.natTrans, pairAction_map f⟩

/-- Both full original Day action maps descend uniquely from their entire pair generators. -/
def ofCompatibleHom {M N : Carrier.{u, v}}
    (f : Enriched.RightActionMapping.CompatibleHom (mappingData M N)) : M ⟶ N :=
  Mod.Hom.mk' (DayFunctor.Hom.mk f.val) (by
    let q : M.X ⟶ N.X := DayFunctor.Hom.mk f.val
    let rM : M.X ⊗ sphereSequence.{u, v} ⟶ M.X :=
      ModObj.smul (M := mop sphereSequence.{u, v}) (X := M.X)
    let rN : N.X ⊗ sphereSequence.{u, v} ⟶ N.X :=
      ModObj.smul (M := mop sphereSequence.{u, v}) (X := N.X)
    change rM ≫ q = (q ▷ sphereSequence.{u, v}) ≫ rN
    apply DayFunctor.tensor_hom_ext
    intro n a
    change ((DayFunctor.η M.X sphereSequence.{u, v}).app (n, a) ≫
        rM.natTrans.app (n ⊗ a)) ≫ f.val.app (n ⊗ a) =
      (DayFunctor.η M.X sphereSequence.{u, v}).app (n, a) ≫
        (q ▷ sphereSequence.{u, v}).natTrans.app (n ⊗ a) ≫ rN.natTrans.app (n ⊗ a)
    exact (f.property n a).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ rN.natTrans.app (n ⊗ a))
          (dayRight_map M N q n a)).symm.trans (Category.assoc _ _ _))))

/-- Every whole original module morphism is recovered. -/
theorem of_toCompatibleHom {M N : Carrier.{u, v}} (f : M ⟶ N) :
    ofCompatibleHom (toCompatibleHom f) = f := by
  apply Mod.hom_ext
  apply DayFunctor.hom_ext
  rfl

/-- Every whole original compatible transformation is recovered. -/
theorem to_ofCompatibleHom {M N : Carrier.{u, v}}
    (f : Enriched.RightActionMapping.CompatibleHom (mappingData M N)) :
    toCompatibleHom (ofCompatibleHom f) = f := by
  apply Subtype.ext
  rfl

/-- The actual original right module Hom is exactly the full compatible transformation space. -/
def compatibleHomEquiv (M N : Carrier.{u, v}) :
    (M ⟶ N) ≃ Enriched.RightActionMapping.CompatibleHom (mappingData M N) where
  toFun := toCompatibleHom
  invFun := ofCompatibleHom
  left_inv := of_toCompatibleHom
  right_inv := to_ofCompatibleHom

/-- The independent actual native topological mapping object is the original product equalizer. -/
@[no_expose]
def Hom (M N : Carrier.{u, v}) : PointedCGWH.{u, v} :=
  Enriched.RightActionMapping.Hom (mappingData M N)

/-- Each full actual level projects from the original independent mapping object. -/
@[no_expose]
def π (M N : Carrier.{u, v}) (n : I) :
    Hom M N ⟶ (ihom (M.X.functor.obj n)).obj (N.X.functor.obj n) :=
  Enriched.RightActionMapping.π (mappingData M N) n

/-- The independent native mapping object represents the actual whole original module Hom. -/
@[no_expose]
def homEquiv (M N : Carrier.{u, v}) : (M ⟶ N) ≃ (𝟙_ PointedCGWH.{u, v} ⟶ Hom M N) :=
  (compatibleHomEquiv M N).trans (Enriched.RightActionMapping.unitHomEquiv (mappingData M N))

/-- Every original full module morphism component is the actual mapping-space projection. -/
theorem homEquiv_π {M N : Carrier.{u, v}} (f : M ⟶ N) (n : I) :
    homEquiv M N f ≫ π M N n = eHomEquiv PointedCGWH.{u, v} (f.hom.natTrans.app n) :=
  Enriched.RightActionMapping.unitHomEquiv_π (mappingData M N) (toCompatibleHom f) n

/-- No extra end or mapping-object premise enters the actual source mapping construction. -/
theorem Hom_eq (M N : Carrier.{u, v}) : Hom M N =
    equalizer (Enriched.RightActionMapping.leftMap (mappingData M N))
      (Enriched.RightActionMapping.rightMap (mappingData M N)) :=
  Enriched.RightActionMapping.Hom_eq (mappingData M N)

/-- Every complete native parameter family is represented
by the actual independent mapping space. -/
@[no_expose]
def parameterEquiv (M N : Carrier.{u, v}) (P : PointedCGWH.{u, v}) :
    (P ⟶ Hom M N) ≃ Enriched.RightActionMapping.CompatibleFamily (mappingData M N) P :=
  Enriched.RightActionMapping.representationEquiv (mappingData M N) P

/-- Each actual represented parameter family retains the full original component map. -/
theorem parameterEquiv_app (M N : Carrier.{u, v}) (P : PointedCGWH.{u, v})
    (f : P ⟶ Hom M N) (n : I) :
    (parameterEquiv M N P f).app n = f ≫ π M N n := by rfl

/-- The exact original mapping value is the full generic original relation equalizer. -/
theorem Hom_eq_generic (M N : Carrier.{u, v}) :
    Hom M N = Enriched.RightActionMapping.Hom (mappingData M N) := by rfl

/-- The actual object equality defines the full original mapping-value identity isomorphism. -/
@[no_expose]
def genericHomIso (M N : Carrier.{u, v}) :
    Hom M N ≅ Enriched.RightActionMapping.Hom (mappingData M N) :=
  eqToIso (Hom_eq_generic M N)

/-- Every complete component is retained by the actual forward mapping-value comparison. -/
@[reassoc]
theorem genericHomIso_hom_π (M N : Carrier.{u, v}) (n : I) :
    (genericHomIso M N).hom ≫ Enriched.RightActionMapping.π (mappingData M N) n = π M N n := by
  change (𝟙 (Enriched.RightActionMapping.Hom (mappingData M N))) ≫
    Enriched.RightActionMapping.π (mappingData M N) n =
      Enriched.RightActionMapping.π (mappingData M N) n
  exact Category.id_comp _

/-- Every complete component is retained by the actual inverse mapping-value comparison. -/
@[reassoc]
theorem genericHomIso_inv_π (M N : Carrier.{u, v}) (n : I) :
    (genericHomIso M N).inv ≫ π M N n = Enriched.RightActionMapping.π (mappingData M N) n := by
  change (𝟙 (Enriched.RightActionMapping.Hom (mappingData M N))) ≫
    Enriched.RightActionMapping.π (mappingData M N) n =
      Enriched.RightActionMapping.π (mappingData M N) n
  exact Category.id_comp _

end PointedCGWH.SymmetricRightModuleMapping
