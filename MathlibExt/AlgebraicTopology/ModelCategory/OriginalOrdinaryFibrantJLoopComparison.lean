/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryJLoopFunctor

/-!
# Original J loops on fibrant objects and both original R-unit maps

The original J projection squares and the opposite cofibrant cube show
that the full point-set J loop map preserves weak equivalences between
fibrant objects. Its actual map on the original R unit is therefore a Ho
isomorphism at a fibrant object.

The same natural unit and earned full J-loop-after-R descent prove that
the point-set J loop map respects all Ho equalities between fibrant maps.
The two original maps R(r_A) and r_(R A) are compared only after localization
and then after the original loop functor. These earned comparisons normalize
the original derived-loop identification on the same original R target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopicalAlgebra.OriginalOrdinaryFibrantJLoopComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "H" => toHomotopyCategory C
local notation "L" => OriginalOrdinaryJLoopFunctor.loopFunctor g Z hZ
local notation "R" => GeneratedFunctorialReplacements.R g
local notation "r" => GeneratedFunctorialReplacements.unit g

private theorem op_isCofibrant (A : C) [IsFibrant A] : IsCofibrant (op A) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from A).op terminalIsTerminal.op).mpr
  exact (cofibration_op_iff _).mpr inferInstance

/-- The complete original J fibre map is weak on every weak map between fibrant original targets. -/
theorem originalFiberMap_weak {A B : C} (f : A ⟶ B)
    [IsFibrant A] [IsFibrant B] [WeakEquivalence f] :
    WeakEquivalence (OriginalOrdinaryJLoopFunctor.originalFiberMap g Z hZ f) := by
  let : IsFibrant Z := (isFibrant_iff_of_isTerminal (𝟙 Z) hZ.isTerminal).mpr (by infer_instance)
  let : IsFibrant ((𝟭 C).obj A) := inferInstanceAs (IsFibrant A)
  let : IsFibrant ((𝟭 C).obj B) := inferInstanceAs (IsFibrant B)
  let : IsCofibrant (op ((𝟭 C).obj A)) := op_isCofibrant _
  let : IsCofibrant (op ((𝟭 C).obj B)) := op_isCofibrant _
  let : IsCofibrant (op A) := op_isCofibrant A
  let : IsCofibrant (op B) := op_isCofibrant B
  let : IsCofibrant (op Z) := op_isCofibrant Z
  let : Cofibration (((OriginalOrdinaryJPathCone.projection g Z hZ).app A).op) :=
    (cofibration_op_iff _).mpr ((fibration_iff _).mpr
      (OriginalOrdinaryJPathCone.projection_fibration g Z hZ A))
  let : Cofibration (((OriginalOrdinaryJPathCone.projection g Z hZ).app B).op) :=
    (cofibration_op_iff _).mpr ((fibration_iff _).mpr
      (OriginalOrdinaryJPathCone.projection_fibration g Z hZ B))
  let : WeakEquivalence (f.op) := (weakEquivalences_op_iff _).mpr inferInstance
  let : WeakEquivalence (((OriginalOrdinaryJPathCone.pathObject g Z hZ).map f).op) :=
    (weakEquivalences_op_iff _).mpr ((weakEquivalence_iff _).mpr
      (OriginalOrdinaryJPathCone.pathObject_map_weak g Z hZ f))
  let : WeakEquivalence (𝟙 (op Z)) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences Cᵒᵖ).of_isIso _)
  have hp := (OriginalOrdinaryJPathCone.projection g Z hZ).naturality f
  change (OriginalOrdinaryJPathCone.pathObject g Z hZ).map f ≫
      (OriginalOrdinaryJPathCone.projection g Z hZ).app B =
    (OriginalOrdinaryJPathCone.projection g Z hZ).app A ≫ f at hp
  have hz : hZ.isInitial.to A ≫ f = hZ.isInitial.to B := hZ.isInitial.hom_ext _ _
  have h : WeakEquivalence ((OriginalOrdinaryJLoopFunctor.originalFiberMap g Z hZ f).op) :=
    weakEquivalence_map_of_isPushouts_of_cofibrant
      (IsPullback.of_hasPullback ((OriginalOrdinaryJPathCone.projection g Z hZ).app B)
        (hZ.isInitial.to B)).op.flip
      (IsPullback.of_hasPullback ((OriginalOrdinaryJPathCone.projection g Z hZ).app A)
        (hZ.isInitial.to A)).op.flip
      (a := f.op) (b := ((OriginalOrdinaryJPathCone.pathObject g Z hZ).map f).op)
      (c := 𝟙 (op Z)) (d := (OriginalOrdinaryJLoopFunctor.originalFiberMap g Z hZ f).op)
      (by simpa only [op_comp] using congrArg Quiver.Hom.op hp)
      (by simpa only [op_comp, Category.comp_id] using congrArg Quiver.Hom.op hz.symm)
      (by simpa only [op_comp] using (congrArg Quiver.Hom.op
        (OriginalOrdinaryJLoopFunctor.originalFiberMap_fst g Z hZ f)))
      (by simpa only [op_comp, Category.id_comp] using (congrArg Quiver.Hom.op
        (OriginalOrdinaryJLoopFunctor.originalFiberMap_snd g Z hZ f)))
  exact (weakEquivalences_op_iff _).mp h

/-- The full original point-set J loop map preserves each weak map between fibrant objects. -/
theorem loopMap_weak {A B : C} (f : A ⟶ B)
    [IsFibrant A] [IsFibrant B] [WeakEquivalence f] :
    WeakEquivalence ((L).map f) := by
  let : WeakEquivalence (OriginalOrdinaryJLoopFunctor.originalFiberMap g Z hZ f) :=
    originalFiberMap_weak g Z hZ f
  exact weakEquivalence_of_postcomp_of_fac
    (OriginalOrdinaryJLoopFunctor.loopIsoFiber_naturality g Z hZ f)

/-- Every original R-unit square remains an actual entire point-set J-loop naturality square. -/
theorem loopUnit_naturality {A B : C} (f : A ⟶ B) :
    (L).map f ≫ (L).map ((r).app B) = (L).map ((r).app A) ≫ (L).map ((R).map f) := by
  rw [← (L).map_comp, ← (L).map_comp]
  exact (L).congr_map ((r).naturality f)

/-- At a fibrant source, the actual original R-unit J-loop map is an earned Ho isomorphism. -/
def loopUnitIso (A : C) [IsFibrant A] : (H).obj ((L).obj A) ≅ (H).obj ((L).obj ((R).obj A)) := by
  let : IsFibrant ((𝟭 C).obj A) := inferInstanceAs (IsFibrant A)
  let : IsFibrant ((R).obj A) := GeneratedFunctorialReplacements.R_isFibrant g A
  let : WeakEquivalence ((r).app A) :=
    (weakEquivalence_iff _).mpr (GeneratedFunctorialReplacements.unit_weak g A)
  let : WeakEquivalence ((L).map ((r).app A)) := loopMap_weak g Z hZ ((r).app A)
  let : IsIso ((H).map ((L).map ((r).app A))) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp ((weakEquivalence_iff _).mp inferInstance)
  exact asIso ((H).map ((L).map ((r).app A)))

/-- The two actual original R-unit maps have the same original Ho image by the original unit's own square. -/
theorem unit_R_unit_image (A : C) :
    (H).map ((R).map ((r).app A)) = (H).map ((r).app ((R).obj A)) := by
  let : IsIso ((H).map ((r).app A)) :=
    Localization.inverts (H) (weakEquivalences C) _ (GeneratedFunctorialReplacements.unit_weak g A)
  apply (cancel_epi ((H).map ((r).app A))).mp
  have h := (r).naturality ((r).app A)
  change (r).app A ≫ (r).app ((R).obj A) = (r).app A ≫ (R).map ((r).app A) at h
  rw [← (H).map_comp, ← (H).map_comp]
  exact (H).congr_map h.symm

end HomotopicalAlgebra.OriginalOrdinaryFibrantJLoopComparison

namespace HomotopicalAlgebra.OriginalOrdinaryFibrantJLoopComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "H" => toHomotopyCategory C
local notation "L" => OriginalOrdinaryJLoopFunctor.loopFunctor g Z hZ
local notation "R" => GeneratedFunctorialReplacements.R g
local notation "r" => GeneratedFunctorialReplacements.unit g
local notation "Ω" => DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)

local instance generatedR_fibrant (A : C) : IsFibrant ((R).obj A) :=
  GeneratedFunctorialReplacements.R_isFibrant g A

/-- The original point-set loop functor respects every original Ho equality between fibrant maps. -/
theorem loopMap_hom_congr {A B : C} [IsFibrant A] [IsFibrant B] (f h : A ⟶ B)
    (hf : (H).map f = (H).map h) : (H).map ((L).map f) = (H).map ((L).map h) := by
  have hn (f' : A ⟶ B) := congrArg (fun q => (H).map q) (loopUnit_naturality g Z hZ f')
  have hAfter :
      (H).map ((L).map ((R).map f)) = (H).map ((L).map ((R).map h)) := by
    have hh := congrArg (fun q => (OriginalOrdinaryJLoopFunctor.hoFunctor Z hZ g).map q) hf
    rw [OriginalOrdinaryJLoopFunctor.hoFunctor_map, OriginalOrdinaryJLoopFunctor.hoFunctor_map] at hh
    exact hh
  have hnf := hn f
  have hnh := hn h
  simp only [Functor.map_comp] at hnf hnh
  change (H).map ((L).map f) ≫ (loopUnitIso g Z hZ B).hom =
      (loopUnitIso g Z hZ A).hom ≫ (H).map ((L).map ((R).map f)) at hnf
  change (H).map ((L).map h) ≫ (loopUnitIso g Z hZ B).hom =
      (loopUnitIso g Z hZ A).hom ≫ (H).map ((L).map ((R).map h)) at hnh
  apply (cancel_epi (loopUnitIso g Z hZ A).inv).mp
  apply (cancel_mono (loopUnitIso g Z hZ B).hom).mp
  simp only [Category.assoc]
  rw [hnf, hnh, Iso.inv_hom_id_assoc, hAfter]
  simp only [Iso.inv_hom_id_assoc]

/-- The two original R-unit maps are compared after the original J-loop functor by earned fibrant homotopy invariance.
-/
theorem loop_unit_R_unit_image (A : C) :
    (H).map ((L).map ((R).map ((r).app A))) = (H).map ((L).map ((r).app ((R).obj A))) := by
  let : IsFibrant ((R).obj A) := GeneratedFunctorialReplacements.R_isFibrant g A
  let : IsFibrant ((R).obj ((R).obj A)) := GeneratedFunctorialReplacements.R_isFibrant g ((R).obj A)
  exact loopMap_hom_congr g Z hZ _ _ (unit_R_unit_image g A)

/-- Actual derived ordinary loops on a fibrant original object compare with its SAME raw original J-loop carrier. -/
def rawLoopsIso (A : C) [IsFibrant A] : (Ω).obj ((H).obj A) ≅ (H).obj ((L).obj A) :=
  OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g A ≪≫ (loopUnitIso g Z hZ A).symm

/-- The earned raw-loop comparison retains every full original map between fibrant objects. -/
theorem rawLoopsIso_naturality {A B : C} [IsFibrant A] [IsFibrant B] (f : A ⟶ B) :
    (Ω).map ((H).map f) ≫ (rawLoopsIso g Z hZ B).hom =
      (rawLoopsIso g Z hZ A).hom ≫ (H).map ((L).map f) := by
  have hCore := OriginalOrdinaryJLoopFunctor.loopsIsoJ_naturality Z hZ g f
  change (Ω).map ((H).map f) ≫ (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g B).hom =
    (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g A).hom ≫ (H).map ((L).map ((R).map f)) at hCore
  have hn := congrArg (fun q => (H).map q) (loopUnit_naturality g Z hZ f)
  simp only [Functor.map_comp] at hn
  change (H).map ((L).map f) ≫ (loopUnitIso g Z hZ B).hom =
    (loopUnitIso g Z hZ A).hom ≫ (H).map ((L).map ((R).map f)) at hn
  have hInv :
      (H).map ((L).map ((R).map f)) ≫ (loopUnitIso g Z hZ B).inv =
        (loopUnitIso g Z hZ A).inv ≫ (H).map ((L).map f) := by
    exact (CommSq.vert_inv (show CommSq ((H).map ((L).map f))
      (loopUnitIso g Z hZ A).hom (loopUnitIso g Z hZ B).hom
      ((H).map ((L).map ((R).map f))) from ⟨hn⟩)).w
  simp only [rawLoopsIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hCore, Category.assoc, hInv]; simp only [Category.assoc]

/-- The original unit normalization retains BOTH distinct R-unit maps until their earned loop-image equality. -/
theorem rawLoopsIso_unit (A : C) :
    (Ω).map ((H).map ((r).app A)) ≫
        (rawLoopsIso g Z hZ ((R).obj A)).hom =
      (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g A).hom := by
  let : IsFibrant ((R).obj A) := GeneratedFunctorialReplacements.R_isFibrant g A
  have h := OriginalOrdinaryJLoopFunctor.loopsIsoJ_naturality Z hZ g ((r).app A)
  change (Ω).map ((H).map ((r).app A)) ≫
      (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g ((R).obj A)).hom =
    (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g A).hom ≫
      (H).map ((L).map ((R).map ((r).app A))) at h
  have hUnits := loop_unit_R_unit_image g Z hZ A
  simp only [rawLoopsIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, h, Category.assoc, hUnits]
  change (OriginalOrdinaryJLoopComparison.loopsIsoJ Z hZ g A).hom ≫
    (loopUnitIso g Z hZ ((R).obj A)).hom ≫ (loopUnitIso g Z hZ ((R).obj A)).inv = _
  simp only [Iso.hom_inv_id, Category.comp_id]

end HomotopicalAlgebra.OriginalOrdinaryFibrantJLoopComparison
