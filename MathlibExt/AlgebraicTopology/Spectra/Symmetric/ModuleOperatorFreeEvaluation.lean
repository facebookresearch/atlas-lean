/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.ModuleOperatorEquivalence
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The original generic sphere free/evaluation adjunctions agree

The existing ordinary Day free spectra and the actual enriched operator
free spectra represent the same complete evaluation functor. Their natural
isomorphism is derived from the original adjunction universal properties.
Both selected Hom functions and both complete unit/counit maps are retained.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V]

/-- The actual original enriched operator free spectrum at every finite index. -/
def genericSphereOperatorFreeAt (T : V) (n : I) : V ⥤ GenericSphereOperatorSpectra T := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedFunctorCat.Free.functor n

/-- The actual original enriched operator evaluation at every finite index. -/
def genericSphereOperatorEvaluation (T : V) (n : I) : GenericSphereOperatorSpectra T ⥤ V := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedFunctorCat.evaluation n

/-- The full selected original genuine free/evaluation adjunction on the actual operator. -/
def genericSphereOperatorFreeEvaluationAdjunction (T : V) (n : I) :
    genericSphereOperatorFreeAt T n ⊣ genericSphereOperatorEvaluation T n := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedFunctorCat.Free.adjunction n

/-- Every original enriched free level is its whole operator Hom tensor coefficient. -/
theorem genericSphereOperatorFreeAt_obj (T : V) (n k : I) (K : V) :
    genericSphereOperatorObject T ((genericSphereOperatorFreeAt T n).obj K) k =
      K ⊗ Spectra.Symmetric.OperatorCoend.Hom T n k := rfl

/-- Every original enriched free map retains its entire Hom coefficient. -/
theorem genericSphereOperatorFreeAt_map (T : V) (n k : I) {K L : V} (h : K ⟶ L) :
    genericSphereOperatorComponent T ((genericSphereOperatorFreeAt T n).map h) k =
      h ▷ Spectra.Symmetric.OperatorCoend.Hom T n k := by
  let _ : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedFunctorCat.Free.coefficientMap_component n h k

/-- Every original enriched free action retains the complete actual operator composition map. -/
theorem genericSphereOperatorFreeAt_action (T : V) (n k l : I) (K : V) :
    MonoidalClosed.uncurry (genericSphereOperatorHomMap T ((genericSphereOperatorFreeAt T n).obj K) k l) =
      (α_ K (Spectra.Symmetric.OperatorCoend.Hom T n k) (Spectra.Symmetric.OperatorCoend.Hom T k l)).hom ≫
        K ◁ Spectra.Symmetric.OperatorCoend.composition T n k l :=
  MonoidalClosed.uncurry_curry _

/-- Evaluation on the actual ordinary module carrier is preserved by the genuine enriched equivalence. -/
def genericSphereModuleOperatorEvaluationIso (T : V) (n : I) :
    (genericSphereModuleOperatorEquivalence T).functor ⋙ genericSphereOperatorEvaluation T n ≅
      genericSpectrumEvaluation T n :=
  NatIso.ofComponents (fun M => Iso.refl (M.X.functor.obj n)) (fun f => by
    change genericSphereOperatorComponent T ((genericSphereModuleOperatorEquivalence T).functor.map f) n ≫
        𝟙 _ = 𝟙 _ ≫ f.hom.natTrans.app n
    rw [genericSphereModuleOperatorEquivalence_map]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Inverse reconstruction preserves the same complete original evaluation functor. -/
def genericSphereOperatorModuleEvaluationIso (T : V) (n : I) :
    (genericSphereModuleOperatorEquivalence T).inverse ⋙ genericSpectrumEvaluation T n ≅
      genericSphereOperatorEvaluation T n :=
  Functor.isoWhiskerLeft (genericSphereModuleOperatorEquivalence T).inverse
    (genericSphereModuleOperatorEvaluationIso T n).symm ≪≫
    (Functor.associator (genericSphereModuleOperatorEquivalence T).inverse
      (genericSphereModuleOperatorEquivalence T).functor (genericSphereOperatorEvaluation T n)).symm ≪≫
    Functor.isoWhiskerRight (genericSphereModuleOperatorEquivalence T).counitIso
      (genericSphereOperatorEvaluation T n) ≪≫ Functor.leftUnitor (genericSphereOperatorEvaluation T n)

/-- The original ordinary free adjunction, through the actual carrier equivalence, evaluates the same spectrum. -/
def genericSphereModuleOperatorFreeAdjunction (T : V) (n : I) :
    genericSpectrumFreeAt T n ⋙ (genericSphereModuleOperatorEquivalence T).functor ⊣
      genericSphereOperatorEvaluation T n :=
  ((genericSpectrumFreeAtEvaluationAdjunction T n).comp
    (genericSphereModuleOperatorEquivalence T).toAdjunction).ofNatIsoRight
      (genericSphereOperatorModuleEvaluationIso T n)

/-- The actual original ordinary Day free spectrum is the actual original enriched operator free spectrum. -/
def genericSphereModuleOperatorFreeIso (T : V) (n : I) :
    genericSpectrumFreeAt T n ⋙ (genericSphereModuleOperatorEquivalence T).functor ≅
      genericSphereOperatorFreeAt T n :=
  Adjunction.leftAdjointUniq (genericSphereModuleOperatorFreeAdjunction T n)
    (genericSphereOperatorFreeEvaluationAdjunction T n)

/-- Every original base map is preserved naturally by the actual free-spectrum comparison. -/
theorem genericSphereModuleOperatorFreeIso_natural (T : V) (n : I) {K L : V} (h : K ⟶ L) :
    (genericSpectrumFreeAt T n ⋙ (genericSphereModuleOperatorEquivalence T).functor).map h ≫
        (genericSphereModuleOperatorFreeIso T n).hom.app L =
      (genericSphereModuleOperatorFreeIso T n).hom.app K ≫ (genericSphereOperatorFreeAt T n).map h :=
  (genericSphereModuleOperatorFreeIso T n).hom.naturality h

/-- The full original units agree under the natural free-spectrum comparison. -/
theorem genericSphereModuleOperatorFreeIso_unit (T : V) (n : I) (K : V) :
    (genericSphereModuleOperatorFreeAdjunction T n).unit.app K ≫
        (genericSphereOperatorEvaluation T n).map ((genericSphereModuleOperatorFreeIso T n).hom.app K) =
      (genericSphereOperatorFreeEvaluationAdjunction T n).unit.app K :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ K

/-- The full original counits agree under the natural free-spectrum comparison. -/
theorem genericSphereModuleOperatorFreeIso_counit (T : V) (n : I) (F : GenericSphereOperatorSpectra T) :
    (genericSphereModuleOperatorFreeIso T n).hom.app ((genericSphereOperatorEvaluation T n).obj F) ≫
        (genericSphereOperatorFreeEvaluationAdjunction T n).counit.app F =
      (genericSphereModuleOperatorFreeAdjunction T n).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

/-- Both original selected adjunctions have the same complete forward Hom function. -/
theorem genericSphereModuleOperatorFreeIso_hom (T : V) (n : I) (K : V) (F : GenericSphereOperatorSpectra T)
    (f : (genericSphereOperatorFreeAt T n).obj K ⟶ F) :
    (genericSphereModuleOperatorFreeAdjunction T n).homEquiv K F
        ((genericSphereModuleOperatorFreeIso T n).hom.app K ≫ f) =
      (genericSphereOperatorFreeEvaluationAdjunction T n).homEquiv K F f := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    genericSphereModuleOperatorFreeIso_unit]

/-- Both original selected adjunctions have the same complete inverse Hom function. -/
theorem genericSphereModuleOperatorFreeIso_hom_inverse (T : V) (n : I) (K : V)
    (F : GenericSphereOperatorSpectra T) (h : K ⟶ (genericSphereOperatorEvaluation T n).obj F) :
    ((genericSphereModuleOperatorFreeAdjunction T n).homEquiv K F).symm h =
      (genericSphereModuleOperatorFreeIso T n).hom.app K ≫
        ((genericSphereOperatorFreeEvaluationAdjunction T n).homEquiv K F).symm h := by
  apply ((genericSphereModuleOperatorFreeAdjunction T n).homEquiv K F).injective
  rw [Equiv.apply_symm_apply, genericSphereModuleOperatorFreeIso_hom, Equiv.apply_symm_apply]

/-- The full original ordinary free/evaluation construction satisfies its selected first triangle. -/
theorem genericSphereModuleOperatorFree_left_triangle (T : V) (n : I) (K : V) :
    (genericSpectrumFreeAt T n ⋙ (genericSphereModuleOperatorEquivalence T).functor).map
        ((genericSphereModuleOperatorFreeAdjunction T n).unit.app K) ≫
      (genericSphereModuleOperatorFreeAdjunction T n).counit.app
        ((genericSpectrumFreeAt T n ⋙ (genericSphereModuleOperatorEquivalence T).functor).obj K) =
      𝟙 _ := (genericSphereModuleOperatorFreeAdjunction T n).left_triangle_components K

/-- The full original evaluation construction satisfies its selected second triangle. -/
theorem genericSphereModuleOperatorFree_right_triangle (T : V) (n : I) (F : GenericSphereOperatorSpectra T) :
    (genericSphereModuleOperatorFreeAdjunction T n).unit.app ((genericSphereOperatorEvaluation T n).obj F) ≫
      (genericSphereOperatorEvaluation T n).map
        ((genericSphereModuleOperatorFreeAdjunction T n).counit.app F) =
      𝟙 _ := (genericSphereModuleOperatorFreeAdjunction T n).right_triangle_components F

end CategoryTheory
