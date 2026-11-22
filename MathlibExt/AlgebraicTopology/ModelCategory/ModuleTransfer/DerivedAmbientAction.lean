/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.AmbientBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# The actual external derived ambient action on module homotopy categories

Both replacement factories are produced from the original generation and
original module source rank. The underlying action is the original ambient
TensorAction on the actual associative module category. The same actual
coefficient/module maps and Brown proofs invert all source weak maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA wC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra Opposite Functor
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (tA : RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C) A) I J κA)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

open CategoryTheory.HomogeneousLocalization.AmbientTensorHom
open CategoryTheory.HomogeneousLocalization

local notation "qA" => tA.replacements
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "M" => Mod C A

/-- The actual produced module model determines the original weak class on its same carrier. -/
abbrev moduleWeak : MorphismProperty M :=
  letI : ModelCategory M := tA.model
  weakEquivalences M

local notation "WA" => moduleWeak tA
local notation "HA" => MorphismProperty.Localization WA
local notation "HC" => MorphismProperty.Localization (weakEquivalences C)
local notation "πA" => MorphismProperty.Q WA
local notation "πC" => MorphismProperty.Q (weakEquivalences C)

/-- The original ambient tensor is evaluated on both actual generated Q objects. -/
def replaced : C ⥤ M ⥤ M := by
  let : ModelCategory M := tA.model
  exact (qC).Q ⋙ leftBifunctor A ⋙ (whiskeringLeft M M M).obj (qA).Q

/-- The raw external derived action retains the canonical projection of the original tensor module. -/
def raw : C ⥤ M ⥤ HA := replaced tA dC ⋙ (whiskeringRight M M HA).obj πA

/-- The actual coefficient and module Q maps invert every original weak pair. -/
theorem raw_inverts : MorphismProperty.IsInvertedBy₂ (weakEquivalences C) WA (raw tA dC) := by
  let : ModelCategory M := tA.model
  rintro ⟨U, N⟩ ⟨V, N'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  let : IsCofibrant ((qC).Q.obj U) := (qC).q_cofibrant U
  let : IsCofibrant ((qC).Q.obj V) := (qC).q_cofibrant V
  let : IsCofibrant ((qA).Q.obj N) := (qA).q_cofibrant N
  let : IsCofibrant ((qA).Q.obj N') := (qA).q_cofibrant N'
  have h₁ := AmbientBrown.coefficient_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    ((qA).Q.obj N) ((qC).Q.map f) ((qC).q_map_weak f hf)
  have h₂ := AmbientBrown.module_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    ((qC).Q.obj V) ((qA).Q.map g) ((qA).q_map_weak g hg)
  change IsIso ((πA).map ((AmbientBrown.coefficientFunctor ((qA).Q.obj N)).map ((qC).Q.map f)) ≫
    (πA).map ((Mod.AmbientTensor.functor A ((qC).Q.obj V)).map ((qA).Q.map g)))
  rw [← (πA).map_comp]
  exact Localization.inverts πA WA _ ((weakEquivalences M).comp_mem _ _ h₁ h₂)

/-- The actual ambient homotopy category acts on the original localized module carrier. -/
def action : HC ⥤ HA ⥤ HA := by
  let : ModelCategory M := tA.model
  exact Localization.lift₂ (raw tA dC) (raw_inverts tA dC) πC πA

instance actionLifting :
    Localization.Lifting₂ πC πA (weakEquivalences C) WA (raw tA dC) (action tA dC) := by
  let : ModelCategory M := tA.model
  unfold action
  infer_instance

/-- The complete actual source calculation retains every coefficient and module map. -/
def projectionIso :
    (((whiskeringLeft₂ HA).obj πC).obj πA).obj (action tA dC) ≅ raw tA dC :=
  Localization.Lifting₂.iso πC πA (weakEquivalences C) WA (raw tA dC) (action tA dC)

/-- Every original source pair keeps the actual ambient tensor of the two generated Q objects. -/
def comparison (U : C) (N : M) :
    letI : ModelCategory M := tA.model
    ((action tA dC).obj ((πC).obj U)).obj ((πA).obj N) ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj U) ((qA).Q.obj N)) := by
  letI : ModelCategory M := tA.model
  exact ((evaluation M HA).obj N).mapIso ((projectionIso tA dC).app U)

/-- The original whole right-to-left braiding and original module right unit give the left unit. -/
def pointSetLeftUnit : Mod.AmbientTensor.functor A (𝟙_ C) ≅ 𝟭 M :=
  (Mod.AmbientTensor.rightToLeftNatIso A (𝟙_ C)).symm ≪≫ Mod.AmbientTensor.rightUnitNatIso A

/-- The actual base unit replacement map is weak under every generated cofibrant module coefficient. -/
theorem unitCoefficientMap_weak [IsCofibrant (𝟙_ C)] (N : M) :
    letI : ModelCategory M := tA.model
    weakEquivalences M ((AmbientBrown.coefficientFunctor ((qA).Q.obj N)).map ((qC).q.app (𝟙_ C))) := by
  let : ModelCategory M := tA.model
  let : IsCofibrant ((qC).Q.obj (𝟙_ C)) := (qC).q_cofibrant (𝟙_ C)
  let : IsCofibrant ((𝟭 C).obj (𝟙_ C)) := (inferInstance : IsCofibrant (𝟙_ C))
  let : IsCofibrant ((qA).Q.obj N) := (qA).q_cofibrant N
  exact AmbientBrown.coefficient_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    ((qA).Q.obj N) ((qC).q.app (𝟙_ C)) ((qC).q_trivialFibration (𝟙_ C)).2

/-- The whole original Q-unit, point-set unit and module Q counit give the actual projected unit map. -/
def rawUnitMap (N : M) :
    letI : ModelCategory M := tA.model
    (πA).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj (𝟙_ C)) ((qA).Q.obj N)) ⟶ (πA).obj N := by
  let : ModelCategory M := tA.model
  exact (πA).map ((AmbientBrown.coefficientFunctor ((qA).Q.obj N)).map ((qC).q.app (𝟙_ C))) ≫
    (πA).map ((pointSetLeftUnit (A := A)).hom.app ((qA).Q.obj N)) ≫ (πA).map ((qA).q.app N)

/-- The actual projected unit map is invertible by the proved coefficient-unit preservation and original weak counit. -/
theorem rawUnitMap_isIso [IsCofibrant (𝟙_ C)] (N : M) : IsIso (rawUnitMap tA dC N) := by
  let : ModelCategory M := tA.model
  let : IsIso ((πA).map ((AmbientBrown.coefficientFunctor ((qA).Q.obj N)).map ((qC).q.app (𝟙_ C)))) :=
    Localization.inverts πA WA _ (unitCoefficientMap_weak tA dC N)
  let : IsIso ((πA).map ((qA).q.app N)) :=
    Localization.inverts πA WA _ ((qA).q_trivialFibration N).2
  unfold rawUnitMap
  infer_instance

/-- Every original module has the actual derived unit comparison, with no diagonal bimodule-cofibrancy premise. -/
def unitComparison [IsCofibrant (𝟙_ C)] (N : M) :
    ((action tA dC).obj ((πC).obj (𝟙_ C))).obj ((πA).obj N) ≅ (πA).obj N := by
  letI : ModelCategory M := tA.model
  letI : IsIso (rawUnitMap tA dC N) := rawUnitMap_isIso tA dC N
  exact comparison tA dC (𝟙_ C) N ≪≫ asIso (rawUnitMap tA dC N)

/-- The original coefficient Q counit, module unit and module Q counit form a whole natural map. -/
def rawUnitNatTrans : (raw tA dC).obj (𝟙_ C) ⟶ πA := by
  letI : ModelCategory M := tA.model
  change (((qA).Q ⋙ Mod.AmbientTensor.functor A ((qC).Q.obj (𝟙_ C))) ⋙ πA) ⟶ πA
  exact whiskerRight
    (whiskerLeft (qA).Q (Mod.AmbientTensor.coefficientNatTrans A ((qC).q.app (𝟙_ C))) ≫
      whiskerLeft (qA).Q (pointSetLeftUnit (A := A)).hom ≫
      (Functor.rightUnitor (qA).Q).hom ≫ (qA).q) πA ≫
    (Functor.leftUnitor πA).hom

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The complete natural unit map has exactly the previously constructed original component. -/
theorem rawUnitNatTrans_app (N : M) :
    (rawUnitNatTrans tA dC).app N = rawUnitMap tA dC N := by
  let : ModelCategory M := tA.model
  have h : (πA).map
      (Mod.AmbientTensor.map A ((qC).q.app (𝟙_ C)) (𝟙 ((qA).Q.obj N)) ≫
        (pointSetLeftUnit (A := A)).hom.app ((qA).Q.obj N) ≫
        𝟙 ((qA).Q.obj N) ≫ (qA).q.app N) ≫ 𝟙 ((πA).obj N) =
    (πA).map (Mod.AmbientTensor.map A ((qC).q.app (𝟙_ C)) (𝟙 ((qA).Q.obj N))) ≫
      (πA).map ((pointSetLeftUnit (A := A)).hom.app ((qA).Q.obj N)) ≫ (πA).map ((qA).q.app N) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [(πA).map_id, Category.id_comp, Category.comp_id]
  exact h

/-- The actual source natural unit is invertible at every original module. -/
def rawUnitNatIso [IsCofibrant (𝟙_ C)] : (raw tA dC).obj (𝟙_ C) ≅ πA := by
  letI : ModelCategory M := tA.model
  refine NatIso.ofComponents (fun N => ?_) (fun {N N'} p => ?_)
  · letI : IsIso (rawUnitMap tA dC N) := rawUnitMap_isIso tA dC N
    exact asIso (rawUnitMap tA dC N)
  · simpa only [asIso_hom, rawUnitNatTrans_app] using (rawUnitNatTrans tA dC).naturality p

/-- The original two-variable lifting also retains the complete unit coefficient source functor. -/
instance unitActionLifting :
    Localization.Lifting πA WA ((raw tA dC).obj (𝟙_ C))
      ((action tA dC).obj ((πC).obj (𝟙_ C))) :=
  ⟨(projectionIso tA dC).app (𝟙_ C)⟩

/-- The actual derived unit is a natural isomorphism on the entire original module localization. -/
def unitIso [IsCofibrant (𝟙_ C)] :
    (action tA dC).obj ((πC).obj (𝟙_ C)) ≅ 𝟭 HA :=
  Localization.liftNatIso πA WA ((raw tA dC).obj (𝟙_ C)) πA
    ((action tA dC).obj ((πC).obj (𝟙_ C))) (𝟭 HA) (rawUnitNatIso tA dC)

/-- The whole localized natural unit retains the exact original projected unit component. -/
theorem unitIso_hom_app [IsCofibrant (𝟙_ C)] (N : M) :
    (unitIso tA dC).hom.app ((πA).obj N) = (unitComparison tA dC N).hom := by
  let : ModelCategory M := tA.model
  change (Localization.liftNatTrans πA WA ((raw tA dC).obj (𝟙_ C)) πA
    ((action tA dC).obj ((πC).obj (𝟙_ C))) (𝟭 HA) (rawUnitNatIso tA dC).hom).app ((πA).obj N) = _
  rw [Localization.liftNatTrans_app]
  change (comparison tA dC (𝟙_ C) N).hom ≫ rawUnitMap tA dC N ≫ 𝟙 ((πA).obj N) =
    (comparison tA dC (𝟙_ C) N).hom ≫ rawUnitMap tA dC N
  exact congrArg ((comparison tA dC (𝟙_ C) N).hom ≫ ·) (Category.comp_id (rawUnitMap tA dC N))

end HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction
