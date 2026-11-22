/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/


import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalSmithModel
import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
import MathlibExt.AlgebraicTopology.ModelCategory.PointedFramingAction
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
import MathlibExt.AlgebraicTopology.ModelCategory.InjectiveDiagramEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CanonicalGeneration
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftRealizationWeak
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type

/-!
# Original diagram replacements and derived limits and colimits

Every diagram object, diagram map, replacement arrow and caller cone/cocone
is retained. The actual limit and colimit universal properties construct
the whole comparison maps before passing to the original localization.
-/

set_option autoImplicit false
noncomputable section
universe uJ vJ uC vC w uD z uE vE
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.DerivedDiagramConstructions



variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory (J ⥤ C)]
  (d : GeneratedFunctorialReplacements.Data (C := J ⥤ C))

section Limits
variable [HasLimitsOfShape J C]

/-- The actual original fibrant-diagram replacement followed by the ordinary limit. -/
def homotopyLimit : (J ⥤ C) ⥤ C := d.R ⋙ lim

/-- Every original object is replaced as a whole diagram before its actual limit is taken. -/
theorem homotopyLimit_obj (F : J ⥤ C) :
    (homotopyLimit d).obj F = limit (d.R.obj F) := rfl

/-- Every original whole-diagram map retains the original R map and actual limit map. -/
theorem homotopyLimit_map {F G : J ⥤ C} (a : F ⟶ G) :
    (homotopyLimit d).map a = lim.map (d.R.map a) := rfl

/-- The full original limit-to-homotopy-limit comparison is induced by the original R unit. -/
def limitComparison : (lim : (J ⥤ C) ⥤ C) ⟶ homotopyLimit d :=
  Functor.whiskerRight d.r lim

/-- Its entire original component is the actual limit map of the original replacement unit. -/
theorem limitComparison_app (F : J ⥤ C) :
    (limitComparison d).app F = lim.map (d.r.app F) := rfl

/-- Every original diagram vertex retains its actual replacement projection. -/
def limitProjection (F : J ⥤ C) (j : J) : (homotopyLimit d).obj F ⟶ (d.R.obj F).obj j :=
  limit.π _ j

/-- The complete limiting cone on the actual original R diagram. -/
def limitCone (F : J ⥤ C) : Cone (d.R.obj F) := limit.cone _

/-- The full actual universal property of that same R-diagram cone. -/
def limitConeIsLimit (F : J ⥤ C) : IsLimit (limitCone d F) := limit.isLimit _

/-- Every caller cone keeps its point and each original leg followed by the same R unit. -/
def replacedCone (F : J ⥤ C) (c : Cone F) : Cone (d.R.obj F) where
  pt := c.pt
  π := c.π ≫ d.r.app F

/-- The caller's whole actual map into the homotopy limit. -/
def lift (F : J ⥤ C) (c : Cone F) : c.pt ⟶ (homotopyLimit d).obj F :=
  limit.lift _ (replacedCone d F c)

/-- Every original caller leg is retained through the original R unit. -/
theorem lift_projection (F : J ⥤ C) (c : Cone F) (j : J) :
    lift d F c ≫ limitProjection d F j = c.π.app j ≫ (d.r.app F).app j :=
  limit.lift_π _ j

/-- The full original replacement legs uniquely determine the caller's whole map. -/
theorem lift_unique (F : J ⥤ C) (c : Cone F) (m : c.pt ⟶ (homotopyLimit d).obj F)
    (hm : ∀ j, m ≫ limitProjection d F j = c.π.app j ≫ (d.r.app F).app j) :
    m = lift d F c := by
  apply limit.hom_ext
  intro j
  exact (hm j).trans (lift_projection d F c j).symm

/-- Every whole diagram map retains every actual R-projection square. -/
theorem map_projection {F G : J ⥤ C} (a : F ⟶ G) (j : J) :
    (homotopyLimit d).map a ≫ limitProjection d G j =
      limitProjection d F j ≫ (d.R.map a).app j := limMap_π _ j

/-- The original comparison retains every actual original diagram leg. -/
theorem comparison_projection (F : J ⥤ C) (j : J) :
    (limitComparison d).app F ≫ limitProjection d F j =
      limit.π F j ≫ (d.r.app F).app j := limMap_π _ j

omit [HasLimitsOfShape J C] in
/-- Every original index arrow remains in the replacement-unit square. -/
theorem original_limit_index_square (F : J ⥤ C) {i j : J} (a : i ⟶ j) :
    F.map a ≫ (d.r.app F).app j = (d.r.app F).app i ≫ (d.R.obj F).map a :=
  (d.r.app F).naturality a

end Limits

section Colimits
variable [HasColimitsOfShape J C]

/-- The actual original cofibrant-diagram replacement followed by the ordinary colimit. -/
def homotopyColimit : (J ⥤ C) ⥤ C := d.Q ⋙ colim

/-- Every original object is replaced as a whole diagram before its actual colimit is taken. -/
theorem homotopyColimit_obj (F : J ⥤ C) :
    (homotopyColimit d).obj F = colimit (d.Q.obj F) := rfl

/-- Every original whole-diagram map retains the original Q map and actual colimit map. -/
theorem homotopyColimit_map {F G : J ⥤ C} (a : F ⟶ G) :
    (homotopyColimit d).map a = colim.map (d.Q.map a) := rfl

/-- The entire original homotopy-colimit comparison is induced by the same Q counit. -/
def colimitComparison : homotopyColimit d ⟶ (colim : (J ⥤ C) ⥤ C) :=
  Functor.whiskerRight d.q colim

/-- Its entire original component is the actual colimit map of the original Q counit. -/
theorem colimitComparison_app (F : J ⥤ C) :
    (colimitComparison d).app F = colim.map (d.q.app F) := rfl

/-- Every original diagram vertex retains its actual Q-replacement injection. -/
def colimitInjection (F : J ⥤ C) (j : J) :
    (d.Q.obj F).obj j ⟶ (homotopyColimit d).obj F := colimit.ι _ j

/-- The entire actual colimiting cocone on the original Q diagram. -/
def colimitCocone (F : J ⥤ C) : Cocone (d.Q.obj F) := colimit.cocone _

/-- The full actual universal property of that same Q-diagram cocone. -/
def colimitCoconeIsColimit (F : J ⥤ C) : IsColimit (colimitCocone d F) := colimit.isColimit _

/-- Every caller cocone keeps its point and each original leg preceded by the same Q counit. -/
def replacedCocone (F : J ⥤ C) (c : Cocone F) : Cocone (d.Q.obj F) where
  pt := c.pt
  ι := d.q.app F ≫ c.ι

/-- The caller's entire actual map out of the homotopy colimit. -/
def desc (F : J ⥤ C) (c : Cocone F) : (homotopyColimit d).obj F ⟶ c.pt :=
  colimit.desc _ (replacedCocone d F c)

/-- Every original caller leg is retained after the original Q counit. -/
theorem injection_desc (F : J ⥤ C) (c : Cocone F) (j : J) :
    colimitInjection d F j ≫ desc d F c = (d.q.app F).app j ≫ c.ι.app j :=
  colimit.ι_desc _ j

/-- The original replacement legs uniquely determine the caller's whole map. -/
theorem desc_unique (F : J ⥤ C) (c : Cocone F) (m : (homotopyColimit d).obj F ⟶ c.pt)
    (hm : ∀ j, colimitInjection d F j ≫ m = (d.q.app F).app j ≫ c.ι.app j) :
    m = desc d F c := by
  apply colimit.hom_ext
  intro j
  exact (hm j).trans (injection_desc d F c j).symm

/-- Every whole diagram map retains every actual Q-injection square. -/
theorem injection_map {F G : J ⥤ C} (a : F ⟶ G) (j : J) :
    colimitInjection d F j ≫ (homotopyColimit d).map a =
      (d.Q.map a).app j ≫ colimitInjection d G j := ι_colimMap _ j

/-- The original comparison retains every actual original diagram injection. -/
theorem injection_comparison (F : J ⥤ C) (j : J) :
    colimitInjection d F j ≫ (colimitComparison d).app F =
      (d.q.app F).app j ≫ colimit.ι F j := ι_colimMap _ j

omit [HasColimitsOfShape J C] in
/-- Every original index arrow remains in the actual Q-counit square. -/
theorem original_colimit_index_square (F : J ⥤ C) {i j : J} (a : i ⟶ j) :
    (d.Q.obj F).map a ≫ (d.q.app F).app j = (d.q.app F).app i ≫ F.map a :=
  (d.q.app F).naturality a

end Colimits
section QuillenColimits

variable [ModelCategory C] [HasColimitsOfShape J C]
  (hF : fibrations (J ⥤ C) = (fibrations C).functorCategory J)
  (hT : trivialFibrations (J ⥤ C) = (trivialFibrations C).functorCategory J)

include hF hT

/-- The original colimit and constant functors are Quillen from the original diagram right classes. -/
theorem colimit_isQuillen :
    (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction :=
by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y a ha
    rw [hF]
    intro j
    exact ha
  · intro X Y a ha
    rw [hT]
    intro j
    exact ha

/-- Every original weak diagram map gives a weak actual homotopy-colimit map. -/
theorem homotopyColimit_map_weak {F G : J ⥤ C} (a : F ⟶ G)
    (ha : weakEquivalences (J ⥤ C) a) :
    weakEquivalences C ((homotopyColimit d).map a) := by
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := colimit_isQuillen hF hT
  let _ : IsCofibrant (d.Q.obj F) := d.q_cofibrant F
  let _ : IsCofibrant (d.Q.obj G) := d.q_cofibrant G
  let _ : WeakEquivalence (d.Q.map a) := (weakEquivalence_iff _).mpr (d.q_map_weak a ha)
  let _ : WeakEquivalence (colim.map (d.Q.map a)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := colimConstAdj) _
  exact (weakEquivalence_iff _).mp (inferInstanceAs (WeakEquivalence (colim.map (d.Q.map a))))

/-- Objectwise original weak maps are sufficient on the same actual diagram model. -/
theorem homotopyColimit_map_objectwise_weak
    (hW : weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J)
    {F G : J ⥤ C} (a : F ⟶ G) (ha : ∀ j, weakEquivalences C (a.app j)) :
    weakEquivalences C ((homotopyColimit d).map a) :=
  homotopyColimit_map_weak d hF hT a (by rw [hW]; exact ha)

/-- The actual Q-comparison computes the homotopy colimit on every genuinely cofibrant diagram. -/
theorem colimitComparison_weak (F : J ⥤ C) [IsCofibrant F] :
    weakEquivalences C ((colimitComparison d).app F) := by
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := colimit_isQuillen hF hT
  let _ : IsCofibrant (d.Q.obj F) := d.q_cofibrant F
  let _ : IsCofibrant ((𝟭 (J ⥤ C)).obj F) := inferInstanceAs (IsCofibrant F)
  let _ : WeakEquivalence (d.q.app F) := (weakEquivalence_iff _).mpr (d.q_trivialFibration F).2
  let _ : WeakEquivalence (colim.map (d.q.app F)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := colimConstAdj) _
  exact (weakEquivalence_iff _).mp (inferInstanceAs (WeakEquivalence (colim.map (d.q.app F))))

/-- The genuine left derived colimit, with its same original diagram Q and every colimit map. -/
def derivedColimit :
    (weakEquivalences (J ⥤ C)).Localization ⥤ (weakEquivalences C).Localization := by
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := colimit_isQuillen hF hT
  exact DerivedFunctorCoherence.left colimConstAdj d

/-- Its entire original projection is the same homotopy-colimit functor followed by localization. -/
theorem derivedColimit_projection :
    (weakEquivalences (J ⥤ C)).Q ⋙ derivedColimit d hF hT =
      homotopyColimit d ⋙ (weakEquivalences C).Q := by
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := colimit_isQuillen hF hT
  exact DerivedFunctorCoherence.left_projection colimConstAdj d

/-- Every original map retains the actual Q diagram map and actual colimit map after localization. -/
theorem derivedColimit_map {F G : J ⥤ C} (a : F ⟶ G) :
    (derivedColimit d hF hT).map ((weakEquivalences (J ⥤ C)).Q.map a) =
      (weakEquivalences C).Q.map (colim.map (d.Q.map a)) :=
  Functor.congr_hom (derivedColimit_projection d hF hT) a

end QuillenColimits

section QuillenLimits

variable [ModelCategory C] [HasLimitsOfShape J C]
  (hC : cofibrations (J ⥤ C) = (cofibrations C).functorCategory J)
  (hT : trivialCofibrations (J ⥤ C) = (trivialCofibrations C).functorCategory J)

include hC hT

/-- The original constant and limit functors are Quillen from the original diagram left classes. -/
theorem limit_isQuillen :
    (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := by
  constructor
  · intro X Y a ha
    rw [hC]
    intro j
    exact ha
  · intro X Y a ha
    rw [hT]
    intro j
    exact ha

/-- Every original weak diagram map gives a weak actual homotopy-limit map. -/
theorem homotopyLimit_map_weak {F G : J ⥤ C} (a : F ⟶ G)
    (ha : weakEquivalences (J ⥤ C) a) :
    weakEquivalences C ((homotopyLimit d).map a) := by
  let _ : (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := limit_isQuillen hC hT
  let _ : IsFibrant (d.R.obj F) := d.r_fibrant F
  let _ : IsFibrant (d.R.obj G) := d.r_fibrant G
  let _ : WeakEquivalence (d.R.map a) := (weakEquivalence_iff _).mpr (d.r_map_weak a ha)
  let _ : WeakEquivalence (lim.map (d.R.map a)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := constLimAdj) _
  exact (weakEquivalence_iff _).mp (inferInstanceAs (WeakEquivalence (lim.map (d.R.map a))))

/-- Objectwise original weak maps are sufficient on the same actual diagram model. -/
theorem homotopyLimit_map_objectwise_weak
    (hW : weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J)
    {F G : J ⥤ C} (a : F ⟶ G) (ha : ∀ j, weakEquivalences C (a.app j)) :
    weakEquivalences C ((homotopyLimit d).map a) :=
  homotopyLimit_map_weak d hC hT a (by rw [hW]; exact ha)

/-- The actual R-comparison computes the homotopy limit on every genuinely fibrant diagram. -/
theorem limitComparison_weak (F : J ⥤ C) [IsFibrant F] :
    weakEquivalences C ((limitComparison d).app F) := by
  let _ : (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := limit_isQuillen hC hT
  let _ : IsFibrant (d.R.obj F) := d.r_fibrant F
  let _ : IsFibrant ((𝟭 (J ⥤ C)).obj F) := inferInstanceAs (IsFibrant F)
  let _ : WeakEquivalence (d.r.app F) := (weakEquivalence_iff _).mpr (d.r_trivialCofibration F).2
  let _ : WeakEquivalence (lim.map (d.r.app F)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := constLimAdj) _
  exact (weakEquivalence_iff _).mp (inferInstanceAs (WeakEquivalence (lim.map (d.r.app F))))

/-- The genuine right derived limit, with its same original diagram R and every limit map. -/
def derivedLimit :
    (weakEquivalences (J ⥤ C)).Localization ⥤ (weakEquivalences C).Localization := by
  let _ : (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := limit_isQuillen hC hT
  exact DerivedFunctorCoherence.right constLimAdj d

/-- Its entire original projection is the same homotopy-limit functor followed by localization. -/
theorem derivedLimit_projection :
    (weakEquivalences (J ⥤ C)).Q ⋙ derivedLimit d hC hT =
      homotopyLimit d ⋙ (weakEquivalences C).Q := by
  let _ : (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := limit_isQuillen hC hT
  exact DerivedFunctorCoherence.right_projection constLimAdj d

/-- Every original map retains the actual R diagram map and actual limit map after localization. -/
theorem derivedLimit_map {F G : J ⥤ C} (a : F ⟶ G) :
    (derivedLimit d hC hT).map ((weakEquivalences (J ⥤ C)).Q.map a) =
      (weakEquivalences C).Q.map (lim.map (d.R.map a)) :=
  Functor.congr_hom (derivedLimit_projection d hC hT) a

end QuillenLimits

end HomotopicalAlgebra.DerivedDiagramConstructions



namespace HomotopicalAlgebra.DerivedDiagramConstructions

section LiftedFrameHom

variable {C : Type uC} [Category.{vC} C]

/-- The actual degreewise frame Hom, with only its scalar value universe enlarged. -/
def liftedLeftHomFunctor (A : CosimplicialObject C) : C ⥤ SSet.{max z vC} :=
  Presheaf.restrictedULiftYoneda.{z} A

/-- The higher-universe Hom is the same complete original resolution Hom under `ULift`. -/
def liftedLeftHomIso (A : CosimplicialObject C) :
    liftedLeftHomFunctor.{uC, vC, z} A ≅
      PointedFramingAction.leftHomFunctor A ⋙ SSet.uliftFunctor.{z, vC} :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    ext x
    apply ULift.ext
    change A.map f.unop ≫ x.down = (ResolutionHomComplex.left A Y).map f x.down
    exact (ResolutionHomComplex.left_map_apply A Y f x.down).symm)) (by
    intro X Y f
    ext n x
    apply ULift.ext
    rfl)

/-- Both scalar transports retain the exact original degreewise coefficient map. -/
theorem liftedLeftHom_map_app (A : CosimplicialObject C) {X Y : C} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (x : ((liftedLeftHomFunctor.{uC, vC, z} A).obj X).obj n) :
    ((liftedLeftHomFunctor.{uC, vC, z} A).map f).app n x = ULift.up (x.down ≫ f) := rfl

variable [HasColimitsOfSize.{0, max z vC} C]

/-- The actual left Kan extension of the whole original frame along the higher-universe simplex functor. -/
def liftedTensor (A : CosimplicialObject C) : SSet.{max z vC} ⥤ C :=
  (uliftYoneda.{max z vC} (C := SimplexCategory)).leftKanExtension A

/-- The genuine higher-universe scalar frame adjunction is produced by the original simplex colimits. -/
def liftedTensorHomAdjunction (A : CosimplicialObject C) :
    liftedTensor.{uC, vC, z} A ⊣ liftedLeftHomFunctor.{uC, vC, z} A :=
  Presheaf.uliftYonedaAdjunction.{z}
    ((uliftYoneda.{max z vC} (C := SimplexCategory)).leftKanExtension A)
    ((uliftYoneda.{max z vC} (C := SimplexCategory)).leftKanExtensionUnit A)

variable {J : Type uJ} [Category.{vJ} J]

/-- Every original caller cone gives the whole scalar cone, with all its original legs. -/
def liftedLeftHomCone (A : CosimplicialObject C) {F : J ⥤ C} (c : Cone F) :
    Cone (F ⋙ liftedLeftHomFunctor.{uC, vC, z} A) :=
  (liftedLeftHomFunctor.{uC, vC, z} A).mapCone c

omit [HasColimitsOfSize.{0, max z vC} C] in
/-- The scalar cone keeps the actual degreewise postcomposition by every original caller leg. -/
theorem liftedLeftHomCone_projection (A : CosimplicialObject C) {F : J ⥤ C}
    (c : Cone F) (j : J) :
    (liftedLeftHomCone.{uJ, vJ, uC, vC, z} A c).π.app j = (liftedLeftHomFunctor.{uC, vC, z} A).map (c.π.app j) := rfl

/-- The actual scalar adjunction preserves the entire caller's limit universal property. -/
def liftedLeftHomConeIsLimit (A : CosimplicialObject C) {F : J ⥤ C}
    (c : Cone F) (hc : IsLimit c) : IsLimit (liftedLeftHomCone.{uJ, vJ, uC, vC, z} A c) := by
  let _ : PreservesLimitsOfSize.{vJ, uJ} (liftedLeftHomFunctor.{uC, vC, z} A) :=
    (liftedTensorHomAdjunction.{uC, vC, z} A).rightAdjoint_preservesLimits
  exact isLimitOfPreserves _ hc

variable [HasLimitsOfShape J C] [HasLimitsOfShape J SSet.{max z vC}]

/-- The full original frame Hom of a limit is the actual limit of the same degreewise mapping diagram. -/
def liftedLeftLimitIso (A : CosimplicialObject C) (F : J ⥤ C) :
    (liftedLeftHomFunctor.{uC, vC, z} A).obj (limit F) ≅ limit (F ⋙ liftedLeftHomFunctor.{uC, vC, z} A) := by
  let _ : PreservesLimitsOfSize.{vJ, uJ} (liftedLeftHomFunctor.{uC, vC, z} A) :=
    (liftedTensorHomAdjunction.{uC, vC, z} A).rightAdjoint_preservesLimits
  exact preservesLimitIso (liftedLeftHomFunctor.{uC, vC, z} A) F

/-- Every forward limit leg remains the original frame Hom function of the caller's projection. -/
theorem liftedLeftLimitIso_hom_projection (A : CosimplicialObject C) (F : J ⥤ C) (j : J) :
    (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).hom ≫ limit.π _ j =
      (liftedLeftHomFunctor.{uC, vC, z} A).map (limit.π F j) := by
  let _ : PreservesLimitsOfSize.{vJ, uJ} (liftedLeftHomFunctor.{uC, vC, z} A) :=
    (liftedTensorHomAdjunction.{uC, vC, z} A).rightAdjoint_preservesLimits
  exact preservesLimitIso_hom_π _ _ j

/-- Every inverse limit leg recovers the same original projection function. -/
theorem liftedLeftLimitIso_inv_projection (A : CosimplicialObject C) (F : J ⥤ C) (j : J) :
    (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).inv ≫ (liftedLeftHomFunctor.{uC, vC, z} A).map (limit.π F j) =
      limit.π _ j := by
  let _ : PreservesLimitsOfSize.{vJ, uJ} (liftedLeftHomFunctor.{uC, vC, z} A) :=
    (liftedTensorHomAdjunction.{uC, vC, z} A).rightAdjoint_preservesLimits
  exact preservesLimitIso_inv_π _ _ j

end LiftedFrameHom

end HomotopicalAlgebra.DerivedDiagramConstructions

namespace HomotopicalAlgebra.DerivedDiagramConstructions

section OriginalProjective

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)

/-- The same original coefficient generation and actual index construct the projective model. -/
@[instance_reducible]
def projectiveModel : ModelCategory (J ⥤ C) :=
  FunctorProjective.SourceConstruction.FromData.modelCategory g s

/-- Both original projective factor factories construct the whole-diagram replacements. -/
def projectiveReplacements :
    letI := projectiveModel g s
    GeneratedFunctorialReplacements.Data (C := J ⥤ C) := by
  letI := projectiveModel g s
  exact GeneratedFunctorialReplacements.fromGeneration
    (FunctorProjective.SourceConstruction.FromData.generationData g s)

/-- The original projective model gives a genuine native colimit Quillen pair. -/
theorem projectiveColimit_isQuillen [HasColimitsOfShape J C] :
    let _ := projectiveModel g s
    (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := by
  let _ := projectiveModel g s
  obtain ⟨_, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  exact colimit_isQuillen hF hT

/-- The original projective Q diagram followed by its actual colimit. -/
def projectiveHomotopyColimit [HasColimitsOfShape J C] : (J ⥤ C) ⥤ C := by
  letI := projectiveModel g s
  exact homotopyColimit (projectiveReplacements g s)

/-- Every original projective index and coefficient map survives in the whole replacement. -/
theorem projectiveHomotopyColimit_map [HasColimitsOfShape J C]
    {F G : J ⥤ C} (a : F ⟶ G) :
    (projectiveHomotopyColimit g s).map a =
      letI := projectiveModel g s
      colim.map ((projectiveReplacements g s).Q.map a) := rfl

/-- Original objectwise weak maps give weak actual projective homotopy-colimit maps. -/
theorem projectiveHomotopyColimit_map_weak [HasColimitsOfShape J C]
    {F G : J ⥤ C} (a : F ⟶ G) (ha : ∀ j, weakEquivalences C (a.app j)) :
    weakEquivalences C ((projectiveHomotopyColimit g s).map a) := by
  let _ := projectiveModel g s
  obtain ⟨hW, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  exact homotopyColimit_map_objectwise_weak (projectiveReplacements g s) hF hT hW a ha

end OriginalProjective

section OriginalInjective

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)

/-- The actual original Smith construction supplies the same injective model. -/
@[instance_reducible]
def injectiveModel : ModelCategory (J ⥤ C) :=
  FunctorInjective.originalSmithModelCategory g κLP s

/-- Both actual original injective factor algorithms construct the whole-diagram replacements. -/
def injectiveReplacements :
    letI := injectiveModel g κLP s
    GeneratedFunctorialReplacements.Data (C := J ⥤ C) := by
  letI := injectiveModel g κLP s
  exact GeneratedFunctorialReplacements.replacementsOfFactors
    (FunctorInjective.originalSmithCofibrantFactorizationData g κLP s)
    (FunctorInjective.originalSmithFibrantFactorizationData g κLP s)

/-- The actual original injective left classes supply the native limit Quillen pair. -/
theorem injectiveLimit_isQuillen [HasLimitsOfShape J C] :
    let _ := injectiveModel g κLP s
    (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := by
  let _ := injectiveModel g κLP s
  exact limit_isQuillen
    (FunctorInjective.originalInjectiveModel_cofibrations g κLP s)
    (FunctorInjective.originalInjectiveModel_trivialCofibrations g κLP s)

/-- The same actual original injective R diagram followed by its genuine limit. -/
def injectiveHomotopyLimit [HasLimitsOfShape J C] : (J ⥤ C) ⥤ C := by
  letI := injectiveModel g κLP s
  exact homotopyLimit (injectiveReplacements g κLP s)

/-- Every original whole diagram morphism retains the actual injective R map and limit map. -/
theorem injectiveHomotopyLimit_map [HasLimitsOfShape J C]
    {F G : J ⥤ C} (a : F ⟶ G) :
    (injectiveHomotopyLimit g κLP s).map a =
      letI := injectiveModel g κLP s
      lim.map ((injectiveReplacements g κLP s).R.map a) := rfl

/-- Original objectwise weak maps give weak actual injective homotopy-limit maps. -/
theorem injectiveHomotopyLimit_map_weak [HasLimitsOfShape J C]
    {F G : J ⥤ C} (a : F ⟶ G) (ha : ∀ j, weakEquivalences C (a.app j)) :
    weakEquivalences C ((injectiveHomotopyLimit g κLP s).map a) := by
  let _ := injectiveModel g κLP s
  exact homotopyLimit_map_objectwise_weak (injectiveReplacements g κLP s)
    (FunctorInjective.originalInjectiveModel_cofibrations g κLP s)
    (FunctorInjective.originalInjectiveModel_trivialCofibrations g κLP s)
    (FunctorInjective.originalSmithModel_weakEquivalences g κLP s) a ha

end OriginalInjective

section OriginalReedy

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The actual Reedy corners and the original two coefficient factories construct diagram replacements. -/
def reedyReplacements :
    letI := ReedyModel.modelCategory r Fc Ff
    GeneratedFunctorialReplacements.Data (C := J ⥤ C) := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact GeneratedFunctorialReplacements.replacementsOfFactors
    (ReedyModel.cofibrantFactorizationData r Fc Ff)
    (ReedyModel.fibrantFactorizationData r Fc Ff)

/-- Every original Reedy homotopy-limit object is the limit of that same actual R diagram. -/
def reedyHomotopyLimit [HasLimitsOfShape J C] : (J ⥤ C) ⥤ C := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact homotopyLimit (reedyReplacements r Fc Ff)

/-- Every original Reedy homotopy-colimit object is the colimit of that same actual Q diagram. -/
def reedyHomotopyColimit [HasColimitsOfShape J C] : (J ⥤ C) ⥤ C := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact homotopyColimit (reedyReplacements r Fc Ff)

end OriginalReedy

end HomotopicalAlgebra.DerivedDiagramConstructions

namespace HomotopicalAlgebra.DerivedDiagramConstructions

open scoped SSet.modelCategoryQuillen

section ScalarWeakClasses

/-- The actual scalar universe lift preserves both original parts of a trivial fibration. -/
theorem ulift_trivialFibration {K L : SSet.{vC}} (p : K ⟶ L)
    (hp : trivialFibrations SSet.{vC} p) :
    trivialFibrations SSet.{max z vC} (SSet.uliftFunctor.{z, vC}.map p) := by
  let _ : Fibration p := (fibration_iff _).mpr hp.1
  exact ⟨(fibration_iff _).mp (SSet.modelCategoryQuillen.uliftFunctor_map_fibration p),
    (SSet.realizationWeak_ulift_map_iff p).mpr hp.2⟩

end ScalarWeakClasses

section LiftedLeftQuillen

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]

/-- Every original coefficient fibration gives a Kan fibration on the full lifted left frame Hom. -/
theorem liftedLeftHom_map_fibration (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hW : ∀ {i j : SimplexCategory} (g : i ⟶ j), weakEquivalences C (A.map g))
    {X Y : C} (p : X ⟶ Y) [Fibration p] :
    Fibration ((liftedLeftHomFunctor.{uC, vC, z} A).map p) := by
  let _ : Fibration ((PointedFramingAction.leftHomFunctor A).map p) :=
    PointedFramingAction.leftHom_map_fibration A hA hW p
  let _ : Fibration (SSet.uliftFunctor.{z, vC}.map
      ((PointedFramingAction.leftHomFunctor A).map p)) :=
    SSet.modelCategoryQuillen.uliftFunctor_map_fibration _
  exact (fibration_iff _).mpr
    (((fibrations SSet.{max z vC}).arrow_mk_iso_iff
      (Arrow.isoMk ((liftedLeftHomIso A).app X) ((liftedLeftHomIso A).app Y)
        ((liftedLeftHomIso A).hom.naturality p).symm)).mpr
      ((fibration_iff _).mp (inferInstanceAs (Fibration
        (SSet.uliftFunctor.{z, vC}.map ((PointedFramingAction.leftHomFunctor A).map p))))))

variable [HasColimitsOfSize.{0, max z vC} C]

/-- The genuine higher-universe scalar adjunction is Quillen, from the actual frame latching maps. -/
theorem liftedTensorHomAdjunction_isQuillen (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hW : ∀ {i j : SimplexCategory} (g : i ⟶ j), weakEquivalences C (A.map g)) :
    (liftedTensorHomAdjunction.{uC, vC, z} A).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y p hp
    let _ : Fibration p := (fibration_iff _).mpr hp
    exact (fibration_iff _).mp (liftedLeftHom_map_fibration A hA hW p)
  · intro X Y p hp
    let _ : Fibration p := (fibration_iff _).mpr hp.1
    let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr hp.2
    have ht := ulift_trivialFibration.{vC, z}
      (ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p))
      (LeftFrameHomWeakEquivalence.postcomp_trivialFibration A hA p)
    exact ((trivialFibrations SSet.{max z vC}).arrow_mk_iso_iff
      (Arrow.isoMk ((liftedLeftHomIso A).app X) ((liftedLeftHomIso A).app Y)
        ((liftedLeftHomIso A).hom.naturality p).symm)).mpr ht

/-- The original two factories give this lifted scalar Quillen pair for every coefficient object. -/
theorem originalLiftedTensor_isQuillen (dC : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (liftedTensorHomAdjunction.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).IsQuillenAdjunction :=
  liftedTensorHomAdjunction_isQuillen _ (PointedFramingAction.leftFrame_latching_cofibration dC X)
    (PointedFramingAction.leftFrame_map_weak dC X)

end LiftedLeftQuillen

section LiftedRightHom

variable {C : Type uC} [Category.{vC} C]

/-- The full original right resolution Hom, with only its scalar values enlarged. -/
def liftedRightHomFunctor (B : SimplicialObject C) : Cᵒᵖ ⥤ SSet.{max z vC} :=
  (ResolutionHomComplex.CanonicalEnrichment.rightBifunctor (C := C)).flip.obj B ⋙
    SSet.uliftFunctor.{z, vC}

/-- The actual opposite frame Hom and the original right resolution Hom are the same lifted mapping space. -/
def liftedRightHomIso (B : SimplicialObject C) :
    liftedLeftHomFunctor.{uC, vC, z} B.rightOp ≅ liftedRightHomFunctor.{uC, vC, z} B :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun _ =>
    { hom := ↾fun f => ULift.up f.down.unop
      inv := ↾fun f => ULift.up f.down.op
      hom_inv_id := by ext f; rfl
      inv_hom_id := by ext f; rfl }) (by
    intro n m g
    ext f
    apply ULift.ext
    change ((B.map g).op ≫ f.down).unop = (ResolutionHomComplex.right X.unop B).map g f.down.unop
    exact (ResolutionHomComplex.right_map_apply X.unop B g f.down.unop).symm)) (by
    intro X Y p
    ext n f
    apply ULift.ext
    rfl)

variable [HasLimitsOfSize.{0, max z vC} C]

/-- The whole scalar cotensor is the actual Kan extension of the same opposite right frame. -/
def liftedCotensorScalar (B : SimplicialObject C) : SSet.{max z vC} ⥤ Cᵒᵖ :=
  liftedTensor.{uC, vC, z} B.rightOp

/-- The higher-universe right Hom has its genuine scalar cotensor left adjoint. -/
def liftedCotensorHomAdjunction (B : SimplicialObject C) :
    liftedCotensorScalar.{uC, vC, z} B ⊣ liftedRightHomFunctor.{uC, vC, z} B :=
  (liftedTensorHomAdjunction.{uC, vC, z} B.rightOp).ofNatIsoRight (liftedRightHomIso B)

end LiftedRightHom

section LiftedRightQuillen

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [HasLimitsOfSize.{0, max z vC} C]

/-- The actual matching fibrations of a right frame prove that its whole lifted cotensor--Hom adjunction is Quillen. -/
theorem liftedCotensorHomAdjunction_isQuillen (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j), weakEquivalences C (B.map g)) :
    (liftedCotensorHomAdjunction.{uC, vC, z} B).IsQuillenAdjunction := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y p hp
    let _ : Fibration p := (fibration_iff _).mpr hp
    let _ : Cofibration p.unop := (cofibration_unop_iff _).mpr inferInstance
    let _ : Fibration (QuillenFrameHomComplex.rightPrecomp p.unop B) :=
      QuillenFrameHomComplex.rightPrecomp_fibration p.unop B hB hW
    exact (fibration_iff _).mp (SSet.modelCategoryQuillen.uliftFunctor_map_fibration
      (QuillenFrameHomComplex.rightPrecomp p.unop B))
  · intro X Y p hp
    let _ : Fibration p := (fibration_iff _).mpr hp.1
    let _ : WeakEquivalence p := (weakEquivalence_iff _).mpr hp.2
    let _ : Cofibration p.unop := (cofibration_unop_iff _).mpr inferInstance
    exact ulift_trivialFibration.{vC, z} (RightFrameHomBoundary.precomp p.unop B)
      (RightFrameHomBoundary.precomp_trivialFibration p.unop B hB)

/-- The same original two factories give the lifted right-frame scalar Quillen pair at every target. -/
theorem originalLiftedCotensor_isQuillen (dC : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (liftedCotensorHomAdjunction.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)).IsQuillenAdjunction :=
  liftedCotensorHomAdjunction_isQuillen _ (PointedFramingAction.rightFrame_matching_fibration dC Y)
    (PointedFramingAction.rightFrame_map_weak dC Y)

end LiftedRightQuillen

section ScalarDiagramModel

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- The actual type and simplex presheaf theorems construct local presentability of the scalar category. -/
theorem scalarPresentable : IsCardinalLocallyPresentable SSet.{vC} Cardinal.aleph0.{vC} := by
  let s : Functor.SmallIndexData.{vC} SimplexCategoryᵒᵖ (Type vC) :=
    { smallIndex := small_max.{vC} _
      locallySmallIndex := ⟨fun _ _ => small_max.{vC} _⟩
      locallySmallCoefficient := locallySmall_self _ }
  exact s.isCardinalLocallyPresentable Cardinal.aleph0

variable (J : Type uJ) [Category.{vJ} J]

/-- The original index gets an actual small-model equivalence in the enlarged scalar universe. -/
def scalarIndex : Functor.EssentialIndexData.{max uJ vJ z} J SSet.{max uJ vJ z} := by
  let s : Functor.SmallIndexData.{max uJ vJ z} J SSet.{max uJ vJ z} :=
    { smallIndex := small_max.{max vJ z} J
      locallySmallIndex := ⟨fun _ _ => small_max.{max uJ z} _⟩
      locallySmallCoefficient := locallySmall_self _ }
  exact s.toEssential

/-- The original Smith construction, with the canonical boundary and horn families, produces the scalar injective
model. -/
@[instance_reducible]
def scalarModel : ModelCategory (J ⥤ SSet.{max uJ vJ z}) := by
  let _ : IsCardinalLocallyPresentable SSet.{max uJ vJ z}
      Cardinal.aleph0.{max uJ vJ z} := scalarPresentable.{max uJ vJ z}
  exact injectiveModel SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z} Cardinal.aleph0
    (scalarIndex.{uJ, vJ, z} J)

/-- Both actual original scalar Smith factors supply the whole-diagram replacement algorithms. -/
def scalarReplacements :
    letI := scalarModel.{uJ, vJ, z} J
    GeneratedFunctorialReplacements.Data (C := J ⥤ SSet.{max uJ vJ z}) := by
  let _ : IsCardinalLocallyPresentable SSet.{max uJ vJ z}
      Cardinal.aleph0.{max uJ vJ z} := scalarPresentable.{max uJ vJ z}
  exact injectiveReplacements SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z} Cardinal.aleph0
    (scalarIndex.{uJ, vJ, z} J)

/-- The genuine homotopy limit of scalar mapping spaces uses that same original whole-diagram R algorithm. -/
def scalarHomotopyLimit : (J ⥤ SSet.{max uJ vJ z}) ⥤ SSet.{max uJ vJ z} := by
  let _ := scalarModel.{uJ, vJ, z} J
  exact homotopyLimit (scalarReplacements.{uJ, vJ, z} J)

/-- The actual scalar constants and limit are Quillen for the constructed original injective classes. -/
theorem scalarLimit_isQuillen :
    letI := scalarModel.{uJ, vJ, z} J
    (constLimAdj (J := J) (C := SSet.{max uJ vJ z})).IsQuillenAdjunction := by
  let _ : IsCardinalLocallyPresentable SSet.{max uJ vJ z}
      Cardinal.aleph0.{max uJ vJ z} := scalarPresentable.{max uJ vJ z}
  exact injectiveLimit_isQuillen SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z} Cardinal.aleph0
    (scalarIndex.{uJ, vJ, z} J)

/-- The whole comparison from the ordinary scalar limit retains the actual original scalar R unit. -/
def scalarLimitComparison :
    (lim : (J ⥤ SSet.{max uJ vJ z}) ⥤ SSet.{max uJ vJ z}) ⟶
      scalarHomotopyLimit.{uJ, vJ, z} J := by
  let _ := scalarModel.{uJ, vJ, z} J
  exact limitComparison (scalarReplacements.{uJ, vJ, z} J)

/-- Every objectwise original weak mapping-space diagram map gives a weak genuine scalar homotopy-limit map. -/
theorem scalarHomotopyLimit_map_weak
    {F G : J ⥤ SSet.{max uJ vJ z}} (a : F ⟶ G)
    (ha : ∀ j, weakEquivalences SSet.{max uJ vJ z} (a.app j)) :
    weakEquivalences SSet.{max uJ vJ z} ((scalarHomotopyLimit.{uJ, vJ, z} J).map a) := by
  let _ : IsCardinalLocallyPresentable SSet.{max uJ vJ z}
      Cardinal.aleph0.{max uJ vJ z} := scalarPresentable.{max uJ vJ z}
  exact injectiveHomotopyLimit_map_weak SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}
    Cardinal.aleph0 (scalarIndex.{uJ, vJ, z} J) a ha

/-- The constructed scalar left class is the original objectwise scalar cofibration class. -/
theorem scalarModel_cofibrations :
    letI := scalarModel.{uJ, vJ, z} J
    cofibrations (J ⥤ SSet.{max uJ vJ z}) = (cofibrations SSet.{max uJ vJ z}).functorCategory J := by
  let _ : IsCardinalLocallyPresentable SSet.{max uJ vJ z}
      Cardinal.aleph0.{max uJ vJ z} := scalarPresentable.{max uJ vJ z}
  exact FunctorInjective.originalInjectiveModel_cofibrations
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z} Cardinal.aleph0 (scalarIndex.{uJ, vJ, z} J)

/-- The same scalar Smith dictionary has the original objectwise trivial cofibration class. -/
theorem scalarModel_trivialCofibrations :
    letI := scalarModel.{uJ, vJ, z} J
    trivialCofibrations (J ⥤ SSet.{max uJ vJ z}) =
      (trivialCofibrations SSet.{max uJ vJ z}).functorCategory J := by
  let _ : IsCardinalLocallyPresentable SSet.{max uJ vJ z}
      Cardinal.aleph0.{max uJ vJ z} := scalarPresentable.{max uJ vJ z}
  exact FunctorInjective.originalInjectiveModel_trivialCofibrations
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z} Cardinal.aleph0 (scalarIndex.{uJ, vJ, z} J)

/-- On an actual fibrant scalar diagram the original scalar R comparison is a weak equivalence. -/
theorem scalarLimitComparison_weak (F : J ⥤ SSet.{max uJ vJ z}) :
    letI := scalarModel.{uJ, vJ, z} J
    IsFibrant F → weakEquivalences SSet.{max uJ vJ z} ((scalarLimitComparison.{uJ, vJ, z} J).app F) := by
  let _ := scalarModel.{uJ, vJ, z} J
  intro hF
  let _ : IsFibrant F := hF
  exact limitComparison_weak (scalarReplacements.{uJ, vJ, z} J)
    (scalarModel_cofibrations.{uJ, vJ, z} J) (scalarModel_trivialCofibrations.{uJ, vJ, z} J) F

end ScalarDiagramModel

section OriginalMappingDiagrams

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The whole original covariant mapping diagram uses the same actual left frame. -/
def intoMappingDiagram (X : C) (F : J ⥤ C) : J ⥤ SSet.{max uJ vJ vC z} :=
  F ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)

/-- The whole original contravariant mapping diagram uses the same actual right frame. -/
def outMappingDiagram (F : J ⥤ C) (Y : C) : Jᵒᵖ ⥤ SSet.{max uJ vJ vC z} :=
  F.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)

/-- Every original covariant index arrow is the same degreewise postcomposition. -/
theorem intoMappingDiagram_index (X : C) (F : J ⥤ C) {i j : J} (a : i ⟶ j)
    (n : SimplexCategoryᵒᵖ) (f : ((intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F).obj i).obj n) :
    ((intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F).map a).app n f = ULift.up (f.down ≫ F.map a) := rfl

/-- Every original contravariant index arrow is the same degreewise precomposition. -/
theorem outMappingDiagram_index (F : J ⥤ C) (Y : C) {i j : J} (a : i ⟶ j)
    (n : SimplexCategoryᵒᵖ) (f : ((outMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y).obj (.op j)).obj n) :
    ((outMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y).map a.op).app n f = ULift.up (F.map a ≫ f.down) := rfl

/-- Every original whole-diagram morphism acts on all the original covariant mapping coefficients. -/
def intoMappingDiagramMap (X : C) {F G : J ⥤ C} (a : F ⟶ G) :
    intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F ⟶ intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X G :=
  Functor.whiskerRight a (liftedLeftHomFunctor.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.leftFrame dC).obj X))

/-- The same original whole-diagram morphism acts contravariantly on the actual mapping coefficients. -/
def outMappingDiagramMap {F G : J ⥤ C} (a : F ⟶ G) (Y : C) :
    outMappingDiagram.{uJ, vJ, uC, vC, z} dC G Y ⟶ outMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y :=
  Functor.whiskerRight (NatTrans.op a) (liftedRightHomFunctor.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.rightFrame dC).obj Y))

end OriginalMappingDiagrams

section OriginalOutAdjunction

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [HasLimitsOfSize.{0, max uJ vJ vC z} C]

/-- The original diagram-opposite equivalence and actual scalar cotensor construct the whole diagram adjunction. -/
def outDiagramAdjunction (B : SimplicialObject C) :
    ((Functor.whiskeringRight Jᵒᵖ SSet.{max uJ vJ vC z} Cᵒᵖ).obj
        (liftedCotensorScalar.{uC, vC, max uJ vJ z} B) ⋙ (Functor.opUnopEquiv J C).inverse) ⊣
      ((Functor.opUnopEquiv J C).functor ⋙
        (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
          (liftedRightHomFunctor.{uC, vC, max uJ vJ z} B)) :=
  ((liftedCotensorHomAdjunction.{uC, vC, max uJ vJ z} B).whiskerRight Jᵒᵖ).comp
    (Functor.opUnopEquiv J C).symm.toAdjunction

end OriginalOutAdjunction

section OriginalInjectiveMappingQuillen

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  [HasColimitsOfSize.{0, max uJ vJ vC z} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- Actual original injective left classes make the full lifted frame Hom a Quillen right adjoint on diagrams. -/
theorem injectiveMapping_isQuillen (X : C) :
    letI := injectiveModel g κLP s
    letI := scalarModel.{uJ, vJ, max vC z} J
    ((liftedTensorHomAdjunction.{uC, vC, max uJ vJ z}
      ((PointedFramingAction.leftFrame dC).obj X)).whiskerRight J).IsQuillenAdjunction := by
  let _ := injectiveModel g κLP s
  let _ := scalarModel.{uJ, vJ, max vC z} J
  let adj := liftedTensorHomAdjunction.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.leftFrame dC).obj X)
  let _ : adj.IsQuillenAdjunction := originalLiftedTensor_isQuillen dC X
  constructor
  · intro K L a ha
    rw [scalarModel_cofibrations.{uJ, vJ, max vC z} J] at ha
    rw [FunctorInjective.originalInjectiveModel_cofibrations g κLP s]
    intro j
    exact Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := adj) _ (ha j)
  · intro K L a ha
    rw [scalarModel_trivialCofibrations.{uJ, vJ, max vC z} J] at ha
    rw [FunctorInjective.originalInjectiveModel_trivialCofibrations g κLP s]
    intro j
    exact Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations (adj := adj) _ (ha j)

/-- The original injective fibrancy condition proves fibrancy of the whole mapping diagram in the actual scalar
model. -/
theorem injectiveMapping_isFibrant (X : C) (F : J ⥤ C) :
    letI := injectiveModel g κLP s
    letI := scalarModel.{uJ, vJ, max vC z} J
    IsFibrant F → IsFibrant (intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F) := by
  let _ := injectiveModel g κLP s
  let _ := scalarModel.{uJ, vJ, max vC z} J
  intro hF
  let adj := (liftedTensorHomAdjunction.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.leftFrame dC).obj X)).whiskerRight J
  let _ : adj.IsQuillenAdjunction := injectiveMapping_isQuillen g κLP s dC X
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) hF

end OriginalInjectiveMappingQuillen

section OriginalProjectiveMappingQuillen

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  [HasLimitsOfSize.{0, max uJ vJ vC z} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- Original projective right classes and the actual opposite-diagram equivalence prove the whole scalar mapping Quillen
pair. -/
theorem projectiveMapping_isQuillen (Y : C) :
    letI := projectiveModel g s
    letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
    (outDiagramAdjunction.{uJ, vJ, uC, vC, z} (J := J) ((PointedFramingAction.rightFrame dC).obj
      Y)).IsQuillenAdjunction := by
  let _ := projectiveModel g s
  let _ := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
  let T := liftedCotensorScalar.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.rightFrame dC).obj Y)
  let adj := liftedCotensorHomAdjunction.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : adj.IsQuillenAdjunction := originalLiftedCotensor_isQuillen dC Y
  obtain ⟨_, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  constructor
  · intro K L a ha
    rw [scalarModel_cofibrations.{uJ, vJ, max vC z} Jᵒᵖ] at ha
    rw [cofibrations_op, hF]
    intro j
    change fibrations C ((T.map (a.app (.op j))).unop)
    have h := Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := adj) _ (ha (.op j))
    rw [cofibrations_op] at h
    exact h
  · intro K L a ha
    rw [scalarModel_trivialCofibrations.{uJ, vJ, max vC z} Jᵒᵖ] at ha
    rw [trivialCofibrations_op, hT]
    intro j
    change trivialFibrations C ((T.map (a.app (.op j))).unop)
    have h := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations (adj := adj) _ (ha (.op j))
    rw [trivialCofibrations_op] at h
    exact h

/-- Original projective cofibrancy proves fibrancy of the entire contravariant mapping diagram in the actual scalar
model. -/
theorem projectiveMapping_isFibrant (F : J ⥤ C) (Y : C) :
    letI := projectiveModel g s
    letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
    IsCofibrant F → IsFibrant (outMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y) := by
  let _ := projectiveModel g s
  let _ := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
  intro hF
  let _ : IsCofibrant F := hF
  let _ : IsFibrant (Opposite.op F) :=
    (isFibrant_iff_of_isTerminal (initial.to F).op initialIsInitial.op).mpr inferInstance
  let adj := outDiagramAdjunction.{uJ, vJ, uC, vC, z} (J := J) ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : adj.IsQuillenAdjunction := projectiveMapping_isQuillen g s dC Y
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance

end OriginalProjectiveMappingQuillen

section OriginalVertexConditions

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)

/-- Original essential-index projective cofibrations are coefficient cofibrations at every original vertex. -/
theorem projectiveModel_cofibrations_le_objectwise :
    letI := projectiveModel g s
    cofibrations (J ⥤ C) ≤ (cofibrations C).functorCategory J := by
  let _ : LocallySmall.{w} s.index := locallySmall_self _
  let _ : ModelCategory (s.index ⥤ C) := FunctorProjective.modelCategory (J := s.index) g
  change (cofibrations (s.index ⥤ C)).inverseImage (s.equivalence.congrLeft (E := C)).functor ≤ _
  rw [← functorCategory_inverseImage_congrLeft s.equivalence (cofibrations C)]
  intro F G a ha
  exact FunctorProjective.cofibrations_le_objectwise g _ ha

/-- The same actual projective cofibrancy condition makes every original coefficient vertex cofibrant. -/
theorem projectiveDiagram_vertex_cofibrant (F : J ⥤ C) :
    letI := projectiveModel g s
    IsCofibrant F → ∀ j, IsCofibrant (F.obj j) := by
  let _ := projectiveModel g s
  intro hF j
  let hC : HasInitial C := inferInstance
  let _ : ∀ k : J, HasColimit ((Functor.empty.{0} (J ⥤ C)).flip.obj k) := fun _ => by
    exact hC.has_colimit _
  let _ : PreservesColimit (Functor.empty.{0} (J ⥤ C)) ((evaluation J C).obj j) :=
    evaluation_preservesColimit _ j
  have h := projectiveModel_cofibrations_le_objectwise g s (initial.to F) ((cofibration_iff _).mp hF) j
  exact (isCofibrant_iff_of_isInitial ((initial.to F).app j)
    (IsInitial.isInitialObj ((evaluation J C).obj j) _ initialIsInitial)).mpr ((cofibration_iff _).mpr h)

/-- Every vertex of the same original projective Q diagram is genuinely cofibrant. -/
theorem projectiveQ_vertex_cofibrant (F : J ⥤ C) (j : J) :
    IsCofibrant
      (letI := projectiveModel g s; ((projectiveReplacements g s).Q.obj F).obj j) := by
  let _ := projectiveModel g s
  exact projectiveDiagram_vertex_cofibrant g s _ ((projectiveReplacements g s).q_cofibrant F) j

/-- The original projective whole-diagram Q counit is weak at every unchanged coefficient vertex. -/
theorem projectiveQ_vertex_weak (F : J ⥤ C) (j : J) :
    weakEquivalences C
      (letI := projectiveModel g s; ((projectiveReplacements g s).q.app F).app j) := by
  let _ := projectiveModel g s
  obtain ⟨hW, _, _, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  have h := ((projectiveReplacements g s).q_trivialFibration F).2
  rw [hW] at h
  exact h j

variable (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]

/-- Actual original injective right classes are coefficient fibrations at every unchanged vertex. -/
theorem injectiveModel_fibrations_le_objectwise :
    letI := injectiveModel g κLP s
    fibrations (J ⥤ C) ≤ (fibrations C).functorCategory J := by
  let _ := injectiveModel g κLP s
  let _ : LocallySmall.{w} J := s.locallySmallIndex
  let _ : HasCoproducts.{w} C := g.J_smallObject.hasCoproducts
  rw [FunctorInjective.originalInjectiveModel_fibrations g κLP s]
  exact (injectiveDiagram_rightClasses_le_pointwise J C).1

/-- The original injective fibrancy condition makes every original coefficient vertex fibrant. -/
theorem injectiveDiagram_vertex_fibrant (F : J ⥤ C) :
    letI := injectiveModel g κLP s
    IsFibrant F → ∀ j, IsFibrant (F.obj j) := by
  let _ := injectiveModel g κLP s
  intro hF j
  let hC : HasTerminal C := inferInstance
  let _ : ∀ k : J, HasLimit ((Functor.empty.{0} (J ⥤ C)).flip.obj k) := fun _ => by
    exact hC.has_limit _
  let _ : PreservesLimit (Functor.empty.{0} (J ⥤ C)) ((evaluation J C).obj j) :=
    evaluation_preservesLimit _ j
  have h := injectiveModel_fibrations_le_objectwise g s κLP (terminal.from F) ((fibration_iff _).mp hF) j
  exact (isFibrant_iff_of_isTerminal ((terminal.from F).app j)
    (IsTerminal.isTerminalObj ((evaluation J C).obj j) _ terminalIsTerminal)).mpr ((fibration_iff _).mpr h)

/-- Each coefficient of the same original injective R diagram is genuinely fibrant. -/
theorem injectiveR_vertex_fibrant (F : J ⥤ C) (j : J) :
    IsFibrant
      (letI := injectiveModel g κLP s; ((injectiveReplacements g κLP s).R.obj F).obj j) := by
  let _ := injectiveModel g κLP s
  exact injectiveDiagram_vertex_fibrant g s κLP _ ((injectiveReplacements g κLP s).r_fibrant F) j

/-- The actual original injective R unit is weak at every original coefficient vertex. -/
theorem injectiveR_vertex_weak (F : J ⥤ C) (j : J) :
    weakEquivalences C
      (letI := injectiveModel g κLP s; ((injectiveReplacements g κLP s).r.app F).app j) := by
  let _ := injectiveModel g κLP s
  have h := ((injectiveReplacements g κLP s).r_trivialCofibration F).2
  rw [FunctorInjective.originalSmithModel_weakEquivalences g κLP s] at h
  exact h j

end OriginalVertexConditions

section OriginalColimitHom

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C]

/-- Every actual caller cocone gives its full opposite right-frame mapping cone. -/
def liftedRightHomCone (B : SimplicialObject C) {F : J ⥤ C} (c : Cocone F) :
    Cone (F.op ⋙ liftedRightHomFunctor.{uC, vC, z} B) :=
  (liftedRightHomFunctor.{uC, vC, z} B).mapCone c.op

/-- Every original cocone injection remains the exact right-Hom precomposition leg. -/
theorem liftedRightHomCone_projection (B : SimplicialObject C) {F : J ⥤ C}
    (c : Cocone F) (j : Jᵒᵖ) :
    (liftedRightHomCone.{uJ, vJ, uC, vC, z} B c).π.app j =
      (liftedRightHomFunctor.{uC, vC, z} B).map (c.ι.app j.unop).op := rfl

variable [HasLimitsOfSize.{0, max z vC} C]

/-- The genuine right-frame scalar adjunction preserves the caller's entire colimit universal property as a limit. -/
def liftedRightHomConeIsLimit (B : SimplicialObject C) {F : J ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsLimit (liftedRightHomCone.{uJ, vJ, uC, vC, z} B c) := by
  let _ : PreservesLimitsOfSize.{vJ, uJ} (liftedRightHomFunctor.{uC, vC, z} B) :=
    (liftedCotensorHomAdjunction.{uC, vC, z} B).rightAdjoint_preservesLimits
  exact isLimitOfPreserves _ hc.op

variable [HasColimitsOfShape J C] [HasLimitsOfShape Jᵒᵖ SSet.{max z vC}]

/-- The entire right-frame Hom out of the original colimit is the genuine limit of its original mapping diagram. -/
def liftedRightColimitIso (B : SimplicialObject C) (F : J ⥤ C) :
    (liftedRightHomFunctor.{uC, vC, z} B).obj (.op (colimit F)) ≅
      limit (F.op ⋙ liftedRightHomFunctor.{uC, vC, z} B) :=
  (limit.isoLimitCone ⟨liftedRightHomCone.{uJ, vJ, uC, vC, z} B (colimit.cocone F),
    liftedRightHomConeIsLimit.{uJ, vJ, uC, vC, z} B (colimit.cocone F) (colimit.isColimit F)⟩).symm

/-- Every forward projection is the same original precomposition by a colimit injection. -/
theorem liftedRightColimitIso_hom_projection (B : SimplicialObject C) (F : J ⥤ C) (j : Jᵒᵖ) :
    (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).hom ≫ limit.π _ j =
      (liftedRightHomFunctor.{uC, vC, z} B).map (colimit.ι F j.unop).op :=
  limit.isoLimitCone_inv_π
    ⟨liftedRightHomCone.{uJ, vJ, uC, vC, z} B (colimit.cocone F),
      liftedRightHomConeIsLimit.{uJ, vJ, uC, vC, z} B (colimit.cocone F) (colimit.isColimit F)⟩ j

/-- Every inverse projection recovers that same original injection function. -/
theorem liftedRightColimitIso_inv_projection (B : SimplicialObject C) (F : J ⥤ C) (j : Jᵒᵖ) :
    (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).inv ≫
        (liftedRightHomFunctor.{uC, vC, z} B).map (colimit.ι F j.unop).op = limit.π _ j :=
  limit.isoLimitCone_hom_π
    ⟨liftedRightHomCone.{uJ, vJ, uC, vC, z} B (colimit.cocone F),
      liftedRightHomConeIsLimit.{uJ, vJ, uC, vC, z} B (colimit.cocone F) (colimit.isColimit F)⟩ j

/-- Every original diagram transformation retains the complete colimit-to-limit mapping square. -/
theorem liftedRightColimitIso_naturality (B : SimplicialObject C) {F G : J ⥤ C} (a : F ⟶ G) :
    (liftedRightHomFunctor.{uC, vC, z} B).map (colim.map a).op ≫
        (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).hom =
      (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B G).hom ≫
        lim.map (Functor.whiskerRight (NatTrans.op a) (liftedRightHomFunctor.{uC, vC, z} B)) := by
  apply limit.hom_ext
  intro j
  rw [Category.assoc, liftedRightColimitIso_hom_projection, Category.assoc]
  rw [show lim.map (Functor.whiskerRight (NatTrans.op a) (liftedRightHomFunctor.{uC, vC, z} B)) =
    limMap (Functor.whiskerRight (NatTrans.op a) (liftedRightHomFunctor.{uC, vC, z} B)) from rfl,
    limMap_π, ← Category.assoc, liftedRightColimitIso_hom_projection]
  change (liftedRightHomFunctor.{uC, vC, z} B).map (colim.map a).op ≫
      (liftedRightHomFunctor.{uC, vC, z} B).map (colimit.ι F j.unop).op =
    (liftedRightHomFunctor.{uC, vC, z} B).map (colimit.ι G j.unop).op ≫
      (liftedRightHomFunctor.{uC, vC, z} B).map (a.app j.unop).op
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply Functor.congr_map
  apply Quiver.Hom.unop_inj
  exact ι_colimMap a j.unop

/-- The inverse keeps the same entire original colimit-map square. -/
theorem liftedRightColimitIso_inv_naturality (B : SimplicialObject C) {F G : J ⥤ C} (a : F ⟶ G) :
    lim.map (Functor.whiskerRight (NatTrans.op a) (liftedRightHomFunctor.{uC, vC, z} B)) ≫
        (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).inv =
      (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B G).inv ≫
        (liftedRightHomFunctor.{uC, vC, z} B).map (colim.map a).op := by
  apply (cancel_epi (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B G).hom).mp
  simp only [← Category.assoc, ← liftedRightColimitIso_naturality B a]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

end OriginalColimitHom

section OriginalLimitHomNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [HasColimitsOfSize.{0, max z vC} C]
  [HasLimitsOfShape J C] [HasLimitsOfShape J SSet.{max z vC}]

/-- Every original diagram transformation retains the complete frame-Hom limit square. -/
theorem liftedLeftLimitIso_naturality (A : CosimplicialObject C) {F G : J ⥤ C} (a : F ⟶ G) :
    (liftedLeftHomFunctor.{uC, vC, z} A).map (lim.map a) ≫
        (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A G).hom =
      (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).hom ≫
        lim.map (Functor.whiskerRight a (liftedLeftHomFunctor.{uC, vC, z} A)) := by
  apply limit.hom_ext
  intro j
  rw [Category.assoc, liftedLeftLimitIso_hom_projection, Category.assoc]
  rw [show lim.map (Functor.whiskerRight a (liftedLeftHomFunctor.{uC, vC, z} A)) =
    limMap (Functor.whiskerRight a (liftedLeftHomFunctor.{uC, vC, z} A)) from rfl,
    limMap_π, ← Category.assoc, liftedLeftLimitIso_hom_projection]
  change (liftedLeftHomFunctor.{uC, vC, z} A).map (lim.map a) ≫
      (liftedLeftHomFunctor.{uC, vC, z} A).map (limit.π G j) =
    (liftedLeftHomFunctor.{uC, vC, z} A).map (limit.π F j) ≫
      (liftedLeftHomFunctor.{uC, vC, z} A).map (a.app j)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact Functor.congr_map _ (limMap_π a j)

/-- The inverse retains that same complete original limit-map square. -/
theorem liftedLeftLimitIso_inv_naturality (A : CosimplicialObject C) {F G : J ⥤ C} (a : F ⟶ G) :
    lim.map (Functor.whiskerRight a (liftedLeftHomFunctor.{uC, vC, z} A)) ≫
        (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A G).inv =
      (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).inv ≫
        (liftedLeftHomFunctor.{uC, vC, z} A).map (lim.map a) := by
  apply (cancel_epi (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).hom).mp
  simp only [← Category.assoc, ← liftedLeftLimitIso_naturality A a]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

end OriginalLimitHomNaturality

section WholeInjectiveMappings

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The full original injective R diagram supplies all mapping targets before taking a homotopy limit. -/
def injectiveRMappingDiagram (X : C) (F : J ⥤ C) : J ⥤ SSet.{max uJ vJ vC z} := by
  letI := injectiveModel g κLP s
  exact intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X ((injectiveReplacements g κLP s).R.obj F)

/-- Every original diagram map retains the whole actual injective R map in the mapping diagram. -/
def injectiveRMappingMap (X : C) {F G : J ⥤ C} (a : F ⟶ G) :
    injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F ⟶
      injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X G := by
  letI := injectiveModel g κLP s
  exact intoMappingDiagramMap.{uJ, vJ, uC, vC, z} dC X ((injectiveReplacements g κLP s).R.map a)

variable [HasColimitsOfSize.{0, max uJ vJ vC z} C]

/-- The actual original injective R fibrancy proves scalar diagram fibrancy, with no mapping-fibrancy input. -/
theorem injectiveRMapping_isFibrant (X : C) (F : J ⥤ C) :
    letI := scalarModel.{uJ, vJ, max vC z} J
    IsFibrant (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F) := by
  let _ := injectiveModel g κLP s
  let _ := scalarModel.{uJ, vJ, max vC z} J
  exact injectiveMapping_isFibrant.{uJ, vJ, uC, vC, w, z} g κLP s dC X _
    ((injectiveReplacements g κLP s).r_fibrant F)

variable [HasLimitsOfShape J C]

/-- The actual left-frame Hom into the original homotopy limit maps to the genuine homotopy limit of its mapping
spaces. -/
def injectiveMappingComparison (X : C) (F : J ⥤ C) :
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).obj
        ((injectiveHomotopyLimit g κLP s).obj F) ⟶
      (scalarHomotopyLimit.{uJ, vJ, max vC z} J).obj
        (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F) := by
  letI := injectiveModel g κLP s
  exact (liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
    ((PointedFramingAction.leftFrame dC).obj X) ((injectiveReplacements g κLP s).R.obj F)).hom ≫
      (scalarLimitComparison.{uJ, vJ, max vC z} J).app
        (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)

/-- Its weakness is proved from actual injective R fibrancy and the two genuine scalar Quillen pairs. -/
theorem injectiveMappingComparison_weak (X : C) (F : J ⥤ C) :
    weakEquivalences SSet.{max uJ vJ vC z}
      (injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F) := by
  let _ := injectiveModel g κLP s
  let _ := scalarModel.{uJ, vJ, max vC z} J
  have h := scalarLimitComparison_weak.{uJ, vJ, max vC z} J _
    (injectiveRMapping_isFibrant.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)
  exact (weakEquivalences SSet.{max uJ vJ vC z}).comp_mem _ _
    ((weakEquivalences SSet.{max uJ vJ vC z}).of_isIso
      (liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
        ((PointedFramingAction.leftFrame dC).obj X) ((injectiveReplacements g κLP s).R.obj F)).hom) h

/-- Every comparison projection retains both the original coefficient R projection and the original scalar R unit. -/
theorem injectiveMappingComparison_projection (X : C) (F : J ⥤ C) (j : J) :
    injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F ≫
        (letI := scalarModel.{uJ, vJ, max vC z} J
         limitProjection (scalarReplacements.{uJ, vJ, max vC z} J)
           (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F) j) =
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        (letI := injectiveModel g κLP s
         limitProjection (injectiveReplacements g κLP s) F j) ≫
        (letI := scalarModel.{uJ, vJ, max vC z} J
         ((scalarReplacements.{uJ, vJ, max vC z} J).r.app
           (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)).app j) := by
  let _ := injectiveModel g κLP s
  let _ := scalarModel.{uJ, vJ, max vC z} J
  change ((liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.leftFrame dC).obj X) ((injectiveReplacements g κLP s).R.obj F)).hom ≫
      (limitComparison (scalarReplacements.{uJ, vJ, max vC z} J)).app _) ≫ _ = _
  erw [Category.assoc, comparison_projection, ← Category.assoc, liftedLeftLimitIso_hom_projection]
  rfl

omit [HasColimitsOfSize.{0, max uJ vJ vC z} C] in
/-- The original injective homotopy-limit object is genuinely fibrant in the original coefficient model. -/
theorem injectiveHomotopyLimit_isFibrant (F : J ⥤ C) :
    IsFibrant ((injectiveHomotopyLimit g κLP s).obj F) := by
  let _ := injectiveModel g κLP s
  let _ : (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := injectiveLimit_isQuillen g κLP s
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := constLimAdj)
    ((injectiveReplacements g κLP s).r_fibrant F)

end WholeInjectiveMappings

section WholeProjectiveMappings

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The full original projective Q diagram supplies all mapping sources before taking the scalar homotopy limit. -/
def projectiveQMappingDiagram (F : J ⥤ C) (Y : C) : Jᵒᵖ ⥤ SSet.{max uJ vJ vC z} := by
  letI := projectiveModel g s
  exact outMappingDiagram.{uJ, vJ, uC, vC, z} dC ((projectiveReplacements g s).Q.obj F) Y

/-- Every original diagram map retains the full actual projective Q map in the inverse mapping diagram. -/
def projectiveQMappingMap {F G : J ⥤ C} (a : F ⟶ G) (Y : C) :
    projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC G Y ⟶
      projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y := by
  letI := projectiveModel g s
  exact outMappingDiagramMap.{uJ, vJ, uC, vC, z} dC ((projectiveReplacements g s).Q.map a) Y

variable [HasLimitsOfSize.{0, max uJ vJ vC z} C]

/-- Original projective Q cofibrancy proves fibrancy of the inverse mapping diagram in the actual scalar model. -/
theorem projectiveQMapping_isFibrant (F : J ⥤ C) (Y : C) :
    letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
    IsFibrant (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y) := by
  let _ := projectiveModel g s
  let _ := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
  exact projectiveMapping_isFibrant.{uJ, vJ, uC, vC, w, z} g s dC _ Y
    ((projectiveReplacements g s).q_cofibrant F)

variable [HasColimitsOfShape J C]

/-- Actual right-frame mapping out of the original homotopy colimit maps to the genuine scalar homotopy limit. -/
def projectiveMappingComparison (F : J ⥤ C) (Y : C) :
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).obj
        (.op ((projectiveHomotopyColimit g s).obj F)) ⟶
      (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).obj
        (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y) := by
  letI := projectiveModel g s
  exact (liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
    ((PointedFramingAction.rightFrame dC).obj Y) ((projectiveReplacements g s).Q.obj F)).hom ≫
      (scalarLimitComparison.{uJ, vJ, max vC z} Jᵒᵖ).app
        (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y)

/-- The whole comparison is weak from the actual projective Q and scalar injective R algorithms. -/
theorem projectiveMappingComparison_weak (F : J ⥤ C) (Y : C) :
    weakEquivalences SSet.{max uJ vJ vC z}
      (projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F Y) := by
  let _ := projectiveModel g s
  let _ := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
  have h := scalarLimitComparison_weak.{uJ, vJ, max vC z} Jᵒᵖ _
    (projectiveQMapping_isFibrant.{uJ, vJ, uC, vC, w, z} g s dC F Y)
  exact (weakEquivalences SSet.{max uJ vJ vC z}).comp_mem _ _
    ((weakEquivalences SSet.{max uJ vJ vC z}).of_isIso
      (liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
        ((PointedFramingAction.rightFrame dC).obj Y) ((projectiveReplacements g s).Q.obj F)).hom) h

/-- Every projection retains the same original projective Q injection and the actual scalar R unit. -/
theorem projectiveMappingComparison_projection (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F Y ≫
        (letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
         limitProjection (scalarReplacements.{uJ, vJ, max vC z} Jᵒᵖ)
           (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y) j) =
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        (letI := projectiveModel g s
         (colimitInjection (projectiveReplacements g s) F j.unop).op) ≫
        (letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
         ((scalarReplacements.{uJ, vJ, max vC z} Jᵒᵖ).r.app
           (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y)).app j) := by
  let _ := projectiveModel g s
  let _ := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
  change ((liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.rightFrame dC).obj Y) ((projectiveReplacements g s).Q.obj F)).hom ≫
      (limitComparison (scalarReplacements.{uJ, vJ, max vC z} Jᵒᵖ)).app _) ≫ _ = _
  erw [Category.assoc, comparison_projection, ← Category.assoc, liftedRightColimitIso_hom_projection]
  rfl

omit [HasLimitsOfSize.{0, max uJ vJ vC z} C] in
/-- The same original projective Q colimit is genuinely cofibrant in the original coefficient model. -/
theorem projectiveHomotopyColimit_isCofibrant (F : J ⥤ C) :
    IsCofibrant ((projectiveHomotopyColimit g s).obj F) := by
  let _ := projectiveModel g s
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := projectiveColimit_isQuillen g s
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := colimConstAdj)
    ((projectiveReplacements g s).q_cofibrant F)

end WholeProjectiveMappings

/-- The actual localization of the chosen scalar Kan--Quillen model. -/
abbrev scalarProjection : SSet.{z} ⥤ (weakEquivalences SSet.{z}).Localization :=
  (weakEquivalences SSet.{z}).Q

section OriginalCoefficientComplexes

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The genuine left homotopy function complex retains the same original left frame and coefficient R. -/
def intoHomotopyFunctionComplex (X Y : C) : SSet.{max z vC} :=
  (liftedLeftHomFunctor.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).obj (dC.R.obj Y)

/-- The genuine right homotopy function complex retains the same original coefficient Q and right frame. -/
def outHomotopyFunctionComplex (X Y : C) : SSet.{max z vC} :=
  (liftedRightHomFunctor.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)).obj (.op (dC.Q.obj X))

/-- The same original coefficient R unit gives the full left-complex comparison. -/
def leftComplexReplacement (X Y : C) :
    (liftedLeftHomFunctor.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).obj Y ⟶
      intoHomotopyFunctionComplex.{uC, vC, z} dC X Y :=
  (liftedLeftHomFunctor.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).map (dC.r.app Y)

/-- The same original coefficient Q counit gives the entire right-complex comparison. -/
def rightComplexReplacement (X Y : C) :
    (liftedRightHomFunctor.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)).obj (.op X) ⟶
      outHomotopyFunctionComplex.{uC, vC, z} dC X Y :=
  (liftedRightHomFunctor.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)).map (dC.q.app X).op

/-- Native opposite initial/terminal duality retains cofibrancy as fibrancy in the same original opposite category. -/
theorem cofibrant_op_isFibrant (X : C) [IsCofibrant X] : IsFibrant (Opposite.op X) :=
  (isFibrant_iff_of_isTerminal (initial.to X).op initialIsInitial.op).mpr inferInstance

variable [HasColimitsOfSize.{0, max z vC} C]

/-- Actual target fibrancy makes the original R unit a weak left-complex comparison. -/
theorem leftComplexReplacement_weak (X Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{max z vC} (leftComplexReplacement.{uC, vC, z} dC X Y) := by
  let adj := liftedTensorHomAdjunction.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)
  let _ : adj.IsQuillenAdjunction := originalLiftedTensor_isQuillen dC X
  let _ : IsFibrant ((𝟭 C).obj Y) := inferInstanceAs (IsFibrant Y)
  let _ : IsFibrant (dC.R.obj Y) := dC.r_fibrant Y
  let _ : WeakEquivalence (dC.r.app Y) := (weakEquivalence_iff _).mpr (dC.r_trivialCofibration Y).2
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) (dC.r.app Y))

/-- The original R unit is inverted by the actual scalar localization, at the stated fibrant target condition. -/
def leftComplexReplacementIso (X Y : C) [IsFibrant Y] :
    scalarProjection.{max z vC}.obj
        ((liftedLeftHomFunctor.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).obj Y) ≅
      scalarProjection.{max z vC}.obj (intoHomotopyFunctionComplex.{uC, vC, z} dC X Y) := by
  let _ : IsIso (scalarProjection.{max z vC}.map (leftComplexReplacement.{uC, vC, z} dC X Y)) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max z vC}) _
      (leftComplexReplacement_weak dC X Y)
  exact asIso (scalarProjection.{max z vC}.map (leftComplexReplacement.{uC, vC, z} dC X Y))

end OriginalCoefficientComplexes

section OriginalRightCoefficientComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [HasLimitsOfSize.{0, max z vC} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- Actual source cofibrancy makes the original coefficient Q counit a weak right-complex comparison. -/
theorem rightComplexReplacement_weak (X Y : C) [IsCofibrant X] :
    weakEquivalences SSet.{max z vC} (rightComplexReplacement.{uC, vC, z} dC X Y) := by
  let adj := liftedCotensorHomAdjunction.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : adj.IsQuillenAdjunction := originalLiftedCotensor_isQuillen dC Y
  let _ : IsCofibrant (dC.Q.obj X) := dC.q_cofibrant X
  let _ : IsFibrant (Opposite.op X) := cofibrant_op_isFibrant X
  let _ : IsFibrant (Opposite.op ((𝟭 C).obj X)) := inferInstanceAs (IsFibrant (Opposite.op X))
  let _ : IsFibrant (Opposite.op (dC.Q.obj X)) := cofibrant_op_isFibrant _
  let _ : WeakEquivalence ((dC.q.app X).op) := (weakEquivalence_iff _).mpr (by
    rw [weakEquivalences_op]
    exact (dC.q_trivialFibration X).2)
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) (dC.q.app X).op)

/-- The same actual original Q counit is inverted by scalar localization at the stated cofibrant source condition. -/
def rightComplexReplacementIso (X Y : C) [IsCofibrant X] :
    scalarProjection.{max z vC}.obj
        ((liftedRightHomFunctor.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)).obj (.op X)) ≅
      scalarProjection.{max z vC}.obj (outHomotopyFunctionComplex.{uC, vC, z} dC X Y) := by
  let _ : IsIso (scalarProjection.{max z vC}.map (rightComplexReplacement.{uC, vC, z} dC X Y)) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max z vC}) _
      (rightComplexReplacement_weak dC X Y)
  exact asIso (scalarProjection.{max z vC}.map (rightComplexReplacement.{uC, vC, z} dC X Y))

end OriginalRightCoefficientComparison

section OriginalInjectiveHomotopyMapping

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The proved full mapping comparison becomes an actual isomorphism in the scalar homotopy category. -/
def injectiveMappingComparisonIso (X : C) (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.obj
        ((liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).obj
          ((injectiveHomotopyLimit g κLP s).obj F)) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).obj
          (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)) := by
  let f := injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F
  let _ : IsIso (scalarProjection.{max uJ vJ vC z}.map f) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (injectiveMappingComparison_weak g κLP s dC X F)
  exact asIso (scalarProjection.{max uJ vJ vC z}.map f)

/-- Genuine derived mapping into the same original injective homotopy limit is the genuine scalar homotopy limit of
mapping spaces. -/
def injectiveReplacedMappingIso (X : C) (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.obj
        (intoHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC X ((injectiveHomotopyLimit g κLP s).obj F)) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).obj
          (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)) := by
  let _ : IsFibrant ((injectiveHomotopyLimit g κLP s).obj F) := injectiveHomotopyLimit_isFibrant g κLP s F
  exact (leftComplexReplacementIso.{uC, vC, max uJ vJ z} dC X
    ((injectiveHomotopyLimit g κLP s).obj F)).symm ≪≫
      injectiveMappingComparisonIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X F

/-- The forward derived comparison retains the inverse of the original coefficient R leg and the full original diagram
comparison. -/
theorem injectiveReplacedMappingIso_hom (X : C) (F : J ⥤ C) :
    (injectiveReplacedMappingIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X F).hom =
      (letI := injectiveHomotopyLimit_isFibrant g κLP s F
       (leftComplexReplacementIso.{uC, vC, max uJ vJ z} dC X ((injectiveHomotopyLimit g κLP s).obj F)).inv) ≫
        scalarProjection.{max uJ vJ vC z}.map
          (injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F) := rfl

end OriginalInjectiveHomotopyMapping

section OriginalProjectiveHomotopyMapping

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The proved original projective mapping comparison is inverted by genuine scalar localization. -/
def projectiveMappingComparisonIso (F : J ⥤ C) (Y : C) :
    scalarProjection.{max uJ vJ vC z}.obj
        ((liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).obj
          (.op ((projectiveHomotopyColimit g s).obj F))) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).obj
          (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y)) := by
  let f := projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F Y
  let _ : IsIso (scalarProjection.{max uJ vJ vC z}.map f) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (projectiveMappingComparison_weak g s dC F Y)
  exact asIso (scalarProjection.{max uJ vJ vC z}.map f)

/-- Genuine derived mapping out of the same actual projective homotopy colimit is the genuine scalar homotopy limit of
its mapping spaces. -/
def projectiveReplacedMappingIso (F : J ⥤ C) (Y : C) :
    scalarProjection.{max uJ vJ vC z}.obj
        (outHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC ((projectiveHomotopyColimit g s).obj F) Y) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).obj
          (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y)) := by
  let _ : IsCofibrant ((projectiveHomotopyColimit g s).obj F) := projectiveHomotopyColimit_isCofibrant g s F
  exact (rightComplexReplacementIso.{uC, vC, max uJ vJ z} dC
    ((projectiveHomotopyColimit g s).obj F) Y).symm ≪≫
      projectiveMappingComparisonIso.{uJ, vJ, uC, vC, w, z} g s dC F Y

/-- The forward derived comparison retains the inverse of the same original coefficient Q leg and the entire diagram
comparison. -/
theorem projectiveReplacedMappingIso_hom (F : J ⥤ C) (Y : C) :
    (projectiveReplacedMappingIso.{uJ, vJ, uC, vC, w, z} g s dC F Y).hom =
      (letI := projectiveHomotopyColimit_isCofibrant g s F
       (rightComplexReplacementIso.{uC, vC, max uJ vJ z} dC ((projectiveHomotopyColimit g s).obj F) Y).inv) ≫
        scalarProjection.{max uJ vJ vC z}.map
          (projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F Y) := rfl

end OriginalProjectiveHomotopyMapping

section WeakCoefficientMapping

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

section Left
variable [HasColimitsOfSize.{0, max z vC} C]

/-- The actual lifted left-frame scalar Quillen pair preserves every original weak map between fibrant coefficients. -/
theorem liftedLeftHom_map_weak (X : C) {Y Z : C} [IsFibrant Y] [IsFibrant Z]
    (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences SSet.{max z vC}
      ((liftedLeftHomFunctor.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).map f) := by
  let adj := liftedTensorHomAdjunction.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)
  let _ : adj.IsQuillenAdjunction := originalLiftedTensor_isQuillen dC X
  let _ : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f)

end Left
section Right
variable [HasLimitsOfSize.{0, max z vC} C]

/-- The genuine lifted right-frame Quillen pair preserves every original weak map between cofibrant coefficients. -/
theorem liftedRightHom_map_weak (Y : C) {X Z : C} [IsCofibrant X] [IsCofibrant Z]
    (f : X ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences SSet.{max z vC}
      ((liftedRightHomFunctor.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)).map f.op) := by
  let adj := liftedCotensorHomAdjunction.{uC, vC, z} ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : adj.IsQuillenAdjunction := originalLiftedCotensor_isQuillen dC Y
  let _ : IsFibrant (Opposite.op X) := cofibrant_op_isFibrant _
  let _ : IsFibrant (Opposite.op Z) := cofibrant_op_isFibrant _
  let _ : WeakEquivalence f.op := (weakEquivalence_iff _).mpr (by rw [weakEquivalences_op]; exact hf)
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f.op)

end Right
end WeakCoefficientMapping

section CanonicalPointwiseMapping

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The original diagram, with the same coefficient R at each original vertex, gives the canonical derived mapping
diagram. -/
def canonicalIntoMappingDiagram (X : C) (F : J ⥤ C) : J ⥤ SSet.{max uJ vJ vC z} :=
  (F ⋙ dC.R) ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)

/-- The original inverse diagram, with the same coefficient Q at each original vertex, gives the canonical derived
mapping diagram. -/
def canonicalOutMappingDiagram (F : J ⥤ C) (Y : C) : Jᵒᵖ ⥤ SSet.{max uJ vJ vC z} :=
  (F.op ⋙ dC.Q.op) ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)

/-- Each original covariant mapping vertex is exactly its genuine original left homotopy function complex. -/
theorem canonicalIntoMappingDiagram_obj (X : C) (F : J ⥤ C) (j : J) :
    (canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F).obj j =
      intoHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC X (F.obj j) := rfl

/-- Each original inverse mapping vertex is exactly its original right homotopy function complex. -/
theorem canonicalOutMappingDiagram_obj (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    (canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y).obj j =
      outHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC (F.obj j.unop) Y := rfl

end CanonicalPointwiseMapping

section CanonicalInjectiveSpan

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The common mapping diagram retains both the actual diagram R and the original coefficient R. -/
def injectiveMappingCenter (X : C) (F : J ⥤ C) : J ⥤ SSet.{max uJ vJ vC z} := by
  letI := injectiveModel g κLP s
  exact canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X ((injectiveReplacements g κLP s).R.obj F)

/-- The first entire natural span leg keeps the original coefficient R unit on each original R-diagram coefficient. -/
def injectiveMappingSpanLeft (X : C) (F : J ⥤ C) :
    injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F ⟶
      injectiveMappingCenter.{uJ, vJ, uC, vC, w, z} g κLP s dC X F := by
  letI := injectiveModel g κLP s
  exact Functor.whiskerRight (Functor.whiskerLeft ((injectiveReplacements g κLP s).R.obj F) dC.r)
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))

/-- The second entire natural span leg retains the original diagram R unit and its original coefficient R image. -/
def injectiveMappingSpanRight (X : C) (F : J ⥤ C) :
    canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F ⟶
      injectiveMappingCenter.{uJ, vJ, uC, vC, w, z} g κLP s dC X F := by
  letI := injectiveModel g κLP s
  exact Functor.whiskerRight (Functor.whiskerRight ((injectiveReplacements g κLP s).r.app F) dC.R)
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))

variable [HasColimitsOfSize.{0, max uJ vJ vC z} C]

/-- The first original injective mapping span leg is weak at every original vertex, from original R-diagram fibrancy. -/
theorem injectiveMappingSpanLeft_weak (X : C) (F : J ⥤ C) (j : J) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((injectiveMappingSpanLeft.{uJ, vJ, uC, vC, w, z} g κLP s dC X F).app j) := by
  let _ := injectiveModel g κLP s
  let _ : IsFibrant (((injectiveReplacements g κLP s).R.obj F).obj j) := injectiveR_vertex_fibrant g s κLP F j
  exact leftComplexReplacement_weak.{uC, vC, max uJ vJ z} dC X
    (((injectiveReplacements g κLP s).R.obj F).obj j)

/-- The second original span leg is weak at every original vertex, from the same original diagram and coefficient R
maps. -/
theorem injectiveMappingSpanRight_weak (X : C) (F : J ⥤ C) (j : J) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((injectiveMappingSpanRight.{uJ, vJ, uC, vC, w, z} g κLP s dC X F).app j) := by
  let _ := injectiveModel g κLP s
  let _ : IsFibrant (dC.R.obj (F.obj j)) := dC.r_fibrant _
  let _ : IsFibrant (dC.R.obj (((injectiveReplacements g κLP s).R.obj F).obj j)) := dC.r_fibrant _
  let f : F.obj j ⟶ ((injectiveReplacements g κLP s).R.obj F).obj j :=
    ((injectiveReplacements g κLP s).r.app F).app j
  exact liftedLeftHom_map_weak.{uC, vC, max uJ vJ z} dC X (dC.R.map f)
    (dC.r_map_weak f (injectiveR_vertex_weak g s κLP F j))

/-- Both original R choices give the same genuine scalar homotopy limit of mapping spaces, with the full span
retained. -/
def injectivePointwiseMappingIso (X : C) (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).obj
          (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).obj
          (canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F)) := by
  let f := (scalarHomotopyLimit.{uJ, vJ, max vC z} J).map
    (injectiveMappingSpanLeft.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)
  let h := (scalarHomotopyLimit.{uJ, vJ, max vC z} J).map
    (injectiveMappingSpanRight.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)
  let _ : IsIso (scalarProjection.{max uJ vJ vC z}.map f) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} J _
        (injectiveMappingSpanLeft_weak g κLP s dC X F))
  let _ : IsIso (scalarProjection.{max uJ vJ vC z}.map h) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} J _
        (injectiveMappingSpanRight_weak g κLP s dC X F))
  exact asIso (scalarProjection.map f) ≪≫ (asIso (scalarProjection.map h)).symm

variable [HasLimitsOfShape J C]

/-- Genuine derived mapping into the original homotopy limit is the genuine homotopy limit of canonical per-vertex
derived mapping spaces. -/
def injectiveHomotopyLimitMappingIso (X : C) (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.obj
        (intoHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC X ((injectiveHomotopyLimit g κLP s).obj F)) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).obj
          (canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F)) :=
  injectiveReplacedMappingIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X F ≪≫
    injectivePointwiseMappingIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X F

end CanonicalInjectiveSpan

section CanonicalProjectiveSpan

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The common inverse mapping diagram retains both actual diagram Q and original coefficient Q. -/
def projectiveMappingCenter (F : J ⥤ C) (Y : C) : Jᵒᵖ ⥤ SSet.{max uJ vJ vC z} := by
  letI := projectiveModel g s
  exact canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC ((projectiveReplacements g s).Q.obj F) Y

/-- The first whole inverse span leg retains each original coefficient Q counit on the original Q diagram. -/
def projectiveMappingSpanLeft (F : J ⥤ C) (Y : C) :
    projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y ⟶
      projectiveMappingCenter.{uJ, vJ, uC, vC, w, z} g s dC F Y := by
  letI := projectiveModel g s
  exact Functor.whiskerRight (Functor.whiskerLeft ((projectiveReplacements g s).Q.obj F).op (NatTrans.op dC.q))
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))

/-- The second whole inverse span leg retains the same original diagram Q counit and its actual coefficient Q image. -/
def projectiveMappingSpanRight (F : J ⥤ C) (Y : C) :
    canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y ⟶
      projectiveMappingCenter.{uJ, vJ, uC, vC, w, z} g s dC F Y := by
  letI := projectiveModel g s
  exact Functor.whiskerRight (Functor.whiskerRight (NatTrans.op ((projectiveReplacements g s).q.app F)) dC.Q.op)
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))

variable [HasLimitsOfSize.{0, max uJ vJ vC z} C]

/-- The first original inverse mapping span leg is weak at every unchanged coefficient, from actual projective Q
cofibrancy. -/
theorem projectiveMappingSpanLeft_weak (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((projectiveMappingSpanLeft.{uJ, vJ, uC, vC, w, z} g s dC F Y).app j) := by
  let _ := projectiveModel g s
  let _ : IsCofibrant (((projectiveReplacements g s).Q.obj F).obj j.unop) := projectiveQ_vertex_cofibrant g s F j.unop
  exact rightComplexReplacement_weak.{uC, vC, max uJ vJ z} dC
    (((projectiveReplacements g s).Q.obj F).obj j.unop) Y

/-- The second inverse span leg is weak at every original coefficient, from the same actual diagram and coefficient Q
maps. -/
theorem projectiveMappingSpanRight_weak (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((projectiveMappingSpanRight.{uJ, vJ, uC, vC, w, z} g s dC F Y).app j) := by
  let _ := projectiveModel g s
  let _ : IsCofibrant (dC.Q.obj (((projectiveReplacements g s).Q.obj F).obj j.unop)) := dC.q_cofibrant _
  let _ : IsCofibrant (dC.Q.obj (F.obj j.unop)) := dC.q_cofibrant _
  let f : ((projectiveReplacements g s).Q.obj F).obj j.unop ⟶ F.obj j.unop :=
    ((projectiveReplacements g s).q.app F).app j.unop
  exact liftedRightHom_map_weak.{uC, vC, max uJ vJ z} dC Y (dC.Q.map f)
    (dC.q_map_weak f (projectiveQ_vertex_weak g s F j.unop))

/-- Both original Q choices give the same actual scalar homotopy limit, retaining the whole original natural comparison
span. -/
def projectivePointwiseMappingIso (F : J ⥤ C) (Y : C) :
    scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).obj
          (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y)) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).obj
          (canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y)) := by
  let f := (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).map
    (projectiveMappingSpanLeft.{uJ, vJ, uC, vC, w, z} g s dC F Y)
  let h := (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).map
    (projectiveMappingSpanRight.{uJ, vJ, uC, vC, w, z} g s dC F Y)
  let _ : IsIso (scalarProjection.{max uJ vJ vC z}.map f) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} Jᵒᵖ _
        (projectiveMappingSpanLeft_weak g s dC F Y))
  let _ : IsIso (scalarProjection.{max uJ vJ vC z}.map h) :=
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} Jᵒᵖ _
        (projectiveMappingSpanRight_weak g s dC F Y))
  exact asIso (scalarProjection.map f) ≪≫ (asIso (scalarProjection.map h)).symm

variable [HasColimitsOfShape J C]

/-- Genuine derived mapping out of the original homotopy colimit is the genuine homotopy limit of canonical per-vertex
derived mapping spaces. -/
def projectiveHomotopyColimitMappingIso (F : J ⥤ C) (Y : C) :
    scalarProjection.{max uJ vJ vC z}.obj
        (outHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC ((projectiveHomotopyColimit g s).obj F) Y) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).obj
          (canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y)) :=
  projectiveReplacedMappingIso.{uJ, vJ, uC, vC, w, z} g s dC F Y ≪≫
    projectivePointwiseMappingIso.{uJ, vJ, uC, vC, w, z} g s dC F Y

end CanonicalProjectiveSpan

section OriginalComplexReadbacks

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [HasZeroObject C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The lifted left complex is the original pointed left homotopy function complex on its original underlying simplicial
carrier. -/
def intoHomotopyFunctionComplexOriginalIso (X Y : C) :
    intoHomotopyFunctionComplex.{uC, vC, z} dC X Y ≅
      SSet.uliftFunctor.{z, vC}.obj (PointedFramingAction.pointedLeftSpace dC X Y).right :=
  (liftedLeftHomIso.{uC, vC, z} ((PointedFramingAction.leftFrame dC).obj X)).app (dC.R.obj Y)

/-- The lifted right complex retains the entire original pointed right homotopy function complex carrier. -/
def outHomotopyFunctionComplexOriginalIso (X Y : C) :
    outHomotopyFunctionComplex.{uC, vC, z} dC X Y ≅
      SSet.uliftFunctor.{z, vC}.obj (PointedFramingAction.pointedRightSpace dC X Y).right := Iso.refl _

end OriginalComplexReadbacks

section FullFrameHomNaturality

variable {C : Type uC} [Category.{vC} C]

/-- Every whole original left-frame arrow gives its actual natural precomposition on all coefficient targets. -/
def leftHomPrecompNat {A A' : CosimplicialObject C} (a : A ⟶ A') :
    PointedFramingAction.leftHomFunctor A' ⟶ PointedFramingAction.leftHomFunctor A :=
  Functor.whiskerLeft (SimplicialObject.const C) (ResolutionHomComplex.bifunctor.map a.op)

/-- The same original frame arrow acts on the full higher-universe left Hom functor. -/
def liftedLeftHomPrecompNat {A A' : CosimplicialObject C} (a : A ⟶ A') :
    liftedLeftHomFunctor.{uC, vC, z} A' ⟶ liftedLeftHomFunctor.{uC, vC, z} A :=
  (liftedLeftHomIso A').hom ≫ Functor.whiskerRight (leftHomPrecompNat a) SSet.uliftFunctor.{z, vC} ≫
    (liftedLeftHomIso A).inv

/-- Every original right-frame arrow acts on all original source coefficients by the same lifted postcomposition. -/
def liftedRightHomPostcompNat {B B' : SimplicialObject C} (b : B ⟶ B') :
    liftedRightHomFunctor.{uC, vC, z} B ⟶ liftedRightHomFunctor.{uC, vC, z} B' :=
  Functor.whiskerRight (ResolutionHomComplex.CanonicalEnrichment.rightBifunctor.flip.map b)
    SSet.uliftFunctor.{z, vC}

/-- Every lifted precomposition coefficient retains the entire original degreewise frame map. -/
theorem liftedLeftHomPrecompNat_app {A A' : CosimplicialObject C} (a : A ⟶ A')
    (Y : C) (n : SimplexCategoryᵒᵖ) (f : ((liftedLeftHomFunctor.{uC, vC, z} A').obj Y).obj n) :
    ((liftedLeftHomPrecompNat.{uC, vC, z} a).app Y).app n f = ULift.up (a.app n.unop ≫ f.down) := rfl

variable [ModelCategory C] (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The source coefficient acts on the genuine left complex through that same complete original left frame map. -/
def intoComplexSourceMap {X X' : C} (a : X ⟶ X') (Y : C) :
    intoHomotopyFunctionComplex.{uC, vC, z} dC X' Y ⟶ intoHomotopyFunctionComplex.{uC, vC, z} dC X Y :=
  (liftedLeftHomPrecompNat.{uC, vC, z} ((PointedFramingAction.leftFrame dC).map a)).app (dC.R.obj Y)

/-- The target coefficient acts through the same original right frame map, retaining the original Q source. -/
def outComplexTargetMap (X : C) {Y Y' : C} (b : Y ⟶ Y') :
    outHomotopyFunctionComplex.{uC, vC, z} dC X Y ⟶ outHomotopyFunctionComplex.{uC, vC, z} dC X Y' :=
  (liftedRightHomPostcompNat.{uC, vC, z} ((PointedFramingAction.rightFrame dC).map b)).app (.op (dC.Q.obj X))

end FullFrameHomNaturality

section OriginalDiagramComparisonNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  (dC : GeneratedFunctorialReplacements.Data (C := C))

section Projective
variable [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]

/-- The entire projective mapping comparison is natural in every original whole-diagram arrow. -/
theorem projectiveMappingComparison_naturality {F G : J ⥤ C} (a : F ⟶ G) (Y : C) :
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        ((projectiveHomotopyColimit g s).map a).op ≫
        projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F Y =
      projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC G Y ≫
        (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).map
          (projectiveQMappingMap.{uJ, vJ, uC, vC, w, z} g s dC a Y) := by
  let _ := projectiveModel g s
  dsimp only [projectiveMappingComparison, projectiveQMappingMap, projectiveHomotopyColimit, homotopyColimit]
  erw [← Category.assoc, liftedRightColimitIso_naturality, Category.assoc]
  exact congrArg (fun m =>
    (liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.rightFrame dC).obj Y) ((projectiveReplacements g s).Q.obj G)).hom ≫ m)
    ((scalarLimitComparison.{uJ, vJ, max vC z} Jᵒᵖ).naturality
      (Functor.whiskerRight (NatTrans.op ((projectiveReplacements g s).Q.map a))
        (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))))

end Projective
section Injective
variable (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]

/-- The entire injective mapping comparison is natural in every original whole-diagram arrow. -/
theorem injectiveMappingComparison_naturality (X : C) {F G : J ⥤ C} (a : F ⟶ G) :
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        ((injectiveHomotopyLimit g κLP s).map a) ≫
        injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X G =
      injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F ≫
        (scalarHomotopyLimit.{uJ, vJ, max vC z} J).map
          (injectiveRMappingMap.{uJ, vJ, uC, vC, w, z} g κLP s dC X a) := by
  let _ := injectiveModel g κLP s
  dsimp only [injectiveMappingComparison, injectiveRMappingMap, injectiveHomotopyLimit, homotopyLimit]
  erw [← Category.assoc, liftedLeftLimitIso_naturality, Category.assoc]
  exact congrArg (fun m =>
    (liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.leftFrame dC).obj X) ((injectiveReplacements g κLP s).R.obj F)).hom ≫ m)
    ((scalarLimitComparison.{uJ, vJ, max vC z} J).naturality
      (Functor.whiskerRight ((injectiveReplacements g κLP s).R.map a)
        (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))))

end Injective
end OriginalDiagramComparisonNaturality

section InjectiveNaturalComparison

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C)) (X : C)

/-- The whole original homotopy-limit functor followed by its actual left frame Hom and scalar localization. -/
def injectiveRawMappingFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  injectiveHomotopyLimit g κLP s ⋙
    liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X) ⋙ scalarProjection

/-- The whole canonical derived mapping functor into the original homotopy limit retains coefficient R. -/
def injectiveDerivedMappingFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  injectiveHomotopyLimit g κLP s ⋙ dC.R ⋙
    liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X) ⋙ scalarProjection

/-- The target functor computes the genuine homotopy limit of each original canonical mapping diagram. -/
def injectiveCanonicalMappingLimitFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
      (dC.R ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)) ⋙
    scalarHomotopyLimit.{uJ, vJ, max vC z} J ⋙ scalarProjection

/-- The original whole-diagram R mapping presentation, as one complete functor. -/
def injectiveReplacedMappingLimitFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := injectiveModel g κLP s
  exact (injectiveReplacements g κLP s).R ⋙
    (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)) ⋙
    scalarHomotopyLimit.{uJ, vJ, max vC z} J ⋙ scalarProjection

/-- The same actual coefficient R unit is an isomorphism of the complete localized source functors. -/
def injectiveSourceReplacementNatIso :
    injectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ≅
      injectiveDerivedMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X := by
  let t : injectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ⟶
      injectiveDerivedMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X :=
    Functor.whiskerRight (Functor.whiskerRight
      (Functor.whiskerLeft (injectiveHomotopyLimit g κLP s) dC.r)
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))) scalarProjection
  let _ : ∀ F, IsIso (t.app F) := fun F => by
    let _ : IsFibrant ((injectiveHomotopyLimit g κLP s).obj F) := injectiveHomotopyLimit_isFibrant g κLP s F
    exact Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (leftComplexReplacement_weak.{uC, vC, max uJ vJ z} dC X ((injectiveHomotopyLimit g κLP s).obj F))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Every original diagram arrow is retained in the actual mapping comparison natural transformation. -/
def injectiveRawMappingNatIso :
    injectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ≅
      injectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X := by
  let t : injectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ⟶
      injectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X :=
    { app F := scalarProjection.map (injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)
      naturality F G a := (scalarProjection.map_comp _ _).symm.trans
        ((scalarProjection.congr_map (injectiveMappingComparison_naturality.{uJ, vJ, uC, vC, w, z}
          g s dC κLP X a)).trans (scalarProjection.map_comp _ _)) }
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (injectiveMappingComparison_weak.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The common original R/R mapping presentation is a single functor on all original diagrams and arrows. -/
def injectiveCenterMappingLimitFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := injectiveModel g κLP s
  exact (injectiveReplacements g κLP s).R ⋙
    (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
      (dC.R ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)) ⋙
    scalarHomotopyLimit.{uJ, vJ, max vC z} J ⋙ scalarProjection

/-- The first actual R/R span leg is an isomorphism of the whole scalar homotopy-limit functors. -/
def injectivePointwiseSpanLeftNatIso :
    injectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ≅
      injectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X := by
  letI := injectiveModel g κLP s
  let t : injectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ⟶
      injectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X :=
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.whiskerLeft (injectiveReplacements g κLP s).R
          ((Functor.whiskeringRight J C C).map dC.r))
        ((Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
          (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))))
      (scalarHomotopyLimit.{uJ, vJ, max vC z} J ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} J _
        (injectiveMappingSpanLeft_weak g κLP s dC X F))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The second original diagram/coefficient R span leg is an isomorphism of whole functors. -/
def injectivePointwiseSpanRightNatIso :
    injectiveCanonicalMappingLimitFunctor.{uJ, vJ, uC, vC, z} dC X ≅
      injectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X := by
  letI := injectiveModel g κLP s
  let t : injectiveCanonicalMappingLimitFunctor.{uJ, vJ, uC, vC, z} dC X ⟶
      injectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X :=
    Functor.whiskerRight
      (Functor.whiskerRight (injectiveReplacements g κLP s).r
        ((Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
          (dC.R ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))))
      (scalarHomotopyLimit.{uJ, vJ, max vC z} J ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} J _
        (injectiveMappingSpanRight_weak g κLP s dC X F))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The genuine derived mapping/holim comparison is one natural isomorphism on every original diagram object and
arrow. -/
def injectiveHomotopyLimitMappingNatIso :
    injectiveDerivedMappingFunctor.{uJ, vJ, uC, vC, w, z} g κLP s dC X ≅
      injectiveCanonicalMappingLimitFunctor.{uJ, vJ, uC, vC, z} dC X :=
  (injectiveSourceReplacementNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).symm ≪≫
    injectiveRawMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X ≪≫
      injectivePointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X ≪≫
        (injectivePointwiseSpanRightNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).symm

end InjectiveNaturalComparison

section ProjectiveNaturalComparison

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C)) (Y : C)

/-- The whole original projective homotopy-colimit functor acts contravariantly through its actual right frame Hom. -/
def projectiveRawMappingFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (projectiveHomotopyColimit g s).op ⋙
    liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y) ⋙ scalarProjection

/-- The complete canonical derived mapping source retains the original coefficient Q of the original hocolim. -/
def projectiveDerivedMappingFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (projectiveHomotopyColimit g s).op ⋙ dC.Q.op ⋙
    liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y) ⋙ scalarProjection

/-- The whole original canonical inverse mapping diagram followed by its actual scalar homotopy limit. -/
def projectiveCanonicalMappingLimitFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (Functor.opUnopEquiv J C).functor ⋙
    (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
      (dC.Q.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)) ⋙
    scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ ⋙ scalarProjection

/-- The actual whole projective Q mapping presentation is one complete inverse-diagram functor. -/
def projectiveReplacedMappingLimitFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := projectiveModel g s
  exact (projectiveReplacements g s).Q.op ⋙ (Functor.opUnopEquiv J C).functor ⋙
    (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)) ⋙
    scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ ⋙ scalarProjection

/-- The same original coefficient Q counit gives an isomorphism of the whole scalar-localized source functors. -/
def projectiveSourceReplacementNatIso :
    projectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ≅
      projectiveDerivedMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y := by
  let t : projectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ⟶
      projectiveDerivedMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y :=
    Functor.whiskerRight (Functor.whiskerRight
      (Functor.whiskerLeft (projectiveHomotopyColimit g s).op (NatTrans.op dC.q))
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))) scalarProjection
  let _ : ∀ F, IsIso (t.app F) := fun F => by
    let _ : IsCofibrant ((projectiveHomotopyColimit g s).obj F.unop) := projectiveHomotopyColimit_isCofibrant g s F.unop
    exact Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (rightComplexReplacement_weak.{uC, vC, max uJ vJ z} dC ((projectiveHomotopyColimit g s).obj F.unop) Y)
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The actual right-complex comparison is one natural isomorphism retaining every original diagram arrow. -/
def projectiveRawMappingNatIso :
    projectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ≅
      projectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y := by
  let t : projectiveRawMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ⟶
      projectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y :=
    { app F := scalarProjection.map (projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F.unop Y)
      naturality F G a := (scalarProjection.map_comp _ _).symm.trans
        ((scalarProjection.congr_map (projectiveMappingComparison_naturality.{uJ, vJ, uC, vC, w, z}
          g s dC a.unop Y)).trans (scalarProjection.map_comp _ _)) }
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (projectiveMappingComparison_weak.{uJ, vJ, uC, vC, w, z} g s dC F.unop Y)
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The original diagram-Q/coefficient-Q common mapping presentation is a whole functor. -/
def projectiveCenterMappingLimitFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := projectiveModel g s
  exact (projectiveReplacements g s).Q.op ⋙ (Functor.opUnopEquiv J C).functor ⋙
    (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
      (dC.Q.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)) ⋙
    scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ ⋙ scalarProjection

/-- The first original Q/Q span is an isomorphism of the whole inverse mapping-limit functors. -/
def projectivePointwiseSpanLeftNatIso :
    projectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ≅
      projectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y := by
  letI := projectiveModel g s
  let t : projectiveReplacedMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ⟶
      projectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y :=
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.whiskerLeft ((projectiveReplacements g s).Q.op ⋙ (Functor.opUnopEquiv J C).functor)
          ((Functor.whiskeringRight Jᵒᵖ Cᵒᵖ Cᵒᵖ).map (NatTrans.op dC.q)))
        ((Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
          (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))))
      (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} Jᵒᵖ _
        (projectiveMappingSpanLeft_weak g s dC F.unop Y))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The second actual Q/Q span retains the original diagram counit as an isomorphism of whole functors. -/
def projectivePointwiseSpanRightNatIso :
    projectiveCanonicalMappingLimitFunctor.{uJ, vJ, uC, vC, z} dC Y ≅
      projectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y := by
  letI := projectiveModel g s
  let t : projectiveCanonicalMappingLimitFunctor.{uJ, vJ, uC, vC, z} dC Y ⟶
      projectiveCenterMappingLimitFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y :=
    Functor.whiskerRight
      (Functor.whiskerRight (NatTrans.op (projectiveReplacements g s).q)
        ((Functor.opUnopEquiv J C).functor ⋙
          (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
            (dC.Q.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))))
      (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarHomotopyLimit_map_weak.{uJ, vJ, max vC z} Jᵒᵖ _
        (projectiveMappingSpanRight_weak g s dC F.unop Y))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The genuine derived mapping/hocolim comparison is one natural isomorphism on all original diagram objects and
arrows. -/
def projectiveHomotopyColimitMappingNatIso :
    projectiveDerivedMappingFunctor.{uJ, vJ, uC, vC, w, z} g s dC Y ≅
      projectiveCanonicalMappingLimitFunctor.{uJ, vJ, uC, vC, z} dC Y :=
  (projectiveSourceReplacementNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).symm ≪≫
    projectiveRawMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y ≪≫
      projectivePointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y ≪≫
        (projectivePointwiseSpanRightNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).symm

end ProjectiveNaturalComparison

section CoefficientLimitNaturality

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]

section Left
variable [HasColimitsOfSize.{0, max z vC} C] [HasLimitsOfShape J C]
  [HasLimitsOfShape J SSet.{max z vC}]

/-- Every original whole frame map commutes with the full actual mapping/limit comparison. -/
theorem liftedLeftLimitIso_frame_naturality {A A' : CosimplicialObject C} (a : A ⟶ A') (F : J ⥤ C) :
    (liftedLeftHomPrecompNat.{uC, vC, z} a).app (limit F) ≫
        (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).hom =
      (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫
        lim.map (Functor.whiskerLeft F (liftedLeftHomPrecompNat.{uC, vC, z} a)) := by
  let α := liftedLeftHomPrecompNat.{uC, vC, z} a
  apply limit.hom_ext
  intro j
  calc
    _ = α.app (limit F) ≫ (liftedLeftHomFunctor.{uC, vC, z} A).map (limit.π F j) :=
      (Category.assoc _ _ _).trans (congrArg (fun m => α.app (limit F) ≫ m)
        (liftedLeftLimitIso_hom_projection.{uJ, vJ, uC, vC, z} A F j))
    _ = (liftedLeftHomFunctor.{uC, vC, z} A').map (limit.π F j) ≫ α.app (F.obj j) :=
      (α.naturality (limit.π F j)).symm
    _ = _ := by
      symm
      calc
        _ = (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫
            (limMap (Functor.whiskerLeft F α) ≫ limit.π (F ⋙ liftedLeftHomFunctor.{uC, vC, z} A) j) :=
          Category.assoc _ _ _
        _ = (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫
            (limit.π (F ⋙ liftedLeftHomFunctor.{uC, vC, z} A') j ≫ α.app (F.obj j)) :=
          congrArg (fun m => (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫ m)
            (limMap_π (Functor.whiskerLeft F α) j)
        _ = _ := (Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ α.app (F.obj j))
            (liftedLeftLimitIso_hom_projection.{uJ, vJ, uC, vC, z} A' F j))

end Left
section Right
variable [HasLimitsOfSize.{0, max z vC} C] [HasColimitsOfShape J C]
  [HasLimitsOfShape Jᵒᵖ SSet.{max z vC}]

/-- Every actual right-frame arrow retains the complete original colimit/mapping comparison square. -/
theorem liftedRightColimitIso_frame_naturality {B B' : SimplicialObject C} (b : B ⟶ B') (F : J ⥤ C) :
    (liftedRightHomPostcompNat.{uC, vC, z} b).app (.op (colimit F)) ≫
        (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B' F).hom =
      (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).hom ≫
        lim.map (Functor.whiskerLeft F.op (liftedRightHomPostcompNat.{uC, vC, z} b)) := by
  apply limit.hom_ext
  intro j
  erw [Category.assoc, liftedRightColimitIso_hom_projection, Category.assoc]
  rw [show lim.map (Functor.whiskerLeft F.op (liftedRightHomPostcompNat.{uC, vC, z} b)) =
    limMap (Functor.whiskerLeft F.op (liftedRightHomPostcompNat.{uC, vC, z} b)) from rfl,
    limMap_π, ← Category.assoc, liftedRightColimitIso_hom_projection]
  exact ((liftedRightHomPostcompNat.{uC, vC, z} b).naturality (colimit.ι F j.unop).op).symm

end Right
end CoefficientLimitNaturality

section OriginalCallerMappingComparisons

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  (dC : GeneratedFunctorialReplacements.Data (C := C))

section Projective
variable [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]

/-- Every original caller cocone retains its same Q leg in the full right-HFC/hocolim comparison. -/
theorem projectiveMappingComparison_desc (F : J ⥤ C) (c : Cocone F) (Y : C) (j : Jᵒᵖ) :
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        (letI := projectiveModel g s; (desc (projectiveReplacements g s) F c).op) ≫
      (projectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g s dC F Y ≫
        (letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
         limitProjection (scalarReplacements.{uJ, vJ, max vC z} Jᵒᵖ)
           (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y) j)) =
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        (letI := projectiveModel g s
         (((projectiveReplacements g s).q.app F).app j.unop ≫ c.ι.app j.unop).op) ≫
        (letI := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
         ((scalarReplacements.{uJ, vJ, max vC z} Jᵒᵖ).r.app
           (projectiveQMappingDiagram.{uJ, vJ, uC, vC, w, z} g s dC F Y)).app j) := by
  let _ := projectiveModel g s
  let _ := scalarModel.{uJ, vJ, max vC z} Jᵒᵖ
  erw [projectiveMappingComparison_projection, ← Category.assoc, ← Functor.map_comp]
  congr 1
  apply Functor.congr_map
  apply Quiver.Hom.unop_inj
  exact injection_desc (projectiveReplacements g s) F c j.unop

end Projective
section Injective
variable (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]

/-- Every original caller cone retains the original R leg in the complete left-HFC/holim comparison. -/
theorem injectiveMappingComparison_lift (X : C) (F : J ⥤ C) (c : Cone F) (j : J) :
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        (letI := injectiveModel g κLP s; lift (injectiveReplacements g κLP s) F c) ≫
      (injectiveMappingComparison.{uJ, vJ, uC, vC, w, z} g κLP s dC X F ≫
        (letI := scalarModel.{uJ, vJ, max vC z} J
         limitProjection (scalarReplacements.{uJ, vJ, max vC z} J)
           (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F) j)) =
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        (letI := injectiveModel g κLP s; c.π.app j ≫ ((injectiveReplacements g κLP s).r.app F).app j) ≫
        (letI := scalarModel.{uJ, vJ, max vC z} J
         ((scalarReplacements.{uJ, vJ, max vC z} J).r.app
           (injectiveRMappingDiagram.{uJ, vJ, uC, vC, w, z} g κLP s dC X F)).app j) := by
  let _ := injectiveModel g κLP s
  let _ := scalarModel.{uJ, vJ, max vC z} J
  erw [injectiveMappingComparison_projection, ← Category.assoc, ← Functor.map_comp, lift_projection]

end Injective
end OriginalCallerMappingComparisons

section ReedySourceConditions

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The original suitable-constants condition consists of actual latching corners of each coefficient cofibration. -/
def CofibrantConstants : Prop := ∀ {X Y : C} (p : X ⟶ Y), cofibrations C p →
  ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r ((Functor.const J).map p) j)

/-- The original dual suitable-constants condition consists of actual matching corners of each coefficient fibration. -/
def FibrantConstants : Prop := ∀ {X Y : C} (p : X ⟶ Y), fibrations C p →
  ∀ j, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r ((Functor.const J).map p) j)

/-- The actual original constant/limit adjunction is Quillen at precisely the stated source constant-corner
criterion. -/
theorem reedyLimit_isQuillen [HasLimitsOfShape J C] (h : CofibrantConstants r (C := C)) :
    letI := ReedyModel.modelCategory r Fc Ff
    (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := by
  let _ := ReedyModel.modelCategory r Fc Ff
  constructor
  · intro X Y p hp
    rw [ReedyModel.cofibrations_eq r Fc Ff]
    exact h p hp
  · intro X Y p hp
    refine ⟨?_, ?_⟩
    · rw [ReedyModel.cofibrations_eq r Fc Ff]
      exact h p hp.1
    · rw [ReedyModel.weakEquivalences_eq r Fc Ff]
      intro j
      exact hp.2

/-- The actual original colimit/constant adjunction is Quillen at the original matching-constant criterion. -/
theorem reedyColimit_isQuillen [HasColimitsOfShape J C] (h : FibrantConstants r (C := C)) :
    letI := ReedyModel.modelCategory r Fc Ff
    (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := by
  let _ := ReedyModel.modelCategory r Fc Ff
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y p hp
    rw [ReedyModel.fibrations_eq r Fc Ff]
    exact h p hp
  · intro X Y p hp
    refine ⟨?_, ?_⟩
    · rw [ReedyModel.fibrations_eq r Fc Ff]
      exact h p hp.1
    · rw [ReedyModel.weakEquivalences_eq r Fc Ff]
      intro j
      exact hp.2

/-- The same original Reedy latching corners prove coefficient cofibrations at every original vertex. -/
theorem reedyModel_cofibrations_le_objectwise :
    letI := ReedyModel.modelCategory r Fc Ff
    cofibrations (J ⥤ C) ≤ (cofibrations C).functorCategory J := by
  let _ := ReedyModel.modelCategory r Fc Ff
  intro X Y a ha j
  rw [ReedyModel.cofibrations_eq r Fc Ff] at ha
  exact ReedyModel.component_cofibration_of_latchingCorners r a ha j

/-- The same actual original Reedy matching corners prove coefficient fibrations at every original vertex. -/
theorem reedyModel_fibrations_le_objectwise :
    letI := ReedyModel.modelCategory r Fc Ff
    fibrations (J ⥤ C) ≤ (fibrations C).functorCategory J := by
  let _ := ReedyModel.modelCategory r Fc Ff
  intro X Y a ha j
  rw [ReedyModel.fibrations_eq r Fc Ff] at ha
  exact ReedyModel.component_fibration_of_matchingCorners r a ha j

/-- Every coefficient of the actual original Reedy Q diagram is cofibrant, from its original corner condition. -/
theorem reedyQ_vertex_cofibrant (F : J ⥤ C) (j : J) :
    IsCofibrant
      (letI := ReedyModel.modelCategory r Fc Ff; ((reedyReplacements r Fc Ff).Q.obj F).obj j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let QF := (reedyReplacements r Fc Ff).Q.obj F
  let hC : HasInitial C := inferInstance
  let _ : ∀ k : J, HasColimit ((Functor.empty.{0} (J ⥤ C)).flip.obj k) := fun _ => hC.has_colimit _
  let _ : PreservesColimit (Functor.empty.{0} (J ⥤ C)) ((evaluation J C).obj j) :=
    evaluation_preservesColimit _ j
  have h := reedyModel_cofibrations_le_objectwise r Fc Ff (initial.to QF)
    ((cofibration_iff _).mp ((reedyReplacements r Fc Ff).q_cofibrant F)) j
  exact (isCofibrant_iff_of_isInitial ((initial.to QF).app j)
    (IsInitial.isInitialObj ((evaluation J C).obj j) _ initialIsInitial)).mpr ((cofibration_iff _).mpr h)

/-- Every coefficient of the original Reedy R diagram is fibrant, from its actual original matching corners. -/
theorem reedyR_vertex_fibrant (F : J ⥤ C) (j : J) :
    IsFibrant
      (letI := ReedyModel.modelCategory r Fc Ff; ((reedyReplacements r Fc Ff).R.obj F).obj j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let RF := (reedyReplacements r Fc Ff).R.obj F
  let hC : HasTerminal C := inferInstance
  let _ : ∀ k : J, HasLimit ((Functor.empty.{0} (J ⥤ C)).flip.obj k) := fun _ => hC.has_limit _
  let _ : PreservesLimit (Functor.empty.{0} (J ⥤ C)) ((evaluation J C).obj j) := evaluation_preservesLimit _ j
  have h := reedyModel_fibrations_le_objectwise r Fc Ff (terminal.from RF)
    ((fibration_iff _).mp ((reedyReplacements r Fc Ff).r_fibrant F)) j
  exact (isFibrant_iff_of_isTerminal ((terminal.from RF).app j)
    (IsTerminal.isTerminalObj ((evaluation J C).obj j) _ terminalIsTerminal)).mpr ((fibration_iff _).mpr h)

end ReedySourceConditions

section ReedyScalarModel

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)

/-- The canonical boundary/horn coefficient factors construct the actual scalar Reedy model on the same index. -/
@[instance_reducible]
def scalarReedyModel : ModelCategory (J ⥤ SSet.{max uJ vJ z}) :=
  ReedyModel.modelCategory r
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.cofibrantFactorizationData
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.fibrantFactorizationData

/-- Both unchanged native scalar factor factories give the whole original Reedy mapping-diagram replacement. -/
def scalarReedyReplacements :
    letI := scalarReedyModel.{uJ, vJ, uD, z} r
    GeneratedFunctorialReplacements.Data (C := J ⥤ SSet.{max uJ vJ z}) :=
  reedyReplacements r
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.cofibrantFactorizationData
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.fibrantFactorizationData

/-- The genuine scalar Reedy homotopy limit uses these same original whole-diagram factors. -/
def scalarReedyHomotopyLimit : (J ⥤ SSet.{max uJ vJ z}) ⥤ SSet.{max uJ vJ z} := by
  letI := scalarReedyModel.{uJ, vJ, uD, z} r
  exact homotopyLimit (scalarReedyReplacements.{uJ, vJ, uD, z} r)

end ReedyScalarModel

section ReedyIntoMappingQuillen

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasColimitsOfSize.{0, max uJ vJ vC z} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The full actual left-frame Hom is Quillen on the original Reedy diagram models, by their original matching
corners. -/
theorem reedyIntoMapping_isQuillen (X : C) :
    letI := ReedyModel.modelCategory r Fc Ff
    letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
    ((liftedTensorHomAdjunction.{uC, vC, max uJ vJ z}
      ((PointedFramingAction.leftFrame dC).obj X)).whiskerRight J).IsQuillenAdjunction := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r
  let adj := liftedTensorHomAdjunction.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)
  let _ : adj.IsQuillenAdjunction := originalLiftedTensor_isQuillen dC X
  let H := liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)
  let _ : H.IsRightAdjoint := adj.isRightAdjoint
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro F G a ha
    rw [ReedyModel.fibrations_eq r Fc Ff] at ha
    rw [ReedyModel.fibrations_eq r
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.cofibrantFactorizationData
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.fibrantFactorizationData]
    intro j
    exact ((fibrations SSet.{max uJ vJ vC z}).arrow_mk_iso_iff
      (CategoryTheory.ReedyStructure.PostcomposeCorners.matchingArrowIso r H a j)).mp
        (Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) _ (ha j))
  · intro F G a ha
    rw [ReedyModel.trivialFibrations_eq r Fc Ff] at ha
    rw [ReedyModel.trivialFibrations_eq r
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.cofibrantFactorizationData
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.fibrantFactorizationData]
    intro j
    exact ((trivialFibrations SSet.{max uJ vJ vC z}).arrow_mk_iso_iff
      (CategoryTheory.ReedyStructure.PostcomposeCorners.matchingArrowIso r H a j)).mp
        (Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := adj) _ (ha j))

/-- Original Reedy diagram fibrancy proves fibrancy of the whole actual mapping diagram in the same scalar Reedy
model. -/
theorem reedyIntoMapping_isFibrant (X : C) (F : J ⥤ C) :
    letI := ReedyModel.modelCategory r Fc Ff
    letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
    IsFibrant F → IsFibrant (intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r
  intro hF
  let adj := (liftedTensorHomAdjunction.{uC, vC, max uJ vJ z}
    ((PointedFramingAction.leftFrame dC).obj X)).whiskerRight J
  let _ : adj.IsQuillenAdjunction := reedyIntoMapping_isQuillen r Fc Ff dC X
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) hF

end ReedyIntoMappingQuillen

section OppositeReedyHomCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The same original latching cocone, opposed along the canonical original boundary equivalence. -/
def originalOppositeLatchingCone (X : J ⥤ C) (j : J) :
    Cone (r.op.matchingDiagram X.op (.op j)) :=
  (Cone.postcompose (CategoryTheory.ReedyStructure.BoundaryOpposite.diagramIso r X j).inv).obj
    ((colimit.cocone (r.latchingDiagram X j)).op.whisker
      (CategoryTheory.ReedyStructure.BoundaryOpposite.equivalence r j).functor)

/-- The entire original latching universal property gives the actual opposite matching limit. -/
def originalOppositeLatchingIsLimit (X : J ⥤ C) (j : J) :
    IsLimit (originalOppositeLatchingCone r X j) :=
  (IsLimit.postcomposeInvEquiv (CategoryTheory.ReedyStructure.BoundaryOpposite.diagramIso r X j) _).symm
    ((colimit.isColimit (r.latchingDiagram X j)).op.whiskerEquivalence
      (CategoryTheory.ReedyStructure.BoundaryOpposite.equivalence r j))

/-- Every original proper boundary arrow retains its same original opposite latching injection. -/
theorem originalOppositeLatchingCone_projection (X : J ⥤ C) (j : J)
    (a : r.op.Matching (.op j)) :
    (originalOppositeLatchingCone r X j).π.app a =
      (colimit.ι (r.latchingDiagram X j) (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r
        j a)).op := by
  change (colimit.ι (r.latchingDiagram X j)
    (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r j a)).op ≫
    𝟙 _ = _
  exact Category.comp_id _

variable {E : Type uE} [Category.{vE} E] (T : Cᵒᵖ ⥤ E) [T.IsRightAdjoint]

/-- The actual right adjoint sends the entire original opposite latching cocone to its full matching cone. -/
def homOppositeMatchingCone (X : J ⥤ C) (j : J) :
    Cone (r.op.matchingDiagram (X.op ⋙ T) (.op j)) :=
  T.mapCone (originalOppositeLatchingCone r X j)

/-- The actual right adjoint preserves the original caller boundary's full universal property. -/
def homOppositeMatchingIsLimit (X : J ⥤ C) (j : J) :
    IsLimit (homOppositeMatchingCone r T X j) :=
  isLimitOfPreserves T (originalOppositeLatchingIsLimit r X j)

omit [T.IsRightAdjoint] in
/-- Every mapped proper boundary leg is the same actual right-adjoint image of the original latching injection. -/
theorem homOppositeMatchingCone_projection (X : J ⥤ C) (j : J)
    (a : r.op.Matching (.op j)) :
    (homOppositeMatchingCone r T X j).π.app a = T.map
      (colimit.ι (r.latchingDiagram X j) (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r
        j a)).op :=
  T.congr_map (originalOppositeLatchingCone_projection r X j a)

/-- The complete caller matching map is the actual right-adjoint image of the original opposite latching map. -/
theorem homOppositeMatchingMapWith (X : J ⥤ C) (j : J) :
    r.op.matchingMapWith (X.op ⋙ T) (.op j)
      (homOppositeMatchingCone r T X j) (homOppositeMatchingIsLimit r T X j) =
        T.map (CategoryTheory.ReedyStructure.latchingMap r X j).op := by
  apply (homOppositeMatchingIsLimit r T X j).hom_ext
  intro a
  erw [r.op.matchingMapWith_π, homOppositeMatchingCone_projection, ← T.map_comp]
  apply T.congr_map
  apply Quiver.Hom.unop_inj
  exact (CategoryTheory.ReedyStructure.latchingMap_ι r X j
    (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r j a)).symm

/-- Every whole original diagram transformation retains its same full opposite latching comparison. -/
theorem homOppositeMatchingComparisonWith {X Y : J ⥤ C} (a : X ⟶ Y) (j : J) :
    r.op.matchingComparisonWith (Functor.whiskerRight (NatTrans.op a) T) (.op j)
      (homOppositeMatchingCone r T Y j) (homOppositeMatchingCone r T X j)
      (homOppositeMatchingIsLimit r T X j) =
        T.map (colimMap (r.latchingTransformation a j)).op := by
  apply (homOppositeMatchingIsLimit r T X j).hom_ext
  intro b
  erw [r.op.matchingComparisonWith_π, homOppositeMatchingCone_projection,
    homOppositeMatchingCone_projection]
  change T.map (colimit.ι (r.latchingDiagram Y j)
      (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r j b)).op ≫
      T.map (a.app (r.op.matchingTarget b).unop).op =
    T.map (colimMap (r.latchingTransformation a j)).op ≫
      T.map (colimit.ι (r.latchingDiagram X j)
        (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r j b)).op
  erw [← T.map_comp, ← T.map_comp]
  apply T.congr_map
  apply Quiver.Hom.unop_inj
  exact (ι_colimMap (r.latchingTransformation a j)
    (CategoryTheory.ReedyStructure.BoundaryOpposite.matchingToLatchingObj r j b)).symm

variable [HasPushouts C]

/-- The original relative latching pushout gives the complete caller matching pullback after opposition and actual right
adjunction. -/
def homOppositeMatchingPullback {X Y : J ⥤ C} (a : X ⟶ Y) (j : J) :
    PullbackCone
      (r.op.matchingComparisonWith (Functor.whiskerRight (NatTrans.op a) T) (.op j)
        (homOppositeMatchingCone r T Y j) (homOppositeMatchingCone r T X j)
        (homOppositeMatchingIsLimit r T X j))
      (r.op.matchingMapWith (X.op ⋙ T) (.op j)
        (homOppositeMatchingCone r T X j) (homOppositeMatchingIsLimit r T X j)) :=
  PullbackCone.mk
    (T.map (pushout.inr (CategoryTheory.ReedyStructure.latchingMap r X j) (colimMap (r.latchingTransformation a j))).op)
    (T.map (pushout.inl (CategoryTheory.ReedyStructure.latchingMap r X j) (colimMap (r.latchingTransformation a
      j))).op) (by
      erw [homOppositeMatchingComparisonWith, homOppositeMatchingMapWith,
        ← T.map_comp, ← T.map_comp]
      apply T.congr_map
      apply Quiver.Hom.unop_inj
      exact (pushout.condition (f := CategoryTheory.ReedyStructure.latchingMap r X j)
        (g := colimMap (r.latchingTransformation a j))).symm)

/-- The actual original pushout universal property is retained as the entire mapped opposite pullback universal
property. -/
def homOppositeMatchingPullbackIsLimit {X Y : J ⥤ C} (a : X ⟶ Y) (j : J) :
    IsLimit (homOppositeMatchingPullback r T a j) := by
  let h := (IsPushout.of_hasPushout (CategoryTheory.ReedyStructure.latchingMap r X j)
    (colimMap (r.latchingTransformation a j))).op.map T
  exact CategoryTheory.ReedyStructure.PostcomposeCorners.pullbackMkIsLimitOfEq (w' := h.w)
    (homOppositeMatchingComparisonWith r T a j) (homOppositeMatchingMapWith r T X j)
    (homOppositeMatchingPullback r T a j).condition h.isLimit

/-- The same entire original opposite latching corner is the complete caller mapped matching corner. -/
theorem homOppositeMatchingCornerWith {X Y : J ⥤ C} (a : X ⟶ Y) (j : J) :
    r.op.matchingCornerWith (Functor.whiskerRight (NatTrans.op a) T) (.op j)
      (homOppositeMatchingCone r T Y j) (homOppositeMatchingIsLimit r T Y j)
      (homOppositeMatchingCone r T X j) (homOppositeMatchingIsLimit r T X j)
      (homOppositeMatchingPullback r T a j) (homOppositeMatchingPullbackIsLimit r T a j) =
        T.map (CategoryTheory.ReedyStructure.latchingCorner r a j).op := by
  apply PullbackCone.IsLimit.hom_ext (homOppositeMatchingPullbackIsLimit r T a j)
  · erw [r.op.matchingCornerWith_fst, homOppositeMatchingMapWith]
    change T.map (CategoryTheory.ReedyStructure.latchingMap r Y j).op =
      T.map (CategoryTheory.ReedyStructure.latchingCorner r a j).op ≫
        T.map (pushout.inr (CategoryTheory.ReedyStructure.latchingMap r X j) (colimMap (r.latchingTransformation
          a j))).op
    erw [← T.map_comp]
    exact T.congr_map (Quiver.Hom.unop_inj (CategoryTheory.ReedyStructure.latchingCorner_inr r a j).symm)
  · erw [r.op.matchingCornerWith_snd]
    change T.map (a.app j).op = T.map (CategoryTheory.ReedyStructure.latchingCorner r a j).op ≫
      T.map (pushout.inl (CategoryTheory.ReedyStructure.latchingMap r X j) (colimMap (r.latchingTransformation a j))).op
    erw [← T.map_comp]
    exact T.congr_map (Quiver.Hom.unop_inj (CategoryTheory.ReedyStructure.latchingCorner_inl r a j).symm)

variable [∀ j : Jᵒᵖ, HasLimitsOfShape (r.op.Matching j) E] [HasPullbacks E]

/-- The original entire relative latching corner and its actual mapped opposite matching corner are isomorphic as
arrows. -/
def homOppositeMatchingCornerArrowIso {X Y : J ⥤ C} (a : X ⟶ Y) (j : J) :
    CategoryTheory.Arrow.mk (T.map (CategoryTheory.ReedyStructure.latchingCorner r a j).op) ≅
      CategoryTheory.Arrow.mk (CategoryTheory.ReedyStructure.matchingCorner r.op (Functor.whiskerRight
        (NatTrans.op a) T) (.op j)) :=
  CategoryTheory.Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (by
    erw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact homOppositeMatchingCornerWith r T a j) ≪≫
      CategoryTheory.ReedyStructure.matchingCornerWithArrowIso r.op (Functor.whiskerRight (NatTrans.op a) T) (.op j)
        (homOppositeMatchingCone r T Y j) (homOppositeMatchingIsLimit r T Y j)
        (homOppositeMatchingCone r T X j) (homOppositeMatchingIsLimit r T X j)
        (homOppositeMatchingPullback r T a j) (homOppositeMatchingPullbackIsLimit r T a j)

end OppositeReedyHomCorners

section ReedyOutMappingQuillen

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasLimitsOfSize.{0, max uJ vJ vC z} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The actual opposite latching/matching universal properties prove the entire original Reedy right-Hom Quillen
pair. -/
theorem reedyOutMapping_isQuillen (Y : C) :
    letI := ReedyModel.modelCategory r Fc Ff
    letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
    (outDiagramAdjunction.{uJ, vJ, uC, vC, z} (J := J) ((PointedFramingAction.rightFrame dC).obj
      Y)).IsQuillenAdjunction := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
  let adj := liftedCotensorHomAdjunction.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : adj.IsQuillenAdjunction := originalLiftedCotensor_isQuillen dC Y
  let H := liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : H.IsRightAdjoint := adj.isRightAdjoint
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Z p hp
    rw [fibrations_op, ReedyModel.cofibrations_eq r Fc Ff] at hp
    rw [ReedyModel.fibrations_eq r.op
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.cofibrantFactorizationData
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.fibrantFactorizationData]
    intro j
    change fibrations SSet.{max uJ vJ vC z}
      (CategoryTheory.ReedyStructure.matchingCorner r.op (Functor.whiskerRight (NatTrans.op p.unop) H) (.op j.unop))
    have h : fibrations Cᵒᵖ (CategoryTheory.ReedyStructure.latchingCorner r p.unop j.unop).op := by
      rw [fibrations_op]
      exact hp j.unop
    exact ((fibrations SSet.{max uJ vJ vC z}).arrow_mk_iso_iff
      (homOppositeMatchingCornerArrowIso r H p.unop j.unop)).mp
        (Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) _ h)
  · intro X Z p hp
    rw [trivialFibrations_op, ReedyModel.trivialCofibrations_eq r Fc Ff] at hp
    rw [ReedyModel.trivialFibrations_eq r.op
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.cofibrantFactorizationData
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ vC z}.fibrantFactorizationData]
    intro j
    change trivialFibrations SSet.{max uJ vJ vC z}
      (CategoryTheory.ReedyStructure.matchingCorner r.op (Functor.whiskerRight (NatTrans.op p.unop) H) (.op j.unop))
    have h : trivialFibrations Cᵒᵖ (CategoryTheory.ReedyStructure.latchingCorner r p.unop j.unop).op := by
      rw [trivialFibrations_op]
      exact hp j.unop
    exact ((trivialFibrations SSet.{max uJ vJ vC z}).arrow_mk_iso_iff
      (homOppositeMatchingCornerArrowIso r H p.unop j.unop)).mp
        (Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := adj) _ h)

/-- Original Reedy cofibrancy proves fibrancy of the entire inverse mapping diagram in the original scalar opposite-
Reedy model. -/
theorem reedyOutMapping_isFibrant (F : J ⥤ C) (Y : C) :
    letI := ReedyModel.modelCategory r Fc Ff
    letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
    IsCofibrant F → IsFibrant (outMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
  intro hF
  let _ : IsCofibrant F := hF
  let _ : IsFibrant (Opposite.op F) := cofibrant_op_isFibrant F
  let adj := outDiagramAdjunction.{uJ, vJ, uC, vC, z} (J := J) ((PointedFramingAction.rightFrame dC).obj Y)
  let _ : adj.IsQuillenAdjunction := reedyOutMapping_isQuillen r Fc Ff dC Y
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance

end ReedyOutMappingQuillen

section ReedyScalarDerivedLimits

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)

/-- The genuine scalar Reedy limit is Quillen from the actual scalar constant latching-corner criterion. -/
theorem scalarReedyLimit_isQuillen (h : CofibrantConstants r (C := SSet.{max uJ vJ z})) :
    letI := scalarReedyModel.{uJ, vJ, uD, z} r
    (constLimAdj (J := J) (C := SSet.{max uJ vJ z})).IsQuillenAdjunction :=
  reedyLimit_isQuillen r
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.cofibrantFactorizationData
    SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.fibrantFactorizationData h

/-- The whole scalar Reedy limit comparison retains the same original scalar Reedy R unit. -/
def scalarReedyLimitComparison :
    (lim : (J ⥤ SSet.{max uJ vJ z}) ⥤ SSet.{max uJ vJ z}) ⟶
      scalarReedyHomotopyLimit.{uJ, vJ, uD, z} r := by
  letI := scalarReedyModel.{uJ, vJ, uD, z} r
  exact limitComparison (scalarReedyReplacements.{uJ, vJ, uD, z} r)

/-- Actual scalar Reedy fibrancy makes the original scalar R comparison weak, at the stated scalar constants
condition. -/
theorem scalarReedyLimitComparison_weak (h : CofibrantConstants r (C := SSet.{max uJ vJ z}))
    (F : J ⥤ SSet.{max uJ vJ z}) :
    letI := scalarReedyModel.{uJ, vJ, uD, z} r
    IsFibrant F → weakEquivalences SSet.{max uJ vJ z} ((scalarReedyLimitComparison.{uJ, vJ, uD, z} r).app F) := by
  let _ := scalarReedyModel.{uJ, vJ, uD, z} r
  intro hF
  let _ : IsFibrant F := hF
  let _ : IsFibrant ((𝟭 (J ⥤ SSet.{max uJ vJ z})).obj F) := inferInstanceAs (IsFibrant F)
  let _ : IsFibrant ((scalarReedyReplacements.{uJ, vJ, uD, z} r).R.obj F) :=
    (scalarReedyReplacements.{uJ, vJ, uD, z} r).r_fibrant F
  let _ : (constLimAdj (J := J) (C := SSet.{max uJ vJ z})).IsQuillenAdjunction := scalarReedyLimit_isQuillen r h
  let _ : WeakEquivalence ((scalarReedyReplacements.{uJ, vJ, uD, z} r).r.app F) :=
    (weakEquivalence_iff _).mpr ((scalarReedyReplacements.{uJ, vJ, uD, z} r).r_trivialCofibration F).2
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := constLimAdj)
      ((scalarReedyReplacements.{uJ, vJ, uD, z} r).r.app F))

/-- Original objectwise weak scalar diagrams give weak genuine Reedy homotopy-limit maps at the original scalar
constants criterion. -/
theorem scalarReedyHomotopyLimit_map_weak (h : CofibrantConstants r (C := SSet.{max uJ vJ z}))
    {F G : J ⥤ SSet.{max uJ vJ z}} (a : F ⟶ G)
    (ha : ∀ j, weakEquivalences SSet.{max uJ vJ z} (a.app j)) :
    weakEquivalences SSet.{max uJ vJ z} ((scalarReedyHomotopyLimit.{uJ, vJ, uD, z} r).map a) := by
  let _ := scalarReedyModel.{uJ, vJ, uD, z} r
  let _ : (constLimAdj (J := J) (C := SSet.{max uJ vJ z})).IsQuillenAdjunction := scalarReedyLimit_isQuillen r h
  let _ : IsFibrant ((scalarReedyReplacements.{uJ, vJ, uD, z} r).R.obj F) :=
    (scalarReedyReplacements.{uJ, vJ, uD, z} r).r_fibrant F
  let _ : IsFibrant ((scalarReedyReplacements.{uJ, vJ, uD, z} r).R.obj G) :=
    (scalarReedyReplacements.{uJ, vJ, uD, z} r).r_fibrant G
  have hw : weakEquivalences (J ⥤ SSet.{max uJ vJ z}) a := by
    rw [ReedyModel.weakEquivalences_eq r
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.cofibrantFactorizationData
      SSet.modelCategoryQuillen.canonicalGenerationData.{max uJ vJ z}.fibrantFactorizationData]
    exact ha
  let _ : WeakEquivalence ((scalarReedyReplacements.{uJ, vJ, uD, z} r).R.map a) :=
    (weakEquivalence_iff _).mpr ((scalarReedyReplacements.{uJ, vJ, uD, z} r).r_map_weak a hw)
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := constLimAdj)
      ((scalarReedyReplacements.{uJ, vJ, uD, z} r).R.map a))

end ReedyScalarDerivedLimits

section ReedyHomotopyMappingConstructions

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The same original Reedy R unit is weak at every unchanged coefficient. -/
theorem reedyR_vertex_weak (F : J ⥤ C) (j : J) :
    weakEquivalences C
      (letI := ReedyModel.modelCategory r Fc Ff; ((reedyReplacements r Fc Ff).r.app F).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  have h := ((reedyReplacements r Fc Ff).r_trivialCofibration F).2
  rw [ReedyModel.weakEquivalences_eq r Fc Ff] at h
  exact h j

/-- The actual original Reedy Q counit is weak at every unchanged coefficient. -/
theorem reedyQ_vertex_weak (F : J ⥤ C) (j : J) :
    weakEquivalences C
      (letI := ReedyModel.modelCategory r Fc Ff; ((reedyReplacements r Fc Ff).q.app F).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  have h := ((reedyReplacements r Fc Ff).q_trivialFibration F).2
  rw [ReedyModel.weakEquivalences_eq r Fc Ff] at h
  exact h j

/-- The full original Reedy R diagram provides all actual mapping targets. -/
def reedyRMappingDiagram (X : C) (F : J ⥤ C) : J ⥤ SSet.{max uJ vJ vC z} := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact intoMappingDiagram.{uJ, vJ, uC, vC, z} dC X ((reedyReplacements r Fc Ff).R.obj F)

/-- The full original Reedy Q diagram provides all actual inverse mapping sources. -/
def reedyQMappingDiagram (F : J ⥤ C) (Y : C) : Jᵒᵖ ⥤ SSet.{max uJ vJ vC z} := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact outMappingDiagram.{uJ, vJ, uC, vC, z} dC ((reedyReplacements r Fc Ff).Q.obj F) Y

end ReedyHomotopyMappingConstructions

section ReedyIntoHomotopyLimit

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasColimitsOfSize.{0, max uJ vJ vC z} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- Actual original Reedy R fibrancy proves fibrancy of the whole mapping diagram in the original scalar Reedy model. -/
theorem reedyRMapping_isFibrant (X : C) (F : J ⥤ C) :
    letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
    IsFibrant (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r
  exact reedyIntoMapping_isFibrant r Fc Ff dC X _ ((reedyReplacements r Fc Ff).r_fibrant F)

variable [HasLimitsOfShape J C]

/-- The entire original left Hom of the Reedy homotopy limit maps to the genuine Reedy scalar homotopy limit. -/
def reedyIntoMappingComparison (X : C) (F : J ⥤ C) :
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).obj
        ((reedyHomotopyLimit r Fc Ff).obj F) ⟶
      (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).obj
        (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F) := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact (liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)
    ((reedyReplacements r Fc Ff).R.obj F)).hom ≫
      (scalarReedyLimitComparison.{uJ, vJ, uD, max vC z} r).app
        (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F)

/-- The comparison is weak from original R fibrancy and the stated actual scalar constant-corner condition. -/
theorem reedyIntoMappingComparison_weak
    (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z})) (X : C) (F : J ⥤ C) :
    weakEquivalences SSet.{max uJ vJ vC z}
      (reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r
  have h := scalarReedyLimitComparison_weak.{uJ, vJ, uD, max vC z} r hS _
    (reedyRMapping_isFibrant r Fc Ff dC X F)
  exact (weakEquivalences SSet.{max uJ vJ vC z}).comp_mem _ _
    ((weakEquivalences SSet.{max uJ vJ vC z}).of_isIso
      (liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)
        ((reedyReplacements r Fc Ff).R.obj F)).hom) h

omit [HasColimitsOfSize.{0, max uJ vJ vC z} C] in
/-- The original C constants criterion makes that same actual Reedy homotopy-limit object fibrant. -/
theorem reedyHomotopyLimit_isFibrant (hC : CofibrantConstants r (C := C)) (F : J ⥤ C) :
    IsFibrant ((reedyHomotopyLimit r Fc Ff).obj F) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ : (constLimAdj (J := J) (C := C)).IsQuillenAdjunction := reedyLimit_isQuillen r Fc Ff hC
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := constLimAdj)
    ((reedyReplacements r Fc Ff).r_fibrant F)

/-- The common Reedy/ordinary coefficient R presentation retains both original replacement choices. -/
def reedyIntoMappingCenter (X : C) (F : J ⥤ C) : J ⥤ SSet.{max uJ vJ vC z} := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X ((reedyReplacements r Fc Ff).R.obj F)

/-- The first full natural Reedy mapping span retains every original coefficient R unit. -/
def reedyIntoMappingSpanLeft (X : C) (F : J ⥤ C) :
    reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F ⟶
      reedyIntoMappingCenter.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact Functor.whiskerRight (Functor.whiskerLeft ((reedyReplacements r Fc Ff).R.obj F) dC.r)
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))

/-- The second entire Reedy span retains the original Reedy unit and its same coefficient R image. -/
def reedyIntoMappingSpanRight (X : C) (F : J ⥤ C) :
    canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F ⟶
      reedyIntoMappingCenter.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact Functor.whiskerRight (Functor.whiskerRight ((reedyReplacements r Fc Ff).r.app F) dC.R)
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))

omit [HasLimitsOfShape J C] in
/-- Original Reedy vertex fibrancy proves weakness of every first comparison-span coefficient. -/
theorem reedyIntoMappingSpanLeft_weak (X : C) (F : J ⥤ C) (j : J) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((reedyIntoMappingSpanLeft.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ : IsFibrant (((reedyReplacements r Fc Ff).R.obj F).obj j) := reedyR_vertex_fibrant r Fc Ff F j
  exact leftComplexReplacement_weak.{uC, vC, max uJ vJ z} dC X (((reedyReplacements r Fc Ff).R.obj F).obj j)

omit [HasLimitsOfShape J C] in
/-- The same original Reedy weak unit and coefficient R functor prove every second span coefficient weak. -/
theorem reedyIntoMappingSpanRight_weak (X : C) (F : J ⥤ C) (j : J) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((reedyIntoMappingSpanRight.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ : IsFibrant (dC.R.obj (F.obj j)) := dC.r_fibrant _
  let _ : IsFibrant (dC.R.obj (((reedyReplacements r Fc Ff).R.obj F).obj j)) := dC.r_fibrant _
  let a : F.obj j ⟶ ((reedyReplacements r Fc Ff).R.obj F).obj j := ((reedyReplacements r Fc Ff).r.app F).app j
  exact liftedLeftHom_map_weak.{uC, vC, max uJ vJ z} dC X (dC.R.map a)
    (dC.r_map_weak a (reedyR_vertex_weak r Fc Ff F j))

/-- The actual Reedy HFC/holim comparison retains original source and scalar constants conditions, original factors, and
canonical pointwise mapping spaces. -/
def reedyHomotopyLimitMappingIso (hC : CofibrantConstants r (C := C))
    (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z})) (X : C) (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.obj
        (intoHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC X ((reedyHomotopyLimit r Fc Ff).obj F)) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).obj
          (canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F)) := by
  let _ : IsFibrant ((reedyHomotopyLimit r Fc Ff).obj F) := reedyHomotopyLimit_isFibrant r Fc Ff hC F
  let m := reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F
  let l := (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).map
    (reedyIntoMappingSpanLeft.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F)
  let k := (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).map
    (reedyIntoMappingSpanRight.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F)
  let _ : IsIso (scalarProjection.map m) := Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ
    vJ vC z}) _
    (reedyIntoMappingComparison_weak r Fc Ff dC hS X F)
  let _ : IsIso (scalarProjection.map l) := Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ
    vJ vC z}) _
    (scalarReedyHomotopyLimit_map_weak r hS _ (reedyIntoMappingSpanLeft_weak r Fc Ff dC X F))
  let _ : IsIso (scalarProjection.map k) := Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ
    vJ vC z}) _
    (scalarReedyHomotopyLimit_map_weak r hS _ (reedyIntoMappingSpanRight_weak r Fc Ff dC X F))
  exact (leftComplexReplacementIso.{uC, vC, max uJ vJ z} dC X ((reedyHomotopyLimit r Fc Ff).obj F)).symm ≪≫
    asIso (scalarProjection.map m) ≪≫ asIso (scalarProjection.map l) ≪≫ (asIso (scalarProjection.map k)).symm

end ReedyIntoHomotopyLimit

section ReedyOutHomotopyColimit

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasLimitsOfSize.{0, max uJ vJ vC z} C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- Actual original Reedy Q cofibrancy proves fibrancy of the whole inverse scalar mapping diagram. -/
theorem reedyQMapping_isFibrant (F : J ⥤ C) (Y : C) :
    letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
    IsFibrant (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
  exact reedyOutMapping_isFibrant r Fc Ff dC _ Y ((reedyReplacements r Fc Ff).q_cofibrant F)

variable [HasColimitsOfShape J C]

/-- The entire right frame Hom out of the actual original Reedy homotopy colimit maps to the genuine scalar opposite-
Reedy holim. -/
def reedyOutMappingComparison (F : J ⥤ C) (Y : C) :
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).obj
        (.op ((reedyHomotopyColimit r Fc Ff).obj F)) ⟶
      (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).obj
        (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y) := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact (liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)
    ((reedyReplacements r Fc Ff).Q.obj F)).hom ≫
      (scalarReedyLimitComparison.{uJ, vJ, uD, max vC z} r.op).app
        (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y)

/-- The complete comparison is weak from original Reedy Q cofibrancy and the actual scalar suitable-constants
corners. -/
theorem reedyOutMappingComparison_weak
    (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z})) (F : J ⥤ C) (Y : C) :
    weakEquivalences SSet.{max uJ vJ vC z}
      (reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
  have h := scalarReedyLimitComparison_weak.{uJ, vJ, uD, max vC z} r.op hS _
    (reedyQMapping_isFibrant r Fc Ff dC F Y)
  exact (weakEquivalences SSet.{max uJ vJ vC z}).comp_mem _ _
    ((weakEquivalences SSet.{max uJ vJ vC z}).of_isIso
      (liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)
        ((reedyReplacements r Fc Ff).Q.obj F)).hom) h

omit [HasLimitsOfSize.{0, max uJ vJ vC z} C] in
/-- The original C matching-constant criterion makes the same actual Reedy homotopy-colimit object cofibrant. -/
theorem reedyHomotopyColimit_isCofibrant (hC : FibrantConstants r (C := C)) (F : J ⥤ C) :
    IsCofibrant ((reedyHomotopyColimit r Fc Ff).obj F) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := reedyColimit_isQuillen r Fc Ff hC
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := colimConstAdj)
    ((reedyReplacements r Fc Ff).q_cofibrant F)

/-- The common Reedy/ordinary coefficient Q mapping presentation retains both original replacement choices. -/
def reedyOutMappingCenter (F : J ⥤ C) (Y : C) : Jᵒᵖ ⥤ SSet.{max uJ vJ vC z} := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC ((reedyReplacements r Fc Ff).Q.obj F) Y

/-- The first entire inverse Reedy span retains every original coefficient Q counit. -/
def reedyOutMappingSpanLeft (F : J ⥤ C) (Y : C) :
    reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y ⟶
      reedyOutMappingCenter.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact Functor.whiskerRight (Functor.whiskerLeft ((reedyReplacements r Fc Ff).Q.obj F).op (NatTrans.op dC.q))
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))

/-- The second entire inverse Reedy span retains the original Reedy Q counit and its same coefficient Q image. -/
def reedyOutMappingSpanRight (F : J ⥤ C) (Y : C) :
    canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y ⟶
      reedyOutMappingCenter.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact Functor.whiskerRight (Functor.whiskerRight (NatTrans.op ((reedyReplacements r Fc Ff).q.app F)) dC.Q.op)
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))

omit [HasColimitsOfShape J C] in
/-- Original Reedy coefficient cofibrancy proves every first inverse span coefficient weak. -/
theorem reedyOutMappingSpanLeft_weak (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((reedyOutMappingSpanLeft.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ : IsCofibrant (((reedyReplacements r Fc Ff).Q.obj F).obj j.unop) := reedyQ_vertex_cofibrant r Fc Ff F j.unop
  exact rightComplexReplacement_weak.{uC, vC, max uJ vJ z} dC (((reedyReplacements r Fc Ff).Q.obj F).obj j.unop) Y

omit [HasColimitsOfShape J C] in
/-- The original Reedy weak counit and original coefficient Q functor prove every second inverse span coefficient
weak. -/
theorem reedyOutMappingSpanRight_weak (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    weakEquivalences SSet.{max uJ vJ vC z}
      ((reedyOutMappingSpanRight.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ : IsCofibrant (dC.Q.obj (((reedyReplacements r Fc Ff).Q.obj F).obj j.unop)) := dC.q_cofibrant _
  let _ : IsCofibrant (dC.Q.obj (F.obj j.unop)) := dC.q_cofibrant _
  let a : ((reedyReplacements r Fc Ff).Q.obj F).obj j.unop ⟶ F.obj j.unop :=
    ((reedyReplacements r Fc Ff).q.app F).app j.unop
  exact liftedRightHom_map_weak.{uC, vC, max uJ vJ z} dC Y (dC.Q.map a)
    (dC.q_map_weak a (reedyQ_vertex_weak r Fc Ff F j.unop))

/-- Genuine derived mapping out of the same original Reedy hocolim is the genuine scalar holim of canonical per-vertex
mapping spaces, at the actual source/scalar constants criteria. -/
def reedyHomotopyColimitMappingIso (hC : FibrantConstants r (C := C))
    (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z})) (F : J ⥤ C) (Y : C) :
    scalarProjection.{max uJ vJ vC z}.obj
        (outHomotopyFunctionComplex.{uC, vC, max uJ vJ z} dC ((reedyHomotopyColimit r Fc Ff).obj F) Y) ≅
      scalarProjection.{max uJ vJ vC z}.obj
        ((scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).obj
          (canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y)) := by
  let _ : IsCofibrant ((reedyHomotopyColimit r Fc Ff).obj F) := reedyHomotopyColimit_isCofibrant r Fc Ff hC F
  let m := reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y
  let l := (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).map
    (reedyOutMappingSpanLeft.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y)
  let k := (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).map
    (reedyOutMappingSpanRight.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y)
  let _ : IsIso (scalarProjection.map m) := Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ
    vJ vC z}) _
    (reedyOutMappingComparison_weak r Fc Ff dC hS F Y)
  let _ : IsIso (scalarProjection.map l) := Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ
    vJ vC z}) _
    (scalarReedyHomotopyLimit_map_weak r.op hS _ (reedyOutMappingSpanLeft_weak r Fc Ff dC F Y))
  let _ : IsIso (scalarProjection.map k) := Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ
    vJ vC z}) _
    (scalarReedyHomotopyLimit_map_weak r.op hS _ (reedyOutMappingSpanRight_weak r Fc Ff dC F Y))
  exact (rightComplexReplacementIso.{uC, vC, max uJ vJ z} dC ((reedyHomotopyColimit r Fc Ff).obj F) Y).symm ≪≫
    asIso (scalarProjection.map m) ≪≫ asIso (scalarProjection.map l) ≪≫ (asIso (scalarProjection.map k)).symm

end ReedyOutHomotopyColimit

section ReedyComparisonNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (dC : GeneratedFunctorialReplacements.Data (C := C))

section Into
variable [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]

/-- Every original Reedy diagram arrow preserves the complete actual into-mapping comparison square. -/
theorem reedyIntoMappingComparison_naturality (X : C) {F G : J ⥤ C} (a : F ⟶ G) :
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        ((reedyHomotopyLimit r Fc Ff).map a) ≫
        reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X G =
      reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F ≫
        (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).map
          (letI := ReedyModel.modelCategory r Fc Ff
           Functor.whiskerRight ((reedyReplacements r Fc Ff).R.map a)
             (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  dsimp only [reedyIntoMappingComparison, reedyHomotopyLimit, homotopyLimit]
  erw [← Category.assoc, liftedLeftLimitIso_naturality, Category.assoc]
  exact congrArg (fun m =>
    (liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.leftFrame dC).obj X) ((reedyReplacements r Fc Ff).R.obj F)).hom ≫ m)
    ((scalarReedyLimitComparison.{uJ, vJ, uD, max vC z} r).naturality
      (Functor.whiskerRight ((reedyReplacements r Fc Ff).R.map a)
        (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))))

end Into
section Out
variable [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]

/-- Every original Reedy diagram arrow preserves the complete original inverse mapping/hocolim square. -/
theorem reedyOutMappingComparison_naturality {F G : J ⥤ C} (a : F ⟶ G) (Y : C) :
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        ((reedyHomotopyColimit r Fc Ff).map a).op ≫
        reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y =
      reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC G Y ≫
        (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).map
          (letI := ReedyModel.modelCategory r Fc Ff
           Functor.whiskerRight (NatTrans.op ((reedyReplacements r Fc Ff).Q.map a))
             (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  dsimp only [reedyOutMappingComparison, reedyHomotopyColimit, homotopyColimit]
  erw [← Category.assoc, liftedRightColimitIso_naturality, Category.assoc]
  exact congrArg (fun m =>
    (liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.rightFrame dC).obj Y) ((reedyReplacements r Fc Ff).Q.obj G)).hom ≫ m)
    ((scalarReedyLimitComparison.{uJ, vJ, uD, max vC z} r.op).naturality
      (Functor.whiskerRight (NatTrans.op ((reedyReplacements r Fc Ff).Q.map a))
        (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))))

end Out
end ReedyComparisonNaturality

section ReedyIntoNaturalComparison

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C)) (X : C)

/-- The whole original homotopy-limit functor followed by its actual left frame Hom and scalar localization. -/
def reedyRawIntoMappingFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  reedyHomotopyLimit r Fc Ff ⋙
    liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X) ⋙ scalarProjection

/-- The whole canonical derived mapping functor into the original homotopy limit retains coefficient R. -/
def reedyDerivedIntoMappingFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  reedyHomotopyLimit r Fc Ff ⋙ dC.R ⋙
    liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X) ⋙ scalarProjection

/-- The target functor computes the genuine homotopy limit of each original canonical mapping diagram. -/
def reedyCanonicalIntoMappingLimitFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
      (dC.R ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)) ⋙
    scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r ⋙ scalarProjection

/-- The original whole-diagram R mapping presentation, as one complete functor. -/
def reedyReplacedIntoMappingLimitFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact (reedyReplacements r Fc Ff).R ⋙
    (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)) ⋙
    scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r ⋙ scalarProjection

/-- The same actual coefficient R unit is an isomorphism of the complete localized source functors. -/
def reedyIntoSourceReplacementNatIso (hC : CofibrantConstants r (C := C)) :
    reedyRawIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ≅
      reedyDerivedIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X := by
  let t : reedyRawIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ⟶
      reedyDerivedIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X :=
    Functor.whiskerRight (Functor.whiskerRight
      (Functor.whiskerLeft (reedyHomotopyLimit r Fc Ff) dC.r)
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))) scalarProjection
  let _ : ∀ F, IsIso (t.app F) := fun F => by
    let _ : IsFibrant ((reedyHomotopyLimit r Fc Ff).obj F) := reedyHomotopyLimit_isFibrant r Fc Ff hC F
    exact Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (leftComplexReplacement_weak.{uC, vC, max uJ vJ z} dC X ((reedyHomotopyLimit r Fc Ff).obj F))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Every original diagram arrow is retained in the actual mapping comparison natural transformation. -/
def reedyIntoRawMappingNatIso (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z})) :
    reedyRawIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ≅
      reedyReplacedIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X := by
  let t : reedyRawIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ⟶
      reedyReplacedIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X :=
    { app F := scalarProjection.map (reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F)
      naturality F G a := (scalarProjection.map_comp _ _).symm.trans
        ((scalarProjection.congr_map (reedyIntoMappingComparison_naturality.{uJ, vJ, uC, vC, uD, z}
          r Fc Ff dC X a)).trans (scalarProjection.map_comp _ _)) }
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (reedyIntoMappingComparison_weak.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC hS X F)
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The common original R/R mapping presentation is a single functor on all original diagrams and arrows. -/
def reedyIntoCenterMappingLimitFunctor : (J ⥤ C) ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact (reedyReplacements r Fc Ff).R ⋙
    (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
      (dC.R ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)) ⋙
    scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r ⋙ scalarProjection

/-- The first actual R/R span leg is an isomorphism of the whole scalar homotopy-limit functors. -/
def reedyIntoPointwiseSpanLeftNatIso (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z})) :
    reedyReplacedIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ≅
      reedyIntoCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X := by
  letI := ReedyModel.modelCategory r Fc Ff
  let t : reedyReplacedIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ⟶
      reedyIntoCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X :=
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.whiskerLeft (reedyReplacements r Fc Ff).R
          ((Functor.whiskeringRight J C C).map dC.r))
        ((Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
          (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))))
      (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarReedyHomotopyLimit_map_weak.{uJ, vJ, uD, max vC z} r hS _
        (reedyIntoMappingSpanLeft_weak r Fc Ff dC X F))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The second original diagram/coefficient R span leg is an isomorphism of whole functors. -/
def reedyIntoPointwiseSpanRightNatIso (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z})) :
    reedyCanonicalIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r dC X ≅
      reedyIntoCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X := by
  letI := ReedyModel.modelCategory r Fc Ff
  let t : reedyCanonicalIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r dC X ⟶
      reedyIntoCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X :=
    Functor.whiskerRight
      (Functor.whiskerRight (reedyReplacements r Fc Ff).r
        ((Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).obj
          (dC.R ⋙ liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X))))
      (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarReedyHomotopyLimit_map_weak.{uJ, vJ, uD, max vC z} r hS _
        (reedyIntoMappingSpanRight_weak r Fc Ff dC X F))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The genuine derived mapping/holim comparison is one natural isomorphism on every original diagram object and
arrow. -/
def reedyHomotopyLimitMappingNatIso (hC : CofibrantConstants r (C := C))
    (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z})) :
    reedyDerivedIntoMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X ≅
      reedyCanonicalIntoMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r dC X :=
  (reedyIntoSourceReplacementNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hC).symm ≪≫
    reedyIntoRawMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hS ≪≫
      reedyIntoPointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hS ≪≫
        (reedyIntoPointwiseSpanRightNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hS).symm

end ReedyIntoNaturalComparison

section ReedyOutNaturalComparison

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C)) (Y : C)

/-- The whole original projective homotopy-colimit functor acts contravariantly through its actual right frame Hom. -/
def reedyRawOutMappingFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (reedyHomotopyColimit r Fc Ff).op ⋙
    liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y) ⋙ scalarProjection

/-- The complete canonical derived mapping source retains the original coefficient Q of the original hocolim. -/
def reedyDerivedOutMappingFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (reedyHomotopyColimit r Fc Ff).op ⋙ dC.Q.op ⋙
    liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y) ⋙ scalarProjection

/-- The whole original canonical inverse mapping diagram followed by its actual scalar homotopy limit. -/
def reedyCanonicalOutMappingLimitFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization :=
  (Functor.opUnopEquiv J C).functor ⋙
    (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
      (dC.Q.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)) ⋙
    scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op ⋙ scalarProjection

/-- The actual whole projective Q mapping presentation is one complete inverse-diagram functor. -/
def reedyReplacedOutMappingLimitFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact (reedyReplacements r Fc Ff).Q.op ⋙ (Functor.opUnopEquiv J C).functor ⋙
    (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)) ⋙
    scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op ⋙ scalarProjection

/-- The same original coefficient Q counit gives an isomorphism of the whole scalar-localized source functors. -/
def reedyOutSourceReplacementNatIso (hC : FibrantConstants r (C := C)) :
    reedyRawOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ≅
      reedyDerivedOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y := by
  let t : reedyRawOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ⟶
      reedyDerivedOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y :=
    Functor.whiskerRight (Functor.whiskerRight
      (Functor.whiskerLeft (reedyHomotopyColimit r Fc Ff).op (NatTrans.op dC.q))
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))) scalarProjection
  let _ : ∀ F, IsIso (t.app F) := fun F => by
    let _ : IsCofibrant ((reedyHomotopyColimit r Fc Ff).obj F.unop) := reedyHomotopyColimit_isCofibrant r Fc Ff
      hC F.unop
    exact Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (rightComplexReplacement_weak.{uC, vC, max uJ vJ z} dC ((reedyHomotopyColimit r Fc Ff).obj F.unop) Y)
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The actual right-complex comparison is one natural isomorphism retaining every original diagram arrow. -/
def reedyOutRawMappingNatIso (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z})) :
    reedyRawOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ≅
      reedyReplacedOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y := by
  let t : reedyRawOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ⟶
      reedyReplacedOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y :=
    { app F := scalarProjection.map (reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F.unop Y)
      naturality F G a := (scalarProjection.map_comp _ _).symm.trans
        ((scalarProjection.congr_map (reedyOutMappingComparison_naturality.{uJ, vJ, uC, vC, uD, z}
          r Fc Ff dC a.unop Y)).trans (scalarProjection.map_comp _ _)) }
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (reedyOutMappingComparison_weak.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC hS F.unop Y)
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The original diagram-Q/coefficient-Q common mapping presentation is a whole functor. -/
def reedyOutCenterMappingLimitFunctor : (J ⥤ C)ᵒᵖ ⥤ (weakEquivalences SSet.{max uJ vJ vC z}).Localization := by
  letI := ReedyModel.modelCategory r Fc Ff
  exact (reedyReplacements r Fc Ff).Q.op ⋙ (Functor.opUnopEquiv J C).functor ⋙
    (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
      (dC.Q.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)) ⋙
    scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op ⋙ scalarProjection

/-- The first original Q/Q span is an isomorphism of the whole inverse mapping-limit functors. -/
def reedyOutPointwiseSpanLeftNatIso (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z})) :
    reedyReplacedOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ≅
      reedyOutCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y := by
  letI := ReedyModel.modelCategory r Fc Ff
  let t : reedyReplacedOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ⟶
      reedyOutCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y :=
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.whiskerLeft ((reedyReplacements r Fc Ff).Q.op ⋙ (Functor.opUnopEquiv J C).functor)
          ((Functor.whiskeringRight Jᵒᵖ Cᵒᵖ Cᵒᵖ).map (NatTrans.op dC.q)))
        ((Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
          (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))))
      (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarReedyHomotopyLimit_map_weak.{uJ, vJ, uD, max vC z} r.op hS _
        (reedyOutMappingSpanLeft_weak r Fc Ff dC F.unop Y))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The second actual Q/Q span retains the original diagram counit as an isomorphism of whole functors. -/
def reedyOutPointwiseSpanRightNatIso (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z})) :
    reedyCanonicalOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r dC Y ≅
      reedyOutCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y := by
  letI := ReedyModel.modelCategory r Fc Ff
  let t : reedyCanonicalOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r dC Y ⟶
      reedyOutCenterMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y :=
    Functor.whiskerRight
      (Functor.whiskerRight (NatTrans.op (reedyReplacements r Fc Ff).q)
        ((Functor.opUnopEquiv J C).functor ⋙
          (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).obj
            (dC.Q.op ⋙ liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y))))
      (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op ⋙ scalarProjection)
  let _ : ∀ F, IsIso (t.app F) := fun F =>
    Localization.inverts scalarProjection (weakEquivalences SSet.{max uJ vJ vC z}) _
      (scalarReedyHomotopyLimit_map_weak.{uJ, vJ, uD, max vC z} r.op hS _
        (reedyOutMappingSpanRight_weak r Fc Ff dC F.unop Y))
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The genuine derived mapping/hocolim comparison is one natural isomorphism on all original diagram objects and
arrows. -/
def reedyHomotopyColimitMappingNatIso (hC : FibrantConstants r (C := C))
    (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z})) :
    reedyDerivedOutMappingFunctor.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y ≅
      reedyCanonicalOutMappingLimitFunctor.{uJ, vJ, uC, vC, uD, z} r dC Y :=
  (reedyOutSourceReplacementNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hC).symm ≪≫
    reedyOutRawMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hS ≪≫
      reedyOutPointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hS ≪≫
        (reedyOutPointwiseSpanRightNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hS).symm

end ReedyOutNaturalComparison

section FrameComparisonTransformations

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]

section Left
variable [HasColimitsOfSize.{0, max z vC} C] [HasLimitsOfShape J C]
  [HasLimitsOfShape J SSet.{max z vC}]

/-- Every original frame arrow commutes with the full ordinary comparison followed by any given natural limit
comparison. -/
theorem leftFrameComparison_naturality {A A' : CosimplicialObject C} (a : A ⟶ A') (F : J ⥤ C)
    (L : (J ⥤ SSet.{max z vC}) ⥤ SSet.{max z vC})
    (t : (lim : (J ⥤ SSet.{max z vC}) ⥤ SSet.{max z vC}) ⟶ L) :
    (liftedLeftHomPrecompNat.{uC, vC, z} a).app (limit F) ≫
        ((liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).hom ≫ t.app (F ⋙ liftedLeftHomFunctor.{uC, vC, z} A)) =
      ((liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫ t.app (F ⋙ liftedLeftHomFunctor.{uC, vC, z} A')) ≫
        L.map (Functor.whiskerLeft F (liftedLeftHomPrecompNat.{uC, vC, z} a)) := by
  calc
    _ = ((liftedLeftHomPrecompNat.{uC, vC, z} a).app (limit F) ≫
        (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A F).hom) ≫ t.app _ := (Category.assoc _ _ _).symm
    _ = ((liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫
        lim.map (Functor.whiskerLeft F (liftedLeftHomPrecompNat.{uC, vC, z} a))) ≫ t.app _ :=
      congrArg (fun m => m ≫ t.app _) (liftedLeftLimitIso_frame_naturality.{uJ, vJ, uC, vC, z} a F)
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun m => (liftedLeftLimitIso.{uJ, vJ, uC, vC, z} A' F).hom ≫ m)
        (t.naturality (Functor.whiskerLeft F (liftedLeftHomPrecompNat.{uC, vC, z} a)))).trans
          (Category.assoc _ _ _).symm)

end Left
section Right
variable [HasLimitsOfSize.{0, max z vC} C] [HasColimitsOfShape J C]
  [HasLimitsOfShape Jᵒᵖ SSet.{max z vC}]

/-- Every whole original right-frame arrow commutes with the full colimit/Hom comparison and the same scalar limit
comparison. -/
theorem rightFrameComparison_naturality {B B' : SimplicialObject C} (b : B ⟶ B') (F : J ⥤ C)
    (L : (Jᵒᵖ ⥤ SSet.{max z vC}) ⥤ SSet.{max z vC})
    (t : (lim : (Jᵒᵖ ⥤ SSet.{max z vC}) ⥤ SSet.{max z vC}) ⟶ L) :
    (liftedRightHomPostcompNat.{uC, vC, z} b).app (.op (colimit F)) ≫
        ((liftedRightColimitIso.{uJ, vJ, uC, vC, z} B' F).hom ≫ t.app (F.op ⋙ liftedRightHomFunctor.{uC, vC, z} B')) =
      ((liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).hom ≫ t.app (F.op ⋙ liftedRightHomFunctor.{uC, vC, z} B)) ≫
        L.map (Functor.whiskerLeft F.op (liftedRightHomPostcompNat.{uC, vC, z} b)) := by
  calc
    _ = ((liftedRightHomPostcompNat.{uC, vC, z} b).app (.op (colimit F)) ≫
        (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B' F).hom) ≫ t.app _ := (Category.assoc _ _ _).symm
    _ = ((liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).hom ≫
        lim.map (Functor.whiskerLeft F.op (liftedRightHomPostcompNat.{uC, vC, z} b))) ≫ t.app _ :=
      congrArg (fun m => m ≫ t.app _) (liftedRightColimitIso_frame_naturality.{uJ, vJ, uC, vC, z} b F)
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun m => (liftedRightColimitIso.{uJ, vJ, uC, vC, z} B F).hom ≫ m)
        (t.naturality (Functor.whiskerLeft F.op (liftedRightHomPostcompNat.{uC, vC, z} b)))).trans
          (Category.assoc _ _ _).symm)

end Right
end FrameComparisonTransformations

section ComparisonIsoAlgebra

variable {E : Type uE} [Category.{vE} E]

/-- The inverse of the same actual comparison is natural in the same original square. -/
theorem comparisonInverse_naturality {A B A' B' : E} (e : A ≅ B) (e' : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : e.hom ≫ g = f ≫ e'.hom) :
    g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- A composite of the four original comparison legs retains their same complete naturality squares. -/
theorem comparisonFourSpan_naturality {A₀ A₁ B₀ B₁ B₂ A₀' A₁' B₀' B₁' B₂' : E}
    (e₀ : A₀ ≅ A₁) (e₁ : A₀ ≅ B₀) (e₂ : B₀ ≅ B₁) (e₃ : B₂ ≅ B₁)
    (e₀' : A₀' ≅ A₁') (e₁' : A₀' ≅ B₀') (e₂' : B₀' ≅ B₁') (e₃' : B₂' ≅ B₁')
    (f₀ : A₀ ⟶ A₀') (f₁ : A₁ ⟶ A₁') (g₀ : B₀ ⟶ B₀') (g₁ : B₁ ⟶ B₁') (g₂ : B₂ ⟶ B₂')
    (h₀ : e₀.hom ≫ f₁ = f₀ ≫ e₀'.hom)
    (h₁ : f₀ ≫ e₁'.hom = e₁.hom ≫ g₀)
    (h₂ : g₀ ≫ e₂'.hom = e₂.hom ≫ g₁)
    (h₃ : e₃.hom ≫ g₁ = g₂ ≫ e₃'.hom) :
    f₁ ≫ (e₀'.symm ≪≫ e₁' ≪≫ e₂' ≪≫ e₃'.symm).hom =
      (e₀.symm ≪≫ e₁ ≪≫ e₂ ≪≫ e₃.symm).hom ≫ g₂ := by
  have hi₀ := comparisonInverse_naturality e₀ e₀' f₀ f₁ h₀
  have hi₃ := comparisonInverse_naturality e₃ e₃' g₂ g₁ h₃
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    _ = e₀.inv ≫ (f₀ ≫ (e₁'.hom ≫ (e₂'.hom ≫ e₃'.inv))) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ (e₁'.hom ≫ (e₂'.hom ≫ e₃'.inv))) hi₀).trans (Category.assoc _ _ _))
    _ = e₀.inv ≫ (e₁.hom ≫ (g₀ ≫ (e₂'.hom ≫ e₃'.inv))) :=
      congrArg (fun m => e₀.inv ≫ m)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ (e₂'.hom ≫ e₃'.inv)) h₁).trans (Category.assoc _ _ _)))
    _ = e₀.inv ≫ (e₁.hom ≫ (e₂.hom ≫ (g₁ ≫ e₃'.inv))) :=
      congrArg (fun m => e₀.inv ≫ (e₁.hom ≫ m))
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ e₃'.inv) h₂).trans (Category.assoc _ _ _)))
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun m => e₀.inv ≫ (e₁.hom ≫ (e₂.hom ≫ m))) hi₃


end ComparisonIsoAlgebra

section CanonicalCoefficientMaps

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- Every original source coefficient map acts on the whole canonical derived mapping diagram through its same original
left frame map. -/
def canonicalIntoCoefficientMap {X X' : C} (a : X ⟶ X') (F : J ⥤ C) :
    canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X' F ⟶
      canonicalIntoMappingDiagram.{uJ, vJ, uC, vC, z} dC X F :=
  Functor.whiskerLeft (F ⋙ dC.R)
    (liftedLeftHomPrecompNat.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).map a))

/-- Every original target coefficient map acts on the whole canonical inverse mapping diagram through the same actual
right frame. -/
def canonicalOutCoefficientMap (F : J ⥤ C) {Y Y' : C} (b : Y ⟶ Y') :
    canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y ⟶
      canonicalOutMappingDiagram.{uJ, vJ, uC, vC, z} dC F Y' :=
  Functor.whiskerLeft (F.op ⋙ dC.Q.op)
    (liftedRightHomPostcompNat.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).map b))

end CanonicalCoefficientMaps

section InjectiveCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The whole derived mapping/holim isomorphism retains every original source coefficient map as well as every diagram
map. -/
theorem injectiveHomotopyLimitMappingNatIso_coefficient {X X' : C} (a : X ⟶ X') (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.map
        (intoComplexSourceMap.{uC, vC, max uJ vJ z} dC a ((injectiveHomotopyLimit g κLP s).obj F)) ≫
        (injectiveHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).hom.app F =
      (injectiveHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').hom.app F ≫
        scalarProjection.{max uJ vJ vC z}.map
          ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).map
            (canonicalIntoCoefficientMap.{uJ, vJ, uC, vC, z} dC a F)) := by
  let _ := injectiveModel g κLP s
  let H := liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)
  let H' := liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X')
  let α := liftedLeftHomPrecompNat.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).map a)
  let N := (injectiveHomotopyLimit g κLP s).obj F
  let RF := (injectiveReplacements g κLP s).R.obj F
  let P := (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).map α
  let S := scalarHomotopyLimit.{uJ, vJ, max vC z} J ⋙ scalarProjection.{max uJ vJ vC z}
  apply comparisonFourSpan_naturality
    ((injectiveSourceReplacementNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').app F)
    ((injectiveRawMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').app F)
    ((injectivePointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').app F)
    ((injectivePointwiseSpanRightNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').app F)
    ((injectiveSourceReplacementNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).app F)
    ((injectiveRawMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).app F)
    ((injectivePointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).app F)
    ((injectivePointwiseSpanRightNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).app F)
    (scalarProjection.map (α.app N))
    (scalarProjection.map (α.app (dC.R.obj N)))
    (S.map (Functor.whiskerLeft RF α))
    (S.map (Functor.whiskerLeft (RF ⋙ dC.R) α))
    (S.map (Functor.whiskerLeft (F ⋙ dC.R) α))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map (α.naturality (dC.r.app N))).trans (scalarProjection.map_comp _ _))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map
        (leftFrameComparison_naturality.{uJ, vJ, uC, vC, max uJ vJ z}
          ((PointedFramingAction.leftFrame dC).map a) RF
          (scalarHomotopyLimit.{uJ, vJ, max vC z} J) (scalarLimitComparison.{uJ, vJ, max vC z} J))).trans
            (scalarProjection.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerLeft RF dC.r)).symm).trans (S.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerRight ((injectiveReplacements g κLP s).r.app F) dC.R))).trans
        (S.map_comp _ _))

end InjectiveCoefficientNaturality

section ReedyIntoCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))
  (hC : CofibrantConstants r (C := C)) (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z}))

/-- The whole derived mapping/holim isomorphism retains every original source coefficient map as well as every diagram
map. -/
theorem reedyHomotopyLimitMappingNatIso_coefficient {X X' : C} (a : X ⟶ X') (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.map
        (intoComplexSourceMap.{uC, vC, max uJ vJ z} dC a ((reedyHomotopyLimit r Fc Ff).obj F)) ≫
        (reedyHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hC hS).hom.app F =
      (reedyHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hC hS).hom.app F ≫
        scalarProjection.{max uJ vJ vC z}.map
          ((scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).map
            (canonicalIntoCoefficientMap.{uJ, vJ, uC, vC, z} dC a F)) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let H := liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)
  let H' := liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X')
  let α := liftedLeftHomPrecompNat.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).map a)
  let N := (reedyHomotopyLimit r Fc Ff).obj F
  let RF := (reedyReplacements r Fc Ff).R.obj F
  let P := (Functor.whiskeringRight J C SSet.{max uJ vJ vC z}).map α
  let S := scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r ⋙ scalarProjection.{max uJ vJ vC z}
  apply comparisonFourSpan_naturality
    ((reedyIntoSourceReplacementNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hC).app F)
    ((reedyIntoRawMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hS).app F)
    ((reedyIntoPointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hS).app F)
    ((reedyIntoPointwiseSpanRightNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hS).app F)
    ((reedyIntoSourceReplacementNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hC).app F)
    ((reedyIntoRawMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hS).app F)
    ((reedyIntoPointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hS).app F)
    ((reedyIntoPointwiseSpanRightNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hS).app F)
    (scalarProjection.map (α.app N))
    (scalarProjection.map (α.app (dC.R.obj N)))
    (S.map (Functor.whiskerLeft RF α))
    (S.map (Functor.whiskerLeft (RF ⋙ dC.R) α))
    (S.map (Functor.whiskerLeft (F ⋙ dC.R) α))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map (α.naturality (dC.r.app N))).trans (scalarProjection.map_comp _ _))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map
        (leftFrameComparison_naturality.{uJ, vJ, uC, vC, max uJ vJ z}
          ((PointedFramingAction.leftFrame dC).map a) RF
          (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r) (scalarReedyLimitComparison.{uJ, vJ, uD, max vC z}
            r))).trans
            (scalarProjection.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerLeft RF dC.r)).symm).trans (S.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerRight ((reedyReplacements r Fc Ff).r.app F) dC.R))).trans
        (S.map_comp _ _))

end ReedyIntoCoefficientNaturality

section ProjectiveCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The entire derived right mapping/hocolim isomorphism retains every original target coefficient arrow and every
diagram arrow. -/
theorem projectiveHomotopyColimitMappingNatIso_coefficient (F : J ⥤ C) {Y Y' : C} (b : Y ⟶ Y') :
    scalarProjection.{max uJ vJ vC z}.map
        (outComplexTargetMap.{uC, vC, max uJ vJ z} dC ((projectiveHomotopyColimit g s).obj F) b) ≫
        (projectiveHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y').hom.app (.op F) =
      (projectiveHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).hom.app (.op F) ≫
        scalarProjection.{max uJ vJ vC z}.map
          ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).map
            (canonicalOutCoefficientMap.{uJ, vJ, uC, vC, z} dC F b)) := by
  let _ := projectiveModel g s
  let β := liftedRightHomPostcompNat.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).map b)
  let N := (projectiveHomotopyColimit g s).obj F
  let QF := (projectiveReplacements g s).Q.obj F
  let P := (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).map β
  let S := scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ ⋙ scalarProjection.{max uJ vJ vC z}
  apply comparisonFourSpan_naturality
    ((projectiveSourceReplacementNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).app (.op F))
    ((projectiveRawMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).app (.op F))
    ((projectivePointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).app (.op F))
    ((projectivePointwiseSpanRightNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).app (.op F))
    ((projectiveSourceReplacementNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y').app (.op F))
    ((projectiveRawMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y').app (.op F))
    ((projectivePointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y').app (.op F))
    ((projectivePointwiseSpanRightNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y').app (.op F))
    (scalarProjection.map (β.app (.op N)))
    (scalarProjection.map (β.app (.op (dC.Q.obj N))))
    (S.map (Functor.whiskerLeft QF.op β))
    (S.map (Functor.whiskerLeft (QF.op ⋙ dC.Q.op) β))
    (S.map (Functor.whiskerLeft (F.op ⋙ dC.Q.op) β))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map (β.naturality (dC.q.app N).op)).trans (scalarProjection.map_comp _ _))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map
        (rightFrameComparison_naturality.{uJ, vJ, uC, vC, max uJ vJ z}
          ((PointedFramingAction.rightFrame dC).map b) QF
          (scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ) (scalarLimitComparison.{uJ, vJ, max vC z} Jᵒᵖ))).trans
            (scalarProjection.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerLeft QF.op (NatTrans.op dC.q))).symm).trans (S.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerRight (NatTrans.op ((projectiveReplacements g s).q.app F))
        dC.Q.op))).trans
        (S.map_comp _ _))

end ProjectiveCoefficientNaturality

section ReedyOutCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))
  (hC : FibrantConstants r (C := C)) (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z}))

/-- The entire derived right mapping/hocolim isomorphism retains every original target coefficient arrow and every
diagram arrow. -/
theorem reedyHomotopyColimitMappingNatIso_coefficient (F : J ⥤ C) {Y Y' : C} (b : Y ⟶ Y') :
    scalarProjection.{max uJ vJ vC z}.map
        (outComplexTargetMap.{uC, vC, max uJ vJ z} dC ((reedyHomotopyColimit r Fc Ff).obj F) b) ≫
        (reedyHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y' hC hS).hom.app (.op F) =
      (reedyHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hC hS).hom.app (.op F) ≫
        scalarProjection.{max uJ vJ vC z}.map
          ((scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).map
            (canonicalOutCoefficientMap.{uJ, vJ, uC, vC, z} dC F b)) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let β := liftedRightHomPostcompNat.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).map b)
  let N := (reedyHomotopyColimit r Fc Ff).obj F
  let QF := (reedyReplacements r Fc Ff).Q.obj F
  let P := (Functor.whiskeringRight Jᵒᵖ Cᵒᵖ SSet.{max uJ vJ vC z}).map β
  let S := scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op ⋙ scalarProjection.{max uJ vJ vC z}
  apply comparisonFourSpan_naturality
    ((reedyOutSourceReplacementNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hC).app (.op F))
    ((reedyOutRawMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hS).app (.op F))
    ((reedyOutPointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hS).app (.op F))
    ((reedyOutPointwiseSpanRightNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hS).app (.op F))
    ((reedyOutSourceReplacementNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y' hC).app (.op F))
    ((reedyOutRawMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y' hS).app (.op F))
    ((reedyOutPointwiseSpanLeftNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y' hS).app (.op F))
    ((reedyOutPointwiseSpanRightNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y' hS).app (.op F))
    (scalarProjection.map (β.app (.op N)))
    (scalarProjection.map (β.app (.op (dC.Q.obj N))))
    (S.map (Functor.whiskerLeft QF.op β))
    (S.map (Functor.whiskerLeft (QF.op ⋙ dC.Q.op) β))
    (S.map (Functor.whiskerLeft (F.op ⋙ dC.Q.op) β))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map (β.naturality (dC.q.app N).op)).trans (scalarProjection.map_comp _ _))
  · exact (scalarProjection.map_comp _ _).symm.trans
      ((scalarProjection.congr_map
        (rightFrameComparison_naturality.{uJ, vJ, uC, vC, max uJ vJ z}
          ((PointedFramingAction.rightFrame dC).map b) QF
          (scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op) (scalarReedyLimitComparison.{uJ, vJ, uD, max vC
            z} r.op))).trans
            (scalarProjection.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerLeft QF.op (NatTrans.op dC.q))).symm).trans (S.map_comp _ _))
  · exact (S.map_comp _ _).symm.trans
      ((S.congr_map (P.naturality (Functor.whiskerRight (NatTrans.op ((reedyReplacements r Fc Ff).q.app F))
        dC.Q.op))).trans
        (S.map_comp _ _))

end ReedyOutCoefficientNaturality

section InjectiveInverseCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} J C)
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The inverse of the same full comparison retains every original coefficient map. -/
theorem injectiveHomotopyLimitMappingNatIso_inv_coefficient {X X' : C} (a : X ⟶ X') (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.map ((scalarHomotopyLimit.{uJ, vJ, max vC z} J).map
      (canonicalIntoCoefficientMap.{uJ, vJ, uC, vC, z} dC a F)) ≫ (injectiveHomotopyLimitMappingNatIso.{uJ, vJ,
      uC, vC, w, z} g κLP s dC X).inv.app (F) =
      (injectiveHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').inv.app (F) ≫
        scalarProjection.{max uJ vJ vC z}.map (intoComplexSourceMap.{uC, vC, max uJ vJ z} dC a
        ((injectiveHomotopyLimit g κLP s).obj F)) :=
  comparisonInverse_naturality ((injectiveHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X').app
    (F)) ((injectiveHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g κLP s dC X).app (F)) _ _
    (injectiveHomotopyLimitMappingNatIso_coefficient.{uJ, vJ, uC, vC, w, z} g κLP s dC a F).symm

end InjectiveInverseCoefficientNaturality


section ProjectiveInverseCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (s : Functor.EssentialIndexData.{w} J C)
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))

/-- The inverse of the same full comparison retains every original coefficient map. -/
theorem projectiveHomotopyColimitMappingNatIso_inv_coefficient (F : J ⥤ C) {Y Y' : C} (b : Y ⟶ Y') :
    scalarProjection.{max uJ vJ vC z}.map ((scalarHomotopyLimit.{uJ, vJ, max vC z} Jᵒᵖ).map
      (canonicalOutCoefficientMap.{uJ, vJ, uC, vC, z} dC F b)) ≫ (projectiveHomotopyColimitMappingNatIso.{uJ,
      vJ, uC, vC, w, z} g s dC Y').inv.app (.op F) =
      (projectiveHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).inv.app (.op F) ≫
        scalarProjection.{max uJ vJ vC z}.map (outComplexTargetMap.{uC, vC, max uJ vJ z} dC
        ((projectiveHomotopyColimit g s).obj F) b) :=
  comparisonInverse_naturality ((projectiveHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y).app
    (.op F)) ((projectiveHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, w, z} g s dC Y').app (.op F)) _ _
    (projectiveHomotopyColimitMappingNatIso_coefficient.{uJ, vJ, uC, vC, w, z} g s dC F b).symm

end ProjectiveInverseCoefficientNaturality


section ReedyIntoInverseCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))
  (hC : CofibrantConstants r (C := C)) (hS : CofibrantConstants r (C := SSet.{max uJ vJ vC z}))

/-- The inverse of the same full comparison retains every original coefficient map. -/
theorem reedyHomotopyLimitMappingNatIso_inv_coefficient {X X' : C} (a : X ⟶ X') (F : J ⥤ C) :
    scalarProjection.{max uJ vJ vC z}.map ((scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r).map
      (canonicalIntoCoefficientMap.{uJ, vJ, uC, vC, z} dC a F)) ≫ (reedyHomotopyLimitMappingNatIso.{uJ, vJ, uC,
      vC, uD, z} r Fc Ff dC X hC hS).inv.app (F) =
      (reedyHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hC hS).inv.app (F) ≫
        scalarProjection.{max uJ vJ vC z}.map (intoComplexSourceMap.{uC, vC, max uJ vJ z} dC a
        ((reedyHomotopyLimit r Fc Ff).obj F)) :=
  comparisonInverse_naturality ((reedyHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X' hC
    hS).app (F)) ((reedyHomotopyLimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X hC hS).app (F)) _ _
    (reedyHomotopyLimitMappingNatIso_coefficient.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC hC hS a F).symm

end ReedyIntoInverseCoefficientNaturality


section ReedyOutInverseCoefficientNaturality

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]
  (dC : GeneratedFunctorialReplacements.Data (C := C))
  (hC : FibrantConstants r (C := C)) (hS : CofibrantConstants r.op (C := SSet.{max uJ vJ vC z}))

/-- The inverse of the same full comparison retains every original coefficient map. -/
theorem reedyHomotopyColimitMappingNatIso_inv_coefficient (F : J ⥤ C) {Y Y' : C} (b : Y ⟶ Y') :
    scalarProjection.{max uJ vJ vC z}.map ((scalarReedyHomotopyLimit.{uJ, vJ, uD, max vC z} r.op).map
      (canonicalOutCoefficientMap.{uJ, vJ, uC, vC, z} dC F b)) ≫ (reedyHomotopyColimitMappingNatIso.{uJ, vJ, uC,
      vC, uD, z} r Fc Ff dC Y' hC hS).inv.app (.op F) =
      (reedyHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hC hS).inv.app (.op F) ≫
        scalarProjection.{max uJ vJ vC z}.map (outComplexTargetMap.{uC, vC, max uJ vJ z} dC
        ((reedyHomotopyColimit r Fc Ff).obj F) b) :=
  comparisonInverse_naturality ((reedyHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y hC
    hS).app (.op F)) ((reedyHomotopyColimitMappingNatIso.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC Y' hC hS).app (.op F)) _ _
    (reedyHomotopyColimitMappingNatIso_coefficient.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC hC hS F b).symm

end ReedyOutInverseCoefficientNaturality

section ReedyOriginalComparisonProjections

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (dC : GeneratedFunctorialReplacements.Data (C := C))

section Into
variable [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]

/-- Every actual Reedy into-mapping projection retains the original C/Reedy R projection and the original scalar/Reedy R
unit. -/
theorem reedyIntoMappingComparison_projection (X : C) (F : J ⥤ C) (j : J) :
    reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
         limitProjection (scalarReedyReplacements.{uJ, vJ, uD, max vC z} r)
           (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F) j) =
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        (letI := ReedyModel.modelCategory r Fc Ff; limitProjection (reedyReplacements r Fc Ff) F j) ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
         ((scalarReedyReplacements.{uJ, vJ, uD, max vC z} r).r.app
           (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F)).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r
  change ((liftedLeftLimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.leftFrame dC).obj X) ((reedyReplacements r Fc Ff).R.obj F)).hom ≫
      (limitComparison (scalarReedyReplacements.{uJ, vJ, uD, max vC z} r)).app _) ≫ _ = _
  erw [Category.assoc, comparison_projection, ← Category.assoc, liftedLeftLimitIso_hom_projection]
  rfl

end Into
section Out
variable [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]

/-- Every actual inverse Reedy mapping projection retains the original Q injection and the same actual scalar Reedy R
unit. -/
theorem reedyOutMappingComparison_projection (F : J ⥤ C) (Y : C) (j : Jᵒᵖ) :
    reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
         limitProjection (scalarReedyReplacements.{uJ, vJ, uD, max vC z} r.op)
           (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y) j) =
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        (letI := ReedyModel.modelCategory r Fc Ff; (colimitInjection (reedyReplacements r Fc Ff) F j.unop).op) ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
         ((scalarReedyReplacements.{uJ, vJ, uD, max vC z} r.op).r.app
           (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y)).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
  change ((liftedRightColimitIso.{uJ, vJ, uC, vC, max uJ vJ z}
      ((PointedFramingAction.rightFrame dC).obj Y) ((reedyReplacements r Fc Ff).Q.obj F)).hom ≫
      (limitComparison (scalarReedyReplacements.{uJ, vJ, uD, max vC z} r.op)).app _) ≫ _ = _
  erw [Category.assoc, comparison_projection, ← Category.assoc, liftedRightColimitIso_hom_projection]
  rfl

end Out
end ReedyOriginalComparisonProjections


section ReedyOriginalCallerMappings

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (dC : GeneratedFunctorialReplacements.Data (C := C))

section Projective
variable [HasLimitsOfSize.{0, max uJ vJ vC z} C] [HasColimitsOfShape J C]

/-- Every original caller cocone retains its same Q leg in the full right-HFC/hocolim comparison. -/
theorem reedyOutMappingComparison_desc (F : J ⥤ C) (c : Cocone F) (Y : C) (j : Jᵒᵖ) :
    (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        (letI := ReedyModel.modelCategory r Fc Ff; (desc (reedyReplacements r Fc Ff) F c).op) ≫
      (reedyOutMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
         limitProjection (scalarReedyReplacements.{uJ, vJ, uD, max vC z} r.op)
           (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y) j)) =
      (liftedRightHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.rightFrame dC).obj Y)).map
        (letI := ReedyModel.modelCategory r Fc Ff
         (((reedyReplacements r Fc Ff).q.app F).app j.unop ≫ c.ι.app j.unop).op) ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
         ((scalarReedyReplacements.{uJ, vJ, uD, max vC z} r.op).r.app
           (reedyQMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC F Y)).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r.op
  erw [reedyOutMappingComparison_projection, ← Category.assoc, ← Functor.map_comp]
  congr 1
  apply Functor.congr_map
  apply Quiver.Hom.unop_inj
  exact injection_desc (reedyReplacements r Fc Ff) F c j.unop

end Projective
section Injective
variable [HasColimitsOfSize.{0, max uJ vJ vC z} C] [HasLimitsOfShape J C]

/-- Every original caller cone retains the original R leg in the complete left-HFC/holim comparison. -/
theorem reedyIntoMappingComparison_lift (X : C) (F : J ⥤ C) (c : Cone F) (j : J) :
    (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        (letI := ReedyModel.modelCategory r Fc Ff; lift (reedyReplacements r Fc Ff) F c) ≫
      (reedyIntoMappingComparison.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
         limitProjection (scalarReedyReplacements.{uJ, vJ, uD, max vC z} r)
           (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F) j)) =
      (liftedLeftHomFunctor.{uC, vC, max uJ vJ z} ((PointedFramingAction.leftFrame dC).obj X)).map
        (letI := ReedyModel.modelCategory r Fc Ff; c.π.app j ≫ ((reedyReplacements r Fc Ff).r.app F).app j) ≫
        (letI := scalarReedyModel.{uJ, vJ, uD, max vC z} r
         ((scalarReedyReplacements.{uJ, vJ, uD, max vC z} r).r.app
           (reedyRMappingDiagram.{uJ, vJ, uC, vC, uD, z} r Fc Ff dC X F)).app j) := by
  let _ := ReedyModel.modelCategory r Fc Ff
  let _ := scalarReedyModel.{uJ, vJ, uD, max vC z} r
  erw [reedyIntoMappingComparison_projection, ← Category.assoc, ← Functor.map_comp, lift_projection]

end Injective
end ReedyOriginalCallerMappings

end HomotopicalAlgebra.DerivedDiagramConstructions
