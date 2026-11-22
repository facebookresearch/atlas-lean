/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableSourceShiftHom
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStablePuppeConnecting
import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# The actual original ordinary-stable cofiber triangles

The coherent integer shift is constructed from the original framing
suspension/loop equivalence. Every input Arrow gives a native triangle
whose maps are its actual Ho input, original Q-cofiber inclusion and
original cone/framing boundary. Every full Arrow square gives a native
triangle morphism. All three consecutive composites vanish by the
original source-built Puppe exactness.

This supplies the actual source triangle family. The further all-Ho
arrow representation, signed rotation and distinguished-triangle axioms
require their source comparison proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits Pretriangulated HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableCofiberTriangle

open OrdinaryStablePuppeGroups

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "H" => toHomotopyCategory C
local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)

/-- The entire original target counit is a natural Iso on all original Arrow objects and maps. -/
def targetCounitNatIso :
    GeneratedOrdinaryPuppe.termFunctor g Z hZ 1 ⋙ (H) ≅ Arrow.rightFunc ⋙ (H) :=
  NatIso.ofComponents (OrdinaryStablePuppeConnecting.targetCounitIso g Z hZ) (fun a => by
    change (H).map ((GeneratedFunctorialReplacements.Q g).map a.right) ≫
        (H).map ((GeneratedFunctorialReplacements.counit g).app _) =
      (H).map ((GeneratedFunctorialReplacements.counit g).app _) ≫ (H).map a.right
    simp only [← Functor.map_comp]
    exact (H).congr_map ((GeneratedFunctorialReplacements.counit g).naturality a.right))

/-- The same inverse target counit and original Puppe step give the full inclusion transformation. -/
def inclusionNatTrans : Arrow.rightFunc ⋙ (H) ⟶
    GeneratedOrdinaryPuppe.termFunctor g Z hZ 2 ⋙ (H) :=
  (targetCounitNatIso g Z hZ).inv ≫
    Functor.whiskerRight (GeneratedOrdinaryPuppe.step g Z hZ 1) (H)

omit [HasZeroObject C] [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- Every entire input square preserves the original target inclusion. -/
theorem inclusion_naturality {F G : Arrow C} (a : F ⟶ G) :
    (H).map a.right ≫ OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ G =
      OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F ≫
        OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a := by
  unfold OrdinaryStablePuppeConnecting.originalTargetArrow
    OrdinaryStablePuppeConnecting.targetArrow OrdinaryStablePuppeConnecting.cofiberMap cofiberHo
  exact (inclusionNatTrans g Z hZ).naturality a

/-- The actual input, original cofiber inclusion and original ordinary boundary give a native triangle. -/
def triangle (F : Arrow C) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    Triangle (HomotopyCategory C) := by
  letI := OrdinaryStableSourceShiftHom.hasShift g
  refine Triangle.mk ((H).map F.hom)
    (OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F) ?_
  change cofiberHo g Z hZ F ⟶ (Σ).obj ((H).obj F.left)
  exact OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F

/-- Both input components and the actual original cofiber map form the whole native triangle square. -/
def map {F G : Arrow C} (a : F ⟶ G) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    triangle g Z hZ F ⟶ triangle g Z hZ G := by
  letI := OrdinaryStableSourceShiftHom.hasShift g
  refine Triangle.homMk _ _ ((H).map a.left) ((H).map a.right)
    (OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a) ?_ ?_ ?_
  · change (H).map F.hom ≫ (H).map a.right = (H).map a.left ≫ (H).map G.hom
    simpa only [← Functor.map_comp] using (H).congr_map a.w.symm
  · exact (inclusion_naturality g Z hZ a).symm
  · exact (OrdinaryStablePuppeConnecting.boundary_naturality g Z hZ a).symm

/-- The complete original source triangle construction is functorial on all actual Arrows. -/
def triangleFunctor :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    Arrow C ⥤ Triangle (HomotopyCategory C) := by
  letI := OrdinaryStableSourceShiftHom.hasShift g
  exact
    { obj := triangle g Z hZ
      map := map g Z hZ
      map_id := fun F => by
        apply Triangle.hom_ext
        · exact (H).map_id F.left
        · exact (H).map_id F.right
        · change OrdinaryStablePuppeConnecting.cofiberMap g Z hZ (𝟙 F) = 𝟙 _
          unfold OrdinaryStablePuppeConnecting.cofiberMap cofiberHo
          exact (GeneratedOrdinaryPuppe.termFunctor g Z hZ 2 ⋙ (H)).map_id F
      map_comp := fun a b => by
        apply Triangle.hom_ext
        · exact (H).map_comp a.left b.left
        · exact (H).map_comp a.right b.right
        · change OrdinaryStablePuppeConnecting.cofiberMap g Z hZ (a ≫ b) =
            OrdinaryStablePuppeConnecting.cofiberMap g Z hZ a ≫
              OrdinaryStablePuppeConnecting.cofiberMap g Z hZ b
          unfold OrdinaryStablePuppeConnecting.cofiberMap cofiberHo
          exact (GeneratedOrdinaryPuppe.termFunctor g Z hZ 2 ⋙ (H)).map_comp a b }

/-- The exact original first and second triangle maps have zero composite at their full Ho endpoints. -/
theorem input_inclusion_zero (F : Arrow C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (H).map F.hom ≫ OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply (OrdinaryStablePuppeConnecting.exact_at_target_original g Z hZ F
    (cofiberHo g Z hZ F) (OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F)).mp
  refine ⟨𝟙 _, ?_⟩
  change OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F ≫
    𝟙 (cofiberHo g Z hZ F) = OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F
  exact Category.comp_id _

/-- The actual second and original framing-boundary maps have zero composite. -/
theorem inclusion_boundary_zero (F : Arrow C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F ≫
      OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply (OrdinaryStablePuppeConnecting.exact_at_cofiber_original g Z hZ F
    ((Σ).obj ((H).obj F.left)) (OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F)).mp
  refine ⟨𝟙 _, ?_⟩
  change OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫
    𝟙 ((Σ).obj ((H).obj F.left)) = OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F
  exact Category.comp_id _

/-- The original boundary followed by the actual suspension of the input map also has zero composite. -/
theorem boundary_suspension_zero (F : Arrow C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫ (Σ).map ((H).map F.hom) = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  apply (OrdinaryStablePuppeConnecting.exact_at_suspension g Z hZ F
    ((Σ).obj ((H).obj F.right)) ((Σ).map ((H).map F.hom))).mp
  refine ⟨𝟙 _, ?_⟩
  change (Σ).map ((H).map F.hom) ≫ 𝟙 ((Σ).obj ((H).obj F.right)) =
    (Σ).map ((H).map F.hom)
  exact Category.comp_id _

/-- The source triangle family retains an entire original input Arrow and all three Iso components. -/
def sourceTriangles :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    Set (Triangle (HomotopyCategory C)) := by
  letI := OrdinaryStableSourceShiftHom.hasShift g
  exact {T | ∃ F : Arrow C, Nonempty (T ≅ triangle g Z hZ F)}

/-- Every original full cofiber triangle belongs to the constructed source family. -/
theorem triangle_mem (F : Arrow C) :
    letI := OrdinaryStableSourceShiftHom.hasShift g
    triangle g Z hZ F ∈ sourceTriangles g Z hZ :=
  ⟨F, ⟨Iso.refl _⟩⟩

/-- An actual whole triangle Iso transports the original source family, with all components retained. -/
theorem sourceTriangles_iso {T T' :
    letI := OrdinaryStableSourceShiftHom.hasShift g; Triangle (HomotopyCategory C)}
    (a : T ≅ T') (hT : T ∈ sourceTriangles g Z hZ) : T' ∈ sourceTriangles g Z hZ := by
  obtain ⟨F, ⟨b⟩⟩ := hT
  exact ⟨F, ⟨a.symm ≪≫ b⟩⟩

end HomotopicalAlgebra.OrdinaryStableCofiberTriangle
