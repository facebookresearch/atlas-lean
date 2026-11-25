/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFiber
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCofiber

/-!
# Universal properties of the canonical homotopy fibers and cofibers

The existing canonical replacement functors provide the actual zero diagrams,
unit/counit legs, and all caller cone/cocone maps. Universal properties are
stated directly for `homotopyFiber` and `homotopyCofiber`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe v u
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra
variable {C : Type u} [Category.{v} C] [ModelCategory C]

section Fibers
variable [HasZeroObject C]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- The original zero cospan followed by the canonical homotopy-pullback replacement. -/
def homotopyFiberDiagram : Arrow C ⥤ WalkingCospan ⥤ C :=
  fiberCospan (C := C) ⋙ homotopyPullbackReplacementFunctor

/-- The canonical homotopy fiber is the limit of that actual replacement diagram. -/
theorem homotopyFiber_obj (f : Arrow C) :
    (homotopyFiber (C := C)).obj f = limit ((homotopyFiberDiagram (C := C)).obj f) :=
  homotopyPullback_obj ((fiberCospan (C := C)).obj f)

/-- The canonical homotopy fiber carries the actual limiting replacement cone. -/
def homotopyFiberCone (f : Arrow C) : Cone ((homotopyFiberDiagram (C := C)).obj f) :=
  (limit.cone _).extend (eqToHom (homotopyFiber_obj f))

/-- Its universal property is transported from the actual chosen limit. -/
def homotopyFiberConeIsLimit (f : Arrow C) : IsLimit (homotopyFiberCone f) :=
  IsLimit.extendIso (eqToHom (homotopyFiber_obj f)) (limit.isLimit _)

/-- The canonical homotopy fiber projects to every actual replacement vertex. -/
def homotopyFiberProjection (f : Arrow C) (j : WalkingCospan) :
    (homotopyFiber (C := C)).obj f ⟶ ((homotopyFiberDiagram (C := C)).obj f).obj j :=
  eqToHom (homotopyFiber_obj f) ≫ limit.π _ j

/-- Every caller cone retains all original legs followed by the canonical replacement unit. -/
def homotopyFiberReplacedCone (f : Arrow C) (c : Cone ((fiberCospan (C := C)).obj f)) :
    Cone ((homotopyFiberDiagram (C := C)).obj f) where
  pt := c.pt
  π := c.π ≫ (homotopyPullbackReplacementUnit (C := C)).app ((fiberCospan (C := C)).obj f)

/-- The caller's full map into the canonical homotopy fiber. -/
def homotopyFiberLift (f : Arrow C) (c : Cone ((fiberCospan (C := C)).obj f)) :
    c.pt ⟶ (homotopyFiber (C := C)).obj f :=
  limit.lift _ (homotopyFiberReplacedCone f c) ≫ eqToHom (homotopyFiber_obj f).symm

/-- Every original caller leg retains the exact canonical replacement-unit component. -/
theorem homotopyFiberLift_projection (f : Arrow C) (c : Cone ((fiberCospan (C := C)).obj f))
    (j : WalkingCospan) :
    homotopyFiberLift f c ≫ homotopyFiberProjection f j =
      c.π.app j ≫
        ((homotopyPullbackReplacementUnit (C := C)).app ((fiberCospan (C := C)).obj f)).app j := by
  simp only [homotopyFiberLift, homotopyFiberProjection, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, limit.lift_π,
    homotopyFiberReplacedCone]
  with_unfolding_all rfl

/-- The entire map into the canonical homotopy fiber is determined by all replaced caller legs. -/
theorem homotopyFiberLift_unique (f : Arrow C) (c : Cone ((fiberCospan (C := C)).obj f))
    (m : c.pt ⟶ (homotopyFiber (C := C)).obj f)
    (hm : ∀ j, m ≫ homotopyFiberProjection f j =
      c.π.app j ≫
        ((homotopyPullbackReplacementUnit (C := C)).app ((fiberCospan (C := C)).obj f)).app j) :
    m = homotopyFiberLift f c := by
  apply (cancel_mono (eqToHom (homotopyFiber_obj f))).mp
  apply limit.hom_ext
  intro j
  simpa only [homotopyFiberProjection, Category.assoc] using
    (hm j).trans (homotopyFiberLift_projection f c j).symm

/-- The canonical fiber map is the actual limit map of its full replaced arrow square. -/
theorem homotopyFiber_map {f g : Arrow C} (sq : f ⟶ g) :
    (homotopyFiber (C := C)).map sq =
      eqToHom (homotopyFiber_obj f) ≫
        lim.map ((homotopyFiberDiagram (C := C)).map sq) ≫ eqToHom (homotopyFiber_obj g).symm :=
  homotopyPullback_map ((fiberCospan (C := C)).map sq)

/-- Every original arrow square retains all canonical fiber projection naturalities. -/
theorem homotopyFiber_map_projection {f g : Arrow C} (sq : f ⟶ g) (j : WalkingCospan) :
    (homotopyFiber (C := C)).map sq ≫ homotopyFiberProjection g j =
      homotopyFiberProjection f j ≫ ((homotopyFiberDiagram (C := C)).map sq).app j := by
  rw [homotopyFiber_map]
  simp only [homotopyFiberProjection, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  apply congrArg (fun h => eqToHom (homotopyFiber_obj f) ≫ h)
  with_unfolding_all exact (limMap_π ((homotopyFiberDiagram (C := C)).map sq) j)

/-- The canonical ordinary-fiber comparison retains the full original replacement unit. -/
theorem homotopyFiberComparison_replacement (f : Arrow C) :
    (homotopyFiberComparison (C := C)).app f ≫ eqToHom (homotopyFiber_obj f) =
      lim.map ((homotopyPullbackReplacementUnit (C := C)).app ((fiberCospan (C := C)).obj f)) :=
  homotopyPullbackComparison_replacement ((fiberCospan (C := C)).obj f)

end Fibers

section Cofibers
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

/-- The original cofiber span followed by the canonical homotopy-pushout replacement. -/
def homotopyCofiberDiagram : Arrow C ⥤ WalkingSpan ⥤ C :=
  cofiberSpan (C := C) ⋙ homotopyPushoutReplacementFunctor

/-- The canonical homotopy cofiber is the colimit of that actual replacement diagram. -/
theorem homotopyCofiber_obj (f : Arrow C) :
    (homotopyCofiber (C := C)).obj f = colimit ((homotopyCofiberDiagram (C := C)).obj f) :=
  homotopyPushout_obj ((cofiberSpan (C := C)).obj f)

/-- The canonical homotopy cofiber carries the actual colimiting replacement cocone. -/
def homotopyCofiberCocone (f : Arrow C) : Cocone ((homotopyCofiberDiagram (C := C)).obj f) :=
  (colimit.cocone _).extend (eqToHom (homotopyCofiber_obj f).symm)

/-- Its universal property is transported from the actual chosen colimit. -/
def homotopyCofiberCoconeIsColimit (f : Arrow C) : IsColimit (homotopyCofiberCocone f) :=
  IsColimit.extendIso (eqToHom (homotopyCofiber_obj f).symm) (colimit.isColimit _)

/-- Every actual replacement vertex injects into the canonical homotopy cofiber. -/
def homotopyCofiberInjection (f : Arrow C) (j : WalkingSpan) :
    ((homotopyCofiberDiagram (C := C)).obj f).obj j ⟶ (homotopyCofiber (C := C)).obj f :=
  colimit.ι _ j ≫ eqToHom (homotopyCofiber_obj f).symm

/-- Every caller cocone retains the canonical replacement counit and all original legs. -/
def homotopyCofiberReplacedCocone (f : Arrow C) (c : Cocone ((cofiberSpan (C := C)).obj f)) :
    Cocone ((homotopyCofiberDiagram (C := C)).obj f) where
  pt := c.pt
  ι := (homotopyPushoutReplacementCounit (C := C)).app ((cofiberSpan (C := C)).obj f) ≫ c.ι

/-- The caller's full map out of the canonical homotopy cofiber. -/
def homotopyCofiberDesc (f : Arrow C) (c : Cocone ((cofiberSpan (C := C)).obj f)) :
    (homotopyCofiber (C := C)).obj f ⟶ c.pt :=
  eqToHom (homotopyCofiber_obj f) ≫ colimit.desc _ (homotopyCofiberReplacedCocone f c)

/-- Every original caller leg retains the exact canonical replacement-counit component. -/
theorem homotopyCofiberInjection_desc (f : Arrow C) (c : Cocone ((cofiberSpan (C := C)).obj f))
    (j : WalkingSpan) :
    homotopyCofiberInjection f j ≫ homotopyCofiberDesc f c =
      ((homotopyPushoutReplacementCounit (C := C)).app ((cofiberSpan (C := C)).obj f)).app j ≫
        c.ι.app j := by
  simp only [homotopyCofiberInjection, homotopyCofiberDesc, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, colimit.ι_desc,
    homotopyCofiberReplacedCocone]
  with_unfolding_all rfl

/-- All replaced caller legs uniquely determine the entire canonical cofiber map. -/
theorem homotopyCofiberDesc_unique (f : Arrow C) (c : Cocone ((cofiberSpan (C := C)).obj f))
    (m : (homotopyCofiber (C := C)).obj f ⟶ c.pt)
    (hm : ∀ j, homotopyCofiberInjection f j ≫ m =
      ((homotopyPushoutReplacementCounit (C := C)).app ((cofiberSpan (C := C)).obj f)).app j ≫
        c.ι.app j) : m = homotopyCofiberDesc f c := by
  apply (cancel_epi (eqToHom (homotopyCofiber_obj f).symm)).mp
  apply colimit.hom_ext
  intro j
  simpa only [homotopyCofiberInjection, Category.assoc] using
    (hm j).trans (homotopyCofiberInjection_desc f c j).symm

/-- The canonical cofiber map is the actual colimit map of its full replaced arrow square. -/
theorem homotopyCofiber_map {f g : Arrow C} (sq : f ⟶ g) :
    (homotopyCofiber (C := C)).map sq =
      eqToHom (homotopyCofiber_obj f) ≫
        colim.map ((homotopyCofiberDiagram (C := C)).map sq) ≫ eqToHom (homotopyCofiber_obj g).symm
            :=
  homotopyPushout_map ((cofiberSpan (C := C)).map sq)

/-- Every original arrow square retains all canonical cofiber injection naturalities. -/
theorem homotopyCofiberInjection_map {f g : Arrow C} (sq : f ⟶ g) (j : WalkingSpan) :
    homotopyCofiberInjection f j ≫ (homotopyCofiber (C := C)).map sq =
      ((homotopyCofiberDiagram (C := C)).map sq).app j ≫ homotopyCofiberInjection g j := by
  rw [homotopyCofiber_map]
  simp only [homotopyCofiberInjection, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun h => h ≫ eqToHom (homotopyCofiber_obj g).symm)
  with_unfolding_all exact (ι_colimMap ((homotopyCofiberDiagram (C := C)).map sq) j)

/-- The canonical ordinary-cofiber comparison retains the full original replacement counit. -/
theorem homotopyCofiberComparison_replacement (f : Arrow C) :
    eqToHom (homotopyCofiber_obj f).symm ≫ (homotopyCofiberComparison (C := C)).app f =
      colim.map ((homotopyPushoutReplacementCounit (C := C)).app ((cofiberSpan (C := C)).obj f)) :=
  homotopyPushoutComparison_replacement ((cofiberSpan (C := C)).obj f)

end Cofibers
end HomotopicalAlgebra
