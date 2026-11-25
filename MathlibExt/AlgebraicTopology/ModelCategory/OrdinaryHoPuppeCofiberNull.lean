/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe

/-!
# Actual chosen Puppe cofiber nullness

The two proved image/kernel laws are applied to the same chosen cofiber
and boundary functions. Injectivity of the original restriction and
surjectivity of its actual suspended restriction force every cofiber
class to be null. Both contractible cones and all original choices remain
explicit. Applications must prove these two restriction properties.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryHoPuppeCofiberNull

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]

/-- The entire original ordinary-Ho restriction function. -/
def precomposition {X Y : C} (f : X ⟶ Y) (E : C) :
    (((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E) →
      (((weakEquivalences C).Q).obj X ⟶ ((weakEquivalences C).Q).obj E) :=
  fun g => ((weakEquivalences C).Q).map f ≫ g

omit [HasZeroObject C] in
/-- Every complete identity restriction is the original identity function. -/
theorem precomposition_id (X E : C) : precomposition (𝟙 X) E = id := by
  funext g
  change ((weakEquivalences C).Q).map (𝟙 X) ≫ g = g
  rw [((weakEquivalences C).Q).map_id, Category.id_comp]

omit [HasZeroObject C] in
/-- The complete original restriction functions compose contravariantly. -/
theorem precomposition_comp {X Y W : C} (f : X ⟶ Y) (g : Y ⟶ W) (E : C) :
    precomposition (f ≫ g) E = precomposition f E ∘ precomposition g E := by
  funext h
  change ((weakEquivalences C).Q).map (f ≫ g) ≫ h =
    ((weakEquivalences C).Q).map f ≫ (((weakEquivalences C).Q).map g ≫ h)
  rw [Functor.map_comp, Category.assoc]

omit [HasZeroObject C] in
/-- Every full target map commutes with the original restriction function. -/
theorem precomposition_target {X Y E E' : C} (f : X ⟶ Y) (p : E ⟶ E')
    (g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E) :
    precomposition f E' (g ≫ ((weakEquivalences C).Q).map p) =
      precomposition f E g ≫ ((weakEquivalences C).Q).map p :=
  (Category.assoc _ _ _).symm

/-- The full restriction retains the same actual null endpoint class. -/
theorem precomposition_null {X Y : C} (f : X ⟶ Y) (E : C) :
    precomposition f E (OrdinaryHoCofiberKernel.nullHom Y E) =
      OrdinaryHoCofiberKernel.nullHom X E :=
  OrdinaryHoCofiberKernel.precomp_nullHom f

variable (Z : C) (hZ : IsZero Z)
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

/-- Both actual image/kernel laws force the SAME chosen cofiber class to be null. -/
theorem cofiberHom_eq_null (F : Arrow C) [IsCofibrant F.left] [IsCofibrant F.right]
    [Cofibration (ι.app F.left)] (E : C) [IsFibrant E]
    (hSourceCone : weakEquivalences C
      (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.left)))
    (hTargetCone : weakEquivalences C
      (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.right)))
    (hRestriction : Function.Injective (precomposition F.hom E))
    (hSuspendedRestriction : Function.Surjective (precomposition
      (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom) E))
    (g : ((weakEquivalences C).Q).obj (c F).pt ⟶ ((weakEquivalences C).Q).obj E) :
    g = OrdinaryHoCofiberKernel.nullHom (c F).pt E := by
  let r := ((weakEquivalences C).Q).map (c F).inr ≫ g
  have hKernel := (OrdinaryHoChosenPuppe.first_exact Z hZ cone ι c hc F E
    hSourceCone r).mp ⟨g, rfl⟩
  have hNullRestriction : r = OrdinaryHoCofiberKernel.nullHom F.right E :=
    hRestriction (hKernel.trans (precomposition_null F.hom E).symm)
  obtain ⟨h, hh⟩ :=
    (OrdinaryHoChosenPuppe.second_exact Z hZ cone ι c hc F E g).mpr hNullRestriction
  obtain ⟨k, hk⟩ := hSuspendedRestriction h
  exact hh.symm.trans ((congrArg
    (fun t => ((weakEquivalences C).Q).map
      (OrdinaryHoChosenPuppe.boundary cone ι c hc Z hZ F) ≫ t) hk.symm).trans
    (OrdinaryHoChosenPuppe.boundary_suspension_post_null Z hZ cone ι c hc F E
      hTargetCone k))

/-- The same two entire restrictions give actual uniqueness of all chosen cofiber classes. -/
theorem cofiberHom_subsingleton (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] [Cofibration (ι.app F.left)]
    (E : C) [IsFibrant E]
    (hSourceCone : weakEquivalences C
      (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.left)))
    (hTargetCone : weakEquivalences C
      (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.right)))
    (hRestriction : Function.Injective (precomposition F.hom E))
    (hSuspendedRestriction : Function.Surjective (precomposition
      (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom) E)) :
    Subsingleton (((weakEquivalences C).Q).obj (c F).pt ⟶ ((weakEquivalences C).Q).obj E) := by
  refine ⟨fun g h => ?_⟩
  exact (cofiberHom_eq_null Z hZ cone ι c hc F E hSourceCone hTargetCone
    hRestriction hSuspendedRestriction g).trans
    (cofiberHom_eq_null Z hZ cone ι c hc F E hSourceCone hTargetCone
      hRestriction hSuspendedRestriction h).symm

omit cone ι c hc [HasZeroObject C] in
/-- The original terminal endpoint has bijective restriction precisely when
its target Hom is unique. -/
theorem toZero_precomposition_bijective_iff (W E : C) [IsFibrant E] :
    Function.Bijective (precomposition (OrdinaryHoChosenPuppe.toZero Z hZ W) E) ↔
      Subsingleton (((weakEquivalences C).Q).obj W ⟶ ((weakEquivalences C).Q).obj E) := by
  have hZero := OrdinaryHoChosenPuppe.actualZeroHom_subsingleton Z hZ E
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    obtain ⟨a₀, rfl⟩ := h.2 a
    obtain ⟨b₀, rfl⟩ := h.2 b
    exact congrArg (precomposition (OrdinaryHoChosenPuppe.toZero Z hZ W) E)
      (hZero.elim a₀ b₀)
  · intro h
    refine ⟨fun a b _ => hZero.elim a b, fun g => ?_⟩
    exact ⟨((weakEquivalences C).Q).map (OrdinaryHoChosenPuppe.fromZero Z hZ E), h.elim _ g⟩

/-- The actual chosen cofiber-to-zero map has bijective restriction by the two proved kernels. -/
theorem cofiber_toZero_precomposition_bijective (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] [Cofibration (ι.app F.left)]
    (E : C) [IsFibrant E]
    (hSourceCone : weakEquivalences C
      (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.left)))
    (hTargetCone : weakEquivalences C
      (OrdinaryHoChosenPuppe.toZero Z hZ (cone.obj F.right)))
    (hRestriction : Function.Injective (precomposition F.hom E))
    (hSuspendedRestriction : Function.Surjective (precomposition
      (OrdinaryHoChosenPuppe.suspensionMap cone ι c hc Z hZ F.hom) E)) :
    Function.Bijective (precomposition
      (OrdinaryHoChosenPuppe.toZero Z hZ (c F).pt) E) :=
  (toZero_precomposition_bijective_iff Z hZ (c F).pt E).mpr
    (cofiberHom_subsingleton Z hZ cone ι c hc F E hSourceCone hTargetCone
      hRestriction hSuspendedRestriction)

end HomotopicalAlgebra.OrdinaryHoPuppeCofiberNull
