/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorHom
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# The full parametrized adjunction of the actual bimodule tensor

The right tensor-Hom adjunction is natural in the original composable
right bimodule. Parameter naturality uses its actual quotient square and
the original internal-Hom pre-map. The Leibniz adjunction then retains
the actual pushout corner and the corresponding actual pullback corner.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w w'

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj Opposite
open scoped MonoidalCategory

namespace Bimod.InternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {A B D : Mon C}

omit [BraidedCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] in
/-- Flipping the original curried tensor retains the entire original fixed-right tensor functor. -/
theorem tensorCurried_flip_obj (N : Bimod B D) :
    (tensorCurried A B D).flip.obj N = tensorRightFunctor (A := A) N := rfl

/-- The complete actual adjunction Hom function retains the two constructed original inverse functions. -/
theorem tensorHomAdjunction_homEquiv (M : Bimod A B) (N : Bimod B D) (P : Bimod A D) :
    (tensorHomAdjunction N).homEquiv M P = tensorHomEquiv M N P := by
  rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The complete forward adjunction function is the original relative curry. -/
theorem tensorHomAdjunction_forward (M : Bimod A B) (N : Bimod B D) (P : Bimod A D)
    (f : tensorBimod M N ⟶ P) : (tensorHomAdjunction N).homEquiv M P f = curry f := by
  rw [tensorHomAdjunction_homEquiv]
  rfl

/-- The complete backward adjunction function is the original relative uncurry. -/
theorem tensorHomAdjunction_reverse (M : Bimod A B) (N : Bimod B D) (P : Bimod A D)
    (f : M ⟶ homObject N P) : ((tensorHomAdjunction N).homEquiv M P).symm f = uncurry f := by
  rw [tensorHomAdjunction_homEquiv]
  rfl

/-- The entire original adjunction unit is obtained by currying the actual tensor identity. -/
theorem tensorHomAdjunction_unit (M : Bimod A B) (N : Bimod B D) :
    (tensorHomAdjunction N).unit.app M = curry (𝟙 (tensorBimod M N)) := by
  rw [← Adjunction.homEquiv_id, tensorHomAdjunction_homEquiv]
  rfl

/-- The complete actual counit is the original evaluator descended through the balancing quotient. -/
theorem tensorHomAdjunction_counit (N : Bimod B D) (P : Bimod A D) :
    (tensorHomAdjunction N).counit.app P = evaluation N P := by
  rw [← Adjunction.homEquiv_symm_id, tensorHomAdjunction_homEquiv]
  change uncurry (𝟙 (homObject N P)) = evaluation N P
  rw [uncurry, id_whiskerRight_bimod, Category.id_comp]

/-- The original tensor unit/counit maps satisfy the complete left triangle on every bimodule. -/
theorem tensorHom_left_triangle (M : Bimod A B) (N : Bimod B D) :
    (tensorRightFunctor N).map ((tensorHomAdjunction N).unit.app M) ≫
      (tensorHomAdjunction N).counit.app (tensorBimod M N) = 𝟙 (tensorBimod M N) :=
  (tensorHomAdjunction N).left_triangle_components M

/-- The original Hom unit/counit maps satisfy the complete right triangle on every bimodule. -/
theorem tensorHom_right_triangle (N : Bimod B D) (P : Bimod A D) :
    (tensorHomAdjunction N).unit.app (homObject N P) ≫
      (homFunctor N).map ((tensorHomAdjunction N).counit.app P) = 𝟙 (homObject N P) :=
  (tensorHomAdjunction N).right_triangle_components P

/-- Every original right-bimodule arrow gives the full parameter naturality of the actual adjunct. -/
def tensorHomParametrized : (tensorCurried A B D).flip ⊣₂ homContravariant (A := A) (B := B) (D := D) :=
  ParametrizedAdjunction.mk' (fun N => tensorHomAdjunction N) (by
    intro N N' f M P k
    let k₀ : tensorBimod M N' ⟶ P := k
    change (tensorHomAdjunction N).homEquiv M P (whiskerLeft M f ≫ k₀) =
      (tensorHomAdjunction N').homEquiv M P k₀ ≫ homPre f P
    rw [tensorHomAdjunction_forward, tensorHomAdjunction_forward]
    change curry (whiskerLeft M f ≫ k₀) = curry k₀ ≫ homPre f P
    apply hom_ext N P
    rw [curry_inclusion, Category.assoc, homPre_inclusion, ← Category.assoc, curry_inclusion]
    apply Bimod.hom_ext
    simp only [Bimod.comp_hom', curryUnbalanced_hom, unbalancedPre_hom]
    rw [← Category.assoc, tensorProjection_whiskerLeft, Category.assoc,
      originalRightTensorAdjunction_homEquiv, originalRightTensorAdjunction_homEquiv,
      MonoidalClosed.curry_pre_app, BraidedCategory.braiding_naturality_left_assoc])

section Leibniz

variable [HasColimitsOfSize.{0, 0} C]

local instance sourcePushouts : HasColimitsOfSize.{0, 0} (Bimod A B) := Bimod.hasColimits A B
local instance targetPushouts : HasColimitsOfSize.{0, 0} (Bimod A D) := Bimod.hasColimits A D
local instance sourcePullbacks : HasLimitsOfSize.{0, 0} (Bimod A B) := Bimod.hasLimits A B

/-- The complete parameter adjunction induces the actual bimodule Leibniz pushout/pullback adjunction. -/
def tensorHomLeibnizAdjunction (g : Arrow (Bimod B D)) :
    ((tensorCurried A B D).flip.leibnizPushout).obj g ⊣
      (homContravariant (A := A) (B := B) (D := D)).leibnizPullback.obj (op g) :=
  Functor.LeibnizAdjunction.adj _ _ tensorHomParametrized g

/-- The actual Leibniz corner functor preserves every supplied source colimit in independent universes. -/
theorem tensorHomLeibniz_preservesColimits (g : Arrow (Bimod B D)) :
    PreservesColimitsOfSize.{w', w} (((tensorCurried A B D).flip.leibnizPushout).obj g) :=
  (tensorHomLeibnizAdjunction g).leftAdjoint_preservesColimits

end Leibniz
end Bimod.InternalHom
