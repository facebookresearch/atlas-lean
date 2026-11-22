/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.InternalHomLeft

/-!
# Parameter naturality of the other original tensor-Hom adjunction

The complete adjunction function is computed through the original opposite
tensor isomorphism and the actual wrapping equivalence unit. Its parameter
naturality follows from the proved opposite tensor naturality and the full
opposite tensor-Hom parameter equation. Both adjunctions of two variables
therefore retain the same original tensor functor.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj Opposite
open scoped MonoidalCategory

namespace Bimod.InternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {A B D : Mon C}

/-- The chosen opposite closed structure used by the fixed-left tensor-Hom parameter equations. -/
local instance leftParameterClosed : MonoidalClosed Cᴹᵒᵖ := leftOppositeClosed
local instance leftParameterColimits : HasColimitsOfSize.{0, 0} Cᴹᵒᵖ := leftOppositeColimits
local instance leftParameterLimits : HasLimitsOfSize.{0, 0} Cᴹᵒᵖ := leftOppositeLimits
local instance leftParameterLeftPreserves (X : Cᴹᵒᵖ) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) := leftOppositeLeftPreserves X
local instance leftParameterRightPreserves (X : Cᴹᵒᵖ) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) := leftOppositeRightPreserves X

omit [HasLimitsOfSize.{0, 0} C] in
/-- The entire tensor comparison retains the original inverse tensor map and actual equivalence unit. -/
theorem leftTensorComparison_hom_app (M : Bimod A B) (N : Bimod B D) :
    (leftTensorComparison M).hom.app N =
      (Bimod.unmopFunctor A D).map (mopTensorIso M N).inv ≫
        (mopEquivalence A D).unitIso.inv.app (tensorBimod M N) := rfl

/-- The complete left adjunct is the original opposite adjunct transported by the actual wrapping unit. -/
theorem leftTensorHomAdjunction_homEquiv (M : Bimod A B) (N : Bimod B D) (P : Bimod A D)
    (f : tensorBimod M N ⟶ P) :
    (leftTensorHomAdjunction M).homEquiv N P f =
      (mopEquivalence B D).unitIso.hom.app N ≫
        (Bimod.unmopFunctor B D).map
          ((tensorHomAdjunction (A := mopMon D) (mopBimodule M)).homEquiv
            (mopBimodule N) (mopBimodule P) ((mopTensorIso M N).inv ≫ mopBimoduleMap f)) := by
  let E := mopEquivalence A D
  let a := E.symm.toAdjunction
  let T := tensorBimod M N
  have hu : a.homEquiv (E.functor.obj T) T (E.unitIso.inv.app T) = 𝟙 (E.functor.obj T) := by
    change a.homEquiv (E.functor.obj T) T (a.counit.app T) = 𝟙 (E.functor.obj T)
    rw [← a.homEquiv_symm_id T]
    exact Equiv.apply_symm_apply _ _
  have he : a.homEquiv (tensorBimod (mopBimodule N) (mopBimodule M)) P
      (E.inverse.map (mopTensorIso M N).inv ≫ E.unitIso.inv.app T ≫ f) =
        (mopTensorIso M N).inv ≫ E.functor.map f := by
    erw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
    erw [hu, Category.id_comp]
    rfl
  rw [leftTensorHomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    leftTensorComparison_hom_app, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Category.assoc]
  change (mopEquivalence B D).toAdjunction.homEquiv N
      ((homFunctor (A := mopMon D) (mopBimodule M)).obj (mopBimodule P))
      ((tensorHomAdjunction (A := mopMon D) (mopBimodule M)).homEquiv
        (mopBimodule N) (mopBimodule P)
        (a.homEquiv (tensorBimod (mopBimodule N) (mopBimodule M)) P
          (E.inverse.map (mopTensorIso M N).inv ≫ E.unitIso.inv.app T ≫ f))) = _
  erw [he]
  exact (mopEquivalence B D).toAdjunction.homEquiv_unit _ _ _

omit [HasLimitsOfSize.{0, 0} C] in
/-- The original first-variable tensor map conjugates to the actual opposite second-variable tensor map. -/
theorem mopTensorIso_inv_whiskerRight {M M' : Bimod A B} (f : M ⟶ M') (N : Bimod B D) :
    (mopTensorIso M N).inv ≫ mopBimoduleMap (whiskerRight f N) =
      whiskerLeft (mopBimodule N) (mopBimoduleMap f) ≫ (mopTensorIso M' N).inv := by
  have h := mopTensorIso_naturality f (𝟙 N)
  have hi : mopBimoduleMap (𝟙 N) = 𝟙 (mopBimodule N) := by apply Bimod.hom_ext; rfl
  rw [hi] at h
  simp only [tensorMap, whiskerLeft_id_bimod, id_whiskerRight_bimod, Category.comp_id,
    Category.id_comp] at h
  apply (cancel_mono (mopTensorIso M' N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

/-- Both original source variables have their full natural tensor-Hom adjunction. -/
def leftTensorHomParametrized : tensorCurried A B D ⊣₂ leftHomContravariant (A := A) (B := B) (D := D) :=
  ParametrizedAdjunction.mk' (fun M => leftTensorHomAdjunction M) (by
    intro M M' f N P k
    let k₀ : tensorBimod M' N ⟶ P := k
    change (leftTensorHomAdjunction M).homEquiv N P (whiskerRight f N ≫ k₀) =
      (leftTensorHomAdjunction M').homEquiv N P k₀ ≫ leftHomPre f P
    rw [leftTensorHomAdjunction_homEquiv, leftTensorHomAdjunction_homEquiv, leftHomPre,
      Category.assoc, ← CategoryTheory.Functor.map_comp]
    have hm : mopBimoduleMap (whiskerRight f N ≫ k₀) =
        mopBimoduleMap (whiskerRight f N) ≫ mopBimoduleMap k₀ := by apply Bimod.hom_ext; rfl
    rw [hm, ← Category.assoc (mopTensorIso M N).inv, mopTensorIso_inv_whiskerRight, Category.assoc]
    have h := (tensorHomParametrized (A := mopMon D) (B := mopMon B) (D := mopMon A)).homEquiv_naturality_one
      (mopBimoduleMap f) ((mopTensorIso M' N).inv ≫ mopBimoduleMap k₀)
    change (tensorHomAdjunction (A := mopMon D) (mopBimodule M)).homEquiv
        (mopBimodule N) (mopBimodule P)
        (whiskerLeft (mopBimodule N) (mopBimoduleMap f) ≫
          (mopTensorIso M' N).inv ≫ mopBimoduleMap k₀) =
      (tensorHomAdjunction (A := mopMon D) (mopBimodule M')).homEquiv
        (mopBimodule N) (mopBimodule P) ((mopTensorIso M' N).inv ≫ mopBimoduleMap k₀) ≫
          homPre (mopBimoduleMap f) (mopBimodule P) at h
    exact congrArg (fun g => (mopEquivalence B D).unitIso.hom.app N ≫ (Bimod.unmopFunctor B D).map g) h)

local instance leftLeibnizSourceColimits : HasColimitsOfSize.{0, 0} (Bimod B D) := Bimod.hasColimits B D
local instance leftLeibnizTargetColimits : HasColimitsOfSize.{0, 0} (Bimod A D) := Bimod.hasColimits A D
local instance leftLeibnizSourceLimits : HasLimitsOfSize.{0, 0} (Bimod B D) := Bimod.hasLimits B D

/-- The other complete parameter adjunction induces the original bimodule Leibniz adjunction. -/
def leftTensorHomLeibnizAdjunction (f : Arrow (Bimod A B)) :
    (tensorCurried A B D).leibnizPushout.obj f ⊣
      (leftHomContravariant (A := A) (B := B) (D := D)).leibnizPullback.obj (op f) :=
  Functor.LeibnizAdjunction.adj _ _ leftTensorHomParametrized f

end Bimod.InternalHom
