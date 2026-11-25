/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.InternalHomFunctor
public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorUniversal

/-!
# The original composable bimodule tensor-Hom adjunction

Evaluation descends the original equalizer pairing through the actual
balanced tensor. Currying uses the original tensor projection and the
right tensor adjunction. Its right-linearity equalizer condition follows
from the source tensor right action and the actual target bimodule map.
Both inverse functions and their naturalities retain these original maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj
open CategoryTheory.HomogeneousLocalization
open scoped MonoidalCategory

namespace Bimod.InternalHom

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {A B D : Mon C}

/-- The original equalizer pairing descends to an actual evaluator preserving both outer actions. -/
def evaluation (N : Bimod B D) (P : Bimod A D) : tensorBimod (homObject N P) N ⟶ P :=
  tensorDesc (homObject N P) N P (underlyingEvaluation N P)
    (underlyingEvaluation_balance N P)
    (by
      have h : (Mod.AmbientTensor.rightModule A.X N.X (toLeftModule (homObject N P))).mod.smul ≫
          (evaluationLeftMap N P).hom =
        (A.X ◁ (evaluationLeftMap N P).hom) ≫ P.actLeft :=
          (evaluationLeftMap N P).isModHom.smul_hom
      rw [Mod.AmbientTensor.rightModule_smul, evaluationLeftMap_hom] at h
      simp only [Category.assoc] at h
      exact h)
    (underlyingEvaluation_right_linear N P)

/-- The entire relative evaluator retains the original inclusion/evaluation pairing on the quotient. -/
@[reassoc] theorem tensorProjection_evaluation (N : Bimod B D) (P : Bimod A D) :
    tensorProjection (homObject N P) N ≫ (evaluation N P).hom = underlyingEvaluation N P :=
  tensorProjection_tensorDescRaw (homObject N P) N (underlyingEvaluation N P)
    (underlyingEvaluation_balance N P)

omit [HasLimitsOfSize.{0, 0} C] in
/-- A map from the actual balanced tensor gives the original A-linear uncurried source pairing. -/
def tensorPairingLeftMap {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) : Mod.AmbientTensor.rightModule A.X N.X (toLeftModule M) ⟶ toLeftModule P :=
  Mod.Hom.mk' (M := Mod.AmbientTensor.rightModule A.X N.X (toLeftModule M)) (N := toLeftModule P)
    (tensorProjection M N ≫ f.hom) (by
    have h : (Mod.AmbientTensor.rightModule A.X N.X (toLeftModule M)).mod.smul ≫
        (tensorProjection M N ≫ f.hom) = (A.X ◁ (tensorProjection M N ≫ f.hom)) ≫ P.actLeft := by
      rw [Mod.AmbientTensor.rightModule_smul]
      change ((α_ A.X M.X N.X).inv ≫ (M.actLeft ▷ N.X)) ≫ (tensorProjection M N ≫ f.hom) =
        (A.X ◁ (tensorProjection M N ≫ f.hom)) ≫ P.actLeft
      rw [Category.assoc, ← tensorProjection_leftAction_assoc, f.left_act_hom,
        ← whiskerLeft_comp_assoc]
    exact h)

omit [HasLimitsOfSize.{0, 0} C] in
/-- Original right currying of that pairing is an actual A-module map. -/
def curryUnbalancedLeft {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) : toLeftModule M ⟶ leftModule N P :=
  (ambientRightAdjunction A N.X).homEquiv (toLeftModule M) (toLeftModule P) (tensorPairingLeftMap f)

omit [HasLimitsOfSize.{0, 0} C] in
/-- The full curry carrier is the original right adjunct of the actual tensor projection. -/
theorem curryUnbalancedLeft_hom {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) :
    (curryUnbalancedLeft f).hom =
      (originalRightTensorAdjunction N.X).homEquiv M.X P.X (tensorProjection M N ≫ f.hom) := by
  rw [curryUnbalancedLeft, ambientRightAdjunction_homEquiv]
  rfl

omit [HasLimitsOfSize.{0, 0} C] in
/-- The actual source balancing equation makes the same curry a morphism of both outer actions. -/
def curryUnbalanced {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) : M ⟶ unbalanced N P where
  hom := (curryUnbalancedLeft f).hom
  left_act_hom := (curryUnbalancedLeft f).isModHom.smul_hom
  right_act_hom := by
    rw [curryUnbalancedLeft_hom]
    apply (Mod.RightLeftTensor.rightCurry_linear_iff (toRightModule M) (toLeftModule N)
      (tensorProjection M N ≫ f.hom)).mpr
    exact tensorProjection_balance_assoc M N f.hom

omit [HasLimitsOfSize.{0, 0} C] in
/-- The complete unbalanced curry retains the original right tensor-Hom function. -/
theorem curryUnbalanced_hom {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) :
    (curryUnbalanced f).hom =
      (originalRightTensorAdjunction N.X).homEquiv M.X P.X (tensorProjection M N ≫ f.hom) :=
  curryUnbalancedLeft_hom f

omit [HasLimitsOfSize.{0, 0} C] in
/-- The original curry is recovered by the entire original right evaluation word. -/
theorem curryUnbalanced_evaluation {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) :
    ((curryUnbalanced f).hom ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X =
      tensorProjection M N ≫ f.hom := by
  let a := originalRightTensorAdjunction N.X
  have h := (a.homEquiv M.X P.X).symm_apply_apply (tensorProjection M N ≫ f.hom)
  rw [a.homEquiv_counit] at h
  rw [curryUnbalanced_hom]
  exact h

omit [HasLimitsOfSize.{0, 0} C] in
/-- Original right scalar linearity of the tensor map proves the complete curry equalizer condition. -/
theorem curryUnbalanced_equalizes {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) :
    curryUnbalanced f ≫ rightLinearityPre N P = curryUnbalanced f ≫ rightLinearityPost N P := by
  apply Bimod.hom_ext
  change (curryUnbalanced f).hom ≫ (rightLinearityPre N P).hom =
    (curryUnbalanced f).hom ≫ (rightLinearityPost N P).hom
  apply (rightLinearity_underlying_iff N P _).mpr
  rw [curryUnbalanced_evaluation, tensorProjection_rightLinear_assoc, f.right_act_hom,
    ← comp_whiskerRight_assoc]

/-- The actual bimodule curry is the original equalizer lift of the original right adjunct. -/
def curry {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) : M ⟶ homObject N P :=
  lift N P (curryUnbalanced f) (curryUnbalanced_equalizes f)

/-- The complete curry square retains the original unbalanced adjunct and equalizer inclusion. -/
theorem curry_inclusion {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) : curry f ≫ inclusion N P = curryUnbalanced f := lift_inclusion _ _ _ _

/-- The entire relative curry retains the original tensor projection/evaluation equation. -/
theorem curry_evaluation {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) :
    ((curry f).hom ▷ N.X) ≫ underlyingEvaluation N P = tensorProjection M N ≫ f.hom := by
  have h := congrArg Bimod.Hom.hom (curry_inclusion f)
  change (curry f).hom ≫ (inclusion N P).hom = (curryUnbalanced f).hom at h
  rw [underlyingEvaluation, ← Category.assoc, ← comp_whiskerRight, h]
  exact curryUnbalanced_evaluation f

/-- The original uncurry composes the actual tensor map with the actual relative evaluator. -/
def uncurry {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (g : M ⟶ homObject N P) : tensorBimod M N ⟶ P := whiskerRight g N ≫ evaluation N P

/-- The entire relative uncurry retains the original pairing on the actual tensor projection. -/
@[reassoc] theorem tensorProjection_uncurry {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (g : M ⟶ homObject N P) :
    tensorProjection M N ≫ (uncurry g).hom = (g.hom ▷ N.X) ≫ underlyingEvaluation N P := by
  rw [uncurry, Bimod.comp_hom', ← Category.assoc, tensorProjection_whiskerRight,
    Category.assoc, tensorProjection_evaluation]

/-- Uncurrying the original curry recovers every original balanced tensor map. -/
theorem uncurry_curry {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (f : tensorBimod M N ⟶ P) : uncurry (curry f) = f := by
  apply tensor_hom_ext M N
  rw [tensorProjection_uncurry, curry_evaluation]

/-- Currying the original uncurry recovers every original relative Hom map. -/
theorem curry_uncurry {M : Bimod A B} {N : Bimod B D} {P : Bimod A D}
    (g : M ⟶ homObject N P) : curry (uncurry g) = g := by
  apply hom_ext N P
  apply Bimod.hom_ext
  apply ((originalRightTensorAdjunction N.X).homEquiv M.X P.X).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change (((curry (uncurry g)).hom ≫ (inclusion N P).hom) ▷ N.X) ≫
      (originalRightTensorAdjunction N.X).counit.app P.X =
    ((g.hom ≫ (inclusion N P).hom) ▷ N.X) ≫ (originalRightTensorAdjunction N.X).counit.app P.X
  simp only [comp_whiskerRight, Category.assoc]
  change ((curry (uncurry g)).hom ▷ N.X) ≫ underlyingEvaluation N P =
    (g.hom ▷ N.X) ≫ underlyingEvaluation N P
  rw [curry_evaluation, tensorProjection_uncurry]

/-- The full original bimodule Hom equivalence has the two proved original inverse functions. -/
def tensorHomEquiv (M : Bimod A B) (N : Bimod B D) (P : Bimod A D) :
    (tensorBimod M N ⟶ P) ≃ (M ⟶ homObject N P) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- The complete original tensor functor is left adjoint to the actual relative mapping bimodule functor. -/
def tensorHomAdjunction (N : Bimod B D) : tensorRightFunctor (A := A) N ⊣ homFunctor N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M P => tensorHomEquiv M N P
      homEquiv_naturality_left_symm := by
        intro M' M P f g
        change uncurry (N := N) (P := P) (f ≫ g) = whiskerRight f N ≫ uncurry (N := N) (P := P) g
        apply tensor_hom_ext M' N
        rw [tensorProjection_uncurry]
        change ((f.hom ≫ g.hom) ▷ N.X) ≫ underlyingEvaluation N P =
          tensorProjection M' N ≫ (whiskerRight f N ≫ uncurry g).hom
        rw [Bimod.comp_hom', ← Category.assoc, tensorProjection_whiskerRight,
          Category.assoc, tensorProjection_uncurry, comp_whiskerRight, Category.assoc]
      homEquiv_naturality_right := by
        intro M P P' f g
        let f₀ : tensorBimod M N ⟶ P := f
        change curry (f₀ ≫ g) = curry f₀ ≫ homMap N g
        apply hom_ext N P'
        rw [curry_inclusion, Category.assoc, homMap_inclusion, ← Category.assoc, curry_inclusion]
        apply Bimod.hom_ext
        simp only [Bimod.comp_hom', curryUnbalanced_hom, unbalancedPost_hom]
        change (originalRightTensorAdjunction N.X).homEquiv M.X P'.X
          (tensorProjection M N ≫ f₀.hom ≫ g.hom) =
          (originalRightTensorAdjunction N.X).homEquiv M.X P.X (tensorProjection M N ≫ f₀.hom) ≫
            (ihom N.X).map g.hom
        rw [← Category.assoc]
        exact (originalRightTensorAdjunction N.X).homEquiv_naturality_right _ g.hom }

end Bimod.InternalHom
