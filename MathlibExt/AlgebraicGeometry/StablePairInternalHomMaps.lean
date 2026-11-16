/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BundleTrace

/-!
# Actual precomposition and postcomposition on sheaf internal Hom

The maps act on the literal morphisms of modules on each localized
slice site. Their scalar action is the native restricted-function
action of ModuleInternalHom. They supply the source differentials of
the perfect-complex endomorphism and trace-free complexes.

Reference: Stacks Project, Tag 04TT; Pandharipande–Thomas,
arXiv:0707.2348v5, §2.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairInternalHomMaps

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open ModuleInternalHom BundleTrace

variable {X : Scheme} {E E' F F' : X.Modules}

/-- The literal precomposition on localized module morphisms. -/
def precompose (f : E' ⟶ E) : homSheaf X E F ⟶ homSheaf X E' F where
  val.app U := by
    let _ := homModule X.presheaf E.val F.val U.unop
    let _ := homModule X.presheaf E'.val F.val U.unop
    exact ModuleCat.ofHom
      (X := internalHomObj X.presheaf E.val F.val U.unop)
      (Y := internalHomObj X.presheaf E'.val F.val U.unop)
      { toFun := fun a => (restrFun X.presheaf U.unop).map f.val ≫ a
        map_add' := by
          intro a b
          change (restrFun X.presheaf U.unop).map f.val ≫ (a + b) =
            ((restrFun X.presheaf U.unop).map f.val ≫ a) +
              ((restrFun X.presheaf U.unop).map f.val ≫ b)
          rw [Preadditive.comp_add]
        map_smul' := by
          intro c a
          change (restrFun X.presheaf U.unop).map f.val ≫
              (a ≫ multEndoHom X.presheaf F.val U.unop c) =
            ((restrFun X.presheaf U.unop).map f.val ≫ a) ≫
              multEndoHom X.presheaf F.val U.unop c
          exact (Category.assoc _ _ _).symm }
  val.naturality {U V} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    rfl

/-- The literal postcomposition on the same localized module morphisms. -/
def postcompose (f : F ⟶ F') : homSheaf X E F ⟶ homSheaf X E F' where
  val.app U := by
    let _ := homModule X.presheaf E.val F.val U.unop
    let _ := homModule X.presheaf E.val F'.val U.unop
    exact ModuleCat.ofHom
      (X := internalHomObj X.presheaf E.val F.val U.unop)
      (Y := internalHomObj X.presheaf E.val F'.val U.unop)
      { toFun := fun a => a ≫ (restrFun X.presheaf U.unop).map f.val
        map_add' := by
          intro a b
          change (a + b) ≫ (restrFun X.presheaf U.unop).map f.val =
            (a ≫ (restrFun X.presheaf U.unop).map f.val) +
              (b ≫ (restrFun X.presheaf U.unop).map f.val)
          rw [Preadditive.add_comp]
        map_smul' := by
          intro c a
          apply PresheafOfModules.hom_ext
          intro V
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change ((restrFun X.presheaf U.unop).map f.val).app V
              ((fRestr X.presheaf U.unop c V) • a.app V x) =
            (fRestr X.presheaf U.unop c V) •
              (((restrFun X.presheaf U.unop).map f.val).app V (a.app V x))
          exact map_smul _ _ _ }
  val.naturality {U V} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    rfl

end MathlibExt.AlgebraicGeometry.StablePairInternalHomMaps
