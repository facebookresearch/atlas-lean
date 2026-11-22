/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorParametrized
public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Forgetting the actual relative tensor-Hom pullback

The left-module forgetful functor creates limits. Applying it to the full
Leibniz-Hom square therefore gives a genuine base internal-Hom pullback,
with the original coefficient pre-map and both original target maps. The
comparison is an isomorphism of whole Arrows, including the canonical map
into the pullback. The scalar actions and relative adjunction are unchanged.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj MonoidalCategory

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {A : C} [MonObj A] [HasPullbacks C]

/-- The forgetful functor creates the small limits used by the relative tensor-Hom pullback. -/
local instance forgetCreatesLimits : CreatesLimitsOfSize.{0, 0} (Mod.forget (D := C) A) :=
  Mod.forgetCreatesLimits.{0} A

local instance : HasPullbacks (Mod C A) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Mod.forget (D := C) A)

/-- The complete forgotten module square is a base internal-Hom pullback with the same maps. -/
def forgottenPullbackPacket {N N' : RightModuleFree.Carrier A} (f : N ⟶ N')
    {X Y : C} (p : X ⟶ Y)
    (R : (homContravariant (A := A)).PullbackObjObj f p) :
    MonoidalClosed.internalHom.PullbackObjObj f.hom p where
  pt := R.pt.X
  fst := R.fst.hom
  snd := R.snd.hom
  isPullback := (Mod.forget (D := C) A).map_isPullback R.isPullback
  π := R.π.hom
  π_fst := by
    have h := congrArg (fun q => q.hom) R.π_fst
    exact h
  π_snd := by
    have h := congrArg (fun q => q.hom) R.π_snd
    exact h

/-- Every actual relative pullback packet forgets to the base pullback-Hom Arrow. -/
def forgetPullbackPacketIso {N N' : RightModuleFree.Carrier A} (f : N ⟶ N')
    {X Y : C} (p : X ⟶ Y)
    (R : (homContravariant (A := A)).PullbackObjObj f p) :
    Arrow.mk R.π.hom ≅ ((op (Arrow.mk f.hom)) ⋔ Arrow.mk p) := by
  let S := forgottenPullbackPacket f p R
  let T := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom f.hom p
  let e : S.pt ≅ T.pt := S.isPullback.isoIsPullback _ _ T.isPullback
  have hfst : e.hom ≫ T.fst = S.fst :=
    S.isPullback.isoIsPullback_hom_fst _ _ T.isPullback
  have hsnd : e.hom ≫ T.snd = S.snd :=
    S.isPullback.isoIsPullback_hom_snd _ _ T.isPullback
  have hπ : S.π ≫ e.hom = T.π := by
    apply T.isPullback.hom_ext
    · rw [Category.assoc, hfst, S.π_fst, T.π_fst]
    · rw [Category.assoc, hsnd, S.π_snd, T.π_snd]
  exact Arrow.isoMk (Iso.refl _) e (by
    simp only [Iso.refl_hom, Category.id_comp, Arrow.mk_hom, MonoidalCategory.Arrow.pullbackHom]
    exact hπ.symm)

/-- The full original canonical Leibniz-Hom Arrow has the same whole-Arrow comparison. -/
def forgetPullbackHomIso (f : Arrow (RightModuleFree.Carrier A)) (p : Arrow C) :
    Arrow.mk ((Mod.forget (D := C) A).map
      ((((homContravariant (A := A)).leibnizPullback.obj (op f)).obj p).hom)) ≅
        ((op (Arrow.mk f.hom.hom)) ⋔ p) :=
  forgetPullbackPacketIso f.hom p.hom
    (Functor.PullbackObjObj.ofHasPullback (homContravariant (A := A)) f.hom p.hom)

end CategoryTheory.Mod.RightLeftTensor
