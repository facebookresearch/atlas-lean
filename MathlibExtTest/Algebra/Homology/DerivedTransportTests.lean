/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.ChainComplex.NativeShift
import MathlibExt.Algebra.Homology.HomologicalComplex.SplitHomology
import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingFunctorTransport
import MathlibExt.Algebra.Category.ModuleCat.RelativeResolutionTensorHomology
import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Tests for shifts, split complexes and relative transport

Odd chain shifts negate the differential and move its source indices. A
nonzero square-zero differential on a one-object loop gives concrete
splitting data whose normalization is square-zero. Tensor and relative
lifting tests use the native category of integer modules.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

namespace MathlibExtTest.Algebra.Homology.DerivedTransport

abbrev V := ModuleCat.of ℤ (ℤ × ℤ)
abbrev Z := ModuleCat.of ℤ ℤ

/-- The square-zero map `(x,y) ↦ (y,0)`. -/
def d : V ⟶ V := ModuleCat.ofHom
  ((LinearMap.inl ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ ℤ))

/-- Its generalized inverse `(x,y) ↦ (0,x)`. -/
def h : V ⟶ V := ModuleCat.ofHom
  ((LinearMap.inr ℤ ℤ ℤ).comp (LinearMap.fst ℤ ℤ ℤ))

/-- A loop complex with a nonzero differential. -/
def loop : HomologicalComplex (ModuleCat ℤ) (ComplexShape.refl Unit) where
  X _ := V
  d _ _ := d
  shape _ _ hn := False.elim (hn (Subsingleton.elim _ _))
  d_comp_d' _ _ _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, y⟩
    rfl

/-- Explicit inverse components for the loop differential. -/
def loopSplit : Splitting loop where
  hom _ _ := h
  zero _ _ hn := False.elim (hn (Subsingleton.elim _ _))
  d_h_d _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x, y⟩
    rfl

/-- The example differential is nonzero. -/
example : d.hom (0, 1) = (1, 0) := rfl

/-- Normalization satisfies the generalized-inverse relation on nonzero data. -/
example : loopSplit.normalize.hom () () ≫ d ≫ loopSplit.normalize.hom () () =
    loopSplit.normalize.hom () () :=
  loopSplit.normalize_h_d_h () ()

/-- Consecutive normalized components vanish even on a loop shape. -/
example : loopSplit.normalize.hom () () ≫ loopSplit.normalize.hom () () = 0 :=
  loopSplit.normalize_hom_comp_hom () () ()

/-- The homology comparison retains its negative normalized inverse homotopy. -/
example : loopSplit.homotopyEquivHomology.homotopyHomInvId.hom () () =
    -loopSplit.normalize.hom () () :=
  loopSplit.homotopyEquivHomology_homotopyHomInvId_hom () ()

/-- Additive transport of this splitting commutes with normalization. -/
example : (loopSplit.map (𝟭 (ModuleCat ℤ))).normalize =
    loopSplit.normalize.map (𝟭 (ModuleCat ℤ)) :=
  loopSplit.map_normalize (𝟭 (ModuleCat ℤ))

section IntegerShift

variable (K : ChainComplex (ModuleCat ℤ) ℤ)

/-- An odd negative shift has the negative differential in degrees three and two. -/
example : ((ChainComplex.nativeShift (ModuleCat ℤ) (-1)).obj K).d 2 1 = -K.d 3 2 := by
  simp [ChainComplex.nativeShift_obj_d]

/-- Morphism transport changes the index without adding a scalar sign. -/
example (f : K ⟶ K) :
    ((ChainComplex.nativeShift (ModuleCat ℤ) (-1)).map f).f 2 = f.f 3 := by
  simp [ChainComplex.nativeShift_map_f]

/-- Native shift additivity is synthesized for the module category. -/
example : (ChainComplex.nativeShift (ModuleCat ℤ) 1).Additive := inferInstance

end IntegerShift

/-- Tensor transport is additive for a nonzero fixed coefficient module. -/
example : (ModuleCat.relativeTensorFunctor (R := ℤ) V).Additive := inferInstance

/-- Identity is relatively projective on the nonzero module, without absolute projectivity assumptions. -/
example : (𝟭 (ModuleCat ℤ)).IsRelativeProjective V :=
  (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).isRelativeProjective_obj V

/-- The first projection is split by its canonical inclusion. -/
def firstSplit : SplitEpi ((𝟭 (ModuleCat ℤ)).map
    (ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ) : V ⟶ Z)) where
  section_ := ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ)
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The adjoint lift factors a nonzero scalar map through the split projection. -/
example :
    (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).liftOfSplitEpi
        (ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ)) firstSplit
        (ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) : Z ⟶ Z) ≫
      ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ) =
        (ModuleCat.ofHom ((2 : ℤ) • LinearMap.id) : Z ⟶ Z) :=
  (Adjunction.id : (𝟭 (ModuleCat ℤ)) ⊣ 𝟭 (ModuleCat ℤ)).liftOfSplitEpi_comp _ _ _

end MathlibExtTest.Algebra.Homology.DerivedTransport
