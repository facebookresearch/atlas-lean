/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.StabilizationAction
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftCotensorAction

/-!
# Symmetric shifts preserve the Omega condition

Computes the stabilization adjoints of a shifted symmetric spectrum using the
block-exchange isomorphism and its associators. The formula proves preservation of the
Omega condition for every source and added-degree pair.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace NativeOmegaRecovery.NativeSymmetricShiftOmega

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- The actual final two index blocks are exchanged with all original associators. -/
def blockSwap (r n a : Operad.SmallFinBijGroupoid) : ((n ⊗ r) ⊗ a) ≅ ((n ⊗ a) ⊗ r) :=
  (α_ n r a) ≪≫ whiskerLeftIso n (β_ r a) ≪≫ (α_ n a r).symm

/-- The original source-to-target block exchange is retained with every inverse associator. -/
theorem blockSwap_inv (r n a : Operad.SmallFinBijGroupoid) :
    (blockSwap r n a).inv = (α_ n a r).hom ≫
      (n ◁ (β_ a r).hom) ≫ (α_ n r a).inv := by
  change (α_ n a r).hom ≫ (n ◁ (β_ r a).inv) ≫ (α_ n r a).inv = _
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding r a]

/-- The original complete shifted stabilization label is the original braid followed by the block
swap. -/
theorem blockSwap_label (r n a : Operad.SmallFinBijGroupoid) :
    PointedCGWH.SymmetricShift.label r n (n ⊗ a) a (β_ a n).hom =
      (β_ a (n ⊗ r)).hom ≫ (blockSwap r n a).hom := by
  change (α_ a n r).inv ≫ ((β_ a n).hom ▷ r) =
    (β_ a (n ⊗ r)).hom ≫ (α_ n r a).hom ≫
      (n ◁ (β_ r a).hom) ≫ (α_ n a r).inv
  rw [braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id, Category.comp_id]

/-- The unchanged native transpose from the actual full symmetric stabilization family. -/
abbrev omegaMap (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (n a : Operad.SmallFinBijGroupoid) :=
  CurrentFree.adjoint (PointedCGWH.symmetricOperatorObj.{u, v} n)
    (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ a)) (PointedCGWH.sphereSequence.{u, v}.functor.obj a)
    (Actual.symmetricNu.{u, v} n a) E

/-- Every source and added-degree pair retains its entire native action after the genuine shift. -/
theorem shift_adjoint (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (r n a : Operad.SmallFinBijGroupoid) :
    omegaMap ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E) n a =
      omegaMap E (n ⊗ r) a ≫ (ihom (PointedCGWH.sphereSequence.{u, v}.functor.obj a)).map
        (((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map
          (blockSwap r n a).hom) := by
  let E' := (PointedCGWH.SymmetricShift.functor.{u, v} r).obj E
  have h₀ := CurrentFree.action_operatorGenerator_eq_reconstructed E' a n (n ⊗ a) (β_ a n).hom
  have h₁ := NativeOmegaPreparation.NativeSymmetricShiftCotensorAction.shift_arrow
    E r a n (n ⊗ a) (β_ a n).hom
  have h₂ := congrArg (reconstructedArrowAction E a (n ⊗ r) ((n ⊗ a) ⊗ r))
    (blockSwap_label r n a)
  have h₃ := (CurrentFree.action_operatorGenerator_eq_reconstructed E a (n ⊗ r)
    ((n ⊗ a) ⊗ r) ((β_ a (n ⊗ r)).hom ≫ (blockSwap r n a).hom)).symm
  have hAction := h₀.trans (h₁.trans (h₂.trans h₃))
  have hCurry := congrArg MonoidalClosed.curry hAction
  have hTarget := CurrentFree.adjoint_operatorGenerator_target E a (n ⊗ r)
    ((n ⊗ r) ⊗ a) ((n ⊗ a) ⊗ r) (β_ a (n ⊗ r)).hom (blockSwap r n a).hom
  exact hCurry.trans hTarget.symm

/-- The genuine full enriched shift preserves the original all-pair Omega condition. -/
theorem shift_isOmega (E : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) (hE : Actual.SymmetricIsOmega E) (r : Operad.SmallFinBijGroupoid) :
    Actual.SymmetricIsOmega ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E) := by
  intro label
  rcases label with ⟨n, a⟩
  let F := ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor
  let p := (ihom (S.{u, v}.functor.obj a)).map (F.map (blockSwap r n a).hom)
  let e := (ihom (S.{u, v}.functor.obj a)).mapIso (F.mapIso (blockSwap r n a))
  have : IsIso p := by change IsIso e.hom; infer_instance
  have hp : weakEquivalences V.{u, v} p := (weakEquivalences V.{u, v}).of_isIso p
  have hOriginal : weakEquivalences V.{u, v} (omegaMap E (n ⊗ r) a) := hE (n ⊗ r, a)
  have hComp := (weakEquivalences V.{u, v}).comp_mem (omegaMap E (n ⊗ r) a) p hOriginal hp
  change weakEquivalences V.{u, v}
    (omegaMap ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E) n a)
  rw [shift_adjoint]
  exact hComp

end NativeOmegaRecovery.NativeSymmetricShiftOmega
