/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith

/-!
# Model-category recognition from two generating families

This file packages the elementary two-family form of model-category
recognition. Given small-object arguments for generating cofibrations `I` and
generating trivial cofibrations `J`, it derives the two weak factorization
systems and their compatibility with a candidate weak-equivalence class.

The resulting data can be transported to caller-selected cofibration,
fibration, and weak-equivalence classes to construct a `ModelCategory`. No
model-category instance, accessibility hypothesis, or specialized spectra
structure is introduced here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.SmithModelStructureData

variable {C : Type u} [Category.{v} C]

/-- Construct Smith model-structure data from two explicit generating
families. The cofibration inclusion for the `J`-left class is derived from
the trivial-fibration equality by antitonicity of left orthogonals. -/
noncomputable def ofGenerators
    (I J W : MorphismProperty C)
    [I.HasSmallObjectArgument.{w}]
    [J.HasSmallObjectArgument.{w}]
    (weak_two_out_of_three : W.HasTwoOutOfThreeProperty)
    (trivialFibrations_eq : I.rlp = J.rlp ⊓ W)
    (trivialCofibrations_weak : J.rlp.llp ≤ W) :
    SmithModelStructureData.{w} (C := C) I W := by
  let _ : W.HasTwoOutOfThreeProperty := weak_two_out_of_three
  have hRight : I.rlp ≤ J.rlp :=
    trivialFibrations_eq.le.trans inf_le_left
  have hCofDerived : J.rlp.llp ≤ I.rlp.llp :=
    MorphismProperty.antitone_llp hRight
  have hForward : J.rlp.llp ≤ I.rlp.llp ⊓ W :=
    le_inf hCofDerived trivialCofibrations_weak
  have hReverse : I.rlp.llp ⊓ W ≤ J.rlp.llp := by
    intro X Y f hf
    let d := factorizationData J.rlp.llp J.rlp f
    have hdiW : W d.i := trivialCofibrations_weak _ d.hi
    have hcomp : W (d.i ≫ d.p) := by
      rw [d.fac]
      exact hf.2
    have hdpW : W d.p := W.of_precomp _ _ hdiW hcomp
    have hdpI : I.rlp d.p := by
      rw [trivialFibrations_eq]
      exact ⟨d.hp, hdpW⟩
    let _ : HasLiftingProperty f d.p := hf.1 _ hdpI
    exact J.rlp.llp.of_retract
      (RetractArrow.ofLeftLiftingProperty d.fac) d.hi
  have hLeft : J.rlp.llp = I.rlp.llp ⊓ W :=
    le_antisymm hForward hReverse
  have hFibrations : J.rlp = (I.rlp.llp ⊓ W).rlp := by
    calc
      J.rlp = J.rlp.llp.rlp := J.rlp_llp_rlp.symm
      _ = (I.rlp.llp ⊓ W).rlp :=
        congrArg MorphismProperty.rlp hLeft
  have hIWfs : MorphismProperty.IsWeakFactorizationSystem
      I.rlp.llp I.rlp :=
    MorphismProperty.IsWeakFactorizationSystem.mk' _ _
      (fun _ _ hi hp => hi _ hp)
  have hJWfs : MorphismProperty.IsWeakFactorizationSystem
      J.rlp.llp J.rlp :=
    MorphismProperty.IsWeakFactorizationSystem.mk' _ _
      (fun _ _ hi hp => hi _ hp)
  exact
    { J := J
      J_smallObject := inferInstance
      cofibration_wfs := hIWfs
      trivialCofibration_wfs := hJWfs
      trivialCofibrations_eq := hLeft
      fibrations_eq := hFibrations
      trivialFibrations_eq := trivialFibrations_eq.symm }

/-- Transport Smith data to caller-selected cofibration, fibration, and weak
equivalence classes and construct the corresponding model category. Weak
retract closure is derived by `ModelCategory.mk'`; it is not an input. -/
@[instance_reducible]
noncomputable def modelCategory
    {I W : MorphismProperty C}
    (d : SmithModelStructureData.{w} (C := C) I W)
    [CategoryWithCofibrations C]
    [CategoryWithFibrations C]
    [CategoryWithWeakEquivalences C]
    [HasFiniteLimits C]
    [HasFiniteColimits C]
    (weak_two_out_of_three : W.HasTwoOutOfThreeProperty)
    (cofibrations_eq : cofibrations C = I.rlp.llp)
    (fibrations_eq : fibrations C = d.J.rlp)
    (weakEquivalences_eq : weakEquivalences C = W) :
    ModelCategory C := by
  have hTC : trivialCofibrations C = d.J.rlp.llp := by
    change cofibrations C ⊓ weakEquivalences C = d.J.rlp.llp
    rw [cofibrations_eq, weakEquivalences_eq,
      ← d.trivialCofibrations_eq]
  have hTF : trivialFibrations C = I.rlp := by
    change fibrations C ⊓ weakEquivalences C = I.rlp
    rw [fibrations_eq, weakEquivalences_eq, d.trivialFibrations_eq]
  let _ : (weakEquivalences C).HasTwoOutOfThreeProperty := by
    rw [weakEquivalences_eq]
    exact weak_two_out_of_three
  let _ : MorphismProperty.IsWeakFactorizationSystem
      (cofibrations C) (trivialFibrations C) := by
    rw [cofibrations_eq, hTF]
    exact d.cofibration_wfs
  let _ : MorphismProperty.IsWeakFactorizationSystem
      (trivialCofibrations C) (fibrations C) := by
    rw [hTC, fibrations_eq]
    exact d.trivialCofibration_wfs
  exact ModelCategory.mk' C

end HomotopicalAlgebra.SmithModelStructureData
