/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedDerivedMapping

/-!
# Original relative mapping lifts at arbitrary endpoints

A weak relative cofibrant comparison transfers a lifting problem back to the
original cofibration. The construction uses its actual pushout, the original
weak comparison, and the two original model factorizations and lifting laws.
The original source and target are not required to be cofibrant.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.OriginalRelativeMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLeftProper C]

/-- The descent from the actual relative pushout is weak by left properness
and the original factor equation. -/
theorem weak_descent_of_isPushout
    {Q A M B P : C} (q : Q ⟶ A) (j : Q ⟶ M) (r : M ⟶ B) (i : A ⟶ B)
    (fac : j ≫ r = q ≫ i) {s : M ⟶ P} {k : A ⟶ P}
    (sq : IsPushout j q s k) [Cofibration j] [WeakEquivalence q]
    [WeakEquivalence r] :
    WeakEquivalence (sq.desc r i fac) := by
  let _ : WeakEquivalence s := IsLeftProper.weakEquivalence_of_isPushout sq
  have hfac : s ≫ sq.desc r i fac = r := sq.inl_desc r i fac
  exact weakEquivalence_of_precomp_of_fac hfac

/-- Every original fibration lift for the relative comparison gives a lift
for the supplied original cofibration. The actual endpoint pushout is retained.
No fibrancy or cofibrancy condition is imposed on its four original endpoints. -/
theorem hasLiftingProperty_of_relative_isPushout
    {Q A M B P X Y : C} (q : Q ⟶ A) (j : Q ⟶ M) (r : M ⟶ B) (i : A ⟶ B)
    (fac : j ≫ r = q ≫ i) {s : M ⟶ P} {k : A ⟶ P}
    (sq : IsPushout j q s k) (p : X ⟶ Y)
    [Cofibration j] [WeakEquivalence q] [WeakEquivalence r]
    [Cofibration i] [Fibration p] [HasLiftingProperty j p] :
    HasLiftingProperty i p := by
  let h : P ⟶ B := sq.desc r i fac
  let _ : WeakEquivalence h := weak_descent_of_isPushout q j r i fac sq
  let d := factorizationData (trivialCofibrations C) (fibrations C) h
  let _ : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
  let _ : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  let _ : Fibration d.p := (fibration_iff _).mpr d.hp
  let _ : WeakEquivalence d.p := weakEquivalence_of_precomp_of_fac d.fac
  let _ : HasLiftingProperty i d.p := inferInstance
  let _ : HasLiftingProperty d.i p := inferInstance
  constructor
  intro a b outer
  let relative : CommSq (q ≫ a) j p (r ≫ b) :=
    ⟨by
      calc
        (q ≫ a) ≫ p = q ≫ (a ≫ p) := Category.assoc _ _ _
        _ = q ≫ (i ≫ b) := congrArg (fun t => q ≫ t) outer.w
        _ = (q ≫ i) ≫ b := (Category.assoc _ _ _).symm
        _ = (j ≫ r) ≫ b := congrArg (fun t => t ≫ b) fac.symm
        _ = j ≫ (r ≫ b) := Category.assoc _ _ _⟩
  let z : P ⟶ X := sq.desc relative.lift a relative.fac_left
  have hz : z ≫ p = h ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.inl_desc, relative.fac_right]
      rw [← Category.assoc, sq.inl_desc]
    · rw [← Category.assoc, sq.inr_desc, outer.w]
      rw [← Category.assoc, sq.inr_desc]
  let extension : CommSq z d.i p (d.p ≫ b) :=
    ⟨by rw [← Category.assoc, d.fac]; exact hz⟩
  let liftSection : CommSq (k ≫ d.i) i d.p (𝟙 B) :=
    ⟨by rw [Category.assoc, d.fac, sq.inr_desc, Category.comp_id]⟩
  exact CommSq.HasLift.mk'
    { l := liftSection.lift ≫ extension.lift
      fac_left := by
        rw [← Category.assoc, liftSection.fac_left, Category.assoc,
          extension.fac_left, sq.inr_desc]
      fac_right := by
        rw [Category.assoc, extension.fac_right, ← Category.assoc,
          liftSection.fac_right, Category.id_comp] }

/-- The same relative lifting statement may use the canonical actual pushout. -/
theorem hasLiftingProperty_of_relative_factor
    {Q A M B X Y : C} (q : Q ⟶ A) (j : Q ⟶ M) (r : M ⟶ B) (i : A ⟶ B)
    (fac : j ≫ r = q ≫ i) (p : X ⟶ Y)
    [Cofibration j] [WeakEquivalence q] [WeakEquivalence r]
    [Cofibration i] [Fibration p] [HasLiftingProperty j p] :
    HasLiftingProperty i p :=
  hasLiftingProperty_of_relative_isPushout q j r i fac
    (IsPushout.of_hasPushout j q) p

end HomotopicalAlgebra.OriginalRelativeMapping
