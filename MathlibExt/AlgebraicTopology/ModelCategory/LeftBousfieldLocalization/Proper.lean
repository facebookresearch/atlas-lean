/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Properness of left Bousfield localizations

Over a left-proper base model category, local equivalences are stable under
cobase change along the unchanged cofibrations. Consequently the
family-keyed localized wrapper is left proper.

No right-properness statement is made: left Bousfield localization need not
preserve right properness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [SimplicialCategory C]
variable [HasFunctorialFactorization
  (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]
variable {I : Type w} {S : I → Arrow C}

/-- Over a left-proper base model category, local equivalences are stable
under cobase change along the unchanged cofibrations. -/
theorem localEquivalences_isStableUnderCobaseChangeAgainst
    (L : LeftBousfieldLocalizationData S) [IsLeftProper C] :
    (localEquivalences S).IsStableUnderCobaseChangeAgainst
      (cofibrations C) := by
  let _ : (localEquivalences S).HasTwoOutOfThreeProperty :=
    L.two_out_of_three
  let _ : IsWeakFactorizationSystem
      (cofibrations C ⊓ localEquivalences S) (localizedFibrations S) :=
    L.localized_wfs
  let _ : MorphismProperty.IsStableUnderCobaseChange
      (cofibrations C ⊓ localEquivalences S) := by
    rw [← llp_eq_of_wfs
      (cofibrations C ⊓ localEquivalences S) (localizedFibrations S)]
    infer_instance
  constructor
  intro A B i hi
  constructor
  intro X Y j f' f sq hf
  let d := factorizationData (cofibrations C) (trivialFibrations C) f
  have hpLocal : localEquivalences S d.p :=
    L.baseWeak_le d.p d.hp.2
  have hiLocal : localEquivalences S d.i := by
    apply (localEquivalences S).of_postcomp d.i d.p hpLocal
    rw [d.fac]
    exact hf
  have hb : (cofibrations C ⊓ localEquivalences S)
      (pushout.inl i d.i) :=
    (cofibrations C ⊓ localEquivalences S).pushout_inl i d.i
      ⟨d.hi, hiLocal⟩
  have hz : cofibrations C (pushout.inr i d.i) :=
    (cofibrations C).pushout_inr i d.i hi
  let q : pushout i d.i ⟶ Y :=
    pushout.desc f' (d.p ≫ j) (by
      rw [← Category.assoc, d.fac]
      exact sq.w)
  have hbq : pushout.inl i d.i ≫ q = f' := by
    dsimp only [q]
    rw [pushout.inl_desc]
  have hzq : pushout.inr i d.i ≫ q = d.p ≫ j := by
    dsimp only [q]
    rw [pushout.inr_desc]
  have sqOuter : IsPushout i (d.i ≫ d.p)
      (pushout.inl i d.i ≫ q) j := by
    rw [d.fac, hbq]
    exact sq
  have sq₂ : IsPushout (pushout.inr i d.i) d.p q j :=
    IsPushout.of_top sqOuter hzq (IsPushout.of_hasPushout i d.i)
  let _ : Cofibration (pushout.inr i d.i) :=
    (cofibration_iff _).mpr hz
  let _ : WeakEquivalence d.p :=
    (weakEquivalence_iff d.p).mpr d.hp.2
  have hqWeak : weakEquivalences C q :=
    (weakEquivalence_iff q).mp
      (IsLeftProper.weakEquivalence_of_isPushout sq₂)
  have hqLocal : localEquivalences S q :=
    L.baseWeak_le q hqWeak
  have hcomp : localEquivalences S
      (pushout.inl i d.i ≫ q) :=
    (localEquivalences S).comp_mem _ _ hb.2 hqLocal
  rw [hbq] at hcomp
  exact hcomp

namespace LeftLocalized

variable (L : LeftBousfieldLocalizationData S)

/-- A family-keyed left Bousfield localization of a left-proper model
category is left proper. -/
noncomputable instance instIsLeftProper [IsLeftProper C] :
    IsLeftProper (LeftLocalized L) where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    let _ : (toBase L).IsEquivalence := by
      simpa only [equivalence] using
        (inferInstance : (equivalence L).inverse.IsEquivalence)
    constructor
    intro A B i hi
    constructor
    intro X Y j f' f sq hf
    have sqBase : IsPushout
        ((toBase L).map i) ((toBase L).map f)
        ((toBase L).map f') ((toBase L).map j) :=
      sq.map (toBase L)
    change cofibrations C ((toBase L).map i) at hi
    change localEquivalences S ((toBase L).map f) at hf
    change localEquivalences S ((toBase L).map f')
    let h := localEquivalences_isStableUnderCobaseChangeAgainst L
    exact (h.isStableUnderCobaseChangeAlong
      ((toBase L).map i) hi).of_isPushout sqBase hf

end LeftLocalized

end HomotopicalAlgebra
