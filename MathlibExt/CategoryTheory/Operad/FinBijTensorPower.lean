/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.SymmetricTensorPower
public import MathlibExt.CategoryTheory.Operad.FinBijSmallEquiv

/-!
# Tensor-power functor on the small finite-bijection groupoid

This file packages the generic symmetric tensor-power action as a functor from
the small finite-bijection groupoid and supplies named strong-monoidal and
braided structures. The generic action and block-coherence theorems live in
`CategoryTheory.MonoidalCategory.SymmetricTensorPower`.

No global instance, Day convolution, spectrum, or model-category structure is
introduced.
-/

@[expose] public section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped MonoidalCategory

namespace CategoryTheory.Operad.SmallFinBijGroupoid

open CategoryTheory.MonoidalCategory.SymmetricTensorPower

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [SymmetricCategory.{v} C]

/-- Tensor powers as a functor on the small finite-bijection groupoid. -/
noncomputable def tensorPowerFunctor (X : C) : SmallFinBijGroupoid ⥤ C := by
  exact
    { obj A := tensorPowObj X A.of.len
      map f := (permutationIso X (smallEquivOfHom f)).hom
      map_id A := by
        rw [smallEquivOfHom_id, permutationIso_refl]
        rfl
      map_comp f g := by
        rw [smallEquivOfHom_comp, permutationIso_trans]
        rfl }

/-- Object formula for the tensor-power functor. -/
@[simp]
theorem tensorPowerFunctor_obj (X : C) (A : SmallFinBijGroupoid) :
    (tensorPowerFunctor X).obj A = tensorPowObj X A.of.len :=
  rfl

/-- Map formula for the tensor-power functor. -/
theorem tensorPowerFunctor_map (X : C)
    {A B : SmallFinBijGroupoid} (f : A ⟶ B) :
    (tensorPowerFunctor X).map f =
      (permutationIso X
        ((Equiv.ulift.symm : Fin A.of.len ≃ ULift (Fin A.of.len)).trans
          ((FinBijGroupoid.equivOfHom
            (smallFinBijEquivalence.functor.map f)).trans
            (Equiv.ulift :
              ULift (Fin B.of.len) ≃ Fin B.of.len)))).hom :=
  rfl

/-- The single strong-monoidal core for symmetric tensor powers. -/
noncomputable def tensorPowerFunctorCoreMonoidal (X : C) :
    (tensorPowerFunctor X).CoreMonoidal := by
  let F := tensorPowerFunctor X
  let μ : ∀ A B : SmallFinBijGroupoid,
      F.obj A ⊗ F.obj B ≅ F.obj (A ⊗ B) :=
    fun A B => (tensorPowObj_add X A.of.len B.of.len).symm
  have permutationIso_finCongr {m n : ℕ} (h : m = n) :
      permutationIso X (finCongr h) =
        eqToIso (congrArg (tensorPowObj X) h) := by
    subst n
    simpa using permutationIso_refl X m
  let smallEquiv {A B : SmallFinBijGroupoid} (f : A ⟶ B) :
      Fin A.of.len ≃ Fin B.of.len :=
    (Equiv.ulift.symm : Fin A.of.len ≃ ULift (Fin A.of.len)).trans
      ((FinBijGroupoid.equivOfHom
        (smallFinBijEquivalence.functor.map f)).trans
          (Equiv.ulift : ULift (Fin B.of.len) ≃ Fin B.of.len))
  let split (p q : ℕ) :
      ULift.{0, 0} (Fin (p + q)) ≃
        ULift.{0, 0} (Fin p) ⊕ ULift.{0, 0} (Fin q) :=
    Equiv.ulift.trans
      (finSumFinEquiv.symm.trans
        (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))
  let unlift {p q : ℕ}
      (e : ULift.{0, 0} (Fin p) ≃ ULift.{0, 0} (Fin q)) :
      Fin p ≃ Fin q :=
    (Equiv.ulift.symm : Fin p ≃ ULift (Fin p)).trans
      (e.trans (Equiv.ulift : ULift (Fin q) ≃ Fin q))
  have unlift_block {p p' q q' : ℕ}
      (e : ULift.{0, 0} (Fin p) ≃ ULift.{0, 0} (Fin p'))
      (f : ULift.{0, 0} (Fin q) ≃ ULift.{0, 0} (Fin q')) :
      unlift ((split p q).trans
        ((Equiv.sumCongr e f).trans (split p' q').symm)) =
        finSumFinEquiv.symm.trans
          ((Equiv.sumCongr (unlift e) (unlift f)).trans
            finSumFinEquiv) := by
    apply Equiv.ext
    intro i
    rcases hq : finSumFinEquiv.symm i with a | b
    · have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      subst i
      apply Fin.ext
      dsimp only [unlift, split, Equiv.trans_apply]
      simp only [finSumFinEquiv_symm_apply_castAdd,
        Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
      simp
    · have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      subst i
      apply Fin.ext
      dsimp only [unlift, split, Equiv.trans_apply]
      simp only [finSumFinEquiv_symm_apply_natAdd,
        Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
      simp
  have split_apply (p q : ℕ) (i : Fin (p + q)) :
      split p q (ULift.up i) =
        Sum.map ULift.up ULift.up (finSumFinEquiv.symm i) := by
    rfl
  have split_symm_apply (p q : ℕ) (z : Fin p ⊕ Fin q) :
      (split p q).symm (Sum.map ULift.up ULift.up z) =
        ULift.up (finSumFinEquiv z) := by
    rcases z with z | z <;> rfl
  have hTensor {A A' B B' : SmallFinBijGroupoid}
      (f : A ⟶ A') (g : B ⟶ B') :
      smallEquiv (f ⊗ₘ g) =
        (finCongr (blockSumObj_len A B)).trans
          ((finSumFinEquiv.symm.trans
            ((Equiv.sumCongr (smallEquiv f)
              (smallEquiv g)).trans finSumFinEquiv)).trans
            (finCongr (blockSumObj_len A' B').symm)) := by
    change unlift (FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map (blockSumHom f g))) = _
    rw [blockSumHom_equivOfHom]
    exact unlift_block _ _
  have hAssoc (A B D : SmallFinBijGroupoid) :
      smallEquiv ((α_ A B D).hom) =
        finCongr (Nat.add_assoc A.of.len B.of.len D.of.len) := by
    let assocE : ULift.{0, 0}
        (Fin ((A.of.len + B.of.len) + D.of.len)) ≃
        ULift.{0, 0} (Fin (A.of.len + (B.of.len + D.of.len))) :=
      (split (A.of.len + B.of.len) D.of.len).trans <|
        (Equiv.sumCongr (split A.of.len B.of.len) (Equiv.refl _)).trans <|
          (Equiv.sumAssoc _ _ _).trans <|
            (Equiv.sumCongr (Equiv.refl _)
              (split B.of.len D.of.len).symm).trans
              (split A.of.len (B.of.len + D.of.len)).symm
    have hAssocRaw :
        (show ULift.{0, 0}
            (Fin ((A.of.len + B.of.len) + D.of.len)) →
            ULift.{0, 0} (Fin (A.of.len + (B.of.len + D.of.len))) from
          (α_ A B D).hom.iso.hom) = assocE := rfl
    apply Equiv.ext
    intro i
    change Fin ((A.of.len + B.of.len) + D.of.len) at i
    apply Fin.ext
    dsimp only [smallEquiv, Equiv.trans_apply]
    change (((show ULift.{0, 0}
        (Fin ((A.of.len + B.of.len) + D.of.len)) →
          ULift.{0, 0} (Fin (A.of.len + (B.of.len + D.of.len))) from
        (α_ A B D).hom.iso.hom) (ULift.up i)).down).val = i.val
    rw [hAssocRaw]
    dsimp only [assocE, Equiv.trans_apply]
    rcases hq : finSumFinEquiv.symm i with ab | d
    · rcases hab : finSumFinEquiv.symm ab with a | b
      · rw [show split (A.of.len + B.of.len) D.of.len (ULift.up i) =
            Sum.inl (ULift.up ab) by rw [split_apply, hq]; rfl]
        simp only [Equiv.sumCongr_apply, Sum.map_inl]
        rw [show split A.of.len B.of.len (ULift.up ab) =
            Sum.inl (ULift.up a) by rw [split_apply, hab]; rfl]
        simp only [Sum.map_inl,
          Equiv.sumAssoc_apply_inl_inl, Equiv.refl_apply]
        rw [show (split A.of.len (B.of.len + D.of.len)).symm
            (Sum.inl (ULift.up a)) =
              ULift.up (Fin.castAdd (B.of.len + D.of.len) a) by
          simpa using split_symm_apply A.of.len (B.of.len + D.of.len)
            (Sum.inl a)]
        have hiOuter := finSumFinEquiv.apply_symm_apply i
        rw [hq] at hiOuter
        have hiInner := finSumFinEquiv.apply_symm_apply ab
        rw [hab] at hiInner
        have hOuter : ab.val = i.val := by
          simpa using congrArg Fin.val hiOuter
        have hInner : a.val = ab.val := by
          simpa using congrArg Fin.val hiInner
        exact hInner.trans hOuter
      · rw [show split (A.of.len + B.of.len) D.of.len (ULift.up i) =
            Sum.inl (ULift.up ab) by rw [split_apply, hq]; rfl]
        simp only [Equiv.sumCongr_apply, Sum.map_inl]
        rw [show split A.of.len B.of.len (ULift.up ab) =
            Sum.inr (ULift.up b) by rw [split_apply, hab]; rfl]
        simp only [Sum.map_inr, Equiv.sumAssoc_apply_inl_inr]
        rw [show (split B.of.len D.of.len).symm
            (Sum.inl (ULift.up b)) =
              ULift.up (finSumFinEquiv (Sum.inl b)) by
          simpa using split_symm_apply B.of.len D.of.len (Sum.inl b)]
        rw [show (split A.of.len (B.of.len + D.of.len)).symm
            (Sum.inr (ULift.up (finSumFinEquiv (Sum.inl b)))) =
              ULift.up (finSumFinEquiv
                (Sum.inr (finSumFinEquiv (Sum.inl b)))) by
          simpa using split_symm_apply A.of.len (B.of.len + D.of.len)
            (Sum.inr (finSumFinEquiv (Sum.inl b)))]
        have hiOuter := finSumFinEquiv.apply_symm_apply i
        rw [hq] at hiOuter
        have hiInner := finSumFinEquiv.apply_symm_apply ab
        rw [hab] at hiInner
        have hOuter : ab.val = i.val := by
          simpa using congrArg Fin.val hiOuter
        have hInner : A.of.len + b.val = ab.val := by
          simpa using congrArg Fin.val hiInner
        simpa using hInner.trans hOuter
    · rw [show split (A.of.len + B.of.len) D.of.len (ULift.up i) =
          Sum.inr (ULift.up d) by rw [split_apply, hq]; rfl]
      simp only [Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.sumAssoc_apply_inr, Equiv.refl_apply]
      rw [show (split B.of.len D.of.len).symm
          (Sum.inr (ULift.up d)) =
            ULift.up (finSumFinEquiv (Sum.inr d)) by
        simpa using split_symm_apply B.of.len D.of.len (Sum.inr d)]
      rw [show (split A.of.len (B.of.len + D.of.len)).symm
          (Sum.inr (ULift.up (finSumFinEquiv (Sum.inr d)))) =
            ULift.up (finSumFinEquiv
              (Sum.inr (finSumFinEquiv (Sum.inr d)))) by
        simpa using split_symm_apply A.of.len (B.of.len + D.of.len)
          (Sum.inr (finSumFinEquiv (Sum.inr d)))]
      have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      simpa [Nat.add_assoc] using congrArg Fin.val hi
  have hLeft (A : SmallFinBijGroupoid) :
      smallEquiv ((λ_ A).hom) =
        finCongr (Nat.zero_add A.of.len) := by
    let zeroObj : SmallFinBijGroupoid :=
      ⟨FintypeCat.Skeleton.mk 0⟩
    let hEmpty : IsEmpty (ULift.{0, 0} (Fin zeroObj.of.len)) := by
      change IsEmpty (ULift.{0, 0} (Fin 0))
      exact ⟨fun z => Fin.elim0 z.down⟩
    let _ : IsEmpty (ULift.{0, 0} (Fin zeroObj.of.len)) := hEmpty
    let leftE := (split 0 A.of.len).trans (Equiv.emptySum _ _)
    have hLeftRaw :
        (show ULift.{0, 0} (Fin (0 + A.of.len)) →
            ULift.{0, 0} (Fin A.of.len) from
          (λ_ A).hom.iso.hom) = leftE := rfl
    apply Equiv.ext
    intro i
    change Fin (0 + A.of.len) at i
    apply Fin.ext
    dsimp only [smallEquiv, Equiv.trans_apply]
    change (((show ULift.{0, 0} (Fin (0 + A.of.len)) →
        ULift.{0, 0} (Fin A.of.len) from
        (λ_ A).hom.iso.hom) (ULift.up i)).down).val = i.val
    rw [hLeftRaw]
    dsimp only [leftE, Equiv.trans_apply]
    rcases hq : finSumFinEquiv.symm i with z | a
    · exact Fin.elim0 z
    · rw [show split 0 A.of.len (ULift.up i) =
          Sum.inr (ULift.up a) by rw [split_apply, hq]; rfl]
      change a.val = i.val
      have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      simpa only [finSumFinEquiv_apply_right, Fin.val_natAdd,
        Nat.zero_add] using congrArg Fin.val hi
  have hRight (A : SmallFinBijGroupoid) :
      smallEquiv ((ρ_ A).hom) =
        finCongr (Nat.add_zero A.of.len) := by
    let zeroObj : SmallFinBijGroupoid :=
      ⟨FintypeCat.Skeleton.mk 0⟩
    let hEmpty : IsEmpty (ULift.{0, 0} (Fin zeroObj.of.len)) := by
      change IsEmpty (ULift.{0, 0} (Fin 0))
      exact ⟨fun z => Fin.elim0 z.down⟩
    let _ : IsEmpty (ULift.{0, 0} (Fin zeroObj.of.len)) := hEmpty
    let rightE := (split A.of.len 0).trans (Equiv.sumEmpty _ _)
    have hRightRaw :
        (show ULift.{0, 0} (Fin (A.of.len + 0)) →
            ULift.{0, 0} (Fin A.of.len) from
          (ρ_ A).hom.iso.hom) = rightE := rfl
    apply Equiv.ext
    intro i
    change Fin (A.of.len + 0) at i
    apply Fin.ext
    dsimp only [smallEquiv, Equiv.trans_apply]
    change (((show ULift.{0, 0} (Fin (A.of.len + 0)) →
        ULift.{0, 0} (Fin A.of.len) from
        (ρ_ A).hom.iso.hom) (ULift.up i)).down).val = i.val
    rw [hRightRaw]
    dsimp only [rightE, Equiv.trans_apply]
    rcases hq : finSumFinEquiv.symm i with a | z
    · rw [show split A.of.len 0 (ULift.up i) =
          Sum.inl (ULift.up a) by rw [split_apply, hq]; rfl]
      change a.val = i.val
      have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      simpa only [finSumFinEquiv_apply_left, Fin.val_castAdd] using
        congrArg Fin.val hi
    · exact Fin.elim0 z
  have hTensorator {A A' B B' : SmallFinBijGroupoid}
      (f : A ⟶ A') (g : B ⟶ B') :
      ((tensorPowerFunctor X).map f ⊗ₘ
          (tensorPowerFunctor X).map g) ≫
          ((tensorPowObj_add X A'.of.len B'.of.len).symm).hom =
        ((tensorPowObj_add X A.of.len B.of.len).symm).hom ≫
          (tensorPowerFunctor X).map (f ⊗ₘ g) := by
    have hTensor₀ : smallEquiv (f ⊗ₘ g) =
        finSumFinEquiv.symm.trans
          ((Equiv.sumCongr (smallEquiv f)
            (smallEquiv g)).trans finSumFinEquiv) := by
      have hAB : finCongr (blockSumObj_len A B) = Equiv.refl _ := by
        apply Equiv.ext
        intro i
        rfl
      have hA'B' : finCongr (blockSumObj_len A' B').symm =
          Equiv.refl _ := by
        apply Equiv.ext
        intro i
        rfl
      rw [hTensor, hAB, hA'B']
      rfl
    have hf : (tensorPowerFunctor X).map f =
        (permutationIso X (smallEquiv f)).hom := rfl
    have hg : (tensorPowerFunctor X).map g =
        (permutationIso X (smallEquiv g)).hom := rfl
    have hfg : (tensorPowerFunctor X).map (f ⊗ₘ g) =
        (permutationIso X
          (finSumFinEquiv.symm.trans
            ((Equiv.sumCongr (smallEquiv f)
              (smallEquiv g)).trans finSumFinEquiv))).hom := by
      change (permutationIso X (smallEquiv (f ⊗ₘ g))).hom = _
      rw [hTensor₀]
      rfl
    simp only [tensorPowerFunctor_obj]
    rw [hf, hg, hfg]
    have h := congrArg Iso.hom
      (blockSumIso_natural X (smallEquiv f) (smallEquiv g))
    simp only [Iso.trans_hom, tensorIso_hom] at h
    exact h
  have invNatLeft :
      ∀ {A B} (f : A ⟶ B) (D : SmallFinBijGroupoid)
        (h : F.map f ▷ F.obj D ≫ (μ B D).hom =
          (μ A D).hom ≫ F.map (f ▷ D)),
        (μ A D).inv ≫ F.map f ▷ F.obj D =
          F.map (f ▷ D) ≫ (μ B D).inv := by
    intro A B f D h
    rw [← cancel_mono (μ B D).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    simp
  have invNatRight :
      ∀ (D : SmallFinBijGroupoid) {A B} (f : A ⟶ B)
        (h : F.obj D ◁ F.map f ≫ (μ D B).hom =
          (μ D A).hom ≫ F.map (D ◁ f)),
        (μ D A).inv ≫ F.obj D ◁ F.map f =
          F.map (D ◁ f) ≫ (μ D B).inv := by
    intro D A B f h
    rw [← cancel_mono (μ D B).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    simp
  have hSmallInv :
      ∀ {A B : SmallFinBijGroupoid} (e : A ≅ B),
        smallEquiv e.inv = (smallEquiv e.hom).symm := by
    intro A B e
    apply Equiv.ext
    intro i
    change ULift.down
        (FinBijGroupoid.equivOfHom
          (smallFinBijEquivalence.functor.map e.inv) (ULift.up i)) = _
    have h := FinBijGroupoid.equivOfHom_inv
      (smallFinBijEquivalence.functor.map e.hom)
    have hMap : smallFinBijEquivalence.functor.map e.inv =
        FinBijGroupoid.inverse
          (smallFinBijEquivalence.functor.map e.hom) := by
      apply (cancel_mono
        (smallFinBijEquivalence.functor.map e.hom)).1
      rw [← smallFinBijEquivalence.functor.map_comp]
      simp [FinBijGroupoid.inverse]
    rw [hMap, h]
    rfl
  refine Functor.CoreMonoidal.mk'
    (Iso.refl (𝟙_ C)) μ ?_ ?_ ?_ ?_ ?_
  · intro A B f D
    apply invNatLeft f D
    dsimp only [F, μ]
    have h := hTensorator f (𝟙 D)
    rw [Functor.map_id, tensorHom_id] at h
    exact h
  · intro A B D f
    apply invNatRight D f
    dsimp only [F, μ]
    have h := hTensorator (𝟙 D) f
    rw [Functor.map_id, id_tensorHom] at h
    exact h
  · intro A B D
    dsimp only [μ, F]
    simp only [tensorPowerFunctor_obj]
    have hMap : (tensorPowerFunctor X).map (α_ A B D).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_assoc A.of.len B.of.len D.of.len))).hom := by
      change (permutationIso X
        (smallEquiv (α_ A B D).hom)).hom = _
      rw [hAssoc]
      exact congrArg Iso.hom
        (permutationIso_finCongr
          (Nat.add_assoc A.of.len B.of.len D.of.len))
    rw [hMap]
    change (tensorPowObj_add X (A.of.len + B.of.len) D.of.len).hom ≫
          ((tensorPowObj_add X A.of.len B.of.len).hom ▷
            tensorPowObj X D.of.len) ≫
          (α_ (tensorPowObj X A.of.len)
            (tensorPowObj X B.of.len) (tensorPowObj X D.of.len)).hom =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_assoc A.of.len B.of.len D.of.len))).hom ≫
          (tensorPowObj_add X A.of.len (B.of.len + D.of.len)).hom ≫
          tensorPowObj X A.of.len ◁
            (tensorPowObj_add X B.of.len D.of.len).hom
    simpa only [tensorPowObj, tensorHom_id, id_tensorHom] using
      (tensorPowObj_add_assoc X A.of.len B.of.len D.of.len).symm
  · intro A
    dsimp only [μ, F]
    simp only [tensorPowerFunctor_obj]
    have hMap : (tensorPowerFunctor X).map (λ_ A).inv =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.zero_add A.of.len))).inv := by
      change (permutationIso X
        (smallEquiv (λ_ A).inv)).hom = _
      have hEq : smallEquiv (λ_ A).inv =
          (finCongr (Nat.zero_add A.of.len)).symm :=
        (hSmallInv (λ_ A)).trans (congrArg Equiv.symm (hLeft A))
      rw [hEq]
      calc
        (permutationIso X
            (finCongr (Nat.zero_add A.of.len)).symm).hom =
            (permutationIso X
              (finCongr (Nat.zero_add A.of.len))).inv := by
          rw [permutationIso_symm]
          rfl
        _ = _ := congrArg Iso.inv
          (permutationIso_finCongr (Nat.zero_add A.of.len))
    rw [hMap]
    change (λ_ (tensorPowObj X A.of.len)).inv =
      (eqToIso (congrArg (tensorPowObj X)
        (Nat.zero_add A.of.len))).inv ≫
        (tensorPowObj_add X 0 A.of.len).hom ≫ 𝟙 _ ▷ _
    simp only [tensorPowObj_zero,
      MonoidalCategory.id_whiskerRight, Category.comp_id]
    rw [← cancel_mono (λ_ (tensorPowObj X A.of.len)).hom]
    simp only [Category.assoc, Iso.inv_hom_id]
    change 𝟙 (tensorPowObj X A.of.len) =
      (eqToIso (congrArg (tensorPowObj X)
        (Nat.zero_add A.of.len))).inv ≫
        ((tensorPowObj_add X 0 A.of.len).hom ≫
          (λ_ (tensorPowObj X A.of.len)).hom)
    rw [tensorPowObj_add_zero_left]
    simp
  · intro A
    dsimp only [μ, F]
    simp only [tensorPowerFunctor_obj]
    have hMap : (tensorPowerFunctor X).map (ρ_ A).inv =
        (eqToIso (congrArg (tensorPowObj X)
          (Nat.add_zero A.of.len))).inv := by
      change (permutationIso X
        (smallEquiv (ρ_ A).inv)).hom = _
      have hEq : smallEquiv (ρ_ A).inv =
          (finCongr (Nat.add_zero A.of.len)).symm :=
        (hSmallInv (ρ_ A)).trans (congrArg Equiv.symm (hRight A))
      rw [hEq]
      calc
        (permutationIso X
            (finCongr (Nat.add_zero A.of.len)).symm).hom =
            (permutationIso X
              (finCongr (Nat.add_zero A.of.len))).inv := by
          rw [permutationIso_symm]
          rfl
        _ = _ := congrArg Iso.inv
          (permutationIso_finCongr (Nat.add_zero A.of.len))
    rw [hMap]
    change (ρ_ (tensorPowObj X A.of.len)).inv =
      (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_zero A.of.len))).inv ≫
        (tensorPowObj_add X A.of.len 0).hom ≫ _ ◁ 𝟙 _
    rw [whiskerLeft_id, Category.comp_id,
      tensorPowObj_add_zero_right]
    simp

/-- Tensor powers preserve the original finite block tensor through their chosen maps. -/
@[instance_reducible]
noncomputable def tensorPowerFunctorMonoidal (X : C) :
    (tensorPowerFunctor X).Monoidal :=
  (tensorPowerFunctorCoreMonoidal X).toMonoidal

/-- Tensor powers retain the original finite block braiding and value braiding. -/
@[instance_reducible]
noncomputable def tensorPowerFunctorBraided (X : C) :
    (tensorPowerFunctor X).Braided := by
  have hBraiding : ∀ A B : SmallFinBijGroupoid,
      smallEquivOfHom ((β_ A B).hom) =
        (finAddFlip : Fin (A.of.len + B.of.len) ≃
          Fin (B.of.len + A.of.len)) := by
    intro A B
    ext i
    have h := congrArg
      (fun e => (e (ULift.up i)).down.val)
      (braiding_equivOfHom A B)
    exact h
  let hM := tensorPowerFunctorMonoidal X
  letI : (tensorPowerFunctor X).Monoidal := hM
  refine { braided := ?_ }
  intro A B
  have hμ (P Q : SmallFinBijGroupoid) :
      Functor.LaxMonoidal.μ (tensorPowerFunctor X) P Q =
        ((tensorPowObj_add X P.of.len Q.of.len).symm).hom := rfl
  have hMap : (tensorPowerFunctor X).map (β_ A B).hom =
      (permutationIso X
        (finAddFlip : Fin (A.of.len + B.of.len) ≃
          Fin (B.of.len + A.of.len))).hom := by
    change (permutationIso X
      (smallEquivOfHom (β_ A B).hom)).hom = _
    rw [hBraiding]
    rfl
  rw [hμ, hμ, hMap]
  change ((tensorPowObj_add X A.of.len B.of.len).symm).hom ≫
      (permutationIso X finAddFlip).hom =
    (β_ (tensorPowObj X A.of.len) (tensorPowObj X B.of.len)).hom ≫
      ((tensorPowObj_add X B.of.len A.of.len).symm).hom
  simpa only [Iso.trans_hom] using
    congrArg Iso.hom (blockSwap X A.of.len B.of.len)

end CategoryTheory.Operad.SmallFinBijGroupoid
