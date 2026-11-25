/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.GroupTheory.Generators
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtension
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementary
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization
import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatStabilizationBasicActions
import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatLeftWeylStabilization
import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatKernelEquality
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementaryStabilizationCompatibility

/-!
# Stabilization of the Matsumoto Bruhat extension

Upper-elementary, Weyl and central generators define the stabilization
homomorphism between the finite-rank left Bruhat extensions in ranks `n ≥ 2`.
The map descends from the generating family and is injective.
-/

@[expose] public section

universe u

open Matrix.GeneralLinearGroup
open MatsumotoTitsBruhatFiber
open MatsumotoBruhatFiber

namespace MatsumotoTitsBruhatFiber

variable (F : Type u) [Field F] (n : ℕ)

inductive LeftExtensionSuccGen (F : Type u) [Field F] (n : ℕ) : Type u where
  | upper : upperElementarySubgroup (Fin n) F → LeftExtensionSuccGen F n
  | weyl : (i j : Fin n) → (hij : i ⋖ j) → LeftExtensionSuccGen F n
  | central : Multiplicative (MilnorK F 2) → LeftExtensionSuccGen F n

section Succession

variable {F n}

-- Source assignment
noncomputable def LeftExtensionSuccGenSource (F : Type u) [Field F] (n : ℕ) :
    LeftExtensionSuccGen F n → leftExtensionSubgroup F n
  | .upper u => ⟨(UpperElementary.toSLHom u, leftUpperPerm (F := F) u),
      leftUpperPair_mem_leftExtensionSubgroup (F := F) (n := n) u⟩
  | .weyl i j hij => ⟨(weylSLUnit i j hij.ne (1 : Fˣ), leftWeylPerm (F := F) hij),
      leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n) hij⟩
  | .central c => ⟨((1 : Matrix.SpecialLinearGroup (Fin n) F), centralPerm (F := F) c),
      centralPair_mem_leftExtensionSubgroup (F := F) (n := n) c⟩

-- Target assignment
noncomputable def LeftExtensionSuccGenTarget (F : Type u) [Field F] (n : ℕ) :
    LeftExtensionSuccGen F n → leftExtensionSubgroup F (n + 1)
  | .upper u =>
      let u' := UpperElementary.stabilization F n u
      ⟨(UpperElementary.toSLHom u', leftUpperPerm (F := F) u'),
        leftUpperPair_mem_leftExtensionSubgroup (F := F) (n := n + 1) u'⟩
  | .weyl i j hij =>
      let hij' := Fin.castSucc_covBy hij
      ⟨(weylSLUnit (Fin.castSucc i) (Fin.castSucc j) hij'.ne (1 : Fˣ),
        leftWeylPerm (F := F) hij'),
        leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n + 1) hij'⟩
  | .central c =>
      ⟨((1 : Matrix.SpecialLinearGroup (Fin (n + 1)) F), centralPerm (F := F) c),
        centralPair_mem_leftExtensionSubgroup (F := F) (n := n + 1) c⟩

@[simp]
private theorem LeftExtensionSuccGenSource_upper (u : upperElementarySubgroup (Fin n) F) :
    (LeftExtensionSuccGenSource F n (LeftExtensionSuccGen.upper (F := F) u)).val =
      (UpperElementary.toSLHom u, leftUpperPerm (F := F) u) :=
  rfl

@[simp]
private theorem LeftExtensionSuccGenTarget_upper (u : upperElementarySubgroup (Fin n) F) :
    (LeftExtensionSuccGenTarget F n (LeftExtensionSuccGen.upper (F := F) u)).val =
      (UpperElementary.toSLHom (UpperElementary.stabilization F n u),
        leftUpperPerm (F := F) (UpperElementary.stabilization F n u)) :=
  rfl

@[simp]
private theorem LeftExtensionSuccGenSource_weyl {i j : Fin n} (hij : i ⋖ j) :
    (LeftExtensionSuccGenSource F n (LeftExtensionSuccGen.weyl (F := F) (n := n) i j hij)).val =
      (weylSLUnit i j hij.ne (1 : Fˣ), leftWeylPerm (F := F) hij) :=
  rfl

@[simp]
private theorem LeftExtensionSuccGenTarget_weyl {i j : Fin n} (hij : i ⋖ j) :
    (LeftExtensionSuccGenTarget F n (LeftExtensionSuccGen.weyl (F := F) (n := n) i j hij)).val =
      (weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
        (Fin.castSucc_covBy hij).ne (1 : Fˣ),
        leftWeylPerm (F := F) (Fin.castSucc_covBy hij)) :=
  rfl

@[simp]
private theorem LeftExtensionSuccGenSource_central (c : Multiplicative (MilnorK F 2)) :
    (LeftExtensionSuccGenSource F n (LeftExtensionSuccGen.central (F := F) (n := n) c)).val =
      ((1 : Matrix.SpecialLinearGroup (Fin n) F), centralPerm (F := F) c) :=
  rfl

@[simp]
private theorem LeftExtensionSuccGenTarget_central (c : Multiplicative (MilnorK F 2)) :
    (LeftExtensionSuccGenTarget F n (LeftExtensionSuccGen.central (F := F) (n := n) c)).val =
      ((1 : Matrix.SpecialLinearGroup (Fin (n + 1)) F), centralPerm (F := F) c) :=
  rfl

/-- The three families used for successor descent, packaged as an actual
generating family of the finite-rank left extension. -/
noncomputable def leftExtensionSuccGenerators (F : Type u) [Field F] (n : ℕ) :
    Group.Generators (leftExtensionSubgroup F n) (LeftExtensionSuccGen F n) := by
  let Q : Group.Generators (leftExtensionSubgroup F n)
      {p : leftExtensionSubgroup F n //
        p.val ∈ leftExtensionPairGenerators F n} :=
    Group.Generators.ofSet
      (Subgroup.closure_preimage_eq_top (leftExtensionPairGenerators F n))
  let e : LeftExtensionSuccGen F n →
      {p : leftExtensionSubgroup F n //
        p.val ∈ leftExtensionPairGenerators F n} := fun g =>
    ⟨LeftExtensionSuccGenSource F n g, by
      cases g with
      | upper u => exact Or.inl (Or.inl ⟨u, rfl⟩)
      | weyl i j hij => exact Or.inl (Or.inr ⟨i, j, hij, rfl⟩)
      | central c => exact Or.inr ⟨c, rfl⟩⟩
  have he : Function.Surjective e := by
    rintro ⟨p, hp⟩
    simp only [leftExtensionPairGenerators, Set.mem_union,
      Set.mem_ofPred_eq] at hp
    rcases hp with (⟨u, hu⟩ | ⟨i, j, hij, hw⟩) | ⟨c, hc⟩
    · refine ⟨LeftExtensionSuccGen.upper u, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hu.symm
    · refine ⟨LeftExtensionSuccGen.weyl i j hij, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hw.symm
    · refine ⟨LeftExtensionSuccGen.central c, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hc.symm
  exact Q.reindex he

@[simp]
theorem leftExtensionSuccGenerators_val (g : LeftExtensionSuccGen F n) :
    (leftExtensionSuccGenerators F n).val g =
      LeftExtensionSuccGenSource F n g :=
  rfl

noncomputable def LeftExtensionSuccSourceLift (F : Type u) [Field F] (n : ℕ) :
    FreeGroup (LeftExtensionSuccGen F n) →* leftExtensionSubgroup F n :=
  (leftExtensionSuccGenerators F n).lift

noncomputable def LeftExtensionSuccTargetLift (F : Type u) [Field F] (n : ℕ) :
    FreeGroup (LeftExtensionSuccGen F n) →* leftExtensionSubgroup F (n + 1) :=
  FreeGroup.lift (LeftExtensionSuccGenTarget F n)

@[simp]
private theorem LeftExtensionSuccSourceLift_of (g : LeftExtensionSuccGen F n) :
    LeftExtensionSuccSourceLift F n (FreeGroup.of g) = LeftExtensionSuccGenSource F n g := by
  simp [LeftExtensionSuccSourceLift]

@[simp]
private theorem LeftExtensionSuccTargetLift_of (g : LeftExtensionSuccGen F n) :
    LeftExtensionSuccTargetLift F n (FreeGroup.of g) = LeftExtensionSuccGenTarget F n g := by
  simp [LeftExtensionSuccTargetLift]

theorem LeftExtensionSuccSourceLift_surjective (F : Type u) [Field F] (n : ℕ) :
    Function.Surjective (LeftExtensionSuccSourceLift F n) :=
  (leftExtensionSuccGenerators F n).lift_surjective

end Succession

section Wordwise

variable {F n}

/-- Wordwise invariant: target first = stabilization of source first,
and permutations intertwined by `XSucc`. -/
private def LeftExtensionSuccWordInvariant
    (F : Type u) [Field F] (n : ℕ)
    (w : FreeGroup (LeftExtensionSuccGen F n)) : Prop :=
  (LeftExtensionSuccTargetLift F n w).val.1 =
      Matrix.SpecialLinearGroup.stabilization F
        (LeftExtensionSuccSourceLift F n w).val.1 ∧
  ∀ x : X F n,
    XSucc F n ((LeftExtensionSuccSourceLift F n w).val.2 x) =
      (LeftExtensionSuccTargetLift F n w).val.2 (XSucc F n x)

private theorem LeftExtensionSuccWordInvariant_one :
    LeftExtensionSuccWordInvariant F n
      (1 : FreeGroup (LeftExtensionSuccGen F n)) := by
  constructor
  · simp [map_one]
  · intro x
    simp

private theorem LeftExtensionSuccForwardImpliesInverse
    {a : Equiv.Perm (X F n)} {b : Equiv.Perm (X F (n + 1))}
    (h : ∀ x : X F n, XSucc F n (a x) = b (XSucc F n x)) :
    ∀ x : X F n, XSucc F n (a⁻¹ x) = b⁻¹ (XSucc F n x) := by
  intro x
  have h1 := h (a⁻¹ x)
  have ha : a (a⁻¹ x) = x := by simp
  rw [ha] at h1
  have h_eq : XSucc F n x = b (XSucc F n (a⁻¹ x)) := h1
  calc XSucc F n (a⁻¹ x) = b⁻¹ (b (XSucc F n (a⁻¹ x))) := by simp
    _ = b⁻¹ (XSucc F n x) := by rw [← h_eq]

private theorem LeftExtensionSuccGenerator_first_lemma (g : LeftExtensionSuccGen F n) :
    (LeftExtensionSuccGenTarget F n g).val.1 =
      Matrix.SpecialLinearGroup.stabilization F
        (LeftExtensionSuccGenSource F n g).val.1 := by
  cases g with
  | upper u =>
    simp [UpperElementary.toSLHom_stabilization]
  | weyl i j hij =>
    simp [stabilization_weylSLUnit]
  | central c =>
    simp

private theorem LeftExtensionSuccGenerator_perm_lemma (g : LeftExtensionSuccGen F n) :
    ∀ x : X F n,
      XSucc F n ((LeftExtensionSuccGenSource F n g).val.2 x) =
        (LeftExtensionSuccGenTarget F n g).val.2 (XSucc F n x) := by
  intro x
  cases g with
  | upper u =>
    change XSucc F n (leftUpperPerm (F := F) u x) =
      leftUpperPerm (F := F)
        (UpperElementary.stabilization F n u) (XSucc F n x)
    simp only [leftUpperPerm_apply]
    exact XSucc_leftUpper (F := F) (n := n) (u := u) (x := x)
  | weyl i j hij =>
    change XSucc F n (leftWeylPerm hij x) =
      leftWeylPerm (Fin.castSucc_covBy hij) (XSucc F n x)
    exact leftWeylPerm_stabilization (F := F) hij x
  | central c =>
    change XSucc F n (centralPerm (F := F) c x) =
      centralPerm (F := F) (n := n + 1) c (XSucc F n x)
    simp only [centralPerm_apply]
    exact XSucc_central (F := F) (n := n) (c := c) (x := x)

private theorem LeftExtensionSuccWordInvariant_of
    (g : LeftExtensionSuccGen F n) :
    LeftExtensionSuccWordInvariant F n (FreeGroup.of g) := by
  constructor
  · simp only [LeftExtensionSuccSourceLift_of,
      LeftExtensionSuccTargetLift_of,
      LeftExtensionSuccGenerator_first_lemma]
  · intro x
    exact LeftExtensionSuccGenerator_perm_lemma g x

private theorem LeftExtensionSuccWordInvariant_inv_of
    (g : LeftExtensionSuccGen F n) :
    LeftExtensionSuccWordInvariant F n ((FreeGroup.of g)⁻¹) := by
  have hg := LeftExtensionSuccWordInvariant_of (F := F) (n := n) g
  obtain ⟨hg_first, hg_perm⟩ := hg
  constructor
  · have h_target_inv :
        (LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹)).val.1 =
          ((LeftExtensionSuccTargetLift F n (FreeGroup.of g)).val.1)⁻¹ := by
      have h :
          LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹) =
            (LeftExtensionSuccTargetLift F n (FreeGroup.of g))⁻¹ :=
        map_inv _ _
      have hval :
          (LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹)).val =
            ((LeftExtensionSuccTargetLift F n (FreeGroup.of g))⁻¹).val :=
        congrArg Subtype.val h
      have :
          ((LeftExtensionSuccTargetLift F n (FreeGroup.of g))⁻¹).val =
            ((LeftExtensionSuccTargetLift F n (FreeGroup.of g)).val)⁻¹ :=
        rfl
      rw [hval, this]
      rfl
    have h_source_inv :
        (LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹)).val.1 =
          ((LeftExtensionSuccSourceLift F n (FreeGroup.of g)).val.1)⁻¹ := by
      have h :
          LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹) =
            (LeftExtensionSuccSourceLift F n (FreeGroup.of g))⁻¹ :=
        map_inv _ _
      have hval :
          (LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹)).val =
            ((LeftExtensionSuccSourceLift F n (FreeGroup.of g))⁻¹).val :=
        congrArg Subtype.val h
      have :
          ((LeftExtensionSuccSourceLift F n (FreeGroup.of g))⁻¹).val =
            ((LeftExtensionSuccSourceLift F n (FreeGroup.of g)).val)⁻¹ :=
        rfl
      rw [hval, this]
      rfl
    calc (LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹)).val.1
        = ((LeftExtensionSuccTargetLift F n (FreeGroup.of g)).val.1)⁻¹ :=
          h_target_inv
      _ = (Matrix.SpecialLinearGroup.stabilization F
            (LeftExtensionSuccSourceLift F n (FreeGroup.of g)).val.1)⁻¹ := by
          rw [hg_first]
      _ = Matrix.SpecialLinearGroup.stabilization F
            ((LeftExtensionSuccSourceLift F n (FreeGroup.of g)).val.1)⁻¹ := by
          rw [← map_inv]
      _ = Matrix.SpecialLinearGroup.stabilization F
            (LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹)).val.1 := by
          rw [← h_source_inv]
  · intro x
    have hg_perm_inv := LeftExtensionSuccForwardImpliesInverse hg_perm
    have h_target_perm :
        (LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹)).val.2 =
          (LeftExtensionSuccTargetLift F n (FreeGroup.of g)).val.2⁻¹ := by
      have h :
          LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹) =
            (LeftExtensionSuccTargetLift F n (FreeGroup.of g))⁻¹ :=
        map_inv _ _
      have hval :
          (LeftExtensionSuccTargetLift F n ((FreeGroup.of g)⁻¹)).val.2 =
            ((LeftExtensionSuccTargetLift F n (FreeGroup.of g))⁻¹).val.2 :=
        congrArg
          (fun p :
            Matrix.SpecialLinearGroup (Fin (n + 1)) F ×
              Equiv.Perm (X F (n + 1)) => p.2)
          (congrArg Subtype.val h)
      have :
          ((LeftExtensionSuccTargetLift F n (FreeGroup.of g))⁻¹).val.2 =
            ((LeftExtensionSuccTargetLift F n (FreeGroup.of g)).val.2)⁻¹ :=
        rfl
      rw [hval, this]
    have h_source_perm :
        (LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹)).val.2 =
          (LeftExtensionSuccSourceLift F n (FreeGroup.of g)).val.2⁻¹ := by
      have h :
          LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹) =
            (LeftExtensionSuccSourceLift F n (FreeGroup.of g))⁻¹ :=
        map_inv _ _
      have hval :
          (LeftExtensionSuccSourceLift F n ((FreeGroup.of g)⁻¹)).val.2 =
            ((LeftExtensionSuccSourceLift F n (FreeGroup.of g))⁻¹).val.2 :=
        congrArg
          (fun p :
            Matrix.SpecialLinearGroup (Fin n) F ×
              Equiv.Perm (X F n) => p.2)
          (congrArg Subtype.val h)
      have :
          ((LeftExtensionSuccSourceLift F n (FreeGroup.of g))⁻¹).val.2 =
            ((LeftExtensionSuccSourceLift F n (FreeGroup.of g)).val.2)⁻¹ :=
        rfl
      rw [hval, this]
    rw [h_source_perm, h_target_perm]
    exact hg_perm_inv x

private theorem LeftExtensionSuccWordInvariant_mul
    (w₁ w₂ : FreeGroup (LeftExtensionSuccGen F n))
    (h₁ : LeftExtensionSuccWordInvariant F n w₁)
    (h₂ : LeftExtensionSuccWordInvariant F n w₂) :
    LeftExtensionSuccWordInvariant F n (w₁ * w₂) := by
  obtain ⟨h₁_first, h₁_perm⟩ := h₁
  obtain ⟨h₂_first, h₂_perm⟩ := h₂
  have h_src_val :
      (LeftExtensionSuccSourceLift F n (w₁ * w₂)).val =
        (LeftExtensionSuccSourceLift F n w₁).val *
          (LeftExtensionSuccSourceLift F n w₂).val := by
    have h := map_mul (f := LeftExtensionSuccSourceLift F n) w₁ w₂
    calc (LeftExtensionSuccSourceLift F n (w₁ * w₂)).val =
          (LeftExtensionSuccSourceLift F n w₁ *
            LeftExtensionSuccSourceLift F n w₂).val :=
        congrArg Subtype.val h
      _ = (LeftExtensionSuccSourceLift F n w₁).val *
          (LeftExtensionSuccSourceLift F n w₂).val :=
        rfl
  have h_tgt_val :
      (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val =
        (LeftExtensionSuccTargetLift F n w₁).val *
          (LeftExtensionSuccTargetLift F n w₂).val := by
    have h := map_mul (f := LeftExtensionSuccTargetLift F n) w₁ w₂
    calc (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val =
          (LeftExtensionSuccTargetLift F n w₁ *
            LeftExtensionSuccTargetLift F n w₂).val :=
        congrArg Subtype.val h
      _ = (LeftExtensionSuccTargetLift F n w₁).val *
          (LeftExtensionSuccTargetLift F n w₂).val :=
        rfl
  constructor
  · have h_src_first :
        (LeftExtensionSuccSourceLift F n (w₁ * w₂)).val.1 =
          (LeftExtensionSuccSourceLift F n w₁).val.1 *
            (LeftExtensionSuccSourceLift F n w₂).val.1 :=
      congrArg Prod.fst h_src_val
    have h_tgt_first :
        (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val.1 =
          (LeftExtensionSuccTargetLift F n w₁).val.1 *
            (LeftExtensionSuccTargetLift F n w₂).val.1 :=
      congrArg Prod.fst h_tgt_val
    calc (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val.1
        = (LeftExtensionSuccTargetLift F n w₁).val.1 *
            (LeftExtensionSuccTargetLift F n w₂).val.1 :=
          h_tgt_first
      _ = Matrix.SpecialLinearGroup.stabilization F
            (LeftExtensionSuccSourceLift F n w₁).val.1 *
            Matrix.SpecialLinearGroup.stabilization F
              (LeftExtensionSuccSourceLift F n w₂).val.1 := by
          rw [h₁_first, h₂_first]
      _ = Matrix.SpecialLinearGroup.stabilization F
            ((LeftExtensionSuccSourceLift F n w₁).val.1 *
              (LeftExtensionSuccSourceLift F n w₂).val.1) := by
          rw [← map_mul]
      _ = Matrix.SpecialLinearGroup.stabilization F
            (LeftExtensionSuccSourceLift F n (w₁ * w₂)).val.1 := by
          rw [← h_src_first]
  · intro x
    have h_src_perm :
        (LeftExtensionSuccSourceLift F n (w₁ * w₂)).val.2 =
          (LeftExtensionSuccSourceLift F n w₁).val.2 *
            (LeftExtensionSuccSourceLift F n w₂).val.2 :=
      congrArg Prod.snd h_src_val
    have h_tgt_perm :
        (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val.2 =
          (LeftExtensionSuccTargetLift F n w₁).val.2 *
            (LeftExtensionSuccTargetLift F n w₂).val.2 :=
      congrArg Prod.snd h_tgt_val
    have h_src_apply :
        (LeftExtensionSuccSourceLift F n (w₁ * w₂)).val.2 x =
          (LeftExtensionSuccSourceLift F n w₁).val.2
            ((LeftExtensionSuccSourceLift F n w₂).val.2 x) := by
      rw [h_src_perm, Equiv.Perm.mul_apply]
    have h_tgt_apply :
        (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val.2 (XSucc F n x) =
          (LeftExtensionSuccTargetLift F n w₁).val.2
            ((LeftExtensionSuccTargetLift F n w₂).val.2 (XSucc F n x)) := by
      rw [h_tgt_perm, Equiv.Perm.mul_apply]
    calc XSucc F n ((LeftExtensionSuccSourceLift F n (w₁ * w₂)).val.2 x)
        = XSucc F n
            ((LeftExtensionSuccSourceLift F n w₁).val.2
              ((LeftExtensionSuccSourceLift F n w₂).val.2 x)) := by
          rw [h_src_apply]
      _ = (LeftExtensionSuccTargetLift F n w₁).val.2
            (XSucc F n ((LeftExtensionSuccSourceLift F n w₂).val.2 x)) :=
          h₁_perm _
      _ = (LeftExtensionSuccTargetLift F n w₁).val.2
            ((LeftExtensionSuccTargetLift F n w₂).val.2 (XSucc F n x)) := by
          rw [h₂_perm]
      _ = (LeftExtensionSuccTargetLift F n (w₁ * w₂)).val.2 (XSucc F n x) := by
          rw [h_tgt_apply]

private theorem LeftExtensionSuccWordInvariant_all
    (w : FreeGroup (LeftExtensionSuccGen F n)) :
    LeftExtensionSuccWordInvariant F n w := by
  induction w using FreeGroup.induction_on with
  | one => exact LeftExtensionSuccWordInvariant_one
  | of g => exact LeftExtensionSuccWordInvariant_of g
  | inv_of g => exact LeftExtensionSuccWordInvariant_inv_of g
  | mul w₁ w₂ ih₁ ih₂ => exact LeftExtensionSuccWordInvariant_mul w₁ w₂ ih₁ ih₂

private theorem LeftExtensionSuccTargetLift_fst_eq_stabilization_sourceLift_fst
    (w : FreeGroup (LeftExtensionSuccGen F n)) :
    (LeftExtensionSuccTargetLift F n w).val.1 =
      Matrix.SpecialLinearGroup.stabilization F
        (LeftExtensionSuccSourceLift F n w).val.1 :=
  (LeftExtensionSuccWordInvariant_all (F := F) (n := n) w).1

private theorem LeftExtensionSuccTargetLift_perm_XSucc
    (w : FreeGroup (LeftExtensionSuccGen F n)) (x : X F n) :
    XSucc F n ((LeftExtensionSuccSourceLift F n w).val.2 x) =
      (LeftExtensionSuccTargetLift F n w).val.2 (XSucc F n x) :=
  (LeftExtensionSuccWordInvariant_all (F := F) (n := n) w).2 x

end Wordwise

section Kernel

variable {F n}

private theorem LeftExtensionSuccXSucc_X_one :
    XSucc F n (X_one F n) = X_one F (n + 1) := by
  apply X.ext
  · simp [XSucc, X_one]
  · simp [XSucc, X_one]

theorem LeftExtensionSuccKer_le : (hn : 2 ≤ n) →
    (LeftExtensionSuccSourceLift F n).ker ≤ (LeftExtensionSuccTargetLift F n).ker := by
  intro hn w hw
  rw [MonoidHom.mem_ker] at hw ⊢
  have hw_src_eq : LeftExtensionSuccSourceLift F n w = 1 := hw
  have h_src_first : (LeftExtensionSuccSourceLift F n w).val.1 = 1 :=
    congrArg (fun p : leftExtensionSubgroup F n => p.val.1) hw_src_eq
  have h_src_perm : (LeftExtensionSuccSourceLift F n w).val.2 = 1 :=
    congrArg (fun p : leftExtensionSubgroup F n => p.val.2) hw_src_eq
  have h_tgt_first : (LeftExtensionSuccTargetLift F n w).val.1 = 1 := by
    calc (LeftExtensionSuccTargetLift F n w).val.1
        = Matrix.SpecialLinearGroup.stabilization F
            (LeftExtensionSuccSourceLift F n w).val.1 :=
          LeftExtensionSuccTargetLift_fst_eq_stabilization_sourceLift_fst w
      _ = Matrix.SpecialLinearGroup.stabilization F
            (1 : Matrix.SpecialLinearGroup (Fin n) F) := by
          rw [h_src_first]
      _ = 1 := by simp
  have h_tgt_mem_ker :
      LeftExtensionSuccTargetLift F n w ∈
        (leftExtensionProjHom F (n + 1)).ker := by
    rw [MonoidHom.mem_ker]
    simp [leftExtensionProjHom_apply, h_tgt_first]
  have hn1 : 2 ≤ n + 1 := Nat.le_succ_of_le hn
  have h_ker_eq :
      (leftExtensionProjHom F (n + 1)).ker =
        (centralPairHom F (n + 1)).range :=
    leftExtensionProjHom_ker_eq_centralPairHom_range F (n + 1) hn1
  rw [h_ker_eq] at h_tgt_mem_ker
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h_tgt_mem_ker
  -- hc : centralPairHom (n+1) c = targetLift w
  have h_tgt_val :
      (LeftExtensionSuccTargetLift F n w).val =
        (centralPairHom F (n + 1) c).val := by
    have h : centralPairHom F (n + 1) c = LeftExtensionSuccTargetLift F n w := hc
    exact (congrArg Subtype.val h).symm
  have h_tgt_perm_eq :
      (LeftExtensionSuccTargetLift F n w).val.2 =
        centralPerm (F := F) (n := n + 1) c := by
    have h1 := congrArg Prod.snd h_tgt_val
    simpa only [centralPairHom_val] using h1
  have h_src_perm_one :
      ∀ x : X F n, (LeftExtensionSuccSourceLift F n w).val.2 x = x := by
    intro x
    simp [h_src_perm]
  have h_tgt_fixes :
      (LeftExtensionSuccTargetLift F n w).val.2
          (XSucc F n (X_one F n)) =
        XSucc F n (X_one F n) := by
    calc (LeftExtensionSuccTargetLift F n w).val.2
            (XSucc F n (X_one F n))
        = XSucc F n
            ((LeftExtensionSuccSourceLift F n w).val.2 (X_one F n)) := by
          rw [← LeftExtensionSuccTargetLift_perm_XSucc w (X_one F n)]
      _ = XSucc F n (X_one F n) := by rw [h_src_perm_one]
  have h_central_fixes :
      centralPerm (F := F) (n := n + 1) c (X_one F (n + 1)) =
        X_one F (n + 1) := by
    rw [← LeftExtensionSuccXSucc_X_one (F := F) (n := n), ← h_tgt_perm_eq]
    exact h_tgt_fixes
  have h_central_eq :
      central (F := F) (n := n + 1) c (X_one F (n + 1)) =
        X_one F (n + 1) := by
    simpa [centralPerm_apply] using h_central_fixes
  have h_snd_eq :
      X.snd (central (F := F) (n := n + 1) c (X_one F (n + 1))) =
        X.snd (X_one F (n + 1)) :=
    congrArg X.snd h_central_eq
  have h_inl_one :
      MatsumotoTitsMonomialExtension.inlHom F (n + 1) c = 1 := by
    simpa only [central_snd, X_one_snd, mul_one] using h_snd_eq
  have hc_one : c = 1 := inlHom_injective F (n + 1) h_inl_one
  have h_tgt_one : LeftExtensionSuccTargetLift F n w = 1 := by
    calc LeftExtensionSuccTargetLift F n w = centralPairHom F (n + 1) c := hc.symm
      _ = centralPairHom F (n + 1) (1 : Multiplicative (MilnorK F 2)) := by
          rw [hc_one]
      _ = 1 := by simp
  exact h_tgt_one

end Kernel

section Descent

variable (F : Type u) [Field F] (n : ℕ) (hn : 2 ≤ n)

noncomputable def leftExtensionSuccHom :
    leftExtensionSubgroup F n →* leftExtensionSubgroup F (n + 1) :=
  (leftExtensionSuccGenerators F n).desc
    (LeftExtensionSuccTargetLift F n)
    (by
      simpa only [LeftExtensionSuccSourceLift] using
        LeftExtensionSuccKer_le (F := F) (n := n) hn)

private theorem leftExtensionSuccHom_src_eq_tgt
    (w : FreeGroup (LeftExtensionSuccGen F n)) :
    leftExtensionSuccHom F n hn (LeftExtensionSuccSourceLift F n w) =
      LeftExtensionSuccTargetLift F n w := by
  simp [leftExtensionSuccHom, LeftExtensionSuccSourceLift]

private theorem leftExtensionSuccHom_generator
    (g : LeftExtensionSuccGen F n) :
    leftExtensionSuccHom F n hn (LeftExtensionSuccGenSource F n g) =
      LeftExtensionSuccGenTarget F n g := by
  calc
    leftExtensionSuccHom F n hn (LeftExtensionSuccGenSource F n g) =
        leftExtensionSuccHom F n hn
          (LeftExtensionSuccSourceLift F n (FreeGroup.of g)) := by
      rw [LeftExtensionSuccSourceLift_of]
    _ = LeftExtensionSuccTargetLift F n (FreeGroup.of g) :=
      leftExtensionSuccHom_src_eq_tgt F n hn _
    _ = LeftExtensionSuccGenTarget F n g := by
      simp [LeftExtensionSuccTargetLift]

theorem leftExtensionSuccHom_proj (p : leftExtensionSubgroup F n) :
    (leftExtensionSuccHom F n hn p).val.1 =
      Matrix.SpecialLinearGroup.stabilization F p.val.1 := by
  obtain ⟨w, rfl⟩ := LeftExtensionSuccSourceLift_surjective F n p
  calc (leftExtensionSuccHom F n hn (LeftExtensionSuccSourceLift F n w)).val.1
      = (LeftExtensionSuccTargetLift F n w).val.1 := by
        rw [leftExtensionSuccHom_src_eq_tgt]
    _ = Matrix.SpecialLinearGroup.stabilization F
          (LeftExtensionSuccSourceLift F n w).val.1 :=
        LeftExtensionSuccTargetLift_fst_eq_stabilization_sourceLift_fst w

theorem leftExtensionSuccHom_XSucc (p : leftExtensionSubgroup F n) (x : X F n) :
    XSucc F n (p.val.2 x) =
      (leftExtensionSuccHom F n hn p).val.2 (XSucc F n x) := by
  obtain ⟨w, rfl⟩ := LeftExtensionSuccSourceLift_surjective F n p
  calc XSucc F n ((LeftExtensionSuccSourceLift F n w).val.2 x)
      = (LeftExtensionSuccTargetLift F n w).val.2 (XSucc F n x) :=
        LeftExtensionSuccTargetLift_perm_XSucc w x
    _ = (leftExtensionSuccHom F n hn (LeftExtensionSuccSourceLift F n w)).val.2
          (XSucc F n x) := by
        rw [leftExtensionSuccHom_src_eq_tgt]

@[simp]
theorem leftExtensionSuccHom_upper (u : upperElementarySubgroup (Fin n) F) :
    leftExtensionSuccHom F n hn
        ⟨(UpperElementary.toSLHom u, leftUpperPerm (F := F) u),
          leftUpperPair_mem_leftExtensionSubgroup (F := F) (n := n) u⟩ =
      ⟨(UpperElementary.toSLHom (UpperElementary.stabilization F n u),
          leftUpperPerm (F := F)
            (UpperElementary.stabilization F n u)),
        leftUpperPair_mem_leftExtensionSubgroup (F := F) (n := n + 1)
          (UpperElementary.stabilization F n u)⟩ := by
  simpa [LeftExtensionSuccGenSource, LeftExtensionSuccGenTarget] using
    leftExtensionSuccHom_generator F n hn
      (LeftExtensionSuccGen.upper (F := F) u)

@[simp]
theorem leftExtensionSuccHom_weyl {i j : Fin n} (hij : i ⋖ j) :
    leftExtensionSuccHom F n hn
        ⟨(weylSLUnit i j hij.ne (1 : Fˣ), leftWeylPerm (F := F) hij),
          leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n) hij⟩ =
      ⟨(weylSLUnit (Fin.castSucc i) (Fin.castSucc j)
          (Fin.castSucc_covBy hij).ne (1 : Fˣ),
          leftWeylPerm (F := F) (Fin.castSucc_covBy hij)),
        leftWeylPair_mem_leftExtensionSubgroup (F := F) (n := n + 1)
          (Fin.castSucc_covBy hij)⟩ := by
  simpa [LeftExtensionSuccGenSource, LeftExtensionSuccGenTarget] using
    leftExtensionSuccHom_generator F n hn
      (LeftExtensionSuccGen.weyl (F := F) (n := n) i j hij)

@[simp]
theorem leftExtensionSuccHom_central (c : Multiplicative (MilnorK F 2)) :
    leftExtensionSuccHom F n hn
        ⟨((1 : Matrix.SpecialLinearGroup (Fin n) F), centralPerm (F := F) c),
          centralPair_mem_leftExtensionSubgroup (F := F) (n := n) c⟩ =
      ⟨((1 : Matrix.SpecialLinearGroup (Fin (n + 1)) F),
          centralPerm (F := F) c),
        centralPair_mem_leftExtensionSubgroup (F := F) (n := n + 1) c⟩ := by
  simpa [LeftExtensionSuccGenSource, LeftExtensionSuccGenTarget] using
    leftExtensionSuccHom_generator F n hn
      (LeftExtensionSuccGen.central (F := F) (n := n) c)

theorem leftExtensionSuccHom_injective :
    Function.Injective (leftExtensionSuccHom F n hn) := by
  intro p q h
  have h_first : p.val.1 = q.val.1 := by
    have h_proj_p := leftExtensionSuccHom_proj F n hn p
    have h_proj_q := leftExtensionSuccHom_proj F n hn q
    have h_eq :
        Matrix.SpecialLinearGroup.stabilization F p.val.1 =
          Matrix.SpecialLinearGroup.stabilization F q.val.1 := by
      calc Matrix.SpecialLinearGroup.stabilization F p.val.1
          = (leftExtensionSuccHom F n hn p).val.1 := h_proj_p.symm
        _ = (leftExtensionSuccHom F n hn q).val.1 := by rw [h]
        _ = Matrix.SpecialLinearGroup.stabilization F q.val.1 := h_proj_q
    exact Matrix.SpecialLinearGroup.stabilization_injective h_eq
  have h_perm : p.val.2 = q.val.2 := by
    apply Equiv.ext
    intro x
    apply XSucc_injective F n
    calc XSucc F n (p.val.2 x)
        = (leftExtensionSuccHom F n hn p).val.2 (XSucc F n x) :=
          leftExtensionSuccHom_XSucc F n hn p x
      _ = (leftExtensionSuccHom F n hn q).val.2 (XSucc F n x) := by rw [h]
      _ = XSucc F n (q.val.2 x) :=
          (leftExtensionSuccHom_XSucc F n hn q x).symm
  have h_val : p.val = q.val := Prod.ext h_first h_perm
  exact Subtype.ext h_val

end Descent

end MatsumotoTitsBruhatFiber

end
