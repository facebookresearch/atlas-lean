/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.ModelCategory.Over
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Extending a section through an actual fiberwise homotopy

A cofibration together with a genuine homotopy OVER the fixed base lets
an existing section of a fibration be retuned to the given source section.
The new map remains a section strictly and restricts to the given source
map strictly. The proof uses the existing model structure on Over and the
existing right-homotopy extension theorem, with no supplied lifting witness.
-/

noncomputable section

open CategoryTheory Limits

universe u v

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private def overInitial (B : C) : IsInitial (Over.mk (initial.to B)) :=
  IsInitial.ofUniqueHom
    (fun X => Over.homMk (initial.to X.left) (initialIsInitial.hom_ext _ _))
    (by
      intro X m
      apply Over.OverMorphism.ext
      exact initialIsInitial.hom_ext _ _)

/-- An actual cofibrant carrier gives a cofibrant object over every base. -/
public theorem overMk_isCofibrant {A B : C} (i : A ⟶ B) [IsCofibrant A] :
    IsCofibrant (Over.mk i) := by
  let j : Over.mk (initial.to B) ⟶ Over.mk i :=
    Over.homMk (initial.to A) (initialIsInitial.hom_ext _ _)
  let : Cofibration j := by
    rw [cofibrations_over_iff]
    change Cofibration (initial.to A)
    infer_instance
  exact (isCofibrant_iff_of_isInitial j (overInitial B)).mpr inferInstance

/-- An actual fibration is a fibrant object over its actual base. -/
public theorem overMk_isFibrant {E B : C} (p : E ⟶ B) [Fibration p] :
    IsFibrant (Over.mk p) := by
  let j : Over.mk p ⟶ Over.mk (𝟙 B) := Over.homMk p (Category.comp_id p)
  let : Fibration j := by
    rw [fibrations_over_iff]
    change Fibration p
    infer_instance
  exact (isFibrant_iff_of_isTerminal j (Over.mkIdTerminal (X := B))).mpr inferInstance

/-- An existing section is retuned by the GIVEN actual fiberwise
homotopy, without changing its fixed base or either prescribed endpoint
encoded in that base. Both section and source equations remain strict. -/
public theorem exists_section_extension_of_fiberwise_homotopy
    {A B E : C} (i : A ⟶ B) [Cofibration i] [IsCofibrant A]
    (p : E ⟶ B) [Fibration p]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
    (k : A ⟶ E) (hk : k ≫ p = i)
    (P : Cylinder (Over.mk i))
    (h : P.LeftHomotopy
      (Over.homMk (i ≫ s) (by
        change (i ≫ s) ≫ p = i
        rw [Category.assoc, hs, Category.comp_id]) : Over.mk i ⟶ Over.mk p)
      (Over.homMk k hk : Over.mk i ⟶ Over.mk p)) :
    ∃ s' : B ⟶ E, s' ≫ p = 𝟙 B ∧ i ≫ s' = k := by
  let : IsCofibrant (Over.mk i) := overMk_isCofibrant i
  let : IsFibrant (Over.mk p) := overMk_isFibrant p
  let i' : Over.mk i ⟶ Over.mk (𝟙 B) := Over.homMk i (Category.comp_id i)
  let : Cofibration i' := by
    rw [cofibrations_over_iff]
    change Cofibration i
    infer_instance
  let s₀ : Over.mk (𝟙 B) ⟶ Over.mk p := Over.homMk s hs
  have hs₀ : i' ≫ s₀ =
      (Over.homMk (i ≫ s) (by
        change (i ≫ s) ≫ p = i
        rw [Category.assoc, hs, Category.comp_id]) : Over.mk i ⟶ Over.mk p) := by
    apply Over.OverMorphism.ext
    rfl
  obtain ⟨Q, hQ, ⟨hR⟩⟩ := h.leftHomotopyRel.rightHomotopyRel.exists_good_pathObject
  let : Q.IsGood := hQ
  obtain ⟨s₁, H, hH⟩ := PathObject.RightHomotopy.homotopy_extension hR i' s₀ hs₀
  have hsource : i' ≫ s₁ = Over.homMk k hk := by
    rw [← H.h₁, ← Category.assoc, hH, hR.h₁]
  refine ⟨s₁.left, Over.w s₁, ?_⟩
  exact congrArg (fun f : Over.mk i ⟶ Over.mk p => f.left) hsource

private def cylinderOver {A B : C} (P : Cylinder A) (i : A ⟶ B) :
    Cylinder (Over.mk i) where
  I := Over.mk (P.π ≫ i)
  i₀ := Over.homMk P.i₀ (by
    change P.i₀ ≫ (P.π ≫ i) = i
    rw [← Category.assoc, P.i₀_π, Category.id_comp])
  i₁ := Over.homMk P.i₁ (by
    change P.i₁ ≫ (P.π ≫ i) = i
    rw [← Category.assoc, P.i₁_π, Category.id_comp])
  π := Over.homMk P.π rfl
  i₀_π := by
    apply Over.OverMorphism.ext
    exact P.i₀_π
  i₁_π := by
    apply Over.OverMorphism.ext
    exact P.i₁_π
  weakEquivalence_π := by
    rw [weakEquivalences_over_iff]
    change WeakEquivalence P.π
    infer_instance

/-- An actual cylinder homotopy through a fixed base is a WHOLE left
homotopy over that base. Both original maps and the original cylinder
carrier are retained; no fiberwise homotopy class is supplied separately. -/
public theorem leftHomotopyRel_over_of_cylinder
    {A E T : C} (p : E ⟶ T) (b : A ⟶ T)
    (s t : A ⟶ E) (hs : s ≫ p = b) (ht : t ≫ p = b)
    (P : Cylinder A) (h : P.LeftHomotopy s t)
    (hbase : h.h ≫ p = P.π ≫ b) :
    LeftHomotopyRel (Over.homMk s hs : Over.mk b ⟶ Over.mk p)
      (Over.homMk t ht : Over.mk b ⟶ Over.mk p) := by
  let Q := cylinderOver P b
  refine ⟨Q, ⟨{ h := Over.homMk h.h hbase, h₀ := ?_, h₁ := ?_ }⟩⟩
  · apply Over.OverMorphism.ext
    exact h.h₀
  · apply Over.OverMorphism.ext
    exact h.h₁

/-- The original map is retuned in the actual slice model category.
Its fixed base and source restriction are strict, and the WHOLE global
right homotopy class from the original map is returned for subsequent
stage composition. The extension and global comparison are both derived. -/
public theorem exists_fibration_extension_with_over_homotopy
    {A B E T : C} (i : A ⟶ B) [Cofibration i] [IsCofibrant A]
    (p : E ⟶ T) [Fibration p]
    (bA : A ⟶ T) (bB : B ⟶ T) (hib : i ≫ bB = bA)
    (s : B ⟶ E) (hs : s ≫ p = bB)
    (k : A ⟶ E) (hk : k ≫ p = bA)
    (h : LeftHomotopyRel
      (Over.homMk (i ≫ s) (by
        change (i ≫ s) ≫ p = bA
        rw [Category.assoc, hs, hib]) : Over.mk bA ⟶ Over.mk p)
      (Over.homMk k hk : Over.mk bA ⟶ Over.mk p)) :
    ∃ (s' : B ⟶ E) (hs' : s' ≫ p = bB),
      i ≫ s' = k ∧
        RightHomotopyRel (Over.homMk s hs : Over.mk bB ⟶ Over.mk p)
          (Over.homMk s' hs' : Over.mk bB ⟶ Over.mk p) := by
  let : IsCofibrant (Over.mk bA) := overMk_isCofibrant bA
  let : IsFibrant (Over.mk p) := overMk_isFibrant p
  let i' : Over.mk bA ⟶ Over.mk bB := Over.homMk i hib
  let : Cofibration i' := by
    rw [cofibrations_over_iff]
    change Cofibration i
    infer_instance
  let s₀ : Over.mk bB ⟶ Over.mk p := Over.homMk s hs
  let k₀ : Over.mk bA ⟶ Over.mk p := Over.homMk k hk
  have hc : i' ≫ s₀ =
      (Over.homMk (i ≫ s) (by
        change (i ≫ s) ≫ p = bA
        rw [Category.assoc, hs, hib]) : Over.mk bA ⟶ Over.mk p) := by
    apply Over.OverMorphism.ext
    rfl
  have h' : LeftHomotopyRel (i' ≫ s₀) k₀ := by
    rw [hc]
    exact h
  obtain ⟨Q, hQ, ⟨hR⟩⟩ := h'.rightHomotopyRel.exists_good_pathObject
  let : Q.IsGood := hQ
  obtain ⟨r, H, hH⟩ := PathObject.RightHomotopy.homotopy_extension hR i' s₀ rfl
  have hir : i' ≫ r = k₀ := by
    rw [← H.h₁, ← Category.assoc, hH, hR.h₁]
  have hr : r = (Over.homMk r.left (Over.w r) : Over.mk bB ⟶ Over.mk p) := by
    apply Over.OverMorphism.ext
    rfl
  refine ⟨r.left, Over.w r, congrArg (fun f : Over.mk bA ⟶ Over.mk p => f.left) hir, ?_⟩
  change RightHomotopyRel s₀ (Over.homMk r.left (Over.w r))
  rw [← hr]
  exact H.rightHomotopyRel

/-- A genuine cylinder homotopy through a fixed fibration fiber retunes
an existing map while retaining the ORIGINAL fixed base and the entire
source restriction strictly. The literal pullback constructs the fiber;
no endpoint-preserving lift or section is a caller input. -/
public theorem exists_fibration_map_extension_of_fiberwise_homotopy
    {A B E T : C} (i : A ⟶ B) [Cofibration i] [IsCofibrant A]
    (p : E ⟶ T) [Fibration p] (b : B ⟶ T)
    (s : B ⟶ E) (hs : s ≫ p = b)
    (k : A ⟶ E) (hk : k ≫ p = i ≫ b)
    (P : Cylinder A) (h : P.LeftHomotopy (i ≫ s) k)
    (hbase : h.h ≫ p = P.π ≫ i ≫ b) :
    ∃ s' : B ⟶ E, s' ≫ p = b ∧ i ≫ s' = k := by
  let pu := pullback.snd p b
  let : Fibration pu := inferInstance
  let s₀ : B ⟶ pullback p b := pullback.lift s (𝟙 B) (by simpa using hs)
  let k₀ : A ⟶ pullback p b := pullback.lift k i hk
  have hs₀ : s₀ ≫ pu = 𝟙 B := pullback.lift_snd _ _ _
  have hk₀ : k₀ ≫ pu = i := pullback.lift_snd _ _ _
  let q : P.I ⟶ pullback p b :=
    pullback.lift h.h (P.π ≫ i) (by simpa only [Category.assoc] using hbase)
  have hq : q ≫ pu = P.π ≫ i := pullback.lift_snd _ _ _
  have h₀ : P.i₀ ≫ q = i ≫ s₀ := by
    apply pullback.hom_ext
    · simpa only [q, s₀, Category.assoc, pullback.lift_fst] using h.h₀
    · calc
        (P.i₀ ≫ q) ≫ pu = P.i₀ ≫ (P.π ≫ i) := by rw [Category.assoc, hq]
        _ = (P.i₀ ≫ P.π) ≫ i := (Category.assoc _ _ _).symm
        _ = i := by rw [P.i₀_π, Category.id_comp]
        _ = (i ≫ s₀) ≫ pu := by rw [Category.assoc, hs₀, Category.comp_id]
  have h₁ : P.i₁ ≫ q = k₀ := by
    apply pullback.hom_ext
    · simpa only [q, k₀, Category.assoc, pullback.lift_fst] using h.h₁
    · calc
        (P.i₁ ≫ q) ≫ pu = P.i₁ ≫ (P.π ≫ i) := by rw [Category.assoc, hq]
        _ = (P.i₁ ≫ P.π) ≫ i := (Category.assoc _ _ _).symm
        _ = i := by rw [P.i₁_π, Category.id_comp]
        _ = k₀ ≫ pu := hk₀.symm
  let Q := cylinderOver P i
  let H : Q.LeftHomotopy
      (Over.homMk (i ≫ s₀) (by
        change (i ≫ s₀) ≫ pu = i
        rw [Category.assoc, hs₀, Category.comp_id]) : Over.mk i ⟶ Over.mk pu)
      (Over.homMk k₀ hk₀ : Over.mk i ⟶ Over.mk pu) :=
    { h := Over.homMk q hq
      h₀ := by
        apply Over.OverMorphism.ext
        exact h₀
      h₁ := by
        apply Over.OverMorphism.ext
        exact h₁ }
  obtain ⟨r, hr, hir⟩ := exists_section_extension_of_fiberwise_homotopy
    i pu s₀ hs₀ k₀ hk₀ Q H
  refine ⟨r ≫ pullback.fst p b, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp]
  · rw [← Category.assoc, hir]
    exact pullback.lift_fst _ _ _

end HomotopicalAlgebra

end
