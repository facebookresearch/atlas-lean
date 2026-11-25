/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingNaiveFibrants
public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystemEndpoints
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrationDeformation

/-!
# Weak naive fibrations with naive fibrant codomain

A testing equivalence which is a naive fibration with naive fibrant codomain
has an actual section and a fixed-cylinder homotopy lying over its base.
The endpoint-one square corrects the original inverse to a strict section;
a fresh homotopy for that section is then rectified on the full three-face
cylinder corner. The naive-fibrant-codomain hypothesis is essential.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Lemma 2.4.28 (printed pp.60–61 / PDF pp.76–77), with the stated
generic exact-cylinder hypotheses. No model structure is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- The actual rectifying lift retains the two inner faces, the outer
endpoint-one face, and the whole map over the base. -/
private lemma exists_rectifying_lift {X Y : C} (p : X ⟶ Y) (hp : An.rlp p)
    (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : (P.app X).LeftHomotopy (𝟙 X) (p ≫ s)) :
    ∃ F : P.I.obj (P.I.obj X) ⟶ X,
      P.I.map (P.app X).i₀ ≫ F = H.h ∧
        P.I.map (P.app X).i₁ ≫ F = H.h ≫ p ≫ s ∧
          (P.app (P.I.obj X)).i₁ ≫ F = (P.app X).π ≫ p ≫ s ∧
            F ≫ p = P.I.map (P.app X).π ≫ H.h ≫ p := by
  let : PreservesColimitsOfSize.{0, 0} P.I :=
    preservesSmallestColimits_of_preservesColimits P.I
  let boundary : X ⨿ X ⟶ P.I.obj X := (P.app X).i
  let a : P.I.obj X ⟶ X := (P.app X).π ≫ p ≫ s
  let b : P.I.obj (X ⨿ X) ⟶ X :=
    inv (coprodComparison P.I X X) ≫ coprod.desc H.h (H.h ≫ p ≫ s)
  let bottom : P.I.obj (P.I.obj X) ⟶ Y := P.I.map (P.app X).π ≫ H.h ≫ p
  have b₀ : P.I.map (coprod.inl : X ⟶ X ⨿ X) ≫ b = H.h := by
    simp [b, map_inl_inv_coprodComparison_assoc]
  have b₁ : P.I.map (coprod.inr : X ⟶ X ⨿ X) ≫ b = H.h ≫ p ≫ s := by
    simp [b, map_inr_inv_coprodComparison_assoc]
  have hps : (p ≫ s) ≫ p = p := by rw [Category.assoc, hs, Category.comp_id]
  have hsp : (p ≫ s) ≫ (p ≫ s) = p ≫ s := by rw [← Category.assoc, hps]
  have overlap : boundary ≫ a = (P.app (X ⨿ X)).endpoint 1 ≫ b := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ boundary ≫ a = p ≫ s := by
          simp only [boundary, a, ← Category.assoc, (P.app X).inl_i,
            (P.app X).i₀_π, Category.id_comp]
        _ = (P.app X).i₁ ≫ H.h := H.h₁.symm
        _ = (P.app X).endpoint 1 ≫ (P.I.map coprod.inl ≫ b) := by rw [b₀]; rfl
        _ = coprod.inl ≫ (P.app (X ⨿ X)).endpoint 1 ≫ b := by
          simpa only [Category.assoc] using
            congrArg (· ≫ b) (P.endpoint_naturality (coprod.inl : X ⟶ X ⨿ X) 1).symm
    · calc
        coprod.inr ≫ boundary ≫ a = p ≫ s := by
          simp only [boundary, a, ← Category.assoc, (P.app X).inr_i,
            (P.app X).i₁_π, Category.id_comp]
        _ = (p ≫ s) ≫ (p ≫ s) := hsp.symm
        _ = (P.app X).i₁ ≫ (H.h ≫ p ≫ s) := by
          simpa only [Category.assoc] using congrArg (· ≫ (p ≫ s)) H.h₁.symm
        _ = (P.app X).endpoint 1 ≫ (P.I.map coprod.inr ≫ b) := by rw [b₁]; rfl
        _ = coprod.inr ≫ (P.app (X ⨿ X)).endpoint 1 ≫ b := by
          simpa only [Category.assoc] using
            congrArg (· ≫ b) (P.endpoint_naturality (coprod.inr : X ⟶ X ⨿ X) 1).symm
  have projection₀ : P.I.map (coprod.inl : X ⟶ X ⨿ X) ≫
      P.I.map boundary ≫ P.I.map (P.app X).π = 𝟙 (P.I.obj X) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [boundary, ← Category.assoc, (P.app X).inl_i,
      (P.app X).i₀_π]
    exact P.I.map_id X
  have projection₁ : P.I.map (coprod.inr : X ⟶ X ⨿ X) ≫
      P.I.map boundary ≫ P.I.map (P.app X).π = 𝟙 (P.I.obj X) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [boundary, ← Category.assoc, (P.app X).inr_i,
      (P.app X).i₁_π]
    exact P.I.map_id X
  have base₀ : P.I.map (coprod.inl : X ⟶ X ⨿ X) ≫ (P.I.map boundary ≫ bottom) =
      H.h ≫ p := by
    simpa only [bottom, Category.assoc, Category.id_comp] using
      congrArg (· ≫ (H.h ≫ p)) projection₀
  have base₁ : P.I.map (coprod.inr : X ⟶ X ⨿ X) ≫ (P.I.map boundary ≫ bottom) =
      H.h ≫ p := by
    simpa only [bottom, Category.assoc, Category.id_comp] using
      congrArg (· ≫ (H.h ≫ p)) projection₁
  have b_over : b ≫ p = P.I.map boundary ≫ bottom := by
    apply (cancel_epi (coprodComparison P.I X X)).mp
    apply coprod.hom_ext
    · rw [inl_coprodComparison_assoc, inl_coprodComparison_assoc]
      rw [← Category.assoc (P.I.map (coprod.inl : X ⟶ X ⨿ X)) b p, b₀, base₀]
    · rw [inr_coprodComparison_assoc, inr_coprodComparison_assoc]
      rw [← Category.assoc (P.I.map (coprod.inr : X ⟶ X ⨿ X)) b p, b₁, base₁]
      simp only [Category.assoc, hs, Category.comp_id]
  let top := pushout.desc a b overlap
  have cornerSq : CommSq top (P.endpointCorner boundary 1) p bottom := by
    constructor
    apply pushout.hom_ext
    · rw [← Category.assoc (pushout.inl boundary ((P.app (X ⨿ X)).endpoint 1)) top p]
      rw [show pushout.inl boundary ((P.app (X ⨿ X)).endpoint 1) ≫ top = a
        from pushout.inl_desc ..]
      rw [inl_endpointCorner_assoc]
      change a ≫ p = (P.app (P.I.obj X)).i₁ ≫ bottom
      calc
        a ≫ p = (P.app X).π ≫ p := by
          simp only [a, Category.assoc, hs, Category.comp_id]
        _ = (P.app X).π ≫ ((P.app X).i₁ ≫ (H.h ≫ p)) := by
          rw [← Category.assoc (P.app X).i₁ H.h p, H.h₁, hps]
        _ = (P.app (P.I.obj X)).i₁ ≫ bottom := by
          simpa only [bottom, Functor.id_map, Category.assoc] using
            congrArg (· ≫ (H.h ≫ p)) (P.i₁.naturality (P.app X).π)
    · rw [← Category.assoc (pushout.inr boundary ((P.app (X ⨿ X)).endpoint 1)) top p]
      rw [show pushout.inr boundary ((P.app (X ⨿ X)).endpoint 1) ≫ top = b
        from pushout.inr_desc ..]
      rw [inr_endpointCorner_assoc]
      exact b_over
  have hAn : An (P.endpointCorner boundary 1) := endpoint_corner boundary 1
  have : HasLiftingProperty (P.endpointCorner boundary 1) p := hp _ hAn
  have restriction : P.I.map boundary ≫ cornerSq.lift = b := by
    have q := congrArg (pushout.inr boundary ((P.app (X ⨿ X)).endpoint 1) ≫ ·)
      cornerSq.fac_left
    simpa only [inr_endpointCorner_assoc, top, pushout.inr_desc] using q
  have F₀ : P.I.map (P.app X).i₀ ≫ cornerSq.lift = H.h := by
    rw [← (P.app X).inl_i, Functor.map_comp, Category.assoc]
    exact (congrArg (P.I.map (coprod.inl : X ⟶ X ⨿ X) ≫ ·) restriction).trans b₀
  have F₁ : P.I.map (P.app X).i₁ ≫ cornerSq.lift = H.h ≫ p ≫ s := by
    rw [← (P.app X).inr_i, Functor.map_comp, Category.assoc]
    exact (congrArg (P.I.map (coprod.inr : X ⟶ X ⨿ X) ≫ ·) restriction).trans b₁
  refine ⟨cornerSq.lift, F₀, F₁, ?_, cornerSq.fac_right⟩
  have outer : (P.app (P.I.obj X)).endpoint 1 ≫ cornerSq.lift = a := by
    have q := congrArg (pushout.inl boundary ((P.app (X ⨿ X)).endpoint 1) ≫ ·)
      cornerSq.fac_left
    simpa only [inl_endpointCorner_assoc, top, pushout.inl_desc] using q
  simpa only [endpoint_one, a] using outer

variable [HasInitial C] [InitialMonoClass C] [HasTerminal C]

/-- A weak naive fibration with naive fibrant codomain has an actual section
and both fixed-cylinder endpoints, with the entire homotopy over its base. -/
theorem exists_dualDeformationData_of_testingEquivalence_of_naiveFibration
    {X Y : C} (p : X ⟶ Y) (hp : An.rlp p) (hY : An.naiveFibrantObjects Y)
    (hw : P.testingEquivalences An p) : Nonempty (P.DualDeformationData p) := by
  have hX : An.naiveFibrantObjects X := by
    change An.rlp (terminal.from X)
    rw [show terminal.from X = p ≫ terminal.from Y from terminal.hom_ext _ _]
    exact An.rlp.comp_mem p (terminal.from Y) hp hY
  obtain ⟨t, _, ⟨k⟩⟩ :=
    (testingEquivalences_iff_exists_leftHomotopy_inverse P An p hX hY).mp hw
  have hAn : An (P.app Y).i₁ := by
    simpa only [endpoint_one] using endpoint_mem_anodyne P An Y 1
  have : HasLiftingProperty (P.app Y).i₁ p := hp _ hAn
  have sectionSq : CommSq t (P.app Y).i₁ p k.h := ⟨k.h₁.symm⟩
  let s : Y ⟶ X := (P.app Y).i₀ ≫ sectionSq.lift
  have hs : s ≫ p = 𝟙 Y := by
    dsimp only [s]
    rw [Category.assoc, sectionSq.fac_right, k.h₀]
  have he := (P.testingEquivalences_iff_homotopyEquivalences An p hX hY).mp hw
  have : IsIso (P.homotopyQuotientFunctor.map p) := (P.homotopyEquivalences_iff p).mp he
  have hclass : P.homotopyQuotientFunctor.map (𝟙 X) =
      P.homotopyQuotientFunctor.map (p ≫ s) := by
    symm
    rw [P.homotopyQuotientFunctor.map_comp, P.homotopyQuotientFunctor.map_id]
    apply (cancel_mono (P.homotopyQuotientFunctor.map p)).mp
    rw [Category.assoc, ← P.homotopyQuotientFunctor.map_comp, hs,
      P.homotopyQuotientFunctor.map_id, Category.comp_id, Category.id_comp]
  obtain ⟨H⟩ := (homotopyQuotientFunctor_map_eq_iff_nonempty_leftHomotopy P An hX
    (𝟙 X) (p ≫ s)).mp hclass
  obtain ⟨F, F₀, F₁, _, hover⟩ := exists_rectifying_lift P An p hp s hs H
  refine ⟨{
    section_ := s
    section_comp := hs
    homotopy := {
      h := (P.app (P.I.obj X)).i₀ ≫ F
      h₀ := ?_
      h₁ := ?_ }
    over_base := ?_ }⟩
  · calc
      (P.app X).i₀ ≫ ((P.app (P.I.obj X)).i₀ ≫ F) =
          (P.app X).i₀ ≫ (P.I.map (P.app X).i₀ ≫ F) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (· ≫ F) (P.i₀.naturality (P.app X).i₀)
      _ = 𝟙 X := by rw [F₀, H.h₀]
  · calc
      (P.app X).i₁ ≫ ((P.app (P.I.obj X)).i₀ ≫ F) =
          (P.app X).i₀ ≫ (P.I.map (P.app X).i₁ ≫ F) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (· ≫ F) (P.i₀.naturality (P.app X).i₁)
      _ = p ≫ s := by rw [F₁, H.h₀_assoc, Category.id_comp]
  · calc
      ((P.app (P.I.obj X)).i₀ ≫ F) ≫ p =
          (P.app (P.I.obj X)).i₀ ≫ (P.I.map (P.app X).π ≫ H.h ≫ p) := by
        rw [Category.assoc, hover]
      _ = (P.app X).π ≫ ((P.app X).i₀ ≫ (H.h ≫ p)) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (· ≫ (H.h ≫ p)) (P.i₀.naturality (P.app X).π).symm
      _ = (P.app X).π ≫ p := by rw [H.h₀_assoc, Category.id_comp]

/-- With naive fibrant codomain, testing equivalence of a naive fibration
is exactly right lifting against every monomorphism. -/
theorem testingEquivalences_iff_rlp_monomorphisms_of_naiveFibration
    {X Y : C} (p : X ⟶ Y) (hp : An.rlp p) (hY : An.naiveFibrantObjects Y) :
    P.testingEquivalences An p ↔ (MorphismProperty.monomorphisms C).rlp p := by
  constructor
  · intro hw
    obtain ⟨D⟩ := exists_dualDeformationData_of_testingEquivalence_of_naiveFibration
      P An p hp hY hw
    exact D.mem_rlp_monomorphisms hp
  · exact P.rlp_monomorphisms_le_testingEquivalences An p

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
