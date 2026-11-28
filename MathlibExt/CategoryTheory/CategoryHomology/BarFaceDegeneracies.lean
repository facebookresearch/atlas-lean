/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarDegeneracies

/-!
# Face-degeneracy identities for coefficient bars

Deleting and repeating vertices in a composable-arrow chain satisfy the two
ordered commutation identities and the two cancellation identities. Applying
the coefficient functor and the coproduct injections gives the corresponding
mixed simplicial identities of coefficient bar maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Left-endpoint coherence for a face preceding a degeneracy. -/
theorem leftHom_face_degeneracy_of_le {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc)
    (F : ComposableArrows C (n + 1)) :
    (degeneracyLeftHom j.succ F ≫
        faceLeftHom i.castSucc ((nerve C).σ j.succ F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 1) ↦ K.left)
        (SSet.δ_comp_σ_of_le_apply (S := nerve C) hij F)) =
    faceLeftHom i F ≫ degeneracyLeftHom j ((nerve C).δ i F) := by
  have hIndex : j.succ.predAbove (i.castSucc.succAbove (0 : Fin (n + 2))) =
      i.succAbove (j.predAbove (0 : Fin (n + 2))) := by
    exact SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_σ_of_le hij) (0 : Fin (n + 2))
  unfold degeneracyLeftHom faceLeftHom
  change (F.map _ ≫ F.map _) ≫ eqToHom _ = F.map _ ≫ F.map _
  rw [← F.map_comp]
  rw [← F.map_comp]
  conv_lhs =>
    rhs
    change eqToHom (congrArg F.obj hIndex)
    exact (eqToHom_map F hIndex).symm
  calc
    F.map _ ≫ F.map (eqToHom hIndex) =
        F.map (_ ≫ eqToHom hIndex) := (F.map_comp _ _).symm
    _ = F.map _ := congrArg F.map (Subsingleton.elim _ _)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Left-endpoint coherence for the first face--degeneracy cancellation. -/
theorem leftHom_face_degeneracy_self {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    (degeneracyLeftHom i F ≫
        faceLeftHom i.castSucc ((nerve C).σ i F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ K.left)
        (SSet.δ_comp_σ_self_apply (S := nerve C) i F)) =
    𝟙 F.left := by
  have hIndex : i.predAbove
      (i.castSucc.succAbove (0 : Fin (n + 1))) = 0 := by
    exact SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_σ_self (i := i)) (0 : Fin (n + 1))
  unfold degeneracyLeftHom faceLeftHom
  change (F.map _ ≫ F.map _) ≫ eqToHom _ = 𝟙 _
  rw [← F.map_comp]
  conv_lhs =>
    rhs
    change eqToHom (congrArg F.obj hIndex)
    exact (eqToHom_map F hIndex).symm
  calc
    F.map _ ≫ F.map (eqToHom hIndex) =
        F.map (_ ≫ eqToHom hIndex) := (F.map_comp _ _).symm
    _ = F.map (𝟙 _) := congrArg F.map (Subsingleton.elim _ _)
    _ = 𝟙 _ := F.map_id _

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Left-endpoint coherence for the second face--degeneracy cancellation. -/
theorem leftHom_face_degeneracy_succ {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    (degeneracyLeftHom i F ≫
        faceLeftHom i.succ ((nerve C).σ i F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ K.left)
        (SSet.δ_comp_σ_succ_apply (S := nerve C) i F)) =
    𝟙 F.left := by
  have hIndex : i.predAbove
      (i.succ.succAbove (0 : Fin (n + 1))) = 0 := by
    exact SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_σ_succ (i := i)) (0 : Fin (n + 1))
  unfold degeneracyLeftHom faceLeftHom
  change (F.map _ ≫ F.map _) ≫ eqToHom _ = 𝟙 _
  rw [← F.map_comp]
  conv_lhs =>
    rhs
    change eqToHom (congrArg F.obj hIndex)
    exact (eqToHom_map F hIndex).symm
  calc
    F.map _ ≫ F.map (eqToHom hIndex) =
        F.map (_ ≫ eqToHom hIndex) := (F.map_comp _ _).symm
    _ = F.map (𝟙 _) := congrArg F.map (Subsingleton.elim _ _)
    _ = 𝟙 _ := F.map_id _

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Left-endpoint coherence for a degeneracy preceding a later face. -/
theorem leftHom_face_degeneracy_of_gt {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i)
    (F : ComposableArrows C (n + 1)) :
    (degeneracyLeftHom j.castSucc F ≫
        faceLeftHom i.succ ((nerve C).σ j.castSucc F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 1) ↦ K.left)
        (SSet.δ_comp_σ_of_gt_apply (S := nerve C) hji F)) =
    faceLeftHom i F ≫ degeneracyLeftHom j ((nerve C).δ i F) := by
  have hIndex : j.castSucc.predAbove (i.succ.succAbove (0 : Fin (n + 2))) =
      i.succAbove (j.predAbove (0 : Fin (n + 2))) := by
    exact SimplexCategory.congr_toOrderHom_apply
      (SimplexCategory.δ_comp_σ_of_gt hji) (0 : Fin (n + 2))
  unfold degeneracyLeftHom faceLeftHom
  change (F.map _ ≫ F.map _) ≫ eqToHom _ = F.map _ ≫ F.map _
  rw [← F.map_comp]
  rw [← F.map_comp]
  conv_lhs =>
    rhs
    change eqToHom (congrArg F.obj hIndex)
    exact (eqToHom_map F hIndex).symm
  calc
    F.map _ ≫ F.map (eqToHom hIndex) =
        F.map (_ ≫ eqToHom hIndex) := (F.map_comp _ _).symm
    _ = F.map _ := congrArg F.map (Subsingleton.elim _ _)

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Coefficient coherence for a face preceding a degeneracy. -/
theorem coefficientHom_face_degeneracy_of_le {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc)
    (F : ComposableArrows C (n + 1)) :
    (coefficientDegeneracyHom M j.succ F ≫
        coefficientFaceHom M i.castSucc ((nerve C).σ j.succ F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 1) ↦ M.obj K.left)
        (SSet.δ_comp_σ_of_le_apply (S := nerve C) hij F)) =
    coefficientFaceHom M i F ≫
      coefficientDegeneracyHom M j ((nerve C).δ i F) := by
  have h := congrArg M.map (leftHom_face_degeneracy_of_le i j hij F)
  simpa only [coefficientDegeneracyHom, coefficientFaceHom,
    Functor.map_comp, eqToHom_map, Category.assoc] using h

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Coefficient coherence for the first cancellation identity. -/
theorem coefficientHom_face_degeneracy_self {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    (coefficientDegeneracyHom M i F ≫
        coefficientFaceHom M i.castSucc ((nerve C).σ i F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ M.obj K.left)
        (SSet.δ_comp_σ_self_apply (S := nerve C) i F)) =
    𝟙 (M.obj F.left) := by
  have h := congrArg M.map (leftHom_face_degeneracy_self i F)
  simpa only [coefficientDegeneracyHom, coefficientFaceHom,
    Functor.map_comp, eqToHom_map, Category.assoc, Functor.map_id] using h

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Coefficient coherence for the second cancellation identity. -/
theorem coefficientHom_face_degeneracy_succ {n : ℕ} (i : Fin (n + 1))
    (F : ComposableArrows C n) :
    (coefficientDegeneracyHom M i F ≫
        coefficientFaceHom M i.succ ((nerve C).σ i F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C n ↦ M.obj K.left)
        (SSet.δ_comp_σ_succ_apply (S := nerve C) i F)) =
    𝟙 (M.obj F.left) := by
  have h := congrArg M.map (leftHom_face_degeneracy_succ i F)
  simpa only [coefficientDegeneracyHom, coefficientFaceHom,
    Functor.map_comp, eqToHom_map, Category.assoc, Functor.map_id] using h

omit [HasCoproducts.{max u₁ v₁} A] in
/-- Coefficient coherence for a degeneracy preceding a later face. -/
theorem coefficientHom_face_degeneracy_of_gt {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i)
    (F : ComposableArrows C (n + 1)) :
    (coefficientDegeneracyHom M j.castSucc F ≫
        coefficientFaceHom M i.succ ((nerve C).σ j.castSucc F)) ≫
      eqToHom (congrArg (fun K : ComposableArrows C (n + 1) ↦ M.obj K.left)
        (SSet.δ_comp_σ_of_gt_apply (S := nerve C) hji F)) =
    coefficientFaceHom M i F ≫
      coefficientDegeneracyHom M j ((nerve C).δ i F) := by
  have h := congrArg M.map (leftHom_face_degeneracy_of_gt i j hji F)
  simpa only [coefficientDegeneracyHom, coefficientFaceHom,
    Functor.map_comp, eqToHom_map, Category.assoc] using h

omit [HasCoproducts.{max u₁ v₁} A] in
private theorem sigmaMap'_comp_eq
    {I₀ I₁ I₁' I₂ : Type w} [HasCoproducts.{w} A]
    {X₀ : I₀ → A} {X₁ : I₁ → A} {X₁' : I₁' → A} {X₂ : I₂ → A}
    (p : I₀ → I₁) (q : I₁ → I₂)
    (hp : ∀ a, X₀ a ⟶ X₁ (p a)) (hq : ∀ b, X₁ b ⟶ X₂ (q b))
    (p' : I₀ → I₁') (q' : I₁' → I₂)
    (hp' : ∀ a, X₀ a ⟶ X₁' (p' a)) (hq' : ∀ b, X₁' b ⟶ X₂ (q' b))
    (hidx : ∀ a, q (p a) = q' (p' a))
    (hhom : ∀ a, (hp a ≫ hq (p a)) ≫
      eqToHom (congrArg X₂ (hidx a)) = hp' a ≫ hq' (p' a)) :
    Sigma.map' p hp ≫ Sigma.map' q hq =
      Sigma.map' p' hp' ≫ Sigma.map' q' hq' := by
  apply Sigma.hom_ext
  intro a
  have transport_ι {x y : I₂} (h : x = y) :
      eqToHom (congrArg X₂ h) ≫ Sigma.ι X₂ y = Sigma.ι X₂ x := by
    subst y
    exact Category.id_comp _
  have hι : eqToHom (congrArg X₂ (hidx a)) ≫
      Sigma.ι X₂ (q' (p' a)) = Sigma.ι X₂ (q (p a)) :=
    transport_ι (hidx a)
  have hL₁ : Sigma.ι X₀ a ≫ Sigma.map' p hp =
      hp a ≫ Sigma.ι X₁ (p a) := by
    dsimp [Sigma.map']
    exact Sigma.ι_comp_desc _ a
  have hL₂ : Sigma.ι X₁ (p a) ≫ Sigma.map' q hq =
      hq (p a) ≫ Sigma.ι X₂ (q (p a)) := by
    dsimp [Sigma.map']
    exact Sigma.ι_comp_desc _ (p a)
  have hR₁ : Sigma.ι X₀ a ≫ Sigma.map' p' hp' =
      hp' a ≫ Sigma.ι X₁' (p' a) := by
    dsimp [Sigma.map']
    exact Sigma.ι_comp_desc _ a
  have hR₂ : Sigma.ι X₁' (p' a) ≫ Sigma.map' q' hq' =
      hq' (p' a) ≫ Sigma.ι X₂ (q' (p' a)) := by
    dsimp [Sigma.map']
    exact Sigma.ι_comp_desc _ (p' a)
  calc
    Sigma.ι X₀ a ≫ (Sigma.map' p hp ≫ Sigma.map' q hq) =
        (Sigma.ι X₀ a ≫ Sigma.map' p hp) ≫ Sigma.map' q hq :=
      (Category.assoc _ _ _).symm
    _ = (hp a ≫ Sigma.ι X₁ (p a)) ≫ Sigma.map' q hq := by
      exact congrArg (fun k ↦ k ≫ Sigma.map' q hq) hL₁
    _ = hp a ≫ (Sigma.ι X₁ (p a) ≫ Sigma.map' q hq) :=
      Category.assoc _ _ _
    _ = hp a ≫ (hq (p a) ≫ Sigma.ι X₂ (q (p a))) := by
      exact congrArg (fun k ↦ hp a ≫ k) hL₂
    _ = (hp a ≫ hq (p a)) ≫ Sigma.ι X₂ (q (p a)) :=
      (Category.assoc _ _ _).symm
    _ = ((hp a ≫ hq (p a)) ≫
          eqToHom (congrArg X₂ (hidx a))) ≫
            Sigma.ι X₂ (q' (p' a)) := by
      calc
        _ = (hp a ≫ hq (p a)) ≫
            (eqToHom (congrArg X₂ (hidx a)) ≫
              Sigma.ι X₂ (q' (p' a))) := by rw [hι]
        _ = _ := (Category.assoc _ _ _).symm
    _ = (hp' a ≫ hq' (p' a)) ≫
          Sigma.ι X₂ (q' (p' a)) := by
      exact congrArg (fun k ↦ k ≫ Sigma.ι X₂ (q' (p' a))) (hhom a)
    _ = hp' a ≫ (hq' (p' a) ≫ Sigma.ι X₂ (q' (p' a))) :=
      Category.assoc _ _ _
    _ = hp' a ≫ (Sigma.ι X₁' (p' a) ≫ Sigma.map' q' hq') := by
      exact congrArg (fun k ↦ hp' a ≫ k) hR₂.symm
    _ = (hp' a ≫ Sigma.ι X₁' (p' a)) ≫ Sigma.map' q' hq' :=
      (Category.assoc _ _ _).symm
    _ = (Sigma.ι X₀ a ≫ Sigma.map' p' hp') ≫ Sigma.map' q' hq' := by
      exact congrArg (fun k ↦ k ≫ Sigma.map' q' hq') hR₁.symm
    _ = Sigma.ι X₀ a ≫ (Sigma.map' p' hp' ≫ Sigma.map' q' hq') :=
      Category.assoc _ _ _

/-- Coefficient bar form of the second simplicial identity. -/
theorem coefficientBar_face_degeneracy_of_le {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    coefficientBarDegeneracy M j.succ ≫ coefficientBarFace M i.castSucc =
      coefficientBarFace M i ≫ coefficientBarDegeneracy M j := by
  unfold coefficientBarDegeneracy coefficientBarFace
  exact sigmaMap'_comp_eq
    (X₀ := coefficientBarFamily M (n + 1))
    (X₁ := coefficientBarFamily M (n + 2))
    (X₁' := coefficientBarFamily M n)
    (X₂ := coefficientBarFamily M (n + 1))
    (fun F ↦ (nerve C).σ j.succ F)
    (fun F ↦ (nerve C).δ i.castSucc F)
    (coefficientDegeneracyHom M j.succ)
    (coefficientFaceHom M i.castSucc)
    (fun F ↦ (nerve C).δ i F)
    (fun F ↦ (nerve C).σ j F)
    (coefficientFaceHom M i)
    (coefficientDegeneracyHom M j)
    (fun F ↦ SSet.δ_comp_σ_of_le_apply (S := nerve C) hij F)
    (fun F ↦ coefficientHom_face_degeneracy_of_le M i j hij F)

/-- Coefficient bar form of the fourth simplicial identity. -/
theorem coefficientBar_face_degeneracy_of_gt {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    coefficientBarDegeneracy M j.castSucc ≫ coefficientBarFace M i.succ =
      coefficientBarFace M i ≫ coefficientBarDegeneracy M j := by
  unfold coefficientBarDegeneracy coefficientBarFace
  exact sigmaMap'_comp_eq
    (X₀ := coefficientBarFamily M (n + 1))
    (X₁ := coefficientBarFamily M (n + 2))
    (X₁' := coefficientBarFamily M n)
    (X₂ := coefficientBarFamily M (n + 1))
    (fun F ↦ (nerve C).σ j.castSucc F)
    (fun F ↦ (nerve C).δ i.succ F)
    (coefficientDegeneracyHom M j.castSucc)
    (coefficientFaceHom M i.succ)
    (fun F ↦ (nerve C).δ i F)
    (fun F ↦ (nerve C).σ j F)
    (coefficientFaceHom M i)
    (coefficientDegeneracyHom M j)
    (fun F ↦ SSet.δ_comp_σ_of_gt_apply (S := nerve C) hji F)
    (fun F ↦ coefficientHom_face_degeneracy_of_gt M i j hji F)

omit [HasCoproducts.{max u₁ v₁} A] in
private theorem sigmaMap'_comp_id
    {I₀ I₁ : Type w} [HasCoproducts.{w} A]
    {X₀ : I₀ → A} {X₁ : I₁ → A}
    (p : I₀ → I₁) (q : I₁ → I₀)
    (hp : ∀ a, X₀ a ⟶ X₁ (p a)) (hq : ∀ b, X₁ b ⟶ X₀ (q b))
    (hidx : ∀ a, q (p a) = a)
    (hhom : ∀ a, (hp a ≫ hq (p a)) ≫
      eqToHom (congrArg X₀ (hidx a)) = 𝟙 (X₀ a)) :
    Sigma.map' p hp ≫ Sigma.map' q hq = 𝟙 _ := by
  apply Sigma.hom_ext
  intro a
  have transport_ι {x y : I₀} (h : x = y) :
      eqToHom (congrArg X₀ h) ≫ Sigma.ι X₀ y = Sigma.ι X₀ x := by
    subst y
    exact Category.id_comp _
  have hι : eqToHom (congrArg X₀ (hidx a)) ≫
      Sigma.ι X₀ a = Sigma.ι X₀ (q (p a)) :=
    transport_ι (hidx a)
  have h₁ : Sigma.ι X₀ a ≫ Sigma.map' p hp =
      hp a ≫ Sigma.ι X₁ (p a) := by
    dsimp [Sigma.map']
    exact Sigma.ι_comp_desc _ a
  have h₂ : Sigma.ι X₁ (p a) ≫ Sigma.map' q hq =
      hq (p a) ≫ Sigma.ι X₀ (q (p a)) := by
    dsimp [Sigma.map']
    exact Sigma.ι_comp_desc _ (p a)
  calc
    Sigma.ι X₀ a ≫ (Sigma.map' p hp ≫ Sigma.map' q hq) =
        (Sigma.ι X₀ a ≫ Sigma.map' p hp) ≫ Sigma.map' q hq :=
      (Category.assoc _ _ _).symm
    _ = (hp a ≫ Sigma.ι X₁ (p a)) ≫ Sigma.map' q hq := by
      exact congrArg (fun k ↦ k ≫ Sigma.map' q hq) h₁
    _ = hp a ≫ (Sigma.ι X₁ (p a) ≫ Sigma.map' q hq) :=
      Category.assoc _ _ _
    _ = hp a ≫ (hq (p a) ≫ Sigma.ι X₀ (q (p a))) := by
      exact congrArg (fun k ↦ hp a ≫ k) h₂
    _ = (hp a ≫ hq (p a)) ≫ Sigma.ι X₀ (q (p a)) :=
      (Category.assoc _ _ _).symm
    _ = ((hp a ≫ hq (p a)) ≫
          eqToHom (congrArg X₀ (hidx a))) ≫ Sigma.ι X₀ a := by
      calc
        _ = (hp a ≫ hq (p a)) ≫
            (eqToHom (congrArg X₀ (hidx a)) ≫ Sigma.ι X₀ a) := by
          rw [hι]
        _ = _ := (Category.assoc _ _ _).symm
    _ = 𝟙 (X₀ a) ≫ Sigma.ι X₀ a := by
      exact congrArg (fun k ↦ k ≫ Sigma.ι X₀ a) (hhom a)
    _ = Sigma.ι X₀ a := Category.id_comp _
    _ = Sigma.ι X₀ a ≫ 𝟙 _ := (Category.comp_id _).symm

/-- The first face--degeneracy cancellation identity for the coefficient bar. -/
theorem coefficientBar_face_degeneracy_self {n : ℕ} (i : Fin (n + 1)) :
    coefficientBarDegeneracy M i ≫ coefficientBarFace M i.castSucc = 𝟙 _ := by
  unfold coefficientBarDegeneracy coefficientBarFace
  exact sigmaMap'_comp_id
    (X₀ := coefficientBarFamily M n)
    (X₁ := coefficientBarFamily M (n + 1))
    (fun F ↦ (nerve C).σ i F)
    (fun F ↦ (nerve C).δ i.castSucc F)
    (coefficientDegeneracyHom M i)
    (coefficientFaceHom M i.castSucc)
    (fun F ↦ SSet.δ_comp_σ_self_apply (S := nerve C) i F)
    (fun F ↦ coefficientHom_face_degeneracy_self M i F)

/-- The second face--degeneracy cancellation identity for the coefficient bar. -/
theorem coefficientBar_face_degeneracy_succ {n : ℕ} (i : Fin (n + 1)) :
    coefficientBarDegeneracy M i ≫ coefficientBarFace M i.succ = 𝟙 _ := by
  unfold coefficientBarDegeneracy coefficientBarFace
  exact sigmaMap'_comp_id
    (X₀ := coefficientBarFamily M n)
    (X₁ := coefficientBarFamily M (n + 1))
    (fun F ↦ (nerve C).σ i F)
    (fun F ↦ (nerve C).δ i.succ F)
    (coefficientDegeneracyHom M i)
    (coefficientFaceHom M i.succ)
    (fun F ↦ SSet.δ_comp_σ_succ_apply (S := nerve C) i F)
    (fun F ↦ coefficientHom_face_degeneracy_succ M i F)

end CategoryTheory.CategoryHomology

end
