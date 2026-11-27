/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomFibration

/-!
# Cylinder deformation invariance of lifting squares

For maps i:A→B and p:X→Y, a cylinder square t:A×Δ[1]→X and b:B×Δ[1]→Y with t≫p=(i×id)≫b
restricts to commuting squares at both endpoints.

If i is monic and p a Kan fibration, the endpoint-zero square has a lift exactly when the
endpoint-one square has a lift. The endpoint maps are the specified restrictions of t,b, and a
lift is a map B→X satisfying both triangles.

The interval orientation is ι₀=δ₁ at vertex zero and ι₁=δ₀ at vertex one. All simplicial sets
may lie in any universe u.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed
  Simplicial SSet HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.CommSq

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}

/-- Let i:A→B and p:X→Y be simplicial maps, with t:A×Δ[1]→X and b:B×Δ[1]→Y satisfying t≫p=(i×id)≫b.
If t|₀=t₀ and b|₀=b₀, the endpoint-zero maps satisfy t₀≫p=i≫b₀, forming a commuting square. -/
theorem commSq₀_of_deformation {t : A ⊗ (Δ[1] : SSet.{u}) ⟶ X}
    {b : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y} (sq : CommSq t (i ▷ (Δ[1] : SSet.{u})) p b)
    {t₀ : A ⟶ X} {b₀ : B ⟶ Y} (ht₀ : SSet.ι₀ ≫ t = t₀) (hb₀ : SSet.ι₀ ≫ b = b₀) :
    CommSq t₀ i p b₀ :=
  ⟨by
    calc t₀ ≫ p = (SSet.ι₀ ≫ t) ≫ p := by rw [ht₀]
      _ = SSet.ι₀ ≫ (t ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₀ ≫ ((i ▷ (Δ[1] : SSet.{u})) ≫ b) := by rw [sq.w]
      _ = (SSet.ι₀ ≫ (i ▷ (Δ[1] : SSet.{u}))) ≫ b := by rw [← Category.assoc]
      _ = (i ≫ SSet.ι₀) ≫ b := by rw [SSet.ι₀_comp]
      _ = i ≫ (SSet.ι₀ ≫ b) := by rw [Category.assoc]
      _ = i ≫ b₀ := by rw [hb₀]⟩

/-- Let i:A→B and p:X→Y be simplicial maps, with t:A×Δ[1]→X and b:B×Δ[1]→Y satisfying t≫p=(i×id)≫b.
If t|₁=t₁ and b|₁=b₁, the endpoint-one maps satisfy t₁≫p=i≫b₁, forming a commuting square. -/
theorem commSq₁_of_deformation {t : A ⊗ (Δ[1] : SSet.{u}) ⟶ X}
    {b : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y} (sq : CommSq t (i ▷ (Δ[1] : SSet.{u})) p b)
    {t₁ : A ⟶ X} {b₁ : B ⟶ Y} (ht₁ : SSet.ι₁ ≫ t = t₁) (hb₁ : SSet.ι₁ ≫ b = b₁) :
    CommSq t₁ i p b₁ :=
  ⟨by
    calc t₁ ≫ p = (SSet.ι₁ ≫ t) ≫ p := by rw [ht₁]
      _ = SSet.ι₁ ≫ (t ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ ((i ▷ (Δ[1] : SSet.{u})) ≫ b) := by rw [sq.w]
      _ = (SSet.ι₁ ≫ (i ▷ (Δ[1] : SSet.{u}))) ≫ b := by rw [← Category.assoc]
      _ = (i ≫ SSet.ι₁) ≫ b := by rw [SSet.ι₁_comp]
      _ = i ≫ (SSet.ι₁ ≫ b) := by rw [Category.assoc]
      _ = i ≫ b₁ := by rw [hb₁]⟩

-- Private bridge: `const (ihom₀Equiv.symm f) = curry (fst ≫ f)` with `fst = rightUnitor.hom`.
private theorem const_ihom₀Equiv_symm_apply_priv (A' X' : SSet.{u}) (f : A' ⟶ X') :
    SSet.const (X := (Δ[0] : SSet.{u})) ((SSet.ihom₀Equiv A' X').symm f) =
      curry (fst A' (Δ[0] : SSet.{u}) ≫ f) := by
  calc SSet.const (X := (Δ[0] : SSet.{u})) ((SSet.ihom₀Equiv A' X').symm f)
      = yonedaEquiv.symm ((SSet.ihom₀Equiv A' X').symm f) := by
        rw [← yonedaEquiv_symm_zero]
    _ = yonedaEquiv.symm (yonedaEquiv (curry ((stdSimplex.rightUnitor A').hom ≫ f))) := by
        rw [ihom₀Equiv_symm_apply]
    _ = curry ((stdSimplex.rightUnitor A').hom ≫ f) := by
        rw [Equiv.symm_apply_apply]
    _ = curry (fst A' (Δ[0] : SSet.{u}) ≫ f) := rfl

-- Private: `A ◁ δ₁ ≫ t = fst ≫ t₀` from `ι₀ ≫ t = t₀`.
private theorem whiskerLeft_δ_one_comp_of_iota₀ {A' : SSet.{u}} {X' : SSet.{u}}
    {t : A' ⊗ (Δ[1] : SSet.{u}) ⟶ X'} {t₀ : A' ⟶ X'} (ht₀ : SSet.ι₀ ≫ t = t₀) :
    A' ◁ (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ t =
      fst A' (Δ[0] : SSet.{u}) ≫ t₀ := by
  calc A' ◁ stdSimplex.δ 1 ≫ t
      = (stdSimplex.rightUnitor A').hom ≫ ι₀ ≫ t := by
        rw [← stdSimplex.rightUnitor_hom_ι₀, Category.assoc]
    _ = (stdSimplex.rightUnitor A').hom ≫ t₀ := by rw [ht₀]
    _ = fst A' (Δ[0] : SSet.{u}) ≫ t₀ := rfl

private theorem whiskerLeft_δ_zero_comp_of_iota₁ {A' : SSet.{u}} {X' : SSet.{u}}
    {t : A' ⊗ (Δ[1] : SSet.{u}) ⟶ X'} {t₁ : A' ⟶ X'} (ht₁ : SSet.ι₁ ≫ t = t₁) :
    A' ◁ (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ t =
      fst A' (Δ[0] : SSet.{u}) ≫ t₁ := by
  calc A' ◁ stdSimplex.δ 0 ≫ t
      = (stdSimplex.rightUnitor A').hom ≫ ι₁ ≫ t := by
        rw [← stdSimplex.rightUnitor_hom_ι₁, Category.assoc]
    _ = (stdSimplex.rightUnitor A').hom ≫ t₁ := by rw [ht₁]
    _ = fst A' (Δ[0] : SSet.{u}) ≫ t₁ := rfl

-- Private edge in the pullback target determined by the curried cylinder maps.
private noncomputable def pullbackTgtEdge_of_deformation
    {t : A ⊗ (Δ[1] : SSet.{u}) ⟶ X} {b : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y}
    (sq : CommSq t (i ▷ (Δ[1] : SSet.{u})) p b) :
    (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}) _⦋1⦌ :=
  yonedaEquiv (pullback.lift (curry t) (curry b)
    (by
      calc curry t ≫ (ihom A).map p
          = curry (t ≫ p) := by rw [curry_natural_right]
        _ = curry ((i ▷ (Δ[1] : SSet.{u})) ≫ b) := by rw [sq.w]
        _ = curry b ≫ (pre i).app Y := by
            rw [← curry_pre_app]))

private theorem pullbackTgtEdge_of_deformation_δ_one
    {t : A ⊗ (Δ[1] : SSet.{u}) ⟶ X} {b : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y}
    (sq : CommSq t (i ▷ (Δ[1] : SSet.{u})) p b)
    {t₀ : A ⟶ X} {b₀ : B ⟶ Y} (ht₀ : SSet.ι₀ ≫ t = t₀) (hb₀ : SSet.ι₀ ≫ b = b₀) :
    (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}).δ 1
      (pullbackTgtEdge_of_deformation (i := i) (p := p) sq) =
      ihomToPullbackTgt₀Mk (commSq₀_of_deformation sq ht₀ hb₀) := by
  apply (Equiv.injective (yonedaEquiv (X :=
    (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u})).symm))
  have h_orig : curry t ≫ (ihom A).map p = curry b ≫ (pre i).app Y := by
    calc curry t ≫ (ihom A).map p
        = curry (t ≫ p) := by rw [curry_natural_right]
      _ = curry ((i ▷ (Δ[1] : SSet.{u})) ≫ b) := by rw [sq.w]
      _ = curry b ≫ (pre i).app Y := by rw [← curry_pre_app]
  have h_cond_one : (stdSimplex.δ (1 : Fin 2) ≫ curry t) ≫ (ihom A).map p =
      (stdSimplex.δ (1 : Fin 2) ≫ curry b) ≫ (pre i).app Y := by
    calc (stdSimplex.δ 1 ≫ curry t) ≫ (ihom A).map p
        = stdSimplex.δ 1 ≫ (curry t ≫ (ihom A).map p) := by rw [Category.assoc]
      _ = stdSimplex.δ 1 ≫ (curry b ≫ (pre i).app Y) := by rw [h_orig]
      _ = (stdSimplex.δ 1 ≫ curry b) ≫ (pre i).app Y := by rw [← Category.assoc]
  have h_eq_cond₀ : SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₀)
      ≫ (ihom A).map p =
      SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₀) ≫ (pre i).app Y := by
    calc SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₀) ≫ (ihom A).map p
        = SSet.const (((ihom A).map p).app _ ((ihom₀Equiv A X).symm t₀)) := by
          rw [SSet.const_comp]
      _ = SSet.const ((ihom₀Equiv A Y).symm (t₀ ≫ p)) := by
          rw [← ihom₀Equiv_symm_map]
      _ = SSet.const ((ihom₀Equiv A Y).symm (i ≫ b₀)) := by
          rw [(commSq₀_of_deformation sq ht₀ hb₀).w]
      _ = SSet.const (((pre i).app Y).app _ ((ihom₀Equiv B Y).symm b₀)) := by
          rw [ihom₀Equiv_symm_pre]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₀) ≫ (pre i).app Y := by
          rw [← SSet.const_comp]
  have h_curry_t : stdSimplex.δ (1 : Fin 2) ≫ curry t =
      SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₀) := by
    calc stdSimplex.δ 1 ≫ curry t
        = curry (A ◁ stdSimplex.δ 1 ≫ t) := by rw [← curry_natural_left]
      _ = curry (fst A (Δ[0] : SSet.{u}) ≫ t₀) := by rw [whiskerLeft_δ_one_comp_of_iota₀ ht₀]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₀) := by
          rw [← const_ihom₀Equiv_symm_apply_priv]
  have h_curry_b : stdSimplex.δ (1 : Fin 2) ≫ curry b =
      SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₀) := by
    calc stdSimplex.δ 1 ≫ curry b
        = curry (B ◁ stdSimplex.δ 1 ≫ b) := by rw [← curry_natural_left]
      _ = curry (fst B (Δ[0] : SSet.{u}) ≫ b₀) := by rw [whiskerLeft_δ_one_comp_of_iota₀ hb₀]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₀) := by
          rw [← const_ihom₀Equiv_symm_apply_priv]
  have h_yoneda_symm_tgt :
      yonedaEquiv.symm (ihomToPullbackTgt₀Mk (commSq₀_of_deformation sq ht₀ hb₀)) =
        pullback.lift (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₀))
          (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₀)) h_eq_cond₀ := by
    apply pullback.hom_ext
    · simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply,
        pullback.lift_fst, yonedaEquiv_symm_zero]
    · simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply,
        pullback.lift_snd, yonedaEquiv_symm_zero]
  calc yonedaEquiv.symm
        ((pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}).δ 1
          (pullbackTgtEdge_of_deformation (i := i) (p := p) sq))
      = stdSimplex.δ 1 ≫
          yonedaEquiv.symm (pullbackTgtEdge_of_deformation (i := i) (p := p) sq) := by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm]
    _ = stdSimplex.δ 1 ≫ pullback.lift (curry t) (curry b) h_orig := by
        simp only [pullbackTgtEdge_of_deformation, Equiv.symm_apply_apply]
    _ = pullback.lift (stdSimplex.δ 1 ≫ curry t) (stdSimplex.δ 1 ≫ curry b) h_cond_one := by
        apply pullback.hom_ext
        · simp [Category.assoc]
        · simp [Category.assoc]
    _ = pullback.lift
          (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₀))
          (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₀)) h_eq_cond₀ := by
        apply pullback.hom_ext
        · simp only [pullback.lift_fst]
          exact h_curry_t
        · simp only [pullback.lift_snd]
          exact h_curry_b
    _ = yonedaEquiv.symm (ihomToPullbackTgt₀Mk (commSq₀_of_deformation sq ht₀ hb₀)) := by
        rw [h_yoneda_symm_tgt]

private theorem pullbackTgtEdge_of_deformation_δ_zero
    {t : A ⊗ (Δ[1] : SSet.{u}) ⟶ X} {b : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y}
    (sq : CommSq t (i ▷ (Δ[1] : SSet.{u})) p b)
    {t₁ : A ⟶ X} {b₁ : B ⟶ Y} (ht₁ : SSet.ι₁ ≫ t = t₁) (hb₁ : SSet.ι₁ ≫ b = b₁) :
    (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}).δ 0
      (pullbackTgtEdge_of_deformation (i := i) (p := p) sq) =
      ihomToPullbackTgt₀Mk (commSq₁_of_deformation sq ht₁ hb₁) := by
  apply (Equiv.injective (yonedaEquiv (X :=
    (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u})).symm))
  have h_orig : curry t ≫ (ihom A).map p = curry b ≫ (pre i).app Y := by
    calc curry t ≫ (ihom A).map p
        = curry (t ≫ p) := by rw [curry_natural_right]
      _ = curry ((i ▷ (Δ[1] : SSet.{u})) ≫ b) := by rw [sq.w]
      _ = curry b ≫ (pre i).app Y := by rw [← curry_pre_app]
  have h_cond_zero : (stdSimplex.δ (0 : Fin 2) ≫ curry t) ≫ (ihom A).map p =
      (stdSimplex.δ (0 : Fin 2) ≫ curry b) ≫ (pre i).app Y := by
    calc (stdSimplex.δ 0 ≫ curry t) ≫ (ihom A).map p
        = stdSimplex.δ 0 ≫ (curry t ≫ (ihom A).map p) := by rw [Category.assoc]
      _ = stdSimplex.δ 0 ≫ (curry b ≫ (pre i).app Y) := by rw [h_orig]
      _ = (stdSimplex.δ 0 ≫ curry b) ≫ (pre i).app Y := by rw [← Category.assoc]
  have h_eq_cond₁ : SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₁)
      ≫ (ihom A).map p =
      SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₁) ≫ (pre i).app Y := by
    calc SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₁) ≫ (ihom A).map p
        = SSet.const (((ihom A).map p).app _ ((ihom₀Equiv A X).symm t₁)) := by
          rw [SSet.const_comp]
      _ = SSet.const ((ihom₀Equiv A Y).symm (t₁ ≫ p)) := by
          rw [← ihom₀Equiv_symm_map]
      _ = SSet.const ((ihom₀Equiv A Y).symm (i ≫ b₁)) := by
          rw [(commSq₁_of_deformation sq ht₁ hb₁).w]
      _ = SSet.const (((pre i).app Y).app _ ((ihom₀Equiv B Y).symm b₁)) := by
          rw [ihom₀Equiv_symm_pre]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₁) ≫ (pre i).app Y := by
          rw [← SSet.const_comp]
  have h_curry_t : stdSimplex.δ (0 : Fin 2) ≫ curry t =
      SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₁) := by
    calc stdSimplex.δ 0 ≫ curry t
        = curry (A ◁ stdSimplex.δ 0 ≫ t) := by rw [← curry_natural_left]
      _ = curry (fst A (Δ[0] : SSet.{u}) ≫ t₁) := by rw [whiskerLeft_δ_zero_comp_of_iota₁ ht₁]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₁) := by
          rw [← const_ihom₀Equiv_symm_apply_priv]
  have h_curry_b : stdSimplex.δ (0 : Fin 2) ≫ curry b =
      SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₁) := by
    calc stdSimplex.δ 0 ≫ curry b
        = curry (B ◁ stdSimplex.δ 0 ≫ b) := by rw [← curry_natural_left]
      _ = curry (fst B (Δ[0] : SSet.{u}) ≫ b₁) := by rw [whiskerLeft_δ_zero_comp_of_iota₁ hb₁]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₁) := by
          rw [← const_ihom₀Equiv_symm_apply_priv]
  have h_yoneda_symm_tgt :
      yonedaEquiv.symm (ihomToPullbackTgt₀Mk (commSq₁_of_deformation sq ht₁ hb₁)) =
        pullback.lift (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₁))
          (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₁)) h_eq_cond₁ := by
    apply pullback.hom_ext
    · simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply,
        pullback.lift_fst, yonedaEquiv_symm_zero]
    · simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply,
        pullback.lift_snd, yonedaEquiv_symm_zero]
  calc yonedaEquiv.symm
        ((pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}).δ 0
          (pullbackTgtEdge_of_deformation (i := i) (p := p) sq))
      = stdSimplex.δ 0 ≫
          yonedaEquiv.symm (pullbackTgtEdge_of_deformation (i := i) (p := p) sq) := by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm]
    _ = stdSimplex.δ 0 ≫ pullback.lift (curry t) (curry b) h_orig := by
        simp only [pullbackTgtEdge_of_deformation, Equiv.symm_apply_apply]
    _ = pullback.lift (stdSimplex.δ 0 ≫ curry t) (stdSimplex.δ 0 ≫ curry b) h_cond_zero := by
        apply pullback.hom_ext
        · simp [Category.assoc]
        · simp [Category.assoc]
    _ = pullback.lift
          (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv A X).symm t₁))
          (SSet.const (X := (Δ[0] : SSet.{u})) ((ihom₀Equiv B Y).symm b₁)) h_eq_cond₁ := by
        apply pullback.hom_ext
        · simp only [pullback.lift_fst]
          exact h_curry_t
        · simp only [pullback.lift_snd]
          exact h_curry_b
    _ = yonedaEquiv.symm (ihomToPullbackTgt₀Mk (commSq₁_of_deformation sq ht₁ hb₁)) := by
        rw [h_yoneda_symm_tgt]

/-- Let i:A→B and p:X→Y be simplicial maps, with t:A×Δ[1]→X and b:B×Δ[1]→Y satisfying t≫p=(i×id)≫b.
Assume i is monic and p a Kan fibration, with specified restrictions t₀,t₁,b₀,b₁ at both
endpoints. There is a map ℓ₀:B→X with i≫ℓ₀=t₀ and ℓ₀≫p=b₀ if and only if there is ℓ₁ with
i≫ℓ₁=t₁ and ℓ₁≫p=b₁. -/
theorem hasLift_iff_of_deformation [Mono i] [Fibration p]
    {t : A ⊗ (Δ[1] : SSet.{u}) ⟶ X} {b : B ⊗ (Δ[1] : SSet.{u}) ⟶ Y}
    (sq : CommSq t (i ▷ (Δ[1] : SSet.{u})) p b)
    {t₀ t₁ : A ⟶ X} {b₀ b₁ : B ⟶ Y}
    (ht₀ : SSet.ι₀ ≫ t = t₀) (ht₁ : SSet.ι₁ ≫ t = t₁)
    (hb₀ : SSet.ι₀ ≫ b = b₀) (hb₁ : SSet.ι₁ ≫ b = b₁) :
    (commSq₀_of_deformation sq ht₀ hb₀).HasLift ↔
      (commSq₁_of_deformation sq ht₁ hb₁).HasLift := by
  have h_edge : (pullback ((ihom A).map p) ((pre i).app Y) : SSet.{u}).Edge
      (ihomToPullbackTgt₀Mk (commSq₀_of_deformation sq ht₀ hb₀))
      (ihomToPullbackTgt₀Mk (commSq₁_of_deformation sq ht₁ hb₁)) :=
    Edge.mk (pullbackTgtEdge_of_deformation (i := i) (p := p) sq)
      (by rw [pullbackTgtEdge_of_deformation_δ_one sq ht₀ hb₀])
      (by rw [pullbackTgtEdge_of_deformation_δ_zero sq ht₁ hb₁])
  exact hasLift_iff_of_edge_ihomToPullbackTgt
    (commSq₀_of_deformation sq ht₀ hb₀) (commSq₁_of_deformation sq ht₁ hb₁) h_edge

end SSet.CommSq
