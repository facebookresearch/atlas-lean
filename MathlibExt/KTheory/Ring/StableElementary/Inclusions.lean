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

public import MathlibExt.KTheory.Ring.StableElementary.Basic

/-! # Stable inclusions: injectivity of finite-stage maps

All finite diagram transitions are injective;
hence the canonical maps `StableGL.of` and `StableE.fromFinite` are injective.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory

open Matrix.GeneralLinearGroup

private theorem finiteGLDiagram_obj_map_injective {R : Type u} [Semiring R]
    {n m : ℕ} (f : n ⟶ m) :
    Function.Injective ((finiteGLDiagram.obj (SemiRingCat.of R)).map f) := by
  induction m generalizing n with
  | zero =>
    have h_le : n ≤ 0 := leOfHom f
    have h_eq : n = 0 := Nat.le_zero.mp h_le
    subst h_eq
    have h_f : f = 𝟙 (0 : ℕ) := Subsingleton.elim f (𝟙 (0 : ℕ))
    rw [h_f]
    have h_map : (finiteGLDiagram.obj (SemiRingCat.of R)).map (𝟙 (0 : ℕ)) =
        𝟙 ((finiteGLDiagram.obj (SemiRingCat.of R)).obj 0) := by simp
    rw [h_map]
    exact Function.injective_id
  | succ m ih =>
    have h_le : n ≤ m + 1 := leOfHom f
    by_cases h_nm : n ≤ m
    · let f₁ : n ⟶ m := homOfLE h_nm
      let f₂ : m ⟶ m + 1 := homOfLE (Nat.le_add_right m 1)
      have h_eq : f = f₁ ≫ f₂ := Subsingleton.elim _ _
      have h_map_eq : (finiteGLDiagram.obj (SemiRingCat.of R)).map f =
          (finiteGLDiagram.obj (SemiRingCat.of R)).map f₁ ≫
            (finiteGLDiagram.obj (SemiRingCat.of R)).map f₂ := by
        rw [h_eq, Functor.map_comp]
      have h_succ : (finiteGLDiagram.obj (SemiRingCat.of R)).map f₂ =
          GrpCat.ofHom (stabilization (R := R) (n := m)) := by
        exact finiteGLDiagram_obj_map_succ (R := SemiRingCat.of R) m
      have h_inj_f₂ : Function.Injective ((finiteGLDiagram.obj (SemiRingCat.of R)).map f₂) := by
        rw [h_succ]
        exact stabilization_injective
      intro x y hxy
      have hxy' : ((finiteGLDiagram.obj (SemiRingCat.of R)).map f) x =
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map f) y := hxy
      rw [h_map_eq] at hxy'
      have h_comp_x : ((finiteGLDiagram.obj (SemiRingCat.of R)).map f₁ ≫
          (finiteGLDiagram.obj (SemiRingCat.of R)).map f₂) x =
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map f₂)
            (((finiteGLDiagram.obj (SemiRingCat.of R)).map f₁) x) := by
        rw [GrpCat.comp_apply]
      have h_comp_y : ((finiteGLDiagram.obj (SemiRingCat.of R)).map f₁ ≫
          (finiteGLDiagram.obj (SemiRingCat.of R)).map f₂) y =
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map f₂)
            (((finiteGLDiagram.obj (SemiRingCat.of R)).map f₁) y) := by
        rw [GrpCat.comp_apply]
      rw [h_comp_x, h_comp_y] at hxy'
      have h_inj_f₁ : Function.Injective ((finiteGLDiagram.obj (SemiRingCat.of R)).map f₁) := ih f₁
      exact h_inj_f₁ (h_inj_f₂ hxy')
    · have h_eq : n = m + 1 := by omega
      subst h_eq
      have h_f : f = 𝟙 (m + 1 : ℕ) := Subsingleton.elim f (𝟙 _)
      rw [h_f]
      have h_map : (finiteGLDiagram.obj (SemiRingCat.of R)).map (𝟙 (m + 1 : ℕ)) =
          𝟙 ((finiteGLDiagram.obj (SemiRingCat.of R)).obj (m + 1)) := by simp
      rw [h_map]
      exact Function.injective_id

namespace StableGL

theorem of_injective {R : Type u} [Semiring R] {n : ℕ} :
    Function.Injective (fun g : Matrix.GeneralLinearGroup (Fin n) R => StableGL.of g) := by
  intro g₁ g₂ h
  have h_iff := (StableGL.of_eq_iff (R := R) (g₁ := g₁) (g₂ := g₂)).mp h
  obtain ⟨k, f₁, f₂, hf⟩ := h_iff
  have h_eq : f₁ = f₂ := Subsingleton.elim _ _
  rw [h_eq] at hf
  exact (finiteGLDiagram_obj_map_injective (R := R) f₂) hf

end StableGL

namespace StableE

theorem fromFinite_injective {R : Type u} [Ring R] (n : ℕ) :
    Function.Injective (StableE.fromFinite (R := R) n) := by
  intro g₁ g₂ h
  have h_coe : (↑(StableE.fromFinite R n g₁) : AlgebraicKTheory.StableGL R) =
      (↑(StableE.fromFinite R n g₂) : AlgebraicKTheory.StableGL R) :=
    congrArg Subtype.val h
  rw [StableE.coe_fromFinite, StableE.coe_fromFinite] at h_coe
  have h_val : (↑g₁ : Matrix.GeneralLinearGroup (Fin n) R) =
      (↑g₂ : Matrix.GeneralLinearGroup (Fin n) R) :=
    StableGL.of_injective h_coe
  exact Subtype.ext h_val

end StableE

end AlgebraicKTheory

end
