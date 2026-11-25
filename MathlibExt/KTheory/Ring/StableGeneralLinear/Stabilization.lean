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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Basic
public import Mathlib.Algebra.Group.Commutator

/-!
# Stabilization lemmas for `StableGL`

Focused stability API for the Whitehead proof:

* `of_map` : diagram morphisms preserve `StableGL` class,
* `of_stabilization` : successor stabilization preserves class,
* `of_mul`, `of_one`, `of_inv`, `of_commutator` : compatibility via
  the canonical inclusion homomorphism,
* common finite stage and commutator representative lemmas.

General `blockDiagonalOne` and `Fin` arithmetic for `n + m` is handled
separately at the finite level.
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicKTheory

namespace StableGL

variable {R : Type u} [Semiring R]

/-- Diagram morphisms do not change the `StableGL` class. -/
theorem of_map {n m : ℕ} (f : n ⟶ m)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of ((finiteGLDiagram.obj (SemiRingCat.of R)).map f g) =
      StableGL.of g := by
  let F := finiteGLDiagram.obj (SemiRingCat.of R)
  change ((GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app m).hom ((F.map f).hom g) =
    ((GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app n).hom g
  have h_nat : F.map f ≫ (GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app m =
      (GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app n := by
    have h := (GrpCat.FilteredColimits.colimitCocone (F := F)).ι.naturality f
    simp only [Functor.const_obj_map] at h ⊢
    exact h
  have h_hom := congrArg GrpCat.Hom.hom h_nat
  have h_app := DFunLike.congr_fun h_hom g
  calc
    ((GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app m).hom ((F.map f).hom g)
        = ((GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app m).hom.comp (F.map f).hom g := rfl
    _ = (F.map f ≫ (GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app m).hom g := by
          rw [← GrpCat.hom_comp]
    _ = ((GrpCat.FilteredColimits.colimitCocone (F := F)).ι.app n).hom g := h_app

/-- Successor stabilization preserves the `StableGL` class. -/
theorem of_stabilization {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of (Matrix.GeneralLinearGroup.stabilization R g) =
      StableGL.of g := by
  have h_map :
      (finiteGLDiagram.obj (SemiRingCat.of R)).map
          (homOfLE (Nat.le_add_right n 1)) =
        GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization (R := R)) :=
    finiteGLDiagram_obj_map_succ (R := SemiRingCat.of R) n
  have h_eq :
      Matrix.GeneralLinearGroup.stabilization (R := R) g =
        (finiteGLDiagram.obj (SemiRingCat.of R)).map
          (homOfLE (Nat.le_add_right n 1)) g := by
    rw [h_map]
    rfl
  rw [h_eq]
  exact of_map (homOfLE (Nat.le_add_right n 1)) g

/-- Successor stabilization in the filtered-colimit representative normal form.
The named `of_stabilization` equation retains its explicit-rewrite interface. -/
@[simp]
theorem G_mk_stabilization {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R))
        ⟨n + 1, Matrix.GeneralLinearGroup.stabilization R g⟩ =
      GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩ :=
  of_stabilization g

theorem of_mul {n : ℕ}
    (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of (g * h) = StableGL.of g * StableGL.of h := by
  have h_mul :
      (StableGL.inclusion n).app (SemiRingCat.of R) (g * h) =
        (StableGL.inclusion n).app (SemiRingCat.of R) g *
          (StableGL.inclusion n).app (SemiRingCat.of R) h :=
    (ConcreteCategory.hom ((StableGL.inclusion n).app (SemiRingCat.of R))).map_mul g h
  calc
    StableGL.of (g * h) =
        (StableGL.inclusion n).app (SemiRingCat.of R) (g * h) :=
      rfl
    _ = (StableGL.inclusion n).app (SemiRingCat.of R) g *
          (StableGL.inclusion n).app (SemiRingCat.of R) h :=
      h_mul
    _ = StableGL.of g * StableGL.of h := rfl

theorem of_one {n : ℕ} :
    (StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) R) : StableGL R) = 1 := by
  have h_one :
      (StableGL.inclusion n).app (SemiRingCat.of R) (1 : _) = 1 :=
    (ConcreteCategory.hom ((StableGL.inclusion n).app (SemiRingCat.of R))).map_one
  calc
    StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) R) =
        (StableGL.inclusion n).app (SemiRingCat.of R) 1 :=
      rfl
    _ = 1 := h_one

/-- The identity representative in the normal form of the filtered colimit.
The named `of_one` equation remains available for explicit rewrites. -/
@[simp]
theorem G_mk_one {n : ℕ} :
    (GrpCat.FilteredColimits.G.mk
      (F := finiteGLDiagram.obj (SemiRingCat.of R))
      ⟨n, (1 : Matrix.GeneralLinearGroup (Fin n) R)⟩ : StableGL R) = 1 :=
  of_one

theorem of_inv {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of g⁻¹ = (StableGL.of g)⁻¹ := by
  have h_inv :
      (StableGL.inclusion n).app (SemiRingCat.of R) g⁻¹ =
        ((StableGL.inclusion n).app (SemiRingCat.of R) g)⁻¹ :=
    (ConcreteCategory.hom ((StableGL.inclusion n).app (SemiRingCat.of R))).map_inv g
  calc
    StableGL.of g⁻¹ =
        (StableGL.inclusion n).app (SemiRingCat.of R) g⁻¹ :=
      rfl
    _ = ((StableGL.inclusion n).app (SemiRingCat.of R) g)⁻¹ := h_inv
    _ = (StableGL.of g)⁻¹ := rfl

open scoped commutatorElement

theorem of_commutator {n : ℕ}
    (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of ⁅g, h⁆ = ⁅StableGL.of g, StableGL.of h⁆ := by
  simp only [commutatorElement_def, of_mul, of_inv]

/-- Any two stable elements have representatives at a common finite stage. -/
theorem exists_common_finite_rep (x y : StableGL R) :
    ∃ (n : ℕ) (g h : Matrix.GeneralLinearGroup (Fin n) R),
      StableGL.of g = x ∧ StableGL.of h = y := by
  obtain ⟨n₁, g₁, hg₁⟩ := StableGL.exists_finite_rep (R := R) x
  obtain ⟨n₂, g₂, hg₂⟩ := StableGL.exists_finite_rep (R := R) y
  let n := Nat.max n₁ n₂
  have h₁ : n₁ ≤ n := Nat.le_max_left _ _
  have h₂ : n₂ ≤ n := Nat.le_max_right _ _
  let f₁ : n₁ ⟶ n := homOfLE h₁
  let f₂ : n₂ ⟶ n := homOfLE h₂
  let F := finiteGLDiagram.obj (SemiRingCat.of R)
  let g : Matrix.GeneralLinearGroup (Fin n) R := F.map f₁ g₁
  let h : Matrix.GeneralLinearGroup (Fin n) R := F.map f₂ g₂
  have hg : StableGL.of g = x := by
    calc
      StableGL.of g = StableGL.of (F.map f₁ g₁) := rfl
      _ = StableGL.of g₁ := of_map f₁ g₁
      _ = x := hg₁
  have hh : StableGL.of h = y := by
    calc
      StableGL.of h = StableGL.of (F.map f₂ g₂) := rfl
      _ = StableGL.of g₂ := of_map f₂ g₂
      _ = y := hg₂
  exact ⟨n, g, h, hg, hh⟩

/-- Any commutator in `StableGL` is represented by a finite commutator at a common stage. -/
theorem exists_finite_commutator_rep (x y : StableGL R) :
    ∃ (n : ℕ) (g h : Matrix.GeneralLinearGroup (Fin n) R),
      StableGL.of ⁅g, h⁆ = ⁅x, y⁆ := by
  obtain ⟨n, g, h, hg, hh⟩ := exists_common_finite_rep (R := R) x y
  exact ⟨n, g, h, by rw [of_commutator, hg, hh]⟩

end StableGL

end AlgebraicKTheory

end
