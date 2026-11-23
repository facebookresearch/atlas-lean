/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Finite
public import MathlibExt.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-!
# Stable general linear groups via explicit filtered colimits

For a semiring `R`, the groups `GLₙ(R)` stabilize via block
`diag(-,1)` inclusions. The colimit of the `ℕ`-indexed diagram
`finiteGLDiagram` in `GrpCat` defines the stable functor
`SemiRingCat ⥤ GrpCat` using the explicit
`GrpCat.FilteredColimits.colimitFunctor`. The type-level `StableGL R`
is the underlying type of its value at `SemiRingCat.of R`, with
representatives via `G.mk`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicKTheory

/-- The stable general linear group functor `SemiRingCat ⥤ GrpCat`
defined as `finiteGLDiagram ⋙ colimitFunctor`. -/
noncomputable def StableGL.functor : SemiRingCat.{u} ⥤ GrpCat.{u} :=
  finiteGLDiagram ⋙ GrpCat.FilteredColimits.colimitFunctor (J := ℕ)

/-- Type-level stable general linear group of a semiring,
as the underlying type of `StableGL.functor` at `SemiRingCat.of R`. -/
abbrev StableGL (R : Type u) [Semiring R] : Type u :=
  ↥(StableGL.functor.obj (SemiRingCat.of R))

/-- Canonical inclusion `GLₙ → StableGL` as a natural transformation. -/
noncomputable def StableGL.inclusion (n : ℕ) :
    finiteGLFunctor (n := n) ⟶ StableGL.functor where
  app R := (GrpCat.FilteredColimits.colimitCocone
    (F := finiteGLDiagram.obj R)).ι.app n
  naturality {R S} f := by
    have hι := GrpCat.FilteredColimits.colimitMap_ι
      (α := finiteGLDiagram.map f) (j := n)
    have happ : (finiteGLDiagram.map f).app n =
        (finiteGLFunctor (n := n)).map f := by
      simp [finiteGLDiagram_map_app]
    have hsymm := hι.symm
    rw [happ] at hsymm
    exact hsymm

@[simp]
lemma StableGL.inclusion_app (n : ℕ) (R : SemiRingCat.{u}) :
    (StableGL.inclusion n).app R =
      (GrpCat.FilteredColimits.colimitCocone
        (F := finiteGLDiagram.obj R)).ι.app n :=
  rfl

/-- Canonical representative `GL (Fin n) R → StableGL R` via `G.mk`. -/
def StableGL.of {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) : StableGL R :=
  GrpCat.FilteredColimits.G.mk (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩

@[simp]
lemma StableGL.of_eq_G_mk {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of g =
      GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩ :=
  rfl

/-- Applying the stage inclusion yields the canonical representative. -/
lemma StableGL.inclusion_apply (n : ℕ) (R : Type u) [Semiring R]
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (StableGL.inclusion n).app (SemiRingCat.of R) g = StableGL.of g :=
  rfl

/-- The stage inclusion in its actual filtered-colimit normal form.
The named `inclusion_apply` equation remains available for explicit rewrites. -/
@[simp]
lemma StableGL.colimitCocone_ι_app_apply (n : ℕ) (R : Type u) [Semiring R]
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ConcreteCategory.hom
      (X := GrpCat.of (Matrix.GeneralLinearGroup (Fin n) R))
      (Y := (GrpCat.FilteredColimits.colimitCocone
        (F := finiteGLDiagram.obj (SemiRingCat.of R))).pt)
      ((GrpCat.FilteredColimits.colimitCocone
        (F := finiteGLDiagram.obj (SemiRingCat.of R))).ι.app n)) g =
      GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩ :=
  StableGL.inclusion_apply n R g

/-- Every element of `StableGL R` is represented at some finite stage. -/
theorem StableGL.exists_finite_rep {R : Type u} [Semiring R] (x : StableGL R) :
    ∃ (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R), StableGL.of g = x := by
  have hsurj := Functor.ιColimitType_jointly_surjective
    (F := finiteGLDiagram.obj (SemiRingCat.of R) ⋙ forget GrpCat.{u}) x
  obtain ⟨n, g, hg⟩ := hsurj
  exact ⟨n, g, hg⟩

/-- Equality of stable representatives holds iff they agree after further stabilization. -/
theorem StableGL.of_eq_iff {R : Type u} [Semiring R] {n₁ n₂ : ℕ}
    {g₁ : Matrix.GeneralLinearGroup (Fin n₁) R}
    {g₂ : Matrix.GeneralLinearGroup (Fin n₂) R} :
    StableGL.of g₁ = StableGL.of g₂ ↔
      ∃ (k : ℕ) (f₁ : n₁ ⟶ k) (f₂ : n₂ ⟶ k),
        (finiteGLDiagram.obj (SemiRingCat.of R)).map f₁ g₁ =
        (finiteGLDiagram.obj (SemiRingCat.of R)).map f₂ g₂ := by
  constructor
  · intro h
    have hι : (finiteGLDiagram.obj (SemiRingCat.of R) ⋙ forget GrpCat).ιColimitType n₁ g₁ =
        (finiteGLDiagram.obj (SemiRingCat.of R) ⋙ forget GrpCat).ιColimitType n₂ g₂ := h
    exact (Functor.ιColimitType_eq_iff_of_isFiltered _ _ _).mp hι
  · rintro ⟨k, f₁, f₂, h⟩
    exact GrpCat.FilteredColimits.G.mk_eq
      (F := finiteGLDiagram.obj (SemiRingCat.of R))
      ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ⟨k, f₁, f₂, h⟩

theorem StableGL.map_of {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.functor.map (SemiRingCat.ofHom f) (StableGL.of g) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  have h := GrpCat.FilteredColimits.colimitMap_mk
    (D₁ := finiteGLDiagram.obj (SemiRingCat.of R))
    (D₂ := finiteGLDiagram.obj (SemiRingCat.of S))
    (α := finiteGLDiagram.map (SemiRingCat.ofHom f)) n g
  simp only [finiteGLDiagram_map_app_ofHom] at h
  exact h

/-- Functoriality on a stable generator in its filtered-colimit normal form.
The named `map_of` equation retains its original explicit-rewrite interface. -/
@[simp]
theorem StableGL.map_G_mk {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.functor.map (SemiRingCat.ofHom f)
        (GrpCat.FilteredColimits.G.mk
          (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩) =
      GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of S))
        ⟨n, Matrix.GeneralLinearGroup.mapRingHom f g⟩ :=
  StableGL.map_of f g

end AlgebraicKTheory

end
