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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Finite
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-!
# Stable general linear groups via explicit filtered colimits

For a semiring `R`, the groups `GLₙ(R)` stabilize via the block inclusions
`diag(-, 1)`. The stable functor `SemiRingCat ⥤ GrpCat` sends `R` to the point
of Mathlib's `GrpCat.FilteredColimits.colimitCocone` of the `ℕ`-indexed
`finiteGLDiagram` at `R`. A coefficient map induces a natural transformation
of these diagrams; the stable functor applies `IsColimit.map` to that
transformation, using `GrpCat.FilteredColimits.colimitCoconeIsColimit` for the
source and the chosen cocone for the target. The type `StableGL R` is the
underlying type of this colimit, with finite representatives given by `G.mk`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicKTheory

/-- For semirings in a fixed universe, the stable functor sends `R` to the
filtered group colimit of `GL (Fin n) R` along `g ↦ diag(g, 1)`. A semiring homomorphism
induces the colimit map whose action on every finite representative is entrywise. -/
noncomputable def StableGL.functor : SemiRingCat.{u} ⥤ GrpCat.{u} where
  obj R := (GrpCat.FilteredColimits.colimitCocone (finiteGLDiagram.obj R)).pt
  map {R S} f := (GrpCat.FilteredColimits.colimitCoconeIsColimit
    (finiteGLDiagram.obj R)).map (GrpCat.FilteredColimits.colimitCocone
      (finiteGLDiagram.obj S)) (finiteGLDiagram.map f)
  map_id R := by
    apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (finiteGLDiagram.obj R)).hom_ext
    intro n
    rw [CategoryTheory.Functor.map_id, IsColimit.ι_map]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp {R S T} f g := by
    apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (finiteGLDiagram.obj R)).hom_ext
    intro n
    rw [CategoryTheory.Functor.map_comp, IsColimit.ι_map, ← Category.assoc, IsColimit.ι_map,
      Category.assoc, IsColimit.ι_map]
    rfl

/-- For a semiring `R`, `StableGL R` is the underlying type of the filtered group
colimit of the `GL (Fin n) R` under the successor maps `g ↦ diag(g, 1)`. -/
abbrev StableGL (R : Type u) [Semiring R] : Type u :=
  ↥(StableGL.functor.obj (SemiRingCat.of R))

/-- For each `n : ℕ`, the canonical maps `GL (Fin n) R → StableGL R` are the
rank-`n` legs of the chosen filtered colimit, natural in semirings `R` in a fixed universe. -/
noncomputable def StableGL.inclusion (n : ℕ) :
    finiteGLFunctor (n := n) ⟶ StableGL.functor where
  app R := (GrpCat.FilteredColimits.colimitCocone
    (F := finiteGLDiagram.obj R)).ι.app n
  naturality {R S} f := by
    have hι := IsColimit.ι_map
      (GrpCat.FilteredColimits.colimitCoconeIsColimit (finiteGLDiagram.obj R))
      (GrpCat.FilteredColimits.colimitCocone (finiteGLDiagram.obj S))
      (finiteGLDiagram.map f) n
    rw [finiteGLDiagram_map_app] at hι
    exact hι.symm

/-- For `n : ℕ` and a semiring `R` in the functor's universe, the component
of `StableGL.inclusion n` at `R` is the rank-`n` leg of the chosen filtered group colimit. -/
@[simp]
lemma StableGL.inclusion_app (n : ℕ) (R : SemiRingCat.{u}) :
    (StableGL.inclusion n).app R =
      (GrpCat.FilteredColimits.colimitCocone
        (F := finiteGLDiagram.obj R)).ι.app n :=
  rfl

/-- For a semiring `R`, the stable class of `g : GL (Fin n) R` is represented by
`G.mk ⟨n, g⟩` in the chosen filtered group colimit. -/
def StableGL.of {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) : StableGL R :=
  GrpCat.FilteredColimits.G.mk (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩

/-- For a semiring `R` and `g : GL (Fin n) R`, `StableGL.of g` is the actual
colimit representative `G.mk ⟨n, g⟩`. -/
@[simp]
lemma StableGL.of_eq_G_mk {R : Type u} [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of g =
      GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩ :=
  rfl

/-- For a semiring `R`, the rank-`n` inclusion sends `g : GL (Fin n) R`
to `StableGL.of g` in `StableGL R`. -/
lemma StableGL.inclusion_apply (n : ℕ) (R : Type u) [Semiring R]
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (StableGL.inclusion n).app (SemiRingCat.of R) g = StableGL.of g :=
  rfl

/-- For a semiring `R`, `n : ℕ`, and `g : GL (Fin n) R`, the
rank-`n` leg `ιₙ` of the chosen filtered group colimit satisfies `ιₙ(g) = G.mk ⟨n, g⟩`. -/
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

/-- For a semiring `R` and any `x : StableGL R`, there are `n : ℕ`
and `g : GL (Fin n) R` with `StableGL.of g = x`. -/
theorem StableGL.exists_finite_rep {R : Type u} [Semiring R] (x : StableGL R) :
    ∃ (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R), StableGL.of g = x := by
  have hsurj := Functor.ιColimitType_jointly_surjective
    (F := finiteGLDiagram.obj (SemiRingCat.of R) ⋙ forget GrpCat.{u}) x
  obtain ⟨n, g, hg⟩ := hsurj
  exact ⟨n, g, hg⟩

/-- For a semiring `R`, let `g₁ : GL (Fin n₁) R` and `g₂ : GL (Fin n₂) R`.
The classes `StableGL.of g₁` and `StableGL.of g₂` are equal if and only if there is a rank
`k ≥ n₁, n₂` at which the images of `g₁` and `g₂` under the two stabilization transitions
of `finiteGLDiagram` are equal in `GL (Fin k) R`. -/
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

/-- For semirings `R`, `S` in the same universe, `f : R →+* S`, and
`g : GL (Fin n) R`, the functor map sends `StableGL.of g` to
`StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g)`. -/
theorem StableGL.map_of {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.functor.map (SemiRingCat.ofHom f) (StableGL.of g) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  have h := ConcreteCategory.congr_hom
    ((StableGL.inclusion n).naturality (SemiRingCat.ofHom f)) g
  exact h.symm

/-- For semirings `R`, `S` in the same universe and `f : R →+* S`, let
`GLₙ(f)` be the entrywise map on rank-`n` general linear groups. On a representative
`g : GL (Fin n) R`, the stable functor map sends `G.mk ⟨n, g⟩` to `G.mk ⟨n, GLₙ(f)(g)⟩`. -/
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
