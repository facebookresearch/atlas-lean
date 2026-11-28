/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.PIDGlobalDimension
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Vanishing of higher Tor over a principal ideal domain

Let `R : Type u` be a commutative principal ideal domain. Modules in `ModuleCat.{u} R` admit
projective resolutions of length at most one. Hence the tensor-derived functor vanishes in
every degree `p ≥ 2` for any pair of modules in this category.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace CategoryTheory

/-- Tor vanishes in degrees at least two over a PID.

For a commutative domain `R` with every ideal principal, modules `A` and `D` in `ModuleCat.{u}
R`, and a natural `p` satisfying `2 ≤ p`, the module `Tor_p^R(A, D)` is zero. -/
theorem isZero_Tor_of_two_le_of_pid
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (A D : ModuleCat.{u} R) (p : ℕ) (hp : 2 ≤ p) :
    IsZero
      (((CategoryTheory.Tor (ModuleCat.{u} R) p).obj A).obj D) := by
  let S := D.projectiveShortComplex
  have hS : S.ShortExact := D.shortExact_projectiveShortComplex
  have hD : HasProjectiveDimensionLT D 2 :=
    ModuleCat.hasProjectiveDimensionLE_one_of_isPrincipalIdealRing D
  have hS₁ : HasProjectiveDimensionLT S.X₁ 1 :=
    (hS.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).1 hD
  let _ : HasProjectiveDimensionLT S.X₁ 1 := hS₁
  let _ : Projective S.X₁ := by infer_instance
  let Q := ProjectiveResolution.ofPresentation S hS
  let F := (tensoringLeft (ModuleCat.{u} R)).obj A
  have hQ : IsZero (Q.complex.X p) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp
    change IsZero (ProjectiveResolution.presentationX S (2 + n))
    rw [Nat.add_comm]
    change IsZero (0 : ModuleCat.{u} R)
    exact isZero_zero _
  have hMapped : IsZero
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).X p) :=
    F.map_isZero hQ
  have hHomology : IsZero
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology p) :=
    ShortComplex.isZero_homology_of_isZero_X₂
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).sc p)
        hMapped
  change IsZero ((F.leftDerived p).obj D)
  exact IsZero.of_iso hHomology (Q.isoLeftDerivedObj F p)

end CategoryTheory

end
