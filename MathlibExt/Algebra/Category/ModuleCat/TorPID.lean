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

private noncomputable def zeroResolutionSuccessor
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    {X₀ X₁ : C} (f : X₁ ⟶ X₀) :
    Σ' (X₂ : C) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
  ⟨(0 : C), 0, by simp⟩

private noncomputable def pidResolutionComplex
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  let S := D.projectiveShortComplex
  ChainComplex.mk' S.X₂ S.X₁ S.f (fun f => zeroResolutionSuccessor f)

@[simp]
private theorem pidResolutionComplex_d_one_zero
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R) :
    (pidResolutionComplex D).d 1 0 = D.projectiveShortComplex.f := by
  simp [pidResolutionComplex]

private theorem isZero_pidResolutionComplex_X
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R) (n : ℕ) (hn : 2 ≤ n) :
    IsZero ((pidResolutionComplex D).X n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let S := D.projectiveShortComplex
  let e := ChainComplex.mk'XIso S.X₂ S.X₁ S.f
    (fun f => zeroResolutionSuccessor f) k
  have hTarget : IsZero
      (zeroResolutionSuccessor
        ((ChainComplex.mk' S.X₂ S.X₁ S.f
          (fun f => zeroResolutionSuccessor f)).d (k + 1) k)).fst := by
    dsimp only [zeroResolutionSuccessor]
    exact isZero_zero (ModuleCat.{u} R)
  have hZero : IsZero
      ((ChainComplex.mk' S.X₂ S.X₁ S.f
        (fun f => zeroResolutionSuccessor f)).X (k + 2)) :=
    IsZero.of_iso hTarget e
  simpa only [pidResolutionComplex, Nat.add_comm] using hZero

private noncomputable def pidResolutionAugmentation
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R) :
    pidResolutionComplex D ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj D :=
  (ChainComplex.toSingle₀Equiv (pidResolutionComplex D) D).symm
    ⟨D.projectiveShortComplex.g, by
      rw [pidResolutionComplex_d_one_zero]
      exact D.projectiveShortComplex.zero⟩

@[simp]
private theorem pidResolutionAugmentation_f_zero
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R) :
    (pidResolutionAugmentation D).f 0 = D.projectiveShortComplex.g :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private theorem pidResolutionComplex_exactAt_succ
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R) (n : ℕ) :
    (pidResolutionComplex D).ExactAt (n + 1) := by
  let S := D.projectiveShortComplex
  have hS : S.ShortExact := D.shortExact_projectiveShortComplex
  cases n with
  | zero =>
      rw [HomologicalComplex.exactAt_iff'
        (pidResolutionComplex D) 2 1 0 (by simp) (by simp)]
      let T := (pidResolutionComplex D).sc' 2 1 0
      change T.Exact
      apply (T.exact_iff_mono
        ((isZero_pidResolutionComplex_X D 2 (by omega)).eq_of_src _ _)).2
      change Mono ((pidResolutionComplex D).d 1 0)
      rw [pidResolutionComplex_d_one_zero]
      exact hS.mono_f
  | succ n =>
      exact HomologicalComplex.ExactAt.of_isZero
        (isZero_pidResolutionComplex_X D (n + 2) (by omega))

private noncomputable def pidProjectiveResolution
    {R : Type u} [CommRing R]
    (D : ModuleCat.{u} R)
    [Projective D.projectiveShortComplex.X₁] :
    ProjectiveResolution D where
  complex := pidResolutionComplex D
  projective n := by
    cases n with
    | zero =>
        change Projective D.projectiveShortComplex.X₂
        infer_instance
    | succ n =>
        cases n with
        | zero =>
            change Projective D.projectiveShortComplex.X₁
            infer_instance
        | succ n =>
            exact (isZero_pidResolutionComplex_X D (n + 2) (by omega)).projective
  π := pidResolutionAugmentation D
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff,
          ShortComplex.quasiIso_iff_of_zeros']
        · let S := D.projectiveShortComplex
          have hS : S.ShortExact := D.shortExact_projectiveShortComplex
          refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
            ⟨hS.exact, hS.epi_g⟩
          exact ShortComplex.isoMk (Iso.refl S.X₁) (Iso.refl S.X₂) (Iso.refl S.X₃)
            (by
              change 𝟙 S.X₁ ≫ S.f = S.f ≫ 𝟙 S.X₂
              simp)
            (by
              change 𝟙 S.X₂ ≫ S.g = S.g ≫ 𝟙 S.X₃
              simp)
        all_goals rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · exact pidResolutionComplex_exactAt_succ D n
        · exact ChainComplex.exactAt_succ_single_obj D n⟩

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
  let Q := pidProjectiveResolution D
  let F := (tensoringLeft (ModuleCat.{u} R)).obj A
  have hQ : IsZero (Q.complex.X p) :=
    isZero_pidResolutionComplex_X D p hp
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
