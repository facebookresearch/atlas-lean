/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated.lean`,
`P2M/Sol/S_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated.lean`,
`Theorems/Thm_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_
of_isClosedImmersion_proj.lean`
and
`P2M/Sol/S_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_
of_isClosedImmersion_proj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicThickening
public import MathlibExt.AlgebraicGeometry.ProjSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import MathlibExt.AlgebraicGeometry.AdicThickeningIsIso

/-!
# Morphisms of projective schemes are determined by adic thickenings

Let `R` be a Noetherian `I`-adically complete ring. Two morphisms `ψ ψ' : X ⟶ Y` over `Spec R`
between closed subschemes of projective spaces over `R` are equal as soon as they agree on
every adic thickening of `X` along `I`. This is the uniqueness half of Grothendieck's
existence theorem; no algebraization (existence) statement is made here.

The proof uses that the equalizer of two morphisms into a separated scheme is represented by a
closed subscheme, and that a closed immersion inducing isomorphisms on all adic thickenings is
an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two morphisms `u v : T ⟶ H` over a separated morphism `q : H ⟶ S` are equalized by a closed
subscheme `Z ⟶ T`: a morphism `ψ : T' ⟶ T` satisfies `ψ ≫ u = ψ ≫ v` if and only if it factors
through `Z`. -/
theorem exists_isClosedImmersion_iff_comp_eq_of_isSeparated
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H)
    (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by
  refine ⟨pullback (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q),
    pullback.fst (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q), inferInstance,
    fun ψ => ⟨fun h => ?_, fun ⟨ψ', hψ'⟩ => ?_⟩⟩
  · refine ⟨pullback.lift ψ (ψ ≫ u) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, h]
  · have hc := pullback.condition (f := pullback.lift u v (hu.trans hv.symm))
      (g := pullback.diagonal q)
    have h1 := congrArg (fun φ => φ ≫ pullback.fst q q) hc
    have h2 := congrArg (fun φ => φ ≫ pullback.snd q q) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [← hψ', Category.assoc, Category.assoc, h1, h2]

/-- Let `R` be a Noetherian `I`-adically complete ring and let `X` and `Y` be closed subschemes
of projective spaces over `R`, with structure morphisms `f` and `g`. Two morphisms
`ψ ψ' : X ⟶ Y` over `Spec R` that agree after restriction to every adic thickening of `X`
along `I` are equal. -/
theorem eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hιX : IsClosedImmersion ιX) (hιXf : ιX ≫ ProjSpace.π R N = f)
    (N' : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R))
    (hιY : IsClosedImmersion ιY) (hιYg : ιY ≫ ProjSpace.π R N' = g)
    (ψ ψ' : X ⟶ Y) (hψ : ψ ≫ g = f) (hψ' : ψ' ≫ g = f)
    (h : ∀ n : ℕ, adicThickeningι f I n ≫ ψ = adicThickeningι f I n ≫ ψ') :
    ψ = ψ' := by
  have := hιX
  have := hιY
  have : IsSeparated g := by rw [← hιYg]; infer_instance
  obtain ⟨E, j, hj, hE⟩ :=
    exists_isClosedImmersion_iff_comp_eq_of_isSeparated g f ψ ψ' hψ hψ'
  have := hj
  have hs : ∀ n : ℕ, ∃ s : adicThickening f I n ⟶ E, s ≫ j = adicThickeningι f I n :=
    fun n => (hE (adicThickeningι f I n)).mp (h n)
  choose s hs using hs
  have hPX := isPullback_adicThickening f I
  have hPE := isPullback_adicThickening (j ≫ f) I
  have hw : ∀ n : ℕ, (adicThickeningι (j ≫ f) I n ≫ j) ≫ f =
      adicThickeningToBase (j ≫ f) I n ≫ adicThickeningBase I n := fun n => by
    rw [Category.assoc]; exact (hPE n).w
  let jn : ∀ n : ℕ, adicThickening (j ≫ f) I n ⟶ adicThickening f I n := fun n =>
    (hPX n).lift (adicThickeningι (j ≫ f) I n ≫ j) (adicThickeningToBase (j ≫ f) I n) (hw n)
  have hjn : ∀ n : ℕ, jn n ≫ adicThickeningι f I n = adicThickeningι (j ≫ f) I n ≫ j :=
    fun n => (hPX n).lift_fst _ _ _
  have hjn' : ∀ n : ℕ,
      jn n ≫ adicThickeningToBase f I n = adicThickeningToBase (j ≫ f) I n :=
    fun n => (hPX n).lift_snd _ _ _
  have hiso : ∀ n : ℕ, IsIso (jn n) := fun n => by
    have : Mono (jn n) := mono_of_mono_fac (hjn n)
    have hσw : s n ≫ (j ≫ f) = adicThickeningToBase f I n ≫ adicThickeningBase I n := by
      rw [← Category.assoc, hs, (hPX n).w]
    let σ : adicThickening f I n ⟶ adicThickening (j ≫ f) I n :=
      (hPE n).lift (s n) (adicThickeningToBase f I n) hσw
    have hσ₁ : σ ≫ adicThickeningι (j ≫ f) I n = s n := (hPE n).lift_fst _ _ _
    have hσ₂ : σ ≫ adicThickeningToBase (j ≫ f) I n = adicThickeningToBase f I n :=
      (hPE n).lift_snd _ _ _
    have hsec : σ ≫ jn n = 𝟙 _ := by
      apply (hPX n).hom_ext
      · rw [Category.assoc, hjn, ← Category.assoc, hσ₁, hs, Category.id_comp]
      · rw [Category.assoc, hjn', hσ₂, Category.id_comp]
    have : IsSplitEpi (jn n) := IsSplitEpi.mk' ⟨σ, hsec⟩
    exact isIso_of_mono_of_isSplitEpi (jn n)
  have : IsIso j :=
    isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
      I (j ≫ f) f N (j ≫ ιX) inferInstance (by rw [Category.assoc, hιXf]) N ιX hιX hιXf j rfl
      jn hjn hjn' hiso
  have hEq : j ≫ ψ = j ≫ ψ' := (hE j).mpr ⟨𝟙 E, Category.id_comp j⟩
  exact (cancel_epi j).mp hEq

end AlgebraicGeometry
