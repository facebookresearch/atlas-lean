/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Artinian.Module

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem finrank_eq_mul_of_rankAtStalk_eq
    (K B C : Type u) [Field K] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra B C] [Algebra K C] [IsScalarTower K B C]
    [Module.Finite K B] [Module.Finite B C] [Module.Flat B C]
    (m : ℕ) (h : ∀ p : PrimeSpectrum B, Module.rankAtStalk (R := B) C p = m) :
    Module.finrank K C = m * Module.finrank K B := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : Subsingleton C := Module.subsingleton B C
    simp [Module.finrank_zero_of_subsingleton]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  have hfree : Module.Free B C := by
    refine Module.free_of_flat_of_finrank_eq (R := B) (M := C) m fun P => ?_
    haveI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    have e := (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ P.asIdeal)
      P.asIdeal.ResidueField P.asIdeal.ResidueField C)
    have h1 : Module.finrank P.asIdeal.ResidueField
        (P.asIdeal.ResidueField ⊗[B ⧸ P.asIdeal] ((B ⧸ P.asIdeal) ⊗[B] C)) =
        Module.finrank (B ⧸ P.asIdeal) ((B ⧸ P.asIdeal) ⊗[B] C) :=
      Module.finrank_baseChange
    rw [← h1, LinearEquiv.finrank_eq e, Ideal.finrank_fiber_eq_rankAtStalk]
    exact h ⟨P.asIdeal, inferInstance⟩
  have hrk : Module.finrank B C = m := by
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum B) := inferInstance
    have := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := B) (M := C)) p
    rw [h p] at this
    exact this.symm
  rw [← Module.finrank_mul_finrank K B C, hrk, mul_comm]

private theorem finrank_comp_SpecMap {K : Type u} [Field K] {B C : CommRingCat.{u}}
    (ψ : CommRingCat.of K ⟶ B) (φ : B ⟶ C)
    [IsFinite (Spec.map ψ)] [Flat (Spec.map ψ)] [IsFinite (Spec.map φ)] [Flat (Spec.map φ)]
    (m : ℕ) (hf : ∀ y, (Spec.map φ).finrank y = m) (z : Spec (CommRingCat.of K)) :
    (Spec.map φ ≫ Spec.map ψ).finrank z = m * (Spec.map ψ).finrank z := by
  have hψ₁ : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).mp inferInstance
  have hψ₂ : ψ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hφ₁ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have hφ₂ : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hc₁ : (ψ ≫ φ).hom.Finite := hφ₁.comp hψ₁
  have hc₂ : (ψ ≫ φ).hom.Flat := hψ₂.comp hφ₂
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank hc₁ hc₂,
    Scheme.Hom.finrank_SpecMap_eq_finrank hψ₁ hψ₂]
  simp_rw [Scheme.Hom.finrank_SpecMap_eq_finrank hφ₁ hφ₂] at hf
  letI : Algebra K B := ψ.hom.toAlgebra
  letI : Algebra B C := φ.hom.toAlgebra
  letI : Algebra K C := (ψ ≫ φ).hom.toAlgebra
  haveI : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite K B := hψ₁
  haveI : Module.Finite B C := hφ₁
  haveI : Module.Flat B C := hφ₂
  change Module.rankAtStalk (R := K) C z = m * Module.rankAtStalk (R := K) B z
  have hf' : ∀ y : PrimeSpectrum B, Module.rankAtStalk (R := B) C y = m := hf
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  exact finrank_eq_mul_of_rankAtStalk_eq K B C m hf'

private theorem finrank_comp_right_of_isIso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Y')
    [IsIso e] [IsFinite f] [Flat f] (y : Y) : (f ≫ e).finrank (e y) = f.finrank y := by
  have sq : IsPullback (𝟙 X) (f ≫ e) f (inv e) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
  congr 1
  simp [← Scheme.Hom.comp_apply]

private theorem finrank_comp_of_field {X Y : Scheme.{u}} (K : Type u) [Field K] (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of K)) [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (m : ℕ) (hf : ∀ y, f.finrank y = m) (z : Spec (CommRingCat.of K)) :
    (f ≫ g).finrank z = m * g.finrank z := by
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of K ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ g)
  let φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  have hg : g = Y.isoSpec.hom ≫ Spec.map ψ := by simp [ψ]
  have hφ : X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom = Spec.map φ := by simp [φ]
  have hfg : f ≫ g = X.isoSpec.hom ≫ (Spec.map φ ≫ Spec.map ψ) := by
    rw [← hφ]; simp [hg]
  haveI : IsFinite (Spec.map ψ) := by
    have : Spec.map ψ = Y.isoSpec.inv ≫ g := by simp [ψ]
    rw [this]; infer_instance
  haveI : Flat (Spec.map ψ) := by
    have : Spec.map ψ = Y.isoSpec.inv ≫ g := by simp [ψ]
    rw [this]; infer_instance
  haveI : IsFinite (Spec.map φ) := by rw [← hφ]; infer_instance
  haveI : Flat (Spec.map φ) := by rw [← hφ]; infer_instance
  have hf' : ∀ y, (Spec.map φ).finrank y = m := by
    intro y
    rw [← hφ, Scheme.Hom.finrank_comp_left_of_isIso]
    obtain ⟨y, rfl⟩ : ∃ y₀ : Y, Y.isoSpec.hom y₀ = y :=
      ⟨Y.isoSpec.inv y, by simp [← Scheme.Hom.comp_apply]⟩
    rw [finrank_comp_right_of_isIso]
    exact hf y
  rw [hfg, hg, Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.hom,
    Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.hom]
  exact finrank_comp_SpecMap ψ φ m hf' z

/-- The fibre rank of a composite of finite flat morphisms multiplies: if
`f` has constant fibre rank `m`, then at every point `z` the composite
`f ≫ g` has rank `m` times the rank of `g` at `z`. -/
public theorem Scheme.Hom.finrank_comp_of_finrank_eq_const
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f]
    [IsFinite g] [Flat g] (m : ℕ) (hf : ∀ y : Y, f.finrank y = m) (z : Z) :
    (f ≫ g).finrank z = m * g.finrank z := by
  let i := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (Z.residueField z)) := inferInstance
  have hz : i pt = z := Z.fromSpecResidueField_apply z pt
  let f' := pullback.snd f (pullback.fst g i)
  let g' := pullback.snd g i
  have hf' : ∀ y, f'.finrank y = m := fun y => by
    rw [Scheme.Hom.finrank_pullback_snd]; exact hf _
  have key := finrank_comp_of_field (Z.residueField z) f' g' m hf' pt
  have e : f' ≫ g' = (pullbackRightPullbackFstIso g i f).hom ≫ pullback.snd (f ≫ g) i := by
    simp [f', g']
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_snd,
    Scheme.Hom.finrank_pullback_snd, hz] at key
  exact key

end AlgebraicGeometry
