/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_
henselianLocalRing_of_isAlgClosed.lean`,
`P2M/Sol/S_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_
henselianLocalRing_of_isAlgClosed.lean`,
`Theorems/Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_
of_henselianLocalRing.lean`,
`P2M/Sol/S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_
of_henselianLocalRing.lean`,
`Theorems/Thm_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt.lean` and
`P2M/Sol/S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Henselian

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import MathlibExt.AlgebraicGeometry.Sections
import MathlibExt.RingTheory.Henselian.EtaleLift

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SmoothSectionsHenselianAux

open IsLocalRing TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

private theorem exists_lift_of_isStandardEtale_mvPolynomial
    {n : ℕ} (A : Type u) [CommRing A] [Algebra R A]
    [Algebra (MvPolynomial (Fin n) R) A] [IsScalarTower R (MvPolynomial (Fin n) R) A]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) R) A]
    (φ : A →ₐ[R] ResidueField R) :
    ∃ ψ : A →ₐ[R] R, ∀ a, algebraMap R (ResidueField R) (ψ a) = φ a := by
  let θ : MvPolynomial (Fin n) R →ₐ[R] ResidueField R :=
    φ.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) A)
  choose c hc using fun i : Fin n => residue_surjective (R := R) (θ (MvPolynomial.X i))
  let θ' : MvPolynomial (Fin n) R →ₐ[R] R := MvPolynomial.aeval c
  have hθ : ∀ r, algebraMap R (ResidueField R) (θ' r) = θ r := by
    intro r
    have h : (Algebra.ofId R (ResidueField R)).comp θ' = θ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [θ', hc]
    simpa using congrArg (fun g => g r) h
  letI iR : Algebra (MvPolynomial (Fin n) R) R := θ'.toRingHom.toAlgebra
  letI iK : Algebra (MvPolynomial (Fin n) R) (ResidueField R) :=
    ((algebraMap R (ResidueField R)).comp θ'.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin n) R) R (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ' : A →ₐ[MvPolynomial (Fin n) R] ResidueField R :=
    { φ.toRingHom with
      commutes' := fun r => by
        change φ (algebraMap (MvPolynomial (Fin n) R) A r) =
          algebraMap R (ResidueField R) (θ' r)
        exact (hθ r).symm }
  let T := R ⊗[MvPolynomial (Fin n) R] A
  let φT : T →ₐ[R] ResidueField R :=
    Algebra.TensorProduct.lift (Algebra.ofId R (ResidueField R)) φ' (fun _ _ => Commute.all _ _)
  haveI : Algebra.Etale R T := inferInstance
  obtain ⟨ψT, hψT⟩ := HenselianLocalRing.exists_algHom_lift_of_etale T φT
  let χ : A →+* R :=
    ψT.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        A →ₐ[MvPolynomial (Fin n) R] T).toRingHom
  have hχ : ∀ a, χ a = ψT ((1 : R) ⊗ₜ[MvPolynomial (Fin n) R] a) := fun a => rfl
  have h1 : ∀ r : R, ((1 : R) ⊗ₜ[MvPolynomial (Fin n) R] algebraMap R A r : T) =
      algebraMap R T r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) A r,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1
    change θ' (algebraMap R (MvPolynomial (Fin n) R) r) • (1 : R) = r
    rw [θ'.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, mul_one]
  let ψ : A →ₐ[R] R :=
    { χ with
      commutes' := fun r => by
        change χ (algebraMap R A r) = r
        rw [hχ, h1, ψT.commutes, Algebra.algebraMap_self, RingHom.id_apply] }
  refine ⟨ψ, fun a => ?_⟩
  change algebraMap R (ResidueField R) (χ a) = φ a
  rw [hχ, hψT]
  change Algebra.TensorProduct.lift _ _ _ ((1 : R) ⊗ₜ[MvPolynomial (Fin n) R] a) = φ a
  rw [Algebra.TensorProduct.lift_tmul]
  simp [φ']

private theorem exists_lift_of_isSmoothAt
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (φ : S →ₐ[R] ResidueField R)
    [(RingHom.ker φ).IsPrime] [Algebra.IsSmoothAt R (RingHom.ker φ)] :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R (ResidueField R) (ψ s) = φ s := by
  obtain ⟨f, hf, n, iA, hT, hE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := RingHom.ker φ)
  have hu : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
    rintro ⟨y, k, rfl⟩
    rw [map_pow]
    refine IsUnit.pow _ (Ne.isUnit ?_)
    simpa [RingHom.mem_ker] using hf
  let φf : Localization.Away f →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := Submonoid.powers f) hu
  have hφf : ∀ s, φf (algebraMap S (Localization.Away f) s) = φ s := fun s => by
    simp [φf, IsLocalization.liftAlgHom_apply]
  letI := iA
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away f) := hT
  haveI : Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := hE
  obtain ⟨ψf, hψf⟩ :=
    exists_lift_of_isStandardEtale_mvPolynomial (n := n) (Localization.Away f) φf
  refine ⟨ψf.comp (IsScalarTower.toAlgHom R S (Localization.Away f)), fun s => ?_⟩
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hψf, hφf]

private theorem exists_lift_of_smooth
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R (ResidueField R) (ψ s) = φ s := by
  haveI := RingHom.ker_isPrime φ
  exact exists_lift_of_isSmoothAt S φ

private theorem exists_section {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) ≫ s = x₀ := by
  let x : X := x₀.base (IsLocalRing.closedPoint (ResidueField R))
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let ι : Spec Γ(X, V) ⟶ X := hV.fromSpec
  have hrange : Set.range x₀.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint (ResidueField R) := Subsingleton.elim _ _
    rw [hV.range_fromSpec]
    exact hxV
  haveI : IsOpenImmersion ι := IsAffineOpen.isOpenImmersion_fromSpec hV
  let y₀ : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec Γ(X, V) :=
    IsOpenImmersion.lift ι x₀ hrange
  have hy₀ : y₀ ≫ ι = x₀ := IsOpenImmersion.lift_fac ι x₀ hrange
  let g : Spec Γ(X, V) ⟶ Spec (CommRingCat.of R) := ι ≫ f
  let φ : CommRingCat.of R ⟶ Γ(X, V) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  let π : Γ(X, V) ⟶ CommRingCat.of (ResidueField R) := Spec.preimage y₀
  have hπ : Spec.map π = y₀ := Spec.map_preimage y₀
  have hcomp : φ ≫ π = CommRingCat.ofHom (algebraMap R (ResidueField R)) := by
    rw [← Spec.map_inj, Spec.map_comp, hπ, hφ]
    change y₀ ≫ ι ≫ f = _
    rw [← Category.assoc, hy₀, hx₀]
  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hs
  letI : Algebra R Γ(X, V) := φ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, V) := hs
  let πa : Γ(X, V) →ₐ[R] ResidueField R :=
    { π.hom with
      commutes' := fun r => by
        change π.hom (φ.hom r) = algebraMap R (ResidueField R) r
        rw [← CommRingCat.comp_apply, hcomp]
        rfl }
  obtain ⟨ψ, hψ⟩ := exists_lift_of_smooth (R := R) Γ(X, V) πa
  have hψφ : φ ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 _ := by
    ext r
    change ψ (φ.hom r) = r
    exact ψ.commutes r
  have hψπ : CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom (algebraMap R (ResidueField R)) = π := by
    ext a
    exact hψ a
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι, ?_, ?_⟩
  · change Spec.map _ ≫ g = 𝟙 _
    rw [← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψπ, hπ, hy₀]

end SmoothSectionsHenselianAux

/-- Closed-fibre points of a smooth scheme over a Henselian local ring with
algebraically closed residue field that admit a section are dense.

For a smooth morphism `t : T ⟶ Spec R`, where `R` is Henselian local with
algebraically closed residue field, the points of the closed fibre of `T`
that are the value at the closed point of a section of `t` form a dense
subset of the closed fibre. The proof pulls back to the residue field,
where rational points are dense, and lifts those points to sections using
smoothness and the Henselian property. -/
public theorem
    AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] :
    Dense {x : {x : T // t.base x = IsLocalRing.closedPoint R} |
      ∃ s : Spec (CommRingCat.of R) ⟶ T, s ≫ t = 𝟙 _ ∧
        s.base (IsLocalRing.closedPoint R) = x.1} := by
  classical
  let κ := IsLocalRing.ResidueField R
  let res : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let ι : pullback t res ⟶ T := pullback.fst t res
  let tκ : pullback t res ⟶ Spec (CommRingCat.of κ) := pullback.snd t res
  have hrange_res : Set.range res.base = {IsLocalRing.closedPoint R} := by
    ext y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨z, rfl⟩
      exact IsLocalRing.PrimeSpectrum.comap_residue R z
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint κ, IsLocalRing.PrimeSpectrum.comap_residue R _⟩
  have hrange : Set.range ι.base = {x : T | t.base x = IsLocalRing.closedPoint R} := by
    change Set.range (pullback.fst t res).base = _
    rw [Scheme.Pullback.range_fst, hrange_res]
    rfl
  let S := {x : T // t.base x = IsLocalRing.closedPoint R}
  have hmem : ∀ y, t.base (ι.base y) = IsLocalRing.closedPoint R := fun y => by
    have h1 : ι.base y ∈ Set.range ι.base := ⟨y, rfl⟩
    rw [hrange] at h1
    exact h1
  let g : ↥(pullback t res) → S := fun y => ⟨ι.base y, hmem y⟩
  have hgc : Continuous g := ι.base.hom.continuous.subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨x, hx⟩
    have h1 : x ∈ Set.range ι.base := by rw [hrange]; exact hx
    obtain ⟨y, rfl⟩ := h1
    exact ⟨y, rfl⟩
  have hdense := AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed tκ
  refine Dense.mono ?_ ((hgs.denseRange).dense_image hgc hdense)
  rintro _ ⟨y, ⟨s₀, hs₀, rfl⟩, rfl⟩
  have hx₀ : (s₀ ≫ ι) ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs₀]
    rfl
  obtain ⟨s, hs, hs'⟩ :=
    SmoothSectionsHenselianAux.exists_section (R := R) t (s₀ ≫ ι) hx₀
  refine ⟨s, hs, ?_⟩
  change s (IsLocalRing.closedPoint R) = ι (s₀ (IsLocalRing.closedPoint κ))
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
        IsLocalRing.closedPoint R :=
    IsLocalRing.PrimeSpectrum.comap_residue R _
  calc s (IsLocalRing.closedPoint R)
      = s ((Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) := by rw [h1]
    _ = (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ s)
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (s₀ ≫ ι) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) := by rw [hs']
    _ = ι (s₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
        Scheme.Hom.comp_apply _ _ _
