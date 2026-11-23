/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HenselianLocalRing_exists_algHom_lift_of_etale.lean` and
`P2M/Sol/S_HenselianLocalRing_exists_algHom_lift_of_etale.lean`
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

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Sections of étale algebras over Henselian rings

Over a Henselian local ring, an étale algebra has a section lifting any
residue-field point: first for standard étale pairs by Hensel's lemma,
then for standard étale algebras, then in general by localizing at a
suitable element.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace HenselianEtaleAux

private theorem standardEtalePair_residueSection_exists
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ret : P.Ring →ₐ[R] R,
      ∀ s : P.Ring, algebraMap R (ResidueField R) (ret s) = φ s := by
  have aeval_eq : ∀ (r : R) (p : R[X]), aeval r p = p.eval r :=
    fun r p => congrFun (coe_aeval_eq_eval r) p
  have hx₀ : P.HasMap (φ P.X) := StandardEtalePair.hasMap_X.map φ
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := R) (φ P.X)
  have ha₀' : algebraMap R (ResidueField R) a₀ = φ P.X := by
    rw [ResidueField.algebraMap_eq]; exact ha₀
  have hresAt : ∀ b : R, algebraMap R (ResidueField R) b = φ P.X →
      ∀ p : R[X], algebraMap R (ResidueField R) (p.eval b) = aeval (φ P.X) p := by
    intro b hb p
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hb]
  have unitOfRes : ∀ b : R, IsUnit (algebraMap R (ResidueField R) b) → IsUnit b := by
    intro b hb
    rw [← notMem_maximalIdeal]
    intro hbm
    exact hb.ne_zero (by
      rw [ResidueField.algebraMap_eq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hbm)
  have hmem : P.f.eval a₀ ∈ maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change algebraMap R (ResidueField R) (P.f.eval a₀) = 0
    rw [hresAt a₀ ha₀']; exact hx₀.1
  have hud : IsUnit ((derivative P.f).eval a₀) :=
    unitOfRes _ (hresAt a₀ ha₀' _ ▸ hx₀.isUnit_derivative_f)
  obtain ⟨a, haroot, hadiff⟩ :=
    HenselianLocalRing.is_henselian P.f P.monic_f a₀ hmem hud
  have hares : algebraMap R (ResidueField R) a = φ P.X := by
    rw [ResidueField.algebraMap_eq, ← ha₀]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a a₀).mpr hadiff
  have hmap : P.HasMap a := ⟨aeval_eq a P.f ▸ haroot,
    aeval_eq a _ ▸ unitOfRes _ (hresAt a hares _ ▸ hx₀.2)⟩
  refine ⟨P.lift a hmap, fun s => ?_⟩
  have hcomp : (Algebra.ofId R (ResidueField R)).comp (P.lift a hmap) = φ :=
    StandardEtalePair.hom_ext (by
      rw [AlgHom.comp_apply, StandardEtalePair.lift_X, Algebra.ofId_apply]; exact hares)
  have hs := AlgHom.congr_fun hcomp s
  rw [AlgHom.comp_apply, Algebra.ofId_apply] at hs; exact hs

private theorem isStandardEtale_residueSection_exists
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsStandardEtale R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  obtain ⟨Pres⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  obtain ⟨ret, hret⟩ :=
    standardEtalePair_residueSection_exists Pres.P (φ.comp Pres.equivRing.symm.toAlgHom)
  refine ⟨ret.comp Pres.equivRing.toAlgHom, fun s => ?_⟩
  have hthis := hret (Pres.equivRing s)
  simpa using hthis

private theorem etale_residueSection_exists_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime φ.toRingHom
  have : Algebra.IsEtaleAt R (RingHom.ker φ.toRingHom) := inferInstance
  obtain ⟨g, hg, hSE⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := S) (RingHom.ker φ.toRingHom)
  let _ := hSE
  have hu : IsUnit (φ.toRingHom g) :=
    isUnit_iff_ne_zero.mpr fun h0 => hg (RingHom.mem_ker.mpr h0)
  have hlift : ∀ s : S,
      IsLocalization.Away.lift (S := Localization.Away g) g hu
        (algebraMap S (Localization.Away g) s) = φ.toRingHom s :=
    fun s => IsLocalization.Away.lift_eq (S := Localization.Away g) g hu s
  let ψ : Localization.Away g →ₐ[R] ResidueField R :=
    { toRingHom := IsLocalization.Away.lift (S := Localization.Away g) g hu
      commutes' := fun r => by
        change IsLocalization.Away.lift (S := Localization.Away g) g hu
            (algebraMap R (Localization.Away g) r) = algebraMap R (ResidueField R) r
        rw [IsScalarTower.algebraMap_apply R S (Localization.Away g), hlift (algebraMap R S r)]
        exact φ.commutes r }
  obtain ⟨ret, hret⟩ := isStandardEtale_residueSection_exists (Localization.Away g) ψ
  refine ⟨ret.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), fun s => ?_⟩
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    hret (algebraMap S (Localization.Away g) s)]
  exact hlift s

end HenselianEtaleAux

/-- Over a Henselian local ring, an étale algebra has a section lifting any
residue-field point. -/
theorem HenselianLocalRing.exists_algHom_lift_of_etale
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ ψ : S →ₐ[R] R,
      ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s :=
  HenselianEtaleAux.etale_residueSection_exists_of_henselianLocalRing S φ
