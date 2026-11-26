/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`
and
`P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`
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

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The local criterion for flatness

Let `R` be a Noetherian ring, `S` a Noetherian local `R`-algebra, `M` a finite `S`-module and `p`
the contraction of the maximal ideal of `S` to `R`. If `p ⊗[R] M → R ⊗[R] M` is injective, then
`M` is flat over `R`.

## Main results

* `Module.flat_of_comap_maximalIdeal_rTensor_injective`

See also `Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero`
in `MathlibExt.RingTheory.LocalRing.FlatTower`, the form of the criterion with a vanishing `Tor₁`
for a local homomorphism of Noetherian local rings in one universe.

## References

* [Stacks Project, Lemma 10.99.7 (Tag 00MK)](https://stacks.math.columbia.edu/tag/00MK)
-/

@[expose] public section

open TensorProduct LinearMap

namespace LocalFlatnessCriterion

universe u v

noncomputable section

section KernelTransfer

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

private theorem lTensor_injective_of_cover
    {N₁ N₂ G L K : Type*} [AddCommGroup N₁] [AddCommGroup N₂] [Module R N₁] [Module R N₂]
    [AddCommGroup G] [AddCommGroup L] [Module R G] [Module R L] [AddCommGroup K] [Module R K]
    {f : N₁ →ₗ[R] N₂} {v : G →ₗ[R] N₂} {i : L →ₗ[R] G} {u : L →ₗ[R] N₁}
    {k : K →ₗ[R] G} {ι' : K →ₗ[R] L}
    (hv : Function.Surjective v) (hu : Function.Surjective u)
    (hcomm : v ∘ₗ i = f ∘ₗ u) (hk : Function.Exact k v)
    (h1 : i ∘ₗ ι' = k) (h2 : u ∘ₗ ι' = 0)
    (hi : Function.Injective (i.lTensor M)) :
    Function.Injective (f.lTensor M) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective M hu x
  have hy : (v.lTensor M) ((i.lTensor M) y) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hx]
  have hex := lTensor_exact M hk hv
  obtain ⟨w, hw⟩ := (hex _).mp hy
  have hzero : (i.lTensor M) (y - (ι'.lTensor M) w) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply (f := i.lTensor M), ← LinearMap.lTensor_comp, h1, hw,
      sub_self]
  have hy0 : y - (ι'.lTensor M) w = 0 := hi (by rw [hzero, map_zero])
  have : y = (ι'.lTensor M) w := by rwa [sub_eq_zero] at hy0
  rw [this, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h2, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

private def cover (N₂ : Type*) [AddCommGroup N₂] [Module R N₂] :
    (N₂ →₀ R) →ₗ[R] N₂ :=
  Finsupp.linearCombination R (id : N₂ → N₂)

private theorem cover_surjective (N₂ : Type*) [AddCommGroup N₂] [Module R N₂] :
    Function.Surjective (cover (R := R) N₂) :=
  Finsupp.linearCombination_id_surjective R N₂

private theorem lTensor_injective_of_comap_cover
    {N₁ N₂ : Type*} [AddCommGroup N₁] [AddCommGroup N₂] [Module R N₁] [Module R N₂]
    (f : N₁ →ₗ[R] N₂) (hf : Function.Injective f)
    (hL : Function.Injective
      (((LinearMap.range f).comap (cover (R := R) N₂)).subtype.lTensor M)) :
    Function.Injective (f.lTensor M) := by
  classical
  set v := cover (R := R) N₂ with hv_def
  set L := (LinearMap.range f).comap v with hL_def
  have hv : Function.Surjective v := cover_surjective N₂
  let e := LinearEquiv.ofInjective f hf
  have he : ∀ y : LinearMap.range f, f (e.symm y) = y := fun y => by
    have := LinearEquiv.ofInjective_apply f (h := hf) (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  let u₀ : L →ₗ[R] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (v.domRestrict L) (fun l => l.2)
  let u : L →ₗ[R] N₁ := e.symm.toLinearMap ∘ₗ u₀
  have hu_apply : ∀ l : L, f (u l) = v l := fun l => by
    change f (e.symm (u₀ l)) = v l
    rw [he]
    rfl
  have hcomm : v ∘ₗ L.subtype = f ∘ₗ u := by
    ext l
    simp [hu_apply]
  have hu : Function.Surjective u := by
    intro n
    obtain ⟨g, hg⟩ := hv (f n)
    refine ⟨⟨g, ?_⟩, hf ?_⟩
    · change v g ∈ LinearMap.range f
      exact ⟨n, hg.symm⟩
    · rw [hu_apply]
      exact hg
  have hker : LinearMap.ker v ≤ L := by
    intro g hg
    change v g ∈ LinearMap.range f
    rw [LinearMap.mem_ker] at hg
    rw [hg]
    exact zero_mem _
  refine lTensor_injective_of_cover (M := M) (G := (N₂ →₀ R)) (L := L)
    (K := LinearMap.ker v)
    (f := f) (v := v) (i := L.subtype) (u := u)
    (k := (LinearMap.ker v).subtype) (ι' := Submodule.inclusion hker) hv hu hcomm
    (LinearMap.exact_subtype_ker_map v) ?_ ?_ hL
  · ext; rfl
  · ext g
    apply hf
    rw [LinearMap.comp_apply, hu_apply]
    have : v g = 0 := g.2
    simp [this]

private theorem lTensor_mapRange_injective (I : Ideal R)
    (hI : Function.Injective (I.subtype.lTensor M)) (ι : Type*) :
    Function.Injective
      ((Finsupp.mapRange.linearMap (α := ι) I.subtype).lTensor M) := by
  classical
  let e₁ := TensorProduct.finsuppRight R R M I ι
  let e₂ := TensorProduct.finsuppRight R R M R ι
  have key : ∀ x, e₂ (((Finsupp.mapRange.linearMap (α := ι) I.subtype).lTensor M) x) =
      Finsupp.mapRange.linearMap (I.subtype.lTensor M) (e₁ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m z =>
      ext i
      simp [e₁, e₂, TensorProduct.finsuppRight_apply_tmul_apply]
    | add x y hx hy => simp [map_add, hx, hy]
  intro x y hxy
  have := congrArg e₂ hxy
  rw [key, key] at this
  have h2 : e₁ x = e₁ y :=
    Finsupp.mapRange_injective _ (map_zero _) hI this
  exact e₁.injective h2

variable (R M) in
private def TorVanish (N : Type u) [AddCommGroup N] [Module R N] : Prop :=
  ∀ ⦃N₁ N₂ : Type u⦄ [AddCommGroup N₁] [AddCommGroup N₂] [Module R N₁] [Module R N₂]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    Function.Injective (f.lTensor M)

private theorem torVanish_of_torsion (I : Ideal R)
    (hsplit : ∀ ⦃Q₁ Q₂ : Type u⦄ [AddCommGroup Q₁] [AddCommGroup Q₂] [Module R Q₁]
      [Module R Q₂] (g : Q₁ →ₗ[R] Q₂), Function.Injective g →
      Module.IsTorsionBySet R Q₁ I → Module.IsTorsionBySet R Q₂ I →
      Function.Injective (g.lTensor M))
    (hI : Function.Injective (I.subtype.lTensor M))
    {N : Type u} [AddCommGroup N] [Module R N] (hN : Module.IsTorsionBySet R N I) :
    TorVanish R M N := by
  classical
  intro N₁ N₂ _ _ _ _ f g hf hg hfg
  apply lTensor_injective_of_comap_cover f hf
  set v := cover (R := R) N₂
  set L := (LinearMap.range f).comap v
  let e := LinearEquiv.refl R (N₂ →₀ R)
  let mr : (N₂ →₀ I) →ₗ[R] (N₂ →₀ R) := Finsupp.mapRange.linearMap I.subtype
  let κ : (N₂ →₀ I) →ₗ[R] (N₂ →₀ R) := e.symm.toLinearMap ∘ₗ mr
  have hκv : ∀ z, v (κ z) ∈ LinearMap.range f := by
    intro z
    rw [← hfg.linearMap_ker_eq]
    rw [LinearMap.mem_ker]
    have : v (κ z) = Finsupp.linearCombination R (id : N₂ → N₂) (mr z) := by
      change Finsupp.linearCombination R (id : N₂ → N₂) (e (e.symm (mr z))) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [this]
    simp only [mr, Finsupp.mapRange.linearMap_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
    rw [map_finsuppSum]
    apply Finset.sum_eq_zero
    intro n _
    simp only [id_eq, Submodule.coe_subtype, map_smul]
    exact hN (a := ⟨_, (z n).2⟩)
  let κ' : (N₂ →₀ I) →ₗ[R] L := LinearMap.codRestrict L κ hκv
  have hκ' : ∀ z, (κ' z : (N₂ →₀ R)) = κ z := fun z => rfl
  have hsmul_mem : ∀ (a : I) (x : (N₂ →₀ R)), (a : R) • x ∈ LinearMap.range κ := by
    intro a x
    refine ⟨Finsupp.mapRange (fun r => (⟨a * r, I.mul_mem_right r a.2⟩ : I))
      (by ext; simp) (e x), ?_⟩
    apply e.injective
    change e (e.symm (mr _)) = e ((a : R) • x)
    rw [LinearEquiv.apply_symm_apply, map_smul]
    ext n
    simp [mr]
  set K := LinearMap.range κ with hK
  have htorG : Module.IsTorsionBySet R ((N₂ →₀ R) ⧸ K) I := by
    rintro x ⟨a, ha⟩
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hsmul_mem ⟨a, ha⟩ x
  set QL : Submodule R ((N₂ →₀ R) ⧸ K) := Submodule.map K.mkQ L with hQL
  have htorL : Module.IsTorsionBySet R QL I := by
    rintro x a
    apply Subtype.ext
    exact htorG (x := (x : (N₂ →₀ R) ⧸ K)) (a := a)
  let qL : L →ₗ[R] QL :=
    LinearMap.codRestrict QL (K.mkQ ∘ₗ L.subtype) (fun l => Submodule.mem_map_of_mem l.2)
  have hqL : Function.Surjective qL := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  have hexact : Function.Exact κ' qL := by
    intro l
    constructor
    · intro hl
      have hl' : K.mkQ (l : (N₂ →₀ R)) = 0 := congrArg Subtype.val hl
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hl'
      obtain ⟨z, hz⟩ := hl'
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      change K.mkQ (κ z) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨z, rfl⟩
  have hsq : QL.subtype ∘ₗ qL = K.mkQ ∘ₗ L.subtype := by ext; rfl
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : (QL.subtype.lTensor M) ((qL.lTensor M) y) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsq,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hy, map_zero]
  have h2 : (qL.lTensor M) y = 0 :=
    hsplit (Q₁ := QL) (Q₂ := (N₂ →₀ R) ⧸ K) QL.subtype (Submodule.injective_subtype _)
      htorL htorG (by rw [h1, map_zero])
  have hex := lTensor_exact (N := L) (P := QL) M hexact hqL
  obtain ⟨w, hw⟩ := (hex _).mp h2
  have h3 : (κ.lTensor M) w = 0 := by
    have : κ = L.subtype ∘ₗ κ' := (LinearMap.subtype_comp_codRestrict _ _ _).symm
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hw, hy]
  have h3' : (mr.lTensor M) w = 0 := by
    apply (e.symm.lTensor M).injective
    rw [map_zero]
    have : κ.lTensor M = (e.symm.lTensor M).toLinearMap ∘ₗ mr.lTensor M := by
      rw [LinearEquiv.coe_lTensor, ← LinearMap.lTensor_comp]
    have h := congrArg (fun φ => φ w) this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    rw [← h, h3]
  have h4 : w = 0 := lTensor_mapRange_injective I hI N₂ (by rw [h3', map_zero])
  rw [← hw, h4, map_zero]

private theorem extension_step {N' : Type u} [AddCommGroup N'] [Module R N']
    (h' : TorVanish R M N') {G : Type u} [AddCommGroup G] [Module R G] (L L' : Submodule R G)
    (hLL' : L ≤ L') (ρ : L' →ₗ[R] N') (hρ : Function.Surjective ρ)
    (hexact : Function.Exact (Submodule.inclusion hLL') ρ)
    (hL' : Function.Injective (L'.subtype.lTensor M)) :
    Function.Injective (L.subtype.lTensor M) := by
  have hL : Function.Injective ((Submodule.inclusion hLL').lTensor M) :=
    h' (Submodule.inclusion hLL') ρ (Submodule.inclusion_injective hLL') hρ hexact
  have : L.subtype = L'.subtype ∘ₗ Submodule.inclusion hLL' := by ext; rfl
  rw [this, LinearMap.lTensor_comp]
  exact hL'.comp hL

private theorem ker_injective {N : Type u} [AddCommGroup N] [Module R N]
    (h : TorVanish R M N) {G : Type u} [AddCommGroup G] [Module R G] (φ : G →ₗ[R] N)
    (hφ : Function.Surjective φ) : Function.Injective ((LinearMap.ker φ).subtype.lTensor M) :=
  h (LinearMap.ker φ).subtype φ (Submodule.injective_subtype _) hφ
    (LinearMap.exact_subtype_ker_map φ)

private theorem torVanish_of_extension {N' N N'' : Type u} [AddCommGroup N'] [AddCommGroup N]
    [AddCommGroup N''] [Module R N'] [Module R N] [Module R N'']
    (ι : N' →ₗ[R] N) (π : N →ₗ[R] N'') (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hιπ : Function.Exact ι π)
    (h' : TorVanish R M N') (h'' : TorVanish R M N'') : TorVanish R M N := by
  classical
  intro N₁ N₂ _ _ _ _ f g hf hg hfg
  apply lTensor_injective_of_comap_cover f hf
  set v := cover (R := R) N₂
  set L := (LinearMap.range f).comap v
  let L' : Submodule R ((N₂ →₀ R)) := LinearMap.ker (π ∘ₗ g ∘ₗ v)
  have hLL' : L ≤ L' := by
    intro x hx
    have hx' : v x ∈ LinearMap.range f := hx
    rw [← hfg.linearMap_ker_eq, LinearMap.mem_ker] at hx'
    change π (g (v x)) = 0
    rw [hx', map_zero]
  have hsurj : Function.Surjective (π ∘ₗ g ∘ₗ v) :=
    hπ.comp (hg.comp (cover_surjective (R := R) N₂))
  have hL' : Function.Injective (L'.subtype.lTensor M) := ker_injective h'' _ hsurj
  let e := LinearEquiv.ofInjective ι hι
  have he : ∀ y : LinearMap.range ι, ι (e.symm y) = y := fun y => by
    have := LinearEquiv.ofInjective_apply ι (h := hι) (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hmem : ∀ l : L', g (v l) ∈ LinearMap.range ι := by
    intro l
    rw [← hιπ.linearMap_ker_eq, LinearMap.mem_ker]
    exact l.2
  let ρ₀ : L' →ₗ[R] LinearMap.range ι :=
    LinearMap.codRestrict (LinearMap.range ι) ((g ∘ₗ v).domRestrict L') hmem
  let ρ : L' →ₗ[R] N' := e.symm.toLinearMap ∘ₗ ρ₀
  have hρ_apply : ∀ l : L', ι (ρ l) = g (v l) := fun l => by
    change ι (e.symm (ρ₀ l)) = g (v l)
    rw [he]
    rfl
  have hρ : Function.Surjective ρ := by
    intro n
    obtain ⟨x, hx⟩ := (hg.comp (cover_surjective (R := R) N₂)) (ι n)
    refine ⟨⟨x, ?_⟩, hι ?_⟩
    · change π (g (v x)) = 0
      change π ((g ∘ v) x) = 0
      rw [hx]
      exact hιπ.apply_apply_eq_zero n
    · rw [hρ_apply]
      exact hx
  have hexact : Function.Exact (Submodule.inclusion hLL') ρ := by
    rw [LinearMap.exact_iff]
    ext l
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hl
      have : g (v l) = 0 := by rw [← hρ_apply, hl, map_zero]
      have hl' : (l : (N₂ →₀ R)) ∈ L := by
        change v l ∈ LinearMap.range f
        rw [← hfg.linearMap_ker_eq, LinearMap.mem_ker]
        exact this
      exact ⟨⟨l, hl'⟩, rfl⟩
    · rintro ⟨l₀, rfl⟩
      apply hι
      rw [hρ_apply, map_zero]
      have : v (l₀ : (N₂ →₀ R)) ∈ LinearMap.range f := l₀.2
      rw [← hfg.linearMap_ker_eq, LinearMap.mem_ker] at this
      exact this
  exact extension_step h' L L' hLL' ρ hρ hexact hL'

private theorem torVanish_of_subsingleton {N : Type u} [AddCommGroup N] [Module R N]
    [Subsingleton N] : TorVanish R M N := by
  intro N₁ N₂ _ _ _ _ f g hf hg hfg
  have hsurj : Function.Surjective f := by
    intro y
    have : g y = 0 := Subsingleton.elim _ _
    exact (hfg y).mp this
  let e := LinearEquiv.ofBijective f ⟨hf, hsurj⟩
  have : f.lTensor M = (e.lTensor M).toLinearMap := by
    ext; rfl
  rw [this]
  exact (e.lTensor M).injective

private theorem torVanish_of_torsion_pow (I : Ideal R)
    (hsplit : ∀ ⦃Q₁ Q₂ : Type u⦄ [AddCommGroup Q₁] [AddCommGroup Q₂] [Module R Q₁]
      [Module R Q₂] (g : Q₁ →ₗ[R] Q₂), Function.Injective g →
      Module.IsTorsionBySet R Q₁ I → Module.IsTorsionBySet R Q₂ I →
      Function.Injective (g.lTensor M))
    (hI : Function.Injective (I.subtype.lTensor M)) (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] [Module R N],
      Module.IsTorsionBySet R N (I ^ n : Ideal R) → TorVanish R M N := by
  induction n with
  | zero =>
    intro N _ _ hN
    have : Subsingleton N := by
      refine ⟨fun x y => ?_⟩
      have hx : (1 : R) • x = 0 := hN (a := ⟨1, by simp⟩)
      have hy : (1 : R) • y = 0 := hN (a := ⟨1, by simp⟩)
      rw [one_smul] at hx hy
      rw [hx, hy]
    exact torVanish_of_subsingleton
  | succ n ih =>
    intro N _ _ hN
    let N' : Submodule R N := I • ⊤
    have hN' : Module.IsTorsionBySet R N' (I ^ n : Ideal R) := by
      rintro ⟨x, hx⟩ ⟨a, ha⟩
      apply Subtype.ext
      change a • x = 0
      induction hx using Submodule.smul_induction_on' with
      | smul b hb y hy =>
        rw [smul_smul]
        have : a * b ∈ I ^ (n + 1) := by
          rw [pow_succ]
          exact Ideal.mul_mem_mul ha hb
        exact hN (a := ⟨_, this⟩)
      | add x hx y hy ihx ihy => rw [smul_add, ihx, ihy, add_zero]
    have hN'' : Module.IsTorsionBySet R (N ⧸ N') I := by
      rintro x ⟨a, ha⟩
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact torVanish_of_extension N'.subtype N'.mkQ (Submodule.injective_subtype _)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ N') (ih hN')
      (torVanish_of_torsion I hsplit hI hN'')

end KernelTransfer

section Tail

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

private theorem ker_le_range_of_torVanish (𝔞 J : Ideal R)
    (h : TorVanish R M (R ⧸ (𝔞 ⊔ J))) (x : M ⊗[R] 𝔞) (hx : (𝔞.subtype.lTensor M) x = 0) :
    x ∈ LinearMap.range ((Submodule.inclusion (inf_le_left : 𝔞 ⊓ J ≤ 𝔞)).lTensor M) := by
  have hinj : Function.Injective ((𝔞 ⊔ J).subtype.lTensor M) :=
    h (𝔞 ⊔ J).subtype (𝔞 ⊔ J).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hx1 : ((Submodule.inclusion (le_sup_left : 𝔞 ≤ 𝔞 ⊔ J)).lTensor M) x = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (𝔞 ⊔ J).subtype ∘ₗ Submodule.inclusion (le_sup_left : 𝔞 ≤ 𝔞 ⊔ J) = 𝔞.subtype := by
      ext; rfl
    rw [this, hx]
  let σ : (𝔞 × J : Type u) →ₗ[R] (𝔞 ⊔ J : Ideal R) :=
    (Submodule.inclusion (le_sup_left : 𝔞 ≤ 𝔞 ⊔ J)).coprod
      (Submodule.inclusion (le_sup_right : J ≤ 𝔞 ⊔ J))
  let τ : (𝔞 ⊓ J : Ideal R) →ₗ[R] (𝔞 × J : Type u) :=
    (Submodule.inclusion (inf_le_left : 𝔞 ⊓ J ≤ 𝔞)).prod
      (-(Submodule.inclusion (inf_le_right : 𝔞 ⊓ J ≤ J)))
  have hσ : Function.Surjective σ := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hτσ : Function.Exact τ σ := by
    intro y
    constructor
    · intro hy
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := y
      have hab : a + b = 0 := congrArg Subtype.val hy
      have hb' : b = -a := eq_neg_of_add_eq_zero_right hab
      subst hb'
      have haJ : a ∈ J := by simpa using J.neg_mem hb
      refine ⟨⟨a, ha, haJ⟩, ?_⟩
      ext <;> rfl
    · rintro ⟨⟨c, hc⟩, rfl⟩
      apply Subtype.ext
      change c + -c = 0
      rw [add_neg_cancel]
  have hex := lTensor_exact M hτσ hσ
  set ξ := ((LinearMap.inl R 𝔞 J).lTensor M) x with hξ
  have hξ0 : (σ.lTensor M) ξ = 0 := by
    rw [hξ, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : σ ∘ₗ LinearMap.inl R 𝔞 J = Submodule.inclusion (le_sup_left : 𝔞 ≤ 𝔞 ⊔ J) := by
      ext; simp [σ]
    rw [this, hx1]
  obtain ⟨ζ, hζ⟩ := (hex _).mp hξ0
  refine ⟨ζ, ?_⟩
  have h1 : ((LinearMap.fst R 𝔞 J).lTensor M) ξ = x := by
    rw [hξ, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.fst_comp_inl,
      LinearMap.lTensor_id, LinearMap.id_apply]
  have h2 : LinearMap.fst R 𝔞 J ∘ₗ τ = Submodule.inclusion (inf_le_left : 𝔞 ⊓ J ≤ 𝔞) := by
    ext; rfl
  rw [← h2, LinearMap.lTensor_comp, LinearMap.comp_apply, hζ, h1]

private theorem range_lTensor_inclusion_le_smul (𝔞 J 𝔟 : Ideal R) (h𝔟 : 𝔟 ≤ J * 𝔞) (hle : 𝔟 ≤ 𝔞) :
    LinearMap.range ((Submodule.inclusion hle).lTensor M) ≤
      (J • ⊤ : Submodule R (M ⊗[R] 𝔞)) := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul m b =>
    rw [LinearMap.lTensor_tmul]
    obtain ⟨b, hb⟩ := b
    have hb' : b ∈ J * 𝔞 := h𝔟 hb
    have key : ∀ (c : R) (hc : c ∈ J * 𝔞) (hc' : c ∈ 𝔞),
        m ⊗ₜ[R] (⟨c, hc'⟩ : 𝔞) ∈ (J • ⊤ : Submodule R (M ⊗[R] 𝔞)) := by
      intro c hc
      rw [← Ideal.smul_eq_mul] at hc
      induction hc using Submodule.smul_induction_on' with
      | smul r hr n hn =>
        intro hc'
        have : (⟨r • n, hc'⟩ : 𝔞) = r • (⟨n, hn⟩ : 𝔞) := Subtype.ext rfl
        rw [this, TensorProduct.tmul_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      | add c hc d hd ihc ihd =>
        intro hcd
        have hc𝔞 : c ∈ 𝔞 := Ideal.mul_le_right hc
        have hd𝔞 : d ∈ 𝔞 := Ideal.mul_le_right hd
        have : (⟨c + d, hcd⟩ : 𝔞) = ⟨c, hc𝔞⟩ + ⟨d, hd𝔞⟩ := Subtype.ext rfl
        rw [this, TensorProduct.tmul_add]
        exact Submodule.add_mem _ (ihc hc𝔞) (ihd hd𝔞)
    exact key b hb' (hle hb)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

variable {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]

private theorem finite_lTensor_ideal [IsNoetherianRing R] [Module.Finite S M] (𝔞 : Ideal R) :
    Module.Finite S (M ⊗[R] 𝔞) := by
  classical
  have h𝔞 : (⊤ : Submodule R 𝔞).FG := Module.Finite.fg_top
  obtain ⟨t, ht⟩ := h𝔞
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := S) (M := M))
  refine ⟨⟨(s ×ˢ t).image (fun p => p.1 ⊗ₜ[R] p.2), ?_⟩⟩
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | tmul m a =>
    have hm : m ∈ Submodule.span S (s : Set M) := by rw [hs]; exact Submodule.mem_top
    have ha : a ∈ Submodule.span R (t : Set 𝔞) := by rw [ht]; exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm =>
      induction ha using Submodule.span_induction with
      | mem a ha =>
        apply Submodule.subset_span
        simp only [Finset.coe_image, Finset.coe_product, Set.mem_image, Set.mem_prod,
          Prod.exists]
        exact ⟨m, a, ⟨hm, ha⟩, rfl⟩
      | zero => simp
      | add a b _ _ iha ihb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ iha ihb
      | smul r a _ iha =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
        exact Submodule.smul_mem _ _ iha
    | zero => simp
    | add m m' _ _ ihm ihm' => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ ihm ihm'
    | smul r m _ ihm =>
      rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ _ ihm
  | add x y hx hy => exact Submodule.add_mem _ hx hy

private theorem flat_of_torVanish_pow [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (I : Ideal R) (hIS : I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson)
    (hTV : ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N],
      Module.IsTorsionBySet R N (I ^ n : Ideal R) → TorVanish R M N) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro 𝔞
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (𝔞 : Submodule R R)
  have hAR : ∀ m : ℕ, 𝔞 ⊓ I ^ (m + c) ≤ I ^ m * 𝔞 := by
    intro m
    have h := hc (m + c) (by omega)
    rw [Nat.add_sub_cancel] at h
    intro y hy
    have hy' : y ∈ I ^ (m + c) • (⊤ : Submodule R R) ⊓ 𝔞 := by
      refine ⟨?_, hy.1⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hy.2
    rw [h] at hy'
    have : I ^ m • (I ^ c • (⊤ : Submodule R R) ⊓ 𝔞) ≤ I ^ m * 𝔞 := by
      rw [← Ideal.smul_eq_mul]
      exact Submodule.smul_mono le_rfl inf_le_right
    exact this hy'
  have hmem : ∀ m : ℕ, x ∈ (I ^ m • ⊤ : Submodule R (M ⊗[R] 𝔞)) := by
    intro m
    have htor : Module.IsTorsionBySet R (R ⧸ (𝔞 ⊔ I ^ (m + c))) (I ^ (m + c) : Ideal R) := by
      rintro y ⟨a, ha⟩
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
        exact Submodule.mem_sup_right (Ideal.mul_mem_right _ _ ha)
    have h1 := ker_le_range_of_torVanish 𝔞 (I ^ (m + c)) (hTV (m + c) _ htor) x hx
    have hle : 𝔞 ⊓ I ^ (m + c) ≤ I ^ m * 𝔞 := hAR m
    have hle' : I ^ m * 𝔞 ≤ 𝔞 := Ideal.mul_le_right
    have hfac : Submodule.inclusion (inf_le_left : 𝔞 ⊓ I ^ (m + c) ≤ 𝔞) =
        Submodule.inclusion hle' ∘ₗ Submodule.inclusion hle := by ext; rfl
    rw [hfac, LinearMap.lTensor_comp] at h1
    have h2 : x ∈ LinearMap.range ((Submodule.inclusion hle').lTensor M) :=
      LinearMap.range_comp_le_range _ _ h1
    exact range_lTensor_inclusion_le_smul 𝔞 (I ^ m) (I ^ m * 𝔞) le_rfl hle' h2
  have : Module.Finite S (M ⊗[R] 𝔞) := finite_lTensor_ideal 𝔞
  have hmemS : ∀ m : ℕ, x ∈ ((I.map (algebraMap R S)) ^ m • ⊤ : Submodule S (M ⊗[R] 𝔞)) := by
    intro m
    have key : ∀ y ∈ (I ^ m • ⊤ : Submodule R (M ⊗[R] 𝔞)),
        y ∈ ((I.map (algebraMap R S)) ^ m • ⊤ : Submodule S (M ⊗[R] 𝔞)) := by
      intro y hy
      induction hy using Submodule.smul_induction_on' with
      | smul r hr z _ =>
        rw [← algebraMap_smul S r z]
        apply Submodule.smul_mem_smul _ Submodule.mem_top
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hr
      | add y _ z _ ihy ihz => exact Submodule.add_mem _ ihy ihz
    exact key x (hmem m)
  have hKrull := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[R] 𝔞)
    (I.map (algebraMap R S)) (Ideal.jacobson_bot (R := S) ▸ hIS)
  have : x ∈ (⨅ i : ℕ, (I.map (algebraMap R S)) ^ i • ⊤ : Submodule S (M ⊗[R] 𝔞)) :=
    (Submodule.mem_iInf _).mpr hmemS
  rw [hKrull] at this
  exact (Submodule.mem_bot S).mp this

end Tail

section Split

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]

private theorem isLocalizedModule_id_of_units (T : Submonoid R)
    (hT : ∀ t : T, IsUnit (algebraMap R S t)) :
    IsLocalizedModule T (LinearMap.id : M →ₗ[R] M) where
  map_units t := by
    obtain ⟨w, hw⟩ := hT t
    rw [Module.End.isUnit_iff]
    have hsmul : ∀ m : M, (t : R) • m = (w : S) • m := fun m => by
      rw [hw, algebraMap_smul]
    constructor
    · intro a b hab
      have hab' : (t : R) • a = (t : R) • b := hab
      rw [hsmul, hsmul] at hab'
      have := congrArg (fun m => (↑w⁻¹ : S) • m) hab'
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this
    · intro b
      refine ⟨(↑w⁻¹ : S) • b, ?_⟩
      change (t : R) • ((↑w⁻¹ : S) • b) = b
      rw [hsmul, smul_smul, Units.mul_inv, one_smul]
  surj y := ⟨(y, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

private theorem isTorsionBySet_baseChange (p : Ideal R) [p.IsPrime] {Q : Type*} [AddCommGroup Q]
    [Module R Q] (hQ : Module.IsTorsionBySet R Q p) :
    Module.IsTorsionBySet (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map,
    ← Module.isTorsionBySet_iff_is_torsion_by_span]
  rintro x ⟨_, ⟨a, ha, rfl⟩⟩
  induction x using TensorProduct.inductionOn with
  | tmul b q =>
    change (algebraMap R _ a) • (b ⊗ₜ[R] q) = 0
    have : a • q = 0 := hQ (a := ⟨a, ha⟩)
    rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, this,
      TensorProduct.tmul_zero]
  | add x y hx hy =>
    change _ • (x + y) = (0 : Localization.AtPrime p ⊗[R] Q)
    rw [smul_add]
    change _ • x = (0 : Localization.AtPrime p ⊗[R] Q) at hx
    change _ • y = (0 : Localization.AtPrime p ⊗[R] Q) at hy
    rw [hx, hy, add_zero]

private theorem lTensor_injective_of_torsion (p : Ideal R) [p.IsPrime]
    (hunit : ∀ t : p.primeCompl, IsUnit (algebraMap R S t))
    {Q₁ Q₂ : Type*} [AddCommGroup Q₁] [AddCommGroup Q₂] [Module R Q₁] [Module R Q₂]
    (g : Q₁ →ₗ[R] Q₂) (hg : Function.Injective g)
    (h₂ : Module.IsTorsionBySet R Q₂ p) :
    Function.Injective (g.lTensor M) := by
  let Rp := Localization.AtPrime p
  have : IsLocalizedModule p.primeCompl (LinearMap.id : M →ₗ[R] M) :=
    isLocalizedModule_id_of_units (S := S) p.primeCompl hunit
  let : Module Rp M := IsLocalizedModule.module p.primeCompl (LinearMap.id : M →ₗ[R] M)
  have : IsScalarTower R Rp M :=
    IsLocalizedModule.isScalarTower_module p.primeCompl (LinearMap.id : M →ₗ[R] M)
  let gp : Rp ⊗[R] Q₁ →ₗ[Rp] Rp ⊗[R] Q₂ := g.baseChange Rp
  have hflat : Module.Flat R Rp := IsLocalization.flat Rp p.primeCompl
  have hgp : Function.Injective gp := Module.Flat.lTensor_preserves_injective_linearMap g hg
  have htor := isTorsionBySet_baseChange p h₂
  have : IsSemisimpleModule Rp (Rp ⊗[R] Q₂) := by
    let : Module (IsLocalRing.ResidueField Rp) (Rp ⊗[R] Q₂) := htor.module
    have : IsSemisimpleModule (IsLocalRing.ResidueField Rp) (Rp ⊗[R] Q₂) := inferInstance
    exact (Module.IsTorsionBySet.isSemisimpleModule_iff htor).mp this
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property gp hgp LinearMap.id
  have hinj : Function.Injective (gp.lTensor M) := by
    intro x y hxy
    have := congrArg (r.lTensor M) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr,
      LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.id_apply] at this
  let c₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp Rp M Q₁
  let c₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp Rp M Q₂
  have hnat : ∀ x, c₂ (gp.lTensor M x) = g.lTensor M (c₁ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m y =>
      induction y using TensorProduct.inductionOn with
      | tmul a q =>
        simp [c₁, c₂, gp, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  obtain ⟨x, rfl⟩ := c₁.surjective x
  obtain ⟨y, rfl⟩ := c₁.surjective y
  rw [← hnat, ← hnat] at hxy
  rw [hinj (c₂.injective hxy)]

end Split

private theorem flat_of_comap_lTensor_injective
    {R : Type u} {S : Type*} {M : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (h : Function.Injective
      (((IsLocalRing.maximalIdeal S).comap (algebraMap R S)).subtype.lTensor M)) :
    Module.Flat R M := by
  set p := (IsLocalRing.maximalIdeal S).comap (algebraMap R S) with hp
  have hunit : ∀ t : p.primeCompl, IsUnit (algebraMap R S t) := by
    intro t
    have ht : algebraMap R S t ∉ IsLocalRing.maximalIdeal S :=
      fun h' => t.2 (Ideal.mem_comap.mpr h')
    exact IsLocalRing.notMem_maximalIdeal.mp ht
  have hsplit : ∀ ⦃Q₁ Q₂ : Type u⦄ [AddCommGroup Q₁] [AddCommGroup Q₂] [Module R Q₁]
      [Module R Q₂] (g : Q₁ →ₗ[R] Q₂), Function.Injective g →
      Module.IsTorsionBySet R Q₁ p → Module.IsTorsionBySet R Q₂ p →
      Function.Injective (g.lTensor M) :=
    fun Q₁ Q₂ _ _ _ _ g hg _ h₂ => lTensor_injective_of_torsion (S := S) p hunit g hg h₂
  refine flat_of_torVanish_pow (S := S) p ?_
    (fun n N _ _ hN => torVanish_of_torsion_pow p hsplit h n hN)
  calc p.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S := Ideal.map_le_iff_le_comap.mpr le_rfl
    _ ≤ (⊥ : Ideal S).jacobson := IsLocalRing.maximalIdeal_le_jacobson _

end

end LocalFlatnessCriterion

/-- **Local criterion for flatness.** Let `R` be a Noetherian ring, `S` a Noetherian local
`R`-algebra, `M` a finite `S`-module and `p` the contraction of the maximal ideal of `S` to `R`. If
`p ⊗[R] M → R ⊗[R] M` is injective, then `M` is flat over `R`.

Source: [Stacks Project, Lemma 10.99.7 (Tag 00MK)](https://stacks.math.columbia.edu/tag/00MK),
stated there for a local homomorphism of Noetherian local rings, with the hypothesis that `Tor₁`
of the residue field of `R` and `M` vanishes. -/
public theorem Module.flat_of_comap_maximalIdeal_rTensor_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M := by
  subst hp
  exact LocalFlatnessCriterion.flat_of_comap_lTensor_injective
    (S := S) ((LinearMap.lTensor_inj_iff_rTensor_inj M _).mpr h)
