/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean`
and
`P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean`
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
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs

import MathlibExt.RingTheory.Flat.OfComapMaximalIdeal
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Noetherian approximation of flatness at a prime

Let `R₀` be a Noetherian ring, `B₀` a finite type `R₀`-algebra and `R` an `R₀`-algebra. If the
localization of `R ⊗[R₀] B₀` at a prime `P` is flat over `R`, then the same holds over some
finitely generated `R₀`-subalgebra `R₁` of `R`, at the prime of `R₁ ⊗[R₀] B₀` below `P`. The proof
uses the local criterion for flatness (`Module.flat_of_comap_maximalIdeal_rTensor_injective`).

## Main results

* `Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct`

## References

* [Stacks Project, Lemma 10.128.3 (Tag 00R6)](https://stacks.math.columbia.edu/tag/00R6)
-/

@[expose] public section

open TensorProduct LinearMap

noncomputable section

namespace FlatDescentFG

universe u v w

/-- The free module on the elements of `X`, as a type of its own so that its module structure
is built on its additive group. -/
private def FreeCover (A : Type u) [CommRing A] (X : Type*) : Type _ := X →₀ A

namespace FreeCover

variable (A : Type u) [CommRing A] (X : Type*)

private instance : AddCommGroup (FreeCover A X) := inferInstanceAs (AddCommGroup (X →₀ A))
private instance : Module A (FreeCover A X) := inferInstanceAs (Module A (X →₀ A))

private def equiv : FreeCover A X ≃ₗ[A] (X →₀ A) := LinearEquiv.refl A _

end FreeCover


section KernelGeneration

variable {A : Type u} [CommRing A] {D : Type v} [CommRing D] [Algebra A D]

private def cover (N₂ : Type*) [AddCommGroup N₂] [Module A N₂] : FreeCover A N₂ →ₗ[A] N₂ :=
  Finsupp.linearCombination A (id : N₂ → N₂) ∘ₗ (FreeCover.equiv A N₂).toLinearMap

private theorem cover_surjective (N₂ : Type*) [AddCommGroup N₂] [Module A N₂] :
    Function.Surjective (cover (A := A) N₂) :=
  (Finsupp.linearCombination_id_surjective A N₂).comp (FreeCover.equiv A N₂).surjective

private theorem baseChange_exact_of_surjective {N₁ N₂ N₃ : Type*} [AddCommGroup N₁]
    [AddCommGroup N₂] [AddCommGroup N₃] [Module A N₁] [Module A N₂] [Module A N₃] {f : N₁ →ₗ[A] N₂}
    {g : N₂ →ₗ[A] N₃} (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.baseChange D) (g.baseChange D) := by
  have := _root_.lTensor_exact D hfg hg
  rwa [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor] at this

private theorem baseChange_surjective_of_surjective {N₁ N₂ : Type*} [AddCommGroup N₁]
    [AddCommGroup N₂] [Module A N₁] [Module A N₂] {f : N₁ →ₗ[A] N₂} (hf : Function.Surjective f) :
    Function.Surjective (f.baseChange D) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact LinearMap.lTensor_surjective D hf

variable (D) in
private def torKer (J : Ideal A) : Submodule D (D ⊗[A] J) :=
  LinearMap.ker ((Submodule.subtype J).baseChange D)

private theorem mem_span_of_mapRange_baseChange_eq_zero (J : Ideal A) (ι : Type*)
    (w : D ⊗[A] (ι →₀ J))
    (hw : (Finsupp.mapRange.linearMap (α := ι) (Submodule.subtype J)).baseChange D w = 0) :
    w ∈ Submodule.span D (⋃ i, (Finsupp.lsingle i : J →ₗ[A] (ι →₀ J)).baseChange D ''
      (torKer D J : Set (D ⊗[A] J))) := by
  classical
  let e₁ := TensorProduct.finsuppRight A D D J ι
  let e₂ := TensorProduct.finsuppRight A D D A ι
  have key : ∀ x, e₂ ((Finsupp.mapRange.linearMap (α := ι) (Submodule.subtype J)).baseChange D
      x) = Finsupp.mapRange.linearMap ((Submodule.subtype J).baseChange D) (e₁ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m z =>
      ext i
      simp [e₁, e₂, TensorProduct.finsuppRight_apply_tmul_apply]
    | add x y hx hy => simp [map_add, hx, hy]
  have hcomp : ∀ i, e₁ w i ∈ torKer D J := by
    intro i
    have := congrArg e₂ hw
    rw [key, map_zero] at this
    have := DFunLike.congr_fun this i
    rw [torKer, LinearMap.mem_ker]
    simpa using this
  have hsingle : ∀ (i : ι) (t : D ⊗[A] J),
      e₁ ((Finsupp.lsingle i : J →ₗ[A] (ι →₀ J)).baseChange D t) = Finsupp.single i t := by
    intro i t
    induction t using TensorProduct.inductionOn with
    | tmul d j =>
      ext i'
      simp only [LinearMap.baseChange_tmul, e₁, TensorProduct.finsuppRight_apply_tmul_apply,
        Finsupp.lsingle_apply, Finsupp.single_apply]
      split_ifs <;> simp
    | add x y hx hy => simp [map_add, hx, hy]
  have hw_eq : w = (e₁ w).sum fun i t =>
      (Finsupp.lsingle i : J →ₗ[A] (ι →₀ J)).baseChange D t := by
    apply e₁.injective
    rw [map_finsuppSum]
    conv_lhs => rw [← Finsupp.sum_single (e₁ w)]
    apply Finsupp.sum_congr
    intro i _
    rw [hsingle]
  rw [hw_eq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨i, ⟨e₁ w i, hcomp i, rfl⟩⟩

private theorem exists_generators_of_ker_baseChange (J : Ideal A) (S : Submonoid D)
    (hrel : ∀ ⦃Q₁ Q₂ : Type (max u w)⦄ [AddCommGroup Q₁] [AddCommGroup Q₂] [Module A Q₁]
      [Module A Q₂] (g : Q₁ →ₗ[A] Q₂), Function.Injective g →
      Module.IsTorsionBySet A Q₂ J →
      ∀ x : D ⊗[A] Q₁, g.baseChange D x = 0 → ∃ s ∈ S, s • x = 0)
    {N₁ N₂ N : Type w} [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N]
    [Module A N₁] [Module A N₂] [Module A N]
    (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hN : Module.IsTorsionBySet A N J) :
    ∃ γ : N₂ → (J →ₗ[A] N₁), (∀ (n : N₂) (j : J), f (γ n j) = (j : A) • n) ∧
      ∀ x : D ⊗[A] N₁, f.baseChange D x = 0 → ∃ s ∈ S,
        s • x ∈ Submodule.span D (⋃ n, (γ n).baseChange D '' (torKer D J : Set (D ⊗[A] J))) := by
  classical
  set v := cover (A := A) N₂ with hv_def
  set L := (LinearMap.range f).comap v with hL_def
  have hv : Function.Surjective v := cover_surjective N₂
  let ef := LinearEquiv.ofInjective f hf
  have hef : ∀ y : LinearMap.range f, f (ef.symm y) = y := fun y => by
    have := LinearEquiv.ofInjective_apply f (h := hf) (ef.symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  let u₀ : L →ₗ[A] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (v.domRestrict L) (fun l => l.2)
  let u : L →ₗ[A] N₁ := ef.symm.toLinearMap ∘ₗ u₀
  have hu_apply : ∀ l : L, f (u l) = v l := fun l => by
    change f (ef.symm (u₀ l)) = v l
    rw [hef]
    rfl
  have hcomm : v ∘ₗ L.subtype = f ∘ₗ u := by
    ext l
    simp [hu_apply]
  have hu : Function.Surjective u := by
    intro n
    obtain ⟨x, hx⟩ := hv (f n)
    refine ⟨⟨x, ?_⟩, hf ?_⟩
    · change v x ∈ LinearMap.range f
      exact ⟨n, hx.symm⟩
    · rw [hu_apply]
      exact hx
  have hker : LinearMap.ker v ≤ L := by
    intro x hx
    change v x ∈ LinearMap.range f
    rw [LinearMap.mem_ker] at hx
    rw [hx]
    exact zero_mem _
  have hu_ker : u ∘ₗ Submodule.inclusion hker = 0 := by
    ext x
    apply hf
    rw [LinearMap.comp_apply, hu_apply]
    have : v x = 0 := x.2
    simp [this]
  let e := FreeCover.equiv A N₂
  let mr : (N₂ →₀ J) →ₗ[A] (N₂ →₀ A) := Finsupp.mapRange.linearMap (Submodule.subtype J)
  let κ : (N₂ →₀ J) →ₗ[A] FreeCover A N₂ := e.symm.toLinearMap ∘ₗ mr
  have hvκ : ∀ z, v (κ z) = Finsupp.linearCombination A (id : N₂ → N₂) (mr z) := by
    intro z
    change Finsupp.linearCombination A (id : N₂ → N₂) (e (e.symm (mr z))) = _
    rw [LinearEquiv.apply_symm_apply]
  have hκv : ∀ z, v (κ z) ∈ LinearMap.range f := by
    intro z
    rw [← hfg.linearMap_ker_eq, LinearMap.mem_ker, hvκ]
    simp only [mr, Finsupp.mapRange.linearMap_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_mapRange_index (fun _ => by simp), map_finsuppSum]
    apply Finset.sum_eq_zero
    intro n _
    simp only [id_eq, Submodule.coe_subtype, map_smul]
    exact hN (a := ⟨_, (z n).2⟩)
  let κ' : (N₂ →₀ J) →ₗ[A] L := LinearMap.codRestrict L κ hκv
  have hκκ' : κ = L.subtype ∘ₗ κ' := (LinearMap.subtype_comp_codRestrict _ _ _).symm
  have hsmul_mem : ∀ (a : J) (x : FreeCover A N₂), (a : A) • x ∈ LinearMap.range κ := by
    intro a x
    refine ⟨Finsupp.mapRange (fun r => (⟨a * r, J.mul_mem_right r a.2⟩ : J))
      (by ext; simp) (e x), ?_⟩
    apply e.injective
    change e (e.symm (mr _)) = e ((a : A) • x)
    rw [LinearEquiv.apply_symm_apply, map_smul]
    ext n
    simp [mr]
  set K := LinearMap.range κ with hK
  have htorG : Module.IsTorsionBySet A (FreeCover A N₂ ⧸ K) J := by
    rintro x ⟨a, ha⟩
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hsmul_mem ⟨a, ha⟩ x
  set QL : Submodule A (FreeCover A N₂ ⧸ K) := Submodule.map K.mkQ L with hQL
  let qL : L →ₗ[A] QL :=
    LinearMap.codRestrict QL (K.mkQ ∘ₗ L.subtype) (fun l => Submodule.mem_map_of_mem l.2)
  have hqL : Function.Surjective qL := by
    rintro ⟨_, ⟨l, hl, rfl⟩⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  have hexact : Function.Exact κ' qL := by
    intro l
    constructor
    · intro hl
      have hl' : K.mkQ (l : FreeCover A N₂) = 0 := congrArg Subtype.val hl
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hl'
      obtain ⟨z, hz⟩ := hl'
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      change K.mkQ (κ z) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨z, rfl⟩
  have hsq : QL.subtype ∘ₗ qL = K.mkQ ∘ₗ L.subtype := by ext; rfl
  let γ : N₂ → (J →ₗ[A] N₁) := fun n => u ∘ₗ κ' ∘ₗ Finsupp.lsingle n
  refine ⟨γ, ?_, ?_⟩
  · intro n j
    change f (u (κ' (Finsupp.single n j))) = (j : A) • n
    rw [hu_apply]
    change v (κ (Finsupp.single n j)) = (j : A) • n
    rw [hvκ]
    simp [mr]
  intro x hx
  obtain ⟨y₀, rfl⟩ := baseChange_surjective_of_surjective (D := D) hu x
  have hy₀ : (v.baseChange D) ((L.subtype.baseChange D) y₀) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomm, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx]
  obtain ⟨w₀, hw₀⟩ :=
    (baseChange_exact_of_surjective (D := D) (LinearMap.exact_subtype_ker_map v) hv _).mp hy₀
  set y := y₀ - ((Submodule.inclusion hker).baseChange D) w₀ with hy_def
  have huy : (u.baseChange D) y = (u.baseChange D) y₀ := by
    rw [hy_def, map_sub, ← LinearMap.comp_apply (f := u.baseChange D),
      ← LinearMap.baseChange_comp, hu_ker]
    simp
  have hy : (L.subtype.baseChange D) y = 0 := by
    rw [hy_def, map_sub, ← LinearMap.comp_apply (f := L.subtype.baseChange D),
      ← LinearMap.baseChange_comp]
    have : L.subtype ∘ₗ Submodule.inclusion hker = (LinearMap.ker v).subtype := by ext; rfl
    rw [this, hw₀, sub_self]
  have h1 : (QL.subtype.baseChange D) ((qL.baseChange D) y) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsq, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hy, map_zero]
  obtain ⟨s, hs, hsy⟩ := hrel (Q₁ := QL) (Q₂ := FreeCover A N₂ ⧸ K) QL.subtype
    (Submodule.injective_subtype _) htorG _ h1
  have h2 : (qL.baseChange D) (s • y) = 0 := by rw [map_smul, hsy]
  obtain ⟨w, hw⟩ := (baseChange_exact_of_surjective (D := D) hexact hqL _).mp h2
  have h3 : (κ.baseChange D) w = 0 := by
    rw [hκκ', LinearMap.baseChange_comp, LinearMap.comp_apply, hw, map_smul, hy, smul_zero]
  have h3' : (mr.baseChange D) w = 0 := by
    have hκe : mr = e.toLinearMap ∘ₗ κ := by
      ext z
      simp [κ]
    rw [hκe, LinearMap.baseChange_comp, LinearMap.comp_apply, h3, map_zero]
  have h4 := mem_span_of_mapRange_baseChange_eq_zero J N₂ w h3'
  refine ⟨s, hs, ?_⟩
  rw [← huy, ← map_smul, ← hw, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  have himage := Submodule.mem_map_of_mem (f := (u ∘ₗ κ').baseChange D) h4
  rw [Submodule.map_span] at himage
  refine Submodule.span_mono ?_ himage
  rintro _ ⟨_, hz, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨t, ht, rfl⟩ := hi
  refine Set.mem_iUnion.mpr ⟨i, ⟨t, ht, ?_⟩⟩
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

end KernelGeneration

section Stage

variable {R₀ : Type*} [CommRing R₀] (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀]
  (p₀ : Ideal R₀)

private def J (A : Type*) [CommRing A] [Algebra R₀ A] : Ideal A := p₀.map (algebraMap R₀ A)

private abbrev T (A : Type*) [CommRing A] [Algebra R₀ A] :
    Submodule (A ⊗[R₀] B₀) ((A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)) :=
  torKer (A ⊗[R₀] B₀) (J p₀ A)

private def Smon [p₀.IsPrime] (A : Type*) [CommRing A] [Algebra R₀ A] : Submonoid (A ⊗[R₀] B₀) :=
  (p₀.primeCompl).map (algebraMap R₀ (A ⊗[R₀] B₀))

private theorem isTorsionBySet_baseChange [p₀.IsPrime] {Q : Type*} [AddCommGroup Q] [Module R₀ Q]
    (hQ : Module.IsTorsionBySet R₀ Q p₀) :
    Module.IsTorsionBySet (Localization.AtPrime p₀) (Localization.AtPrime p₀ ⊗[R₀] Q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p₀)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map,
    ← Module.isTorsionBySet_iff_is_torsion_by_span]
  rintro x ⟨_, ⟨a, ha, rfl⟩⟩
  induction x using TensorProduct.inductionOn with
  | tmul b q =>
    change (algebraMap R₀ _ a) • (b ⊗ₜ[R₀] q) = 0
    have : a • q = 0 := hQ (a := ⟨a, ha⟩)
    rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, this,
      TensorProduct.tmul_zero]
  | add x y hx hy =>
    change _ • (x + y) = (0 : Localization.AtPrime p₀ ⊗[R₀] Q)
    rw [smul_add]
    change _ • x = (0 : Localization.AtPrime p₀ ⊗[R₀] Q) at hx
    change _ • y = (0 : Localization.AtPrime p₀ ⊗[R₀] Q) at hy
    rw [hx, hy, add_zero]

private theorem rTensor_ker_torsion [p₀.IsPrime] {Q₁ Q₂ : Type*} [AddCommGroup Q₁] [AddCommGroup Q₂]
    [Module R₀ Q₁] [Module R₀ Q₂] (g : Q₁ →ₗ[R₀] Q₂) (hg : Function.Injective g)
    (h₂ : Module.IsTorsionBySet R₀ Q₂ p₀) (y : Q₁ ⊗[R₀] B₀) (hy : g.rTensor B₀ y = 0) :
    ∃ s ∈ p₀.primeCompl, s • y = 0 := by
  let L₀ := Localization.AtPrime p₀
  have hflat : Module.Flat R₀ L₀ := IsLocalization.flat L₀ p₀.primeCompl
  let gp : L₀ ⊗[R₀] Q₁ →ₗ[L₀] L₀ ⊗[R₀] Q₂ := g.baseChange L₀
  have hgp : Function.Injective gp := Module.Flat.lTensor_preserves_injective_linearMap g hg
  have htor := isTorsionBySet_baseChange p₀ h₂
  have : IsSemisimpleModule L₀ (L₀ ⊗[R₀] Q₂) := by
    let : Module (IsLocalRing.ResidueField L₀) (L₀ ⊗[R₀] Q₂) := htor.module
    have : IsSemisimpleModule (IsLocalRing.ResidueField L₀) (L₀ ⊗[R₀] Q₂) := inferInstance
    exact (Module.IsTorsionBySet.isSemisimpleModule_iff htor).mp this
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property gp hgp LinearMap.id
  have hinj : Function.Injective ((g.lTensor L₀).rTensor B₀) := by
    have hcomp : (r.restrictScalars R₀) ∘ₗ g.lTensor L₀ = LinearMap.id := by
      ext a q
      have := congrArg (fun φ => φ (a ⊗ₜ[R₀] q)) hr
      simpa [gp] using this
    intro x x' hxx'
    have := congrArg ((r.restrictScalars R₀).rTensor B₀) hxx'
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp,
      LinearMap.rTensor_id, LinearMap.id_apply, LinearMap.id_apply] at this
  let α₁ := (TensorProduct.assoc R₀ L₀ Q₁ B₀).symm
  let α₂ := (TensorProduct.assoc R₀ L₀ Q₂ B₀).symm
  have hnat : ∀ z, α₂ ((g.rTensor B₀).lTensor L₀ z) = (g.lTensor L₀).rTensor B₀ (α₁ z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      induction x using TensorProduct.inductionOn with
      | tmul q b => simp [α₁, α₂]
      | add x x' hx hx' => simp only [TensorProduct.tmul_add, map_add, hx, hx']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hzero : (1 : L₀) ⊗ₜ[R₀] y = 0 := by
    apply α₁.injective
    apply hinj
    rw [← hnat, LinearMap.lTensor_tmul, hy, TensorProduct.tmul_zero, map_zero, map_zero,
      map_zero]
  have := (IsLocalizedModule.eq_zero_iff p₀.primeCompl
    (TensorProduct.mk R₀ L₀ (Q₁ ⊗[R₀] B₀) 1)).mp hzero
  obtain ⟨s, hs⟩ := this
  exact ⟨s, s.2, hs⟩

variable (A : Type u) [CommRing A] [Algebra R₀ A]

private def Φ (Q : Type*) [AddCommGroup Q] [Module A Q] [Module R₀ Q] [IsScalarTower R₀ A Q] :
    (A ⊗[R₀] B₀) ⊗[A] Q ≃ₗ[A] Q ⊗[R₀] B₀ :=
  (TensorProduct.comm A _ Q).trans (TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ A A Q B₀)

private theorem Φ_tmul {Q : Type*} [AddCommGroup Q] [Module A Q] [Module R₀ Q]
    [IsScalarTower R₀ A Q]
    (a : A) (b : B₀) (q : Q) : Φ B₀ A Q ((a ⊗ₜ[R₀] b) ⊗ₜ[A] q) = (a • q) ⊗ₜ[R₀] b := by
  simp [Φ, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

private theorem rel_torsion [p₀.IsPrime] {Q₁ Q₂ : Type*} [AddCommGroup Q₁] [AddCommGroup Q₂]
    [Module A Q₁] [Module A Q₂] (g : Q₁ →ₗ[A] Q₂) (hg : Function.Injective g)
    (h₂ : Module.IsTorsionBySet A Q₂ (J p₀ A)) (x : (A ⊗[R₀] B₀) ⊗[A] Q₁)
    (hx : g.baseChange (A ⊗[R₀] B₀) x = 0) : ∃ s ∈ Smon B₀ p₀ A, s • x = 0 := by
  let : Module R₀ Q₁ := Module.compHom Q₁ (algebraMap R₀ A)
  let : Module R₀ Q₂ := Module.compHom Q₂ (algebraMap R₀ A)
  have : IsScalarTower R₀ A Q₁ := ⟨fun r a q => by
    change ((r • a) • q : Q₁) = algebraMap R₀ A r • (a • q)
    rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower R₀ A Q₂ := ⟨fun r a q => by
    change ((r • a) • q : Q₂) = algebraMap R₀ A r • (a • q)
    rw [Algebra.smul_def, mul_smul]⟩
  have h₂' : Module.IsTorsionBySet R₀ Q₂ p₀ := by
    rintro q ⟨r, hr⟩
    change algebraMap R₀ A r • q = 0
    exact h₂ (a := ⟨_, Ideal.mem_map_of_mem _ hr⟩)
  let g' : Q₁ →ₗ[R₀] Q₂ := g.restrictScalars R₀
  have hnat : ∀ z, Φ B₀ A Q₂ (g.baseChange (A ⊗[R₀] B₀) z) = g'.rTensor B₀ (Φ B₀ A Q₁ z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul d q =>
      induction d using TensorProduct.inductionOn with
      | tmul a b => simp [Φ_tmul, g']
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hy : g'.rTensor B₀ (Φ B₀ A Q₁ x) = 0 := by rw [← hnat, hx, map_zero]
  obtain ⟨s, hs, hsx⟩ := rTensor_ker_torsion B₀ p₀ g' hg h₂' _ hy
  refine ⟨algebraMap R₀ _ s, ⟨s, hs, rfl⟩, ?_⟩
  apply (Φ B₀ A Q₁).injective
  rw [algebraMap_smul, map_zero]
  have : algebraMap R₀ A s • x = s • x := algebraMap_smul A s x
  rw [← this, map_smul, algebraMap_smul, hsx]

end Stage

section Transition

variable {R₀ : Type*} [CommRing R₀] (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀]
  (p₀ : Ideal R₀)
variable {A : Type*} [CommRing A] [Algebra R₀ A] {A' : Type*} [CommRing A'] [Algebra R₀ A']
  {A'' : Type*} [CommRing A''] [Algebra R₀ A'']

private def δ (h : A →ₐ[R₀] A') : A ⊗[R₀] B₀ →ₐ[R₀] A' ⊗[R₀] B₀ :=
  Algebra.TensorProduct.map h (AlgHom.id R₀ B₀)

@[scoped simp] private theorem δ_tmul (h : A →ₐ[R₀] A') (a : A) (b : B₀) :
    δ B₀ h (a ⊗ₜ[R₀] b) = h a ⊗ₜ[R₀] b := rfl

private theorem δ_comp (h : A →ₐ[R₀] A') (h' : A' →ₐ[R₀] A'') (d : A ⊗[R₀] B₀) :
    δ B₀ h' (δ B₀ h d) = δ B₀ (h'.comp h) d := by
  induction d using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem δ_smul (h : A →ₐ[R₀] A') (a : A) (d : A ⊗[R₀] B₀) :
    δ B₀ h (a • d) = h a • δ B₀ h d := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  rfl

private theorem mem_J_map (h : A →ₐ[R₀] A') {a : A} (ha : a ∈ J p₀ A) : h a ∈ J p₀ A' := by
  have : J p₀ A ≤ (J p₀ A').comap h.toRingHom := by
    rw [J, Ideal.map_le_iff_le_comap]
    intro r hr
    change h (algebraMap R₀ A r) ∈ J p₀ A'
    rw [h.commutes]
    exact Ideal.mem_map_of_mem _ hr
  exact this ha

private def ιJ (h : A →ₐ[R₀] A') : ↥(J p₀ A) →ₗ[R₀] ↥(J p₀ A') where
  toFun j := ⟨h j, mem_J_map p₀ h j.2⟩
  map_add' j j' := Subtype.ext (by simp)
  map_smul' r j := Subtype.ext (by simp [Algebra.smul_def])

@[scoped simp] private theorem coe_ιJ (h : A →ₐ[R₀] A') (j : J p₀ A) : (ιJ p₀ h j : A') = h j := rfl

private theorem ιJ_comp (h : A →ₐ[R₀] A') (h' : A' →ₐ[R₀] A'') (j : J p₀ A) :
    ιJ p₀ h' (ιJ p₀ h j) = ιJ p₀ (h'.comp h) j := rfl

private theorem ιJ_injective (h : A →ₐ[R₀] A') (hh : Function.Injective h) :
    Function.Injective (ιJ p₀ h) := by
  intro j j' hjj'
  apply Subtype.ext
  apply hh
  exact congrArg Subtype.val hjj'

private def ξ (h : A →ₐ[R₀] A') :
    (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A) →+ (A' ⊗[R₀] B₀) ⊗[A'] ↥(J p₀ A') :=
  TensorProduct.liftAddHom
    { toFun := fun d =>
        (TensorProduct.mk A' (A' ⊗[R₀] B₀) ↥(J p₀ A') (δ B₀ h d)).toAddMonoidHom.comp
          (ιJ p₀ h).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
    (by
      intro a d j
      change δ B₀ h (a • d) ⊗ₜ[A'] ιJ p₀ h j = δ B₀ h d ⊗ₜ[A'] ιJ p₀ h (a • j)
      have : ιJ p₀ h (a • j) = h a • ιJ p₀ h j := Subtype.ext (by simp)
      rw [δ_smul, this, TensorProduct.smul_tmul])

@[scoped simp] private theorem ξ_tmul (h : A →ₐ[R₀] A') (d : A ⊗[R₀] B₀) (j : J p₀ A) :
    ξ B₀ p₀ h (d ⊗ₜ[A] j) = δ B₀ h d ⊗ₜ[A'] ιJ p₀ h j := rfl

private theorem ξ_smul (h : A →ₐ[R₀] A') (c : A ⊗[R₀] B₀) (x : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)) :
    ξ B₀ p₀ h (c • x) = δ B₀ h c • ξ B₀ p₀ h x := by
  induction x using TensorProduct.inductionOn with
  | tmul d j =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, ξ_tmul, ξ_tmul, map_mul,
      TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem ξ_comp (h : A →ₐ[R₀] A') (h' : A' →ₐ[R₀] A'') (x : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)) :
    ξ B₀ p₀ h' (ξ B₀ p₀ h x) = ξ B₀ p₀ (h'.comp h) x := by
  induction x using TensorProduct.inductionOn with
  | tmul d j => rw [ξ_tmul, ξ_tmul, ξ_tmul, δ_comp, ιJ_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (A) in
private def ρ : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A) →ₗ[A ⊗[R₀] B₀] A ⊗[R₀] B₀ :=
  (TensorProduct.AlgebraTensorModule.rid A (A ⊗[R₀] B₀) (A ⊗[R₀] B₀)).toLinearMap ∘ₗ
    (Submodule.subtype (J p₀ A)).baseChange (A ⊗[R₀] B₀)

@[scoped simp] private theorem ρ_tmul (d : A ⊗[R₀] B₀) (j : J p₀ A) :
    ρ B₀ p₀ A (d ⊗ₜ[A] j) = (j : A) • d := by
  simp [ρ, TensorProduct.AlgebraTensorModule.rid_tmul]

private theorem mem_T_iff (x : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)) : x ∈ T B₀ p₀ A ↔ ρ B₀ p₀ A x = 0 := by
  simp only [T, torKer, LinearMap.mem_ker, ρ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff]

private theorem ρ_ξ (h : A →ₐ[R₀] A') (x : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)) :
    ρ B₀ p₀ A' (ξ B₀ p₀ h x) = δ B₀ h (ρ B₀ p₀ A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul d j => rw [ξ_tmul, ρ_tmul, ρ_tmul, coe_ιJ, δ_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem ξ_mem_T (h : A →ₐ[R₀] A') {x : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)} (hx : x ∈ T B₀ p₀ A) :
    ξ B₀ p₀ h x ∈ T B₀ p₀ A' := by
  rw [mem_T_iff] at hx ⊢
  rw [ρ_ξ, hx, map_zero]

private theorem δ_mem_Smon [p₀.IsPrime] (h : A →ₐ[R₀] A') {s : A ⊗[R₀] B₀} (hs : s ∈ Smon B₀ p₀ A) :
    δ B₀ h s ∈ Smon B₀ p₀ A' := by
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  exact ⟨s₀, hs₀, (AlgHom.commutes _ _).symm⟩

section Theta

variable (A A')
variable [Algebra A A'] [IsScalarTower R₀ A A']

private def δA : A ⊗[R₀] B₀ →ₐ[A] A' ⊗[R₀] B₀ :=
  Algebra.TensorProduct.map (Algebra.ofId A A') (AlgHom.id R₀ B₀)

@[scoped simp] private theorem δA_tmul (a : A) (b : B₀) :
    δA B₀ A A' (a ⊗ₜ[R₀] b) = algebraMap A A' a ⊗ₜ[R₀] b := rfl

private theorem δA_eq_δ (d : A ⊗[R₀] B₀) :
    δA B₀ A A' d = δ B₀ (IsScalarTower.toAlgHom R₀ A A') d := by
  induction d using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (N' : Type*) [AddCommGroup N'] [Module A' N'] [Module A N'] [IsScalarTower A A' N']

private def Θ : (A ⊗[R₀] B₀) ⊗[A] N' →ₗ[A] (A' ⊗[R₀] B₀) ⊗[A'] N' :=
  TensorProduct.lift
    (LinearMap.mk₂ A (fun d n => δA B₀ A A' d ⊗ₜ[A'] n)
      (fun d₁ d₂ n => by simp only [map_add, TensorProduct.add_tmul])
      (fun c d n => by
        rw [map_smul, TensorProduct.smul_tmul'])
      (fun d n₁ n₂ => by simp only [TensorProduct.tmul_add])
      (fun c d n => by
        rw [← algebraMap_smul A' c n, ← TensorProduct.smul_tmul, algebraMap_smul,
          TensorProduct.smul_tmul']))

variable {N'}

@[scoped simp] private theorem Θ_tmul (d : A ⊗[R₀] B₀) (n : N') :
    Θ B₀ A A' N' (d ⊗ₜ[A] n) = δA B₀ A A' d ⊗ₜ[A'] n := by
  simp [Θ]

private theorem Θ_smul (c : A ⊗[R₀] B₀) (y : (A ⊗[R₀] B₀) ⊗[A] N') :
    Θ B₀ A A' N' (c • y) = δA B₀ A A' c • Θ B₀ A A' N' y := by
  induction y using TensorProduct.inductionOn with
  | tmul d n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, Θ_tmul, Θ_tmul, map_mul,
      TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem Θ_surjective : Function.Surjective (Θ (R₀ := R₀) B₀ A A' N') := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul d' n =>
    induction d' using TensorProduct.inductionOn with
    | tmul a' b =>
      refine ⟨((1 : A) ⊗ₜ[R₀] b) ⊗ₜ[A] (a' • n), ?_⟩
      rw [Θ_tmul, δA_tmul, map_one, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', TensorProduct.add_tmul]⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

private theorem Θ_naturality {N'' : Type*} [AddCommGroup N''] [Module A' N''] [Module A N'']
    [IsScalarTower A A' N''] (φ' : N' →ₗ[A'] N'') (y : (A ⊗[R₀] B₀) ⊗[A] N') :
    Θ B₀ A A' N'' ((φ'.restrictScalars A).baseChange (A ⊗[R₀] B₀) y) =
      (φ'.baseChange (A' ⊗[R₀] B₀)) (Θ B₀ A A' N' y) := by
  induction y using TensorProduct.inductionOn with
  | tmul d n => simp
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem Θ_span_le (Z : Set ((A ⊗[R₀] B₀) ⊗[A] N')) {y : (A ⊗[R₀] B₀) ⊗[A] N'}
    (hy : y ∈ Submodule.span (A ⊗[R₀] B₀) Z) :
    Θ B₀ A A' N' y ∈ Submodule.span (A' ⊗[R₀] B₀) (Θ B₀ A A' N' '' Z) := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Θ_smul]; exact Submodule.smul_mem _ _ hx

private theorem Θ_injective_self : Function.Injective (Θ (R₀ := R₀) B₀ A A' A') := by
  let μ : (A ⊗[R₀] B₀) ⊗[A] A' ≃ₗ[A] A' ⊗[R₀] B₀ :=
    (TensorProduct.comm A _ A').trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ A A A' B₀)
  let rd := TensorProduct.AlgebraTensorModule.rid A' (A' ⊗[R₀] B₀) (A' ⊗[R₀] B₀)
  have key : ∀ y, rd (Θ B₀ A A' A' y) = μ y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul d a' =>
      induction d using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [Θ_tmul, δA_tmul, μ, rd, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm a']
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro y y' hyy'
  have := congrArg rd hyy'
  rw [key, key] at this
  exact μ.injective this

end Theta

private theorem claim [p₀.IsPrime] (h : A →ₐ[R₀] A') (x : (A' ⊗[R₀] B₀) ⊗[A'] ↥(J p₀ A'))
    (hx : x ∈ T B₀ p₀ A') :
    ∃ s ∈ Smon B₀ p₀ A', s • x ∈ Submodule.span (A' ⊗[R₀] B₀)
      (ξ B₀ p₀ h '' (T B₀ p₀ A : Set ((A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)))) := by
  let : Algebra A A' := h.toRingHom.toAlgebra
  have : IsScalarTower R₀ A A' :=
    IsScalarTower.of_algebraMap_eq (fun r => (h.commutes r).symm)
  have hto : IsScalarTower.toAlgHom R₀ A A' = h := AlgHom.ext (fun _ => rfl)
  have hδA : ∀ d, δA B₀ A A' d = δ B₀ h d := fun d => by
    rw [δA_eq_δ, hto]
  let f : ↥(J p₀ A') →ₗ[A] A' := (Submodule.subtype (J p₀ A')).restrictScalars A
  let g : A' →ₗ[A] (A' ⧸ (J p₀ A')) := (Ideal.Quotient.mkₐ A (J p₀ A')).toLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  have hfg : Function.Exact f g := by
    intro a'
    simp only [g, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Set.mem_range]
    constructor
    · intro ha'
      exact ⟨⟨a', ha'⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  have hN : Module.IsTorsionBySet A (A' ⧸ (J p₀ A')) (J p₀ A) := by
    rintro q ⟨a, ha⟩
    induction q using Quotient.inductionOn' with
    | h a' =>
      change a • Ideal.Quotient.mk (J p₀ A') a' = 0
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A A' (A' ⧸ (J p₀ A')),
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right a' (J p₀ A') (mem_J_map p₀ h ha)
  obtain ⟨γ, hγ, hker⟩ := exists_generators_of_ker_baseChange (D := A ⊗[R₀] B₀) (J p₀ A)
    (Smon B₀ p₀ A)
    (fun Q₁ Q₂ _ _ _ _ g hg hQ₂ x hx => rel_torsion B₀ p₀ A g hg hQ₂ x hx) f g hf hfg hN
  obtain ⟨y, hyx⟩ := Θ_surjective B₀ A A' (N' := ↥(J p₀ A')) x
  have hy : f.baseChange (A ⊗[R₀] B₀) y = 0 := by
    apply Θ_injective_self B₀ A A'
    rw [map_zero]
    have hnat := Θ_naturality B₀ A A' (N' := ↥(J p₀ A')) (N'' := A')
      (Submodule.subtype (J p₀ A')) y
    change Θ B₀ A A' A'
      (((Submodule.subtype (J p₀ A')).restrictScalars A).baseChange (A ⊗[R₀] B₀) y) = 0
    rw [hnat, hyx]
    exact LinearMap.mem_ker.mp hx
  obtain ⟨s, hs, hsy⟩ := hker y hy
  refine ⟨δ B₀ h s, δ_mem_Smon B₀ p₀ h hs, ?_⟩
  rw [← hyx, ← hδA, ← Θ_smul]
  refine Submodule.span_le.mpr ?_ (Θ_span_le B₀ A A' _ hsy)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  obtain ⟨t, ht, rfl⟩ := hn
  have key : ∀ t : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A),
      Θ B₀ A A' (↥(J p₀ A')) ((γ n).baseChange (A ⊗[R₀] B₀) t) =
        algebraMap A' (A' ⊗[R₀] B₀) n • ξ B₀ p₀ h t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul d j =>
      have hγnj : γ n j = n • ιJ p₀ h j := by
        apply Subtype.ext
        change f (γ n j) = n * h j
        rw [hγ, mul_comm]
        rfl
      rw [LinearMap.baseChange_tmul, Θ_tmul, ξ_tmul, hδA, hγnj, algebraMap_smul,
        TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)

end Transition

section Descent

variable {R₀ : Type*} [CommRing R₀] (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀]
  (p₀ : Ideal R₀) {R : Type*} [CommRing R] [Algebra R₀ R]

section RForm

variable {A : Type*} [CommRing A] [Algebra R₀ A] {A' : Type*} [CommRing A'] [Algebra R₀ A']

variable (A) in
private def Ψ : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A) ≃ₗ[A] ↥(J p₀ A) ⊗[R₀] B₀ := Φ B₀ A ↥(J p₀ A)

private theorem Ψ_ξ (h : A →ₐ[R₀] A') (x : (A ⊗[R₀] B₀) ⊗[A] ↥(J p₀ A)) :
    Ψ B₀ p₀ A' (ξ B₀ p₀ h x) = (ιJ p₀ h).rTensor B₀ (Ψ B₀ p₀ A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul d j =>
    induction d using TensorProduct.inductionOn with
    | tmul a b =>
      have : ιJ p₀ h (a • j) = h a • ιJ p₀ h j := Subtype.ext (by simp)
      rw [ξ_tmul, δ_tmul, Ψ, Ψ, Φ_tmul, Φ_tmul, LinearMap.rTensor_tmul, this]
    | add x y hx hy =>
      rw [TensorProduct.add_tmul, AddMonoidHom.map_add, LinearEquiv.map_add,
        LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  | add x y hx hy =>
    rw [AddMonoidHom.map_add, LinearEquiv.map_add, LinearEquiv.map_add, LinearMap.map_add,
      hx, hy]

end RForm

private def JR (E : Subalgebra R₀ R) : Submodule R₀ ↥(J p₀ R) := LinearMap.range (ιJ p₀ E.val)

private theorem ιJ_val_injective (E : Subalgebra R₀ R) : Function.Injective (ιJ p₀ E.val) :=
  ιJ_injective p₀ E.val Subtype.val_injective

private theorem JR_mono {E E' : Subalgebra R₀ R} (hle : E ≤ E') : JR p₀ E ≤ JR p₀ E' := by
  rintro _ ⟨j, rfl⟩
  exact ⟨ιJ p₀ (Subalgebra.inclusion hle) j, rfl⟩

private def eJR (E : Subalgebra R₀ R) : ↥(J p₀ ↥E) ≃ₗ[R₀] ↥(JR p₀ E) :=
  LinearEquiv.ofInjective _ (ιJ_val_injective p₀ E)

private theorem coe_eJR (E : Subalgebra R₀ R) (j : J p₀ ↥E) :
    ((eJR p₀ E j : ↥(JR p₀ E)) : ↥(J p₀ R)) = ιJ p₀ E.val j :=
  LinearEquiv.ofInjective_apply _ (h := ιJ_val_injective p₀ E) j

private theorem subtype_comp_eJR (E : Subalgebra R₀ R) :
    (JR p₀ E).subtype ∘ₗ (eJR p₀ E : ↥(J p₀ ↥E) →ₗ[R₀] ↥(JR p₀ E)) = ιJ p₀ E.val :=
  LinearMap.ext fun j => coe_eJR p₀ E j

private theorem val_comp_inclusion {E E' : Subalgebra R₀ R} (hle : E ≤ E') :
    E'.val.comp (Subalgebra.inclusion hle) = E.val := AlgHom.ext (fun _ => rfl)

private theorem inclusion_comp_inclusion {E E' E'' : Subalgebra R₀ R} (h₁ : E ≤ E')
    (h₂ : E' ≤ E'') :
    (Subalgebra.inclusion h₂).comp (Subalgebra.inclusion h₁) = Subalgebra.inclusion (h₁.trans h₂) :=
  AlgHom.ext (fun _ => rfl)

private theorem exists_fg_mem_JR (g : J p₀ R) : ∃ E : Subalgebra R₀ R, E.FG ∧ g ∈ JR p₀ E := by
  suffices H : ∀ r ∈ J p₀ R, ∃ E : Subalgebra R₀ R, E.FG ∧ ∃ j : J p₀ E, (j : R) = r by
    obtain ⟨E, hE, j, hj⟩ := H g g.2
    exact ⟨E, hE, j, Subtype.ext hj⟩
  intro r hr
  have hr' : r ∈ Submodule.span R (algebraMap R₀ R '' p₀) := hr
  clear hr
  induction hr' using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    exact ⟨⊥, Subalgebra.fg_bot, ⟨algebraMap R₀ _ x, Ideal.mem_map_of_mem _ hx⟩, rfl⟩
  | zero => exact ⟨⊥, Subalgebra.fg_bot, 0, rfl⟩
  | add r r' _ _ hr hr' =>
    obtain ⟨E, hE, j, hj⟩ := hr
    obtain ⟨E', hE', j', hj'⟩ := hr'
    refine ⟨E ⊔ E', hE.sup hE', ιJ p₀ (Subalgebra.inclusion le_sup_left) j +
      ιJ p₀ (Subalgebra.inclusion le_sup_right) j', ?_⟩
    rw [← hj, ← hj']
    rfl
  | smul a r _ hr =>
    obtain ⟨E, hE, j, hj⟩ := hr
    have ha : a ∈ E ⊔ Algebra.adjoin R₀ {a} := Algebra.mem_sup_right (Algebra.subset_adjoin rfl)
    have hle : E ≤ E ⊔ Algebra.adjoin R₀ {a} := le_sup_left
    let j' : ↥(J p₀ ↥(E ⊔ Algebra.adjoin R₀ {a})) := ιJ p₀ (Subalgebra.inclusion hle) j
    refine ⟨E ⊔ Algebra.adjoin R₀ {a}, hE.sup (by simpa using Subalgebra.fg_adjoin_finset {a}),
      ⟨(⟨a, ha⟩ : ↥(E ⊔ Algebra.adjoin R₀ {a})) * (j' : ↥(E ⊔ Algebra.adjoin R₀ {a})),
        Ideal.mul_mem_left _ _ j'.2⟩, ?_⟩
    rw [← hj]
    rfl

private theorem exists_fg_le_JR (E₀ : Subalgebra R₀ R) (hE₀ : E₀.FG) (N : Submodule R₀ ↥(J p₀ R))
    (hN : N.FG) : ∃ E : Subalgebra R₀ R, E₀ ≤ E ∧ E.FG ∧ N ≤ JR p₀ E := by
  classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction_on with
  | empty => exact ⟨E₀, le_rfl, hE₀, by simp⟩
  | insert g s _ ih =>
    obtain ⟨E, hE₀E, hE, hsE⟩ := ih
    obtain ⟨E', hE', hgE'⟩ := exists_fg_mem_JR p₀ g
    refine ⟨E ⊔ E', hE₀E.trans le_sup_left, hE.sup hE', ?_⟩
    rw [Finset.coe_insert, Submodule.span_insert, sup_le_iff]
    constructor
    · rw [Submodule.span_singleton_le_iff_mem]
      exact JR_mono p₀ le_sup_right hgE'
    · exact hsE.trans (JR_mono p₀ le_sup_left)

private theorem exists_fg_ξ_eq_zero (E : Subalgebra R₀ R) (hE : E.FG)
    (z : (↥E ⊗[R₀] B₀) ⊗[↥E] ↥(J p₀ ↥E)) (hz : ξ B₀ p₀ E.val z = 0) :
    ∃ E' : Subalgebra R₀ R, ∃ hle : E ≤ E', E'.FG ∧
      ξ B₀ p₀ (Subalgebra.inclusion hle) z = 0 := by
  set y := Ψ B₀ p₀ (↥E) z with hy_def
  have hy : (ιJ p₀ E.val).rTensor B₀ y = 0 := by
    rw [hy_def, ← Ψ_ξ, hz, LinearEquiv.map_zero]
  set y₁ := ((eJR p₀ E : ↥(J p₀ ↥E) →ₗ[R₀] ↥(JR p₀ E)).rTensor B₀) y with hy₁_def
  have hy₁ : ((JR p₀ E).subtype.rTensor B₀) y₁ = 0 := by
    rw [hy₁_def, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, subtype_comp_eJR, hy]
  obtain ⟨N, hNfg, hNle, y₂, hy₂⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion y₁
  have hy₂0 : (N.subtype.rTensor B₀) y₂ = (N.subtype.rTensor B₀) 0 := by
    rw [LinearMap.map_zero]
    have : N.subtype = (JR p₀ E).subtype ∘ₗ Submodule.inclusion hNle := by ext; rfl
    rw [this, LinearMap.rTensor_comp, LinearMap.comp_apply, ← hy₂, hy₁]
  obtain ⟨N', hN'fg, hNN', hvan⟩ := hNfg.exists_rTensor_fg_inclusion_eq hy₂0
  rw [LinearMap.map_zero] at hvan
  obtain ⟨E', hEE', hE', hN'E'⟩ := exists_fg_le_JR p₀ E hE N' hN'fg
  refine ⟨E', hEE', hE', ?_⟩
  apply (Ψ B₀ p₀ (↥E')).injective
  rw [LinearEquiv.map_zero, Ψ_ξ, ← hy_def]
  apply ((eJR p₀ E').rTensor B₀).injective
  rw [LinearEquiv.map_zero]
  have hsq : (eJR p₀ E' : ↥(J p₀ ↥E') →ₗ[R₀] ↥(JR p₀ E')) ∘ₗ ιJ p₀ (Subalgebra.inclusion hEE') =
      Submodule.inclusion (JR_mono p₀ hEE') ∘ₗ (eJR p₀ E : ↥(J p₀ ↥E) →ₗ[R₀] ↥(JR p₀ E)) := by
    refine LinearMap.ext fun j => Subtype.ext ?_
    change ((eJR p₀ E') (ιJ p₀ (Subalgebra.inclusion hEE') j) : ↥(J p₀ R)) =
      (eJR p₀ E j : ↥(J p₀ R))
    rw [coe_eJR, coe_eJR, ιJ_comp, val_comp_inclusion]
  have hinc : Submodule.inclusion (JR_mono p₀ hEE') ∘ₗ Submodule.inclusion hNle =
      Submodule.inclusion hN'E' ∘ₗ Submodule.inclusion hNN' := by ext; rfl
  change ((eJR p₀ E' : ↥(J p₀ ↥E') →ₗ[R₀] ↥(JR p₀ E')).rTensor B₀)
    (((ιJ p₀ (Subalgebra.inclusion hEE')).rTensor B₀) y) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hsq, LinearMap.rTensor_comp,
    LinearMap.comp_apply, ← hy₁_def, hy₂, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    hinc, LinearMap.rTensor_comp, LinearMap.comp_apply, hvan, LinearMap.map_zero]

private theorem exists_fg_mem_range_δ (b : R ⊗[R₀] B₀) :
    ∃ E : Subalgebra R₀ R, E.FG ∧ b ∈ Set.range (δ B₀ E.val) := by
  induction b using TensorProduct.inductionOn with
  | tmul r b =>
    refine ⟨Algebra.adjoin R₀ {r}, by simpa using Subalgebra.fg_adjoin_finset {r},
      (⟨r, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin R₀ {r}) ⊗ₜ[R₀] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨E, hE, x', rfl⟩ := hx
    obtain ⟨E', hE', y', rfl⟩ := hy
    refine ⟨E ⊔ E', hE.sup hE', δ B₀ (Subalgebra.inclusion le_sup_left) x' +
      δ B₀ (Subalgebra.inclusion le_sup_right) y', ?_⟩
    rw [map_add, δ_comp, δ_comp, val_comp_inclusion, val_comp_inclusion]

private theorem torsion_of_mem_span {D X : Type*} [CommRing D] [AddCommGroup X] [Module D X]
    (Q : Ideal D) [hQ : Q.IsPrime] (S : Set X) (hS : ∀ y ∈ S, ∃ c ∉ Q, c • y = 0) {x : X}
    (hx : x ∈ Submodule.span D S) : ∃ c ∉ Q, c • x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact ⟨1, (Ideal.ne_top_iff_one _).mp hQ.ne_top, by rw [one_smul]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, hQ.mul_notMem hc hd, ?_⟩
    have h1 : (c * d) • x = 0 := by rw [mul_comm, mul_smul, hcx, smul_zero]
    have h2 : (c * d) • y = 0 := by rw [mul_smul, hdy, smul_zero]
    rw [smul_add, h1, h2, add_zero]
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    exact ⟨c, hc, by rw [smul_smul, mul_comm, mul_smul, hcx, smul_zero]⟩

private theorem map_mem_span_image {D₀ D X₀ X : Type*} [CommRing D₀] [CommRing D] [AddCommGroup X₀]
    [Module D₀ X₀] [AddCommGroup X] [Module D X] (δ' : D₀ → D) (ψ : X₀ →+ X)
    (hψ : ∀ (c : D₀) (x : X₀), ψ (c • x) = δ' c • ψ x) (S : Set X₀) {t : X₀}
    (ht : t ∈ Submodule.span D₀ S) : ψ t ∈ Submodule.span D (ψ '' S) := by
  induction ht using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [AddMonoidHom.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [AddMonoidHom.map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [hψ]; exact Submodule.smul_mem _ _ hx

variable (P : Ideal (R ⊗[R₀] B₀))

local notation "Rb" => (⊥ : Subalgebra R₀ R)

private def Tors (E : Subalgebra R₀ R) (t : (↥Rb ⊗[R₀] B₀) ⊗[↥Rb]
    ↥(J p₀ ↥Rb)) : Prop :=
  ∃ c ∉ P.comap (δ B₀ E.val), c • ξ B₀ p₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ E)) t = 0

private theorem Tors.mono {E E' : Subalgebra R₀ R} (hle : E ≤ E') {t} (ht : Tors B₀ p₀ P E t) :
    Tors B₀ p₀ P E' t := by
  obtain ⟨c, hc, hct⟩ := ht
  refine ⟨δ B₀ (Subalgebra.inclusion hle) c, ?_, ?_⟩
  · rwa [Ideal.mem_comap, δ_comp, val_comp_inclusion]
  · have := congrArg (ξ B₀ p₀ (Subalgebra.inclusion hle)) hct
    rwa [map_zero, ξ_smul, ξ_comp, inclusion_comp_inclusion] at this

private theorem exists_fg_tors (htop : ∀ x ∈ T B₀ p₀ R, ∃ b ∉ P, b • x = 0)
    (t : (↥Rb ⊗[R₀] B₀) ⊗[↥Rb]
      ↥(J p₀ ↥Rb)) (ht : t ∈ T B₀ p₀ ↥Rb) :
    ∃ E : Subalgebra R₀ R, E.FG ∧ Tors B₀ p₀ P E t := by
  obtain ⟨b, hbP, hb⟩ := htop _ (ξ_mem_T B₀ p₀ (⊥ : Subalgebra R₀ R).val ht)
  obtain ⟨Eb, hEb, b', rfl⟩ := exists_fg_mem_range_δ B₀ b
  set z := b' • ξ B₀ p₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ Eb)) t with hz_def
  have hz : ξ B₀ p₀ Eb.val z = 0 := by
    rw [hz_def, ξ_smul, ξ_comp, val_comp_inclusion, hb]
  obtain ⟨E', hle, hE', hz'⟩ := exists_fg_ξ_eq_zero B₀ p₀ Eb hEb z hz
  refine ⟨E', hE', δ B₀ (Subalgebra.inclusion hle) b', ?_, ?_⟩
  · rwa [Ideal.mem_comap, δ_comp, val_comp_inclusion]
  · rw [hz_def, ξ_smul, ξ_comp, inclusion_comp_inclusion] at hz'
    exact hz'

private theorem Smon_disjoint [p₀.IsPrime] (hP : P.comap (algebraMap R₀ (R ⊗[R₀] B₀)) = p₀)
    (E : Subalgebra R₀ R) {s : ↥E ⊗[R₀] B₀} (hs : s ∈ Smon B₀ p₀ ↥E) :
    s ∉ P.comap (δ B₀ E.val) := by
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  rw [Ideal.mem_comap, AlgHom.commutes, ← Ideal.mem_comap, hP]
  exact hs₀

private theorem exists_fg_T_torsion [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀] [p₀.IsPrime]
    [P.IsPrime]
    (hP : P.comap (algebraMap R₀ (R ⊗[R₀] B₀)) = p₀)
    (htop : ∀ x ∈ T B₀ p₀ R, ∃ b ∉ P, b • x = 0) :
    ∃ E : Subalgebra R₀ R, E.FG ∧
      ∀ x ∈ T B₀ p₀ ↥E, ∃ c ∉ P.comap (δ B₀ E.val), c • x = 0 := by
  classical
  have : IsNoetherianRing ↥Rb := isNoetherianRing_of_fg Subalgebra.fg_bot
  have : IsNoetherianRing (↥Rb ⊗[R₀] B₀) := Algebra.FiniteType.isNoetherianRing ↥Rb _
  have hfg : (T B₀ p₀ ↥Rb).FG := IsNoetherian.noetherian _
  obtain ⟨tset, htset⟩ := hfg
  have hstage : ∀ s : Finset ((↥Rb ⊗[R₀] B₀) ⊗[↥Rb] ↥(J p₀ ↥Rb)),
      (↑s : Set ((↥Rb ⊗[R₀] B₀) ⊗[↥Rb] ↥(J p₀ ↥Rb))) ⊆ ↑(T B₀ p₀ ↥Rb) →
      ∃ E : Subalgebra R₀ R, E.FG ∧ ∀ t ∈ s, Tors B₀ p₀ P E t := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro; exact ⟨⊥, Subalgebra.fg_bot, by simp⟩
    | insert a s _ ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨E₁, hE₁, h₁⟩ := ih hs.2
      obtain ⟨E₂, hE₂, h₂⟩ := exists_fg_tors B₀ p₀ P htop a hs.1
      refine ⟨E₁ ⊔ E₂, hE₁.sup hE₂, ?_⟩
      intro t ht
      rw [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exact h₂.mono B₀ p₀ P le_sup_right
      · exact (h₁ t ht).mono B₀ p₀ P le_sup_left
  have htsub : (↑tset : Set ((↥Rb ⊗[R₀] B₀) ⊗[↥Rb] ↥(J p₀ ↥Rb))) ⊆ ↑(T B₀ p₀ ↥Rb) := by
    rw [← htset]; exact Submodule.subset_span
  obtain ⟨E, hE, hgen⟩ := hstage tset htsub
  refine ⟨E, hE, ?_⟩
  have hQ : (P.comap (δ B₀ E.val)).IsPrime := Ideal.comap_isPrime (δ B₀ E.val) P
  have himage : ∀ y ∈ ξ B₀ p₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ E)) '' (T B₀ p₀ ↥Rb : Set _),
      ∃ c ∉ P.comap (δ B₀ E.val), c • y = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ Submodule.span (↥Rb ⊗[R₀] B₀) (↑tset : Set _) := by rwa [htset]
    have hmem := map_mem_span_image (δ B₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ E)))
      (ξ B₀ p₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ E)))
      (ξ_smul B₀ p₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ E))) _ ht'
    refine torsion_of_mem_span (P.comap (δ B₀ E.val)) _ ?_ hmem
    rintro _ ⟨t, ht, rfl⟩
    exact hgen t ht
  intro x hx
  obtain ⟨s, hs, hsx⟩ := claim B₀ p₀ (Subalgebra.inclusion (bot_le : ⊥ ≤ E)) x hx
  obtain ⟨c, hc, hcsx⟩ := torsion_of_mem_span (P.comap (δ B₀ E.val)) _ himage hsx
  refine ⟨c * s, hQ.mul_notMem hc (Smon_disjoint B₀ p₀ P hP E hs), ?_⟩
  rw [mul_smul, hcsx]

end Descent

section Endgame

private theorem cancelBaseChange_lTensor_baseChange {A D M' : Type*} [CommRing A] [CommRing D]
    [CommRing M'] [Algebra A D] [Algebra D M'] [Algebra A M'] [IsScalarTower A D M']
    {N N'' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N''] [Module A N'']
    (f : N →ₗ[A] N'') (z : M' ⊗[D] (D ⊗[A] N)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N''
        ((f.baseChange D).lTensor M' z) =
      f.lTensor M' (TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m y =>
    induction y using TensorProduct.inductionOn with
    | tmul d n => simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem lTensor_localization_injective {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
    (P : Ideal D) [P.IsPrime] {N N'' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'']
    [Module A N''] (f : N →ₗ[A] N'')
    (htor : ∀ z, f.baseChange D z = 0 → ∃ c ∉ P, c • z = 0) :
    Function.Injective (f.lTensor (Localization.AtPrime P)) := by
  let M' := Localization.AtPrime P
  have : Module.Flat D M' := IsLocalization.flat M' P.primeCompl
  set K := LinearMap.ker (f.baseChange D) with hK
  have hzero : ∀ w : M' ⊗[D] K, (K.subtype.lTensor M') w = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul m k =>
      obtain ⟨c, hc, hck⟩ := htor k k.2
      have hu : IsUnit (algebraMap D M' c) :=
        IsLocalization.map_units M' (⟨c, hc⟩ : P.primeCompl)
      obtain ⟨u, hu⟩ := hu
      have hm : m = c • ((↑u⁻¹ : M') * m) := by
        rw [Algebra.smul_def, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, hm, TensorProduct.smul_tmul, hck,
        TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have hex := Module.Flat.lTensor_exact M' (N := ↥K) (N' := D ⊗[A] N) (N'' := D ⊗[A] N'')
    (f := K.subtype) (g := f.baseChange D) (LinearMap.exact_subtype_ker_map (f.baseChange D))
  have hinj : Function.Injective ((f.baseChange D).lTensor M') := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (hex z).mp hz
    exact hzero w
  intro x y hxy
  obtain ⟨x, rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N).surjective x
  obtain ⟨y, rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N).surjective y
  rw [← cancelBaseChange_lTensor_baseChange, ← cancelBaseChange_lTensor_baseChange] at hxy
  rw [hinj ((TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N'').injective hxy)]

variable {R₀ : Type*} [CommRing R₀] (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀]
  (p₀ : Ideal R₀) (A : Type u) [CommRing A] [Algebra R₀ A]

private theorem flat_localization_of_T_torsion [p₀.IsPrime] [IsNoetherianRing A]
    [IsNoetherianRing (A ⊗[R₀] B₀)] (P₁ : Ideal (A ⊗[R₀] B₀)) [P₁.IsPrime]
    (hP₁ : P₁.comap (algebraMap R₀ (A ⊗[R₀] B₀)) = p₀)
    (htor : ∀ x ∈ T B₀ p₀ A, ∃ c ∉ P₁, c • x = 0) :
    Module.Flat A (Localization.AtPrime P₁) := by
  set p₁ := P₁.comap (algebraMap A (A ⊗[R₀] B₀)) with hp₁
  have hJp : J p₀ A ≤ p₁ := by
    rw [J, Ideal.map_le_iff_le_comap, hp₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      hP₁]
  have hN : Module.IsTorsionBySet A (A ⧸ p₁) (J p₀ A) := by
    rintro q ⟨a, ha⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact p₁.mul_mem_right _ (hJp ha)
  obtain ⟨γ, -, hker⟩ := exists_generators_of_ker_baseChange (D := A ⊗[R₀] B₀) (J p₀ A)
    (Smon B₀ p₀ A) (fun Q₁ Q₂ _ _ _ _ g hg hQ₂ x hx => rel_torsion B₀ p₀ A g hg hQ₂ x hx)
    p₁.subtype p₁.mkQ (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ p₁) hN
  have hKtor : ∀ z, (p₁.subtype).baseChange (A ⊗[R₀] B₀) z = 0 → ∃ c ∉ P₁, c • z = 0 := by
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hker z hz
    have hgen : ∀ y ∈ ⋃ n, (γ n).baseChange (A ⊗[R₀] B₀) ''
        (torKer (A ⊗[R₀] B₀) (J p₀ A) : Set _), ∃ c ∉ P₁, c • y = 0 := by
      intro y hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      obtain ⟨t, ht, rfl⟩ := hn
      obtain ⟨c, hc, hct⟩ := htor t ht
      exact ⟨c, hc, by rw [← map_smul, hct, map_zero]⟩
    obtain ⟨c, hc, hcz⟩ := torsion_of_mem_span P₁ _ hgen hsz
    have hsP : s ∉ P₁ := by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      rw [← Ideal.mem_comap, hP₁]
      exact hs₀
    exact ⟨c * s, Ideal.IsPrime.mul_notMem inferInstance hc hsP, by rw [mul_smul, hcz]⟩
  have hinj := lTensor_localization_injective P₁ p₁.subtype hKtor
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime P₁)).comap
      (algebraMap A (Localization.AtPrime P₁)) = p₁ := by
    rw [IsScalarTower.algebraMap_eq A (A ⊗[R₀] B₀) (Localization.AtPrime P₁),
      ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime P₁)).under (A ⊗[R₀] B₀)).comap _ = p₁
    rw [Localization.AtPrime.under_maximalIdeal]
  exact Module.flat_of_comap_maximalIdeal_rTensor_injective (S := Localization.AtPrime P₁) p₁ hp
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hinj)

end Endgame

section Main

variable {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀] [Algebra R₀ R] [Algebra R₀ B₀]

private theorem torsion_of_flat_localization {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
    (P : Ideal D) [P.IsPrime] [Module.Flat A (Localization.AtPrime P)]
    {N N'' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N''] [Module A N'']
    (f : N →ₗ[A] N'') (hf : Function.Injective f) (x : D ⊗[A] N)
    (hx : f.baseChange D x = 0) : ∃ b ∉ P, b • x = 0 := by
  let M' := Localization.AtPrime P
  have hinj : Function.Injective (f.lTensor M') :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have h1 : TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N
      ((1 : M') ⊗ₜ[D] x) = 0 := by
    apply hinj
    rw [map_zero, ← cancelBaseChange_lTensor_baseChange, LinearMap.lTensor_tmul, hx,
      TensorProduct.tmul_zero, map_zero]
  have h2 : (1 : M') ⊗ₜ[D] x = 0 :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A D M' M' N).injective
      (by rw [h1, map_zero])
  obtain ⟨b, hb⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl
    (TensorProduct.mk D M' (D ⊗[A] N) 1)).mp h2
  exact ⟨b, b.2, hb⟩

private theorem T_top_torsion (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] (p₀ : Ideal R₀) (x : (R ⊗[R₀] B₀) ⊗[R] ↥(J p₀ R))
    (hx : x ∈ T B₀ p₀ R) : ∃ b ∉ P, b • x = 0 :=
  torsion_of_flat_localization P (Submodule.subtype (J p₀ R)) (Submodule.injective_subtype _) x
    (LinearMap.mem_ker.mp hx)

end Main

end FlatDescentFG

end

open FlatDescentFG in
/-- **Noetherian approximation of flatness at a prime.** Let `R₀` be a Noetherian ring, `B₀` a
finite type `R₀`-algebra and `R` an `R₀`-algebra. If the localization of `R ⊗[R₀] B₀` at a prime
`P` is flat over `R`, then for some finitely generated `R₀`-subalgebra `R₁` of `R`, the
localization of `R₁ ⊗[R₀] B₀` at the prime below `P` is flat over `R₁`.

Source: [Stacks Project, Lemma 10.128.3 (Tag 00R6)](https://stacks.math.columbia.edu/tag/00R6),
stated there for the directed systems of local rings of Lemma 10.127.13 (Tag 00QX). -/
public theorem Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ B₀)).toRingHom)) := by
  set p₀ := P.comap (algebraMap R₀ (R ⊗[R₀] B₀)) with hp₀
  have : p₀.IsPrime := Ideal.comap_isPrime _ P
  obtain ⟨E, hE, htorE⟩ := exists_fg_T_torsion B₀ p₀ P rfl (T_top_torsion P p₀)
  refine ⟨E, hE, ?_⟩
  have : IsNoetherianRing ↥E := isNoetherianRing_of_fg hE
  have : IsNoetherianRing (↥E ⊗[R₀] B₀) := Algebra.FiniteType.isNoetherianRing ↥E _
  set P₁ := P.comap (Algebra.TensorProduct.map E.val (AlgHom.id R₀ B₀)).toRingHom with hP₁
  have hP₁' : P₁ = P.comap (δ B₀ E.val) := Ideal.ext (fun _ => Iff.rfl)
  have : P₁.IsPrime := Ideal.comap_isPrime _ P
  have hcontr : P₁.comap (algebraMap R₀ (↥E ⊗[R₀] B₀)) = p₀ := by
    ext r
    rw [hP₁', Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes, hp₀, Ideal.mem_comap]
  refine flat_localization_of_T_torsion B₀ p₀ (↥E) P₁ hcontr ?_
  rw [hP₁']
  exact htorE
