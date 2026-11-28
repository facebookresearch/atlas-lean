/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Theorems/Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_
moduleFinite_of_henselianLocalRing.lean`
and
`P2M/Sol/S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_
moduleFinite_of_henselianLocalRing.lean`
and the upstream results it uses, from
`Theorems/Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_
quotient_of_moduleFinite.lean`,
`P2M/Sol/S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_
quotient_of_moduleFinite.lean`,
`Theorems/Thm_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_
henselianLocalRing.lean`,
`P2M/Sol/S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_
henselianLocalRing.lean`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Tactic
import MathlibExt.RingTheory.Henselian.IdempotentLifting

@[expose] public section

universe u v w

open scoped TensorProduct


set_option autoImplicit false

section hensSplitHelpers

open IsLocalRing

private theorem hensSplit_map_maximalIdeal_le {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] (m : Ideal S) (hm : m.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ m := by
  rw [Ideal.map_le_iff_le_comap]
  haveI := hm
  have hmax : (m.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
      (fun x => Algebra.IsIntegral.isIntegral x) m
  rw [IsLocalRing.eq_maximalIdeal hmax]

private theorem hensSplit_finite_maximalSpectrum {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  set J : Ideal S := (maximalIdeal R).map (algebraMap R S) with hJ
  have : IsArtinianRing (S ⧸ J) := by
    let := Ideal.Quotient.field (maximalIdeal R)
    have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := .of_restrictScalars_finite R _ _
    exact .of_finite (R ⧸ maximalIdeal R) _
  let F : MaximalSpectrum S → MaximalSpectrum (S ⧸ J) := fun m =>
    have := m.isMaximal
    ⟨m.asIdeal.map (Ideal.Quotient.mk J),
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hensSplit_map_maximalIdeal_le (R := R) _ m.isMaximal)⟩
  refine Finite.of_injective F ?_
  intro m₁ m₂ h
  have h2 : (m₁.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) =
      (m₂.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) := by
    have := congrArg MaximalSpectrum.asIdeal h
    simp only [F] at this
    rw [this]
  rw [Ideal.comap_map_mk (hensSplit_map_maximalIdeal_le (R := R) _ m₁.isMaximal),
    Ideal.comap_map_mk (hensSplit_map_maximalIdeal_le (R := R) _ m₂.isMaximal)] at h2
  exact MaximalSpectrum.ext h2

private theorem hensSplit_isIdempotentElem_eq_of_mk_eq {R : Type u} [CommRing R]
  [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) a =
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) : a = b :=
  (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
      (Ideal.Quotient.mk _ a) (ha.map _)).unique ⟨ha, rfl⟩ ⟨hb, h.symm⟩

private theorem hensSplit_isLocalRing_quotient {S : Type v} [CommRing S] (e : S) (m : Ideal S) (hm
  : m.IsMaximal)
    (h1 : 1 - e ∈ m) (h2 : ∀ m' : Ideal S, m'.IsMaximal → m' ≠ m → e ∈ m') :
    IsLocalRing (S ⧸ Ideal.span {1 - e}) := by
  apply IsLocalRing.of_unique_max_ideal
  set K : Ideal S := Ideal.span {1 - e} with hKdef
  have hK : K ≤ m := by
    rw [hKdef, Ideal.span_le, Set.singleton_subset_iff]
    exact h1
  refine ⟨m.map (Ideal.Quotient.mk K),
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker]), ?_⟩
  intro N hN
  have hNc : (N.comap (Ideal.Quotient.mk K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have heq : N.comap (Ideal.Quotient.mk K) = m := by
    by_contra hne
    have he : e ∈ N.comap (Ideal.Quotient.mk K) := h2 _ hNc hne
    have hKmem : 1 - e ∈ K := Ideal.subset_span (Set.mem_singleton _)
    have h1e : 1 - e ∈ N.comap (Ideal.Quotient.mk K) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hKmem]
      exact N.zero_mem
    have : (1 : S) ∈ N.comap (Ideal.Quotient.mk K) := by
      have := add_mem h1e he
      rwa [sub_add_cancel] at this
    exact hNc.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  rw [← heq, Ideal.map_comap_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective]

end hensSplitHelpers

private theorem HenselianLocalRing.exists_completeOrthogonalIdempotents_quotient
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (_ : Fintype (MaximalSpectrum S)) (e : MaximalSpectrum S → S),
      CompleteOrthogonalIdempotents e ∧
      (∀ m : MaximalSpectrum S, e m ∉ m.asIdeal) ∧
      (∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal) ∧
      (∀ m : MaximalSpectrum S, IsLocalRing (S ⧸ Ideal.span {1 - e m})) := by
  classical
  haveI : Finite (MaximalSpectrum S) := hensSplit_finite_maximalSpectrum (R := R)
  letI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  have : IsArtinianRing (S ⧸ J) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ J) :=
      .of_restrictScalars_finite R _ _
    exact .of_finite (R ⧸ IsLocalRing.maximalIdeal R) _
  have hJle : ∀ m : MaximalSpectrum S, J ≤ m.asIdeal := fun m =>
    hensSplit_map_maximalIdeal_le (R := R) m.asIdeal m.isMaximal

  let P : MaximalSpectrum S → Type v := fun m => S ⧸ m.asIdeal
  let π : S →+* (∀ m, P m) := RingHom.pi fun m => Ideal.Quotient.mk m.asIdeal
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum S => m.asIdeal) := by
    intro m m' h
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne m.isMaximal m'.isMaximal
      (fun h' => h (MaximalSpectrum.ext h'))
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨r, funext hr⟩
  have hJπ : ∀ s ∈ J, π s = 0 := by
    intro s hs
    funext m
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJle m hs)
  let ψ : S ⧸ J →+* (∀ m, P m) := Ideal.Quotient.lift J π hJπ
  have hψmk : ∀ s, ψ (Ideal.Quotient.mk J s) = π s := fun s => Ideal.Quotient.lift_mk J π hJπ
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨s, hs⟩ := hπ x
    exact ⟨Ideal.Quotient.mk J s, by rw [hψmk, hs]⟩

  have hnil : ∀ x ∈ RingHom.ker ψ, IsNilpotent x := by
    intro x hx
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hs : ∀ m : MaximalSpectrum S, s ∈ m.asIdeal := by
      intro m
      have h0 : π s = 0 := by rw [← hψmk]; exact hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h0 m)
    have hmem : Ideal.Quotient.mk J s ∈ Ideal.jacobson (⊥ : Ideal (S ⧸ J)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro N ⟨-, hN⟩
      haveI := hN
      have hNc : (N.comap (Ideal.Quotient.mk J)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      exact hs ⟨_, hNc⟩
    rw [Ideal.jacobson_bot] at hmem
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson (S ⧸ J)
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hmem n
    rw [hn] at this
    simpa using this

  have hf : CompleteOrthogonalIdempotents fun m : MaximalSpectrum S => (Pi.single m 1 : ∀ m, P m) :=
    CompleteOrthogonalIdempotents.single P
  obtain ⟨ē, hē, hēf⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker ψ hnil hf (fun m => hψ _)

  have hex := fun m : MaximalSpectrum S =>
    (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite (ē m) (hē.idem
      m)).exists
  choose e he hemk using hex
  have hπe : ∀ m m' : MaximalSpectrum S,
      Ideal.Quotient.mk m'.asIdeal (e m) = (Pi.single m 1 : ∀ m, P m) m' := by
    intro m m'
    have h1 : π (e m) = Pi.single m 1 := by
      rw [← hψmk, hemk]
      exact congrFun hēf m
    exact congrFun h1 m'
  have hnotMem : ∀ m : MaximalSpectrum S, e m ∉ m.asIdeal := by
    intro m hm
    have h1 := hπe m m
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, Pi.single_eq_same] at h1
    exact m.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp h1)
  have hmem : ∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal := by
    intro m m' h
    have h1 := hπe m m'
    rw [Pi.single_eq_of_ne (Ne.symm h)] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro m m' h
    refine hensSplit_isIdempotentElem_eq_of_mk_eq (R := R) ((he m).mul (he m'))
      (IsIdempotentElem.zero) ?_
    rw [map_mul, map_zero, hemk, hemk]
    exact hē.ortho h
  have hcomplete : ∑ m, e m = 1 := by
    refine hensSplit_isIdempotentElem_eq_of_mk_eq (R := R) hortho.isIdempotentElem_sum
      (IsIdempotentElem.one) ?_
    rw [map_sum, map_one]
    simp_rw [hemk]
    exact hē.complete
  refine ⟨inferInstance, e, ⟨hortho, hcomplete⟩, hnotMem, hmem, ?_⟩

  intro m
  refine hensSplit_isLocalRing_quotient (e m) m.asIdeal m.isMaximal ?_ ?_
  · have h1 := hπe m m
    rw [Pi.single_eq_same] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h1, sub_self]
  · intro m' hm' hne
    exact hmem m ⟨m', hm'⟩ (fun h => hne (congrArg MaximalSpectrum.asIdeal h).symm)

set_option autoImplicit false


open scoped TensorProduct

private theorem Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (B : Type w) [CommRing B] [Algebra R B] [Module.Finite R B]
    (φ ψ : E →ₐ[R] B)
    (h : ∀ x : E, φ x - ψ x ∈ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :
    φ = ψ := by
  classical
  set I : Ideal B := Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) with hI

  have hIJ : I ≤ Ideal.jacobson (⊥ : Ideal B) := by
    refine le_sInf fun J hJ => ?_
    obtain ⟨-, hJmax⟩ := hJ
    rw [hI, Ideal.map_le_iff_le_comap]
    have hc : (J.comap (algebraMap R B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R B)
      (fun x => Algebra.IsIntegral.isIntegral x) J
    rw [← IsLocalRing.eq_maximalIdeal hc]

  set e : E ⊗[R] E := Algebra.FormallyUnramified.elem R E with he
  have he1 : ∀ s : E, ((1 : E) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : E)) * e = 0 :=
    fun s => Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem s
  have he2 : Algebra.TensorProduct.lmul' R e = 1 := Algebra.FormallyUnramified.lmul_elem
  set Φ : E ⊗[R] E →ₐ[R] B := Algebra.TensorProduct.productMap φ ψ with hΦ

  have hΦμ : ∀ t : E ⊗[R] E, Φ t - φ (Algebra.TensorProduct.lmul' R t) ∈ I := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
        rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          ← mul_sub]
        refine I.mul_mem_left _ ?_
        have := I.neg_mem (h b)
        rwa [neg_sub] at this
    | add u v hu hv =>
        rw [map_add, map_add, map_add]
        convert I.add_mem hu hv using 1
        ring
  have hΦe : Φ e - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := by
    apply hIJ
    simpa [he2] using hΦμ e
  have hunit : IsUnit (Φ e) :=
    Ideal.isUnit_of_sub_one_mem_jacobson _ (by rwa [← Ideal.jacobson_bot])

  refine AlgHom.ext fun x => ?_
  have hdx : Φ (x ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x) = φ x - ψ x := by
    rw [map_sub, hΦ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul,
      map_one, map_one, mul_one, one_mul]
  have hann : (x ⊗ₜ[R] (1 : E) - (1 : E) ⊗ₜ[R] x) * e = 0 := by
    rw [← neg_sub, neg_mul, he1 x, neg_zero]
  have hkey : (φ x - ψ x) * Φ e = 0 := by
    rw [← hdx, ← map_mul, hann, map_zero]
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hkey)

set_option autoImplicit false

open scoped TensorProduct


namespace H1Aux

open IsLocalRing

section LocalHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem isLocalHom_algebraMap_of_moduleFinite [IsLocalRing A] [IsLocalRing B]
  [Module.Finite A B] :
    IsLocalHom (algebraMap A B) :=
  ((local_hom_tfae (algebraMap A B)).out 1 3).mpr
    (hensSplit_map_maximalIdeal_le (maximalIdeal B) (maximalIdeal.isMaximal B))

private theorem restrictScalars_maximalIdeal_le_smul_top [IsLocalRing A] [IsLocalRing B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ((maximalIdeal B).restrictScalars A : Submodule A B) ≤ maximalIdeal A • (⊤ : Submodule A B) :=
      by
  rw [Ideal.smul_top_eq_map, h]

end LocalHom

section Residue

variable {R : Type u} [CommRing R] [IsLocalRing R] {C : Type w} [CommRing C] [Algebra R C]

private theorem one_tmul_eq_zero_iff (c : C) :
    (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ∈ (maximalIdeal R).map (algebraMap R C) := by
  have h1 : (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ⊗ₜ[R] (1 : ResidueField R) = 0 := by
    rw [← (Algebra.TensorProduct.comm R (ResidueField R) C).injective.eq_iff, map_zero,
      Algebra.TensorProduct.comm_tmul]
  have h2 : c ∈ (maximalIdeal R).map (algebraMap R C) ↔ c ⊗ₜ[R] (1 : ResidueField R) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal R)).injective.eq_iff,
        map_zero,
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rfl
  exact h1.trans h2.symm

end Residue

end H1Aux

namespace H1Aux

open IsLocalRing

section Core

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {O : Type v} [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
  {C : Type w} [CommRing C] [Algebra R C] [Module.Finite R C]

private theorem algHom_eq_of_map_eq (ψ₁ ψ₂ : O →ₐ[R] C)
    (h : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ₁ =
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ₂) : ψ₁ = ψ₂ := by
  apply Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing R O C
  intro x
  rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, sub_eq_zero]
  have := AlgHom.congr_fun h ((1 : ResidueField R) ⊗ₜ[R] x)
  simpa [Algebra.TensorProduct.map_tmul] using this

private theorem exists_algHom_of_isLocalRing [IsLocalRing C]
    (ψbar : ResidueField R ⊗[R] O →ₐ[ResidueField R] ResidueField R ⊗[R] C) :
    ∃ ψ : O →ₐ[R] C, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ =
      ψbar := by
  classical
  haveI : IsLocalHom (algebraMap R C) := isLocalHom_algebraMap_of_moduleFinite

  let f₀ : ResidueField R →ₐ[R] ResidueField C :=
    { toRingHom := ResidueField.map (algebraMap R C), commutes' := fun r => rfl }
  let θ : ResidueField R ⊗[R] C →ₐ[R] ResidueField C :=
    Algebra.TensorProduct.lift f₀ (IsScalarTower.toAlgHom R C (ResidueField C)) (fun _ _ =>
      Commute.all _ _)
  have hθ : ∀ (a : ResidueField R) (c : C), θ (a ⊗ₜ[R] c) = f₀ a * residue C c :=
    fun a c => Algebra.TensorProduct.lift_tmul _ _ _ a c

  let q : O →ₐ[R] ResidueField C :=
    θ.comp ((ψbar.restrictScalars R).comp (Algebra.TensorProduct.includeRight (A := ResidueField
      R)))
  let pbar : C ⊗[R] O →ₐ[C] ResidueField C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (ResidueField C)) q (fun _ _ => Commute.all _ _)
  have hpbar : ∀ (c : C) (o : O), pbar (c ⊗ₜ[R] o) = residue C c * q o :=
    fun c o => Algebra.TensorProduct.lift_tmul _ _ _ c o
  have hpsurj : Function.Surjective pbar := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective (R := C) x
    exact ⟨c ⊗ₜ 1, by rw [hpbar, map_one, mul_one]⟩

  obtain ⟨hfin, e, hce, hnot, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_quotient
      (R := R) (S := C ⊗[R] O)
  let m₀ : MaximalSpectrum (C ⊗[R] O) :=
    ⟨RingHom.ker (pbar : C ⊗[R] O →+* ResidueField C), RingHom.ker_isMaximal_of_surjective _ hpsurj⟩
  have he₀ : pbar (e m₀) = 1 := by
    have hne : pbar (e m₀) ≠ 0 := fun h => hnot m₀ (by
      show e m₀ ∈ RingHom.ker (pbar : C ⊗[R] O →+* ResidueField C)
      rwa [RingHom.mem_ker])
    have hid : IsIdempotentElem (pbar (e m₀)) := (hce.idem m₀).map pbar
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp hid).resolve_left hne
  let I : Ideal (C ⊗[R] O) := Ideal.span {1 - e m₀}
  haveI hL : IsLocalRing ((C ⊗[R] O) ⧸ I) := hloc m₀

  haveI : IsLocalHom (algebraMap C ((C ⊗[R] O) ⧸ I)) :=
    isLocalHom_algebraMap_of_moduleFinite (A := C) (B := (C ⊗[R] O) ⧸ I)
  haveI : Algebra.FormallyUnramified C ((C ⊗[R] O) ⧸ I) := Algebra.FormallyUnramified.quotient I

  haveI : Module.Flat C ((C ⊗[R] O) ⧸ I) := by
    let r : (C ⊗[R] O) →ₗ[C] ((C ⊗[R] O) ⧸ I) := (Ideal.Quotient.mkₐ C I).toLinearMap
    let i₀ : ((C ⊗[R] O) ⧸ I.restrictScalars C) →ₗ[C] (C ⊗[R] O) :=
      (I.restrictScalars C).liftQ (LinearMap.mulLeft C (e m₀)) (by
        intro x hx
        rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx
        obtain ⟨y, rfl⟩ := hx
        rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, ← mul_assoc, (hce.idem
          m₀).mul_one_sub_self, zero_mul])
    let i : ((C ⊗[R] O) ⧸ I) →ₗ[C] (C ⊗[R] O) :=
      i₀ ∘ₗ (Submodule.Quotient.restrictScalarsEquiv C I).symm.toLinearMap
    refine Module.Flat.of_retract i r ?_
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk I (i₀ ((Submodule.Quotient.restrictScalarsEquiv C I).symm
      (Ideal.Quotient.mk I x))) =
      Ideal.Quotient.mk I x
    rw [show (Submodule.Quotient.restrictScalarsEquiv C I).symm (Ideal.Quotient.mk I x) =
        Submodule.Quotient.mk x from rfl]
    show Ideal.Quotient.mk I (e m₀ * x) = Ideal.Quotient.mk I x
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-x, by ring⟩
  haveI : Module.Free C ((C ⊗[R] O) ⧸ I) := Module.free_of_flat_of_isLocalRing
  have hmL := Algebra.FormallyUnramified.map_maximalIdeal (R := C) (S := (C ⊗[R] O) ⧸ I)

  let pL : ((C ⊗[R] O) ⧸ I) →ₐ[C] ResidueField C := Ideal.Quotient.liftₐ I pbar (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_sub, map_one, he₀, sub_self, zero_mul])
  have hpL : ∀ d, pL (Ideal.Quotient.mk I d) = pbar d := fun d => rfl
  have hpLsurj : Function.Surjective pL := by
    intro x
    obtain ⟨d, rfl⟩ := hpsurj x
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  let ιₐ : C →ₐ[C] ((C ⊗[R] O) ⧸ I) := Algebra.ofId C ((C ⊗[R] O) ⧸ I)

  have hιsurj : Function.Surjective ιₐ := by
    have key : (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) ≤ LinearMap.range ιₐ.toLinearMap ⊔
        (maximalIdeal ((C ⊗[R] O) ⧸ I)).restrictScalars C := by
      intro ℓ _
      obtain ⟨c, hc⟩ := residue_surjective (R := C) (pL ℓ)
      have hmem : ℓ - ιₐ c ∈ maximalIdeal ((C ⊗[R] O) ⧸ I) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply (hu.map pL).ne_zero
        rw [map_sub, sub_eq_zero, ← hc]
        exact (pL.commutes c).symm
      exact Submodule.mem_sup.mpr ⟨ιₐ c, ⟨c, rfl⟩, ℓ - ιₐ c, hmem, by abel⟩
    have hsmul : ((maximalIdeal ((C ⊗[R] O) ⧸ I)).restrictScalars C : Submodule C ((C ⊗[R] O) ⧸ I))
      ≤
        maximalIdeal C • (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) :=
      restrictScalars_maximalIdeal_le_smul_top (A := C) (B := (C ⊗[R] O) ⧸ I) hmL
    have hle : (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) ≤ LinearMap.range ιₐ.toLinearMap :=
      Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top
        (ringJacobson_eq_maximalIdeal C).ge (key.trans (sup_le_sup_left hsmul _))
    intro ℓ
    obtain ⟨c, hc⟩ := hle (Submodule.mem_top : ℓ ∈ ⊤)
    exact ⟨c, hc⟩

  have hιinj : Function.Injective ιₐ := by
    let b := Module.Free.chooseBasis C ((C ⊗[R] O) ⧸ I)
    obtain ⟨i₀⟩ := b.index_nonempty
    let g : C →ₗ[C] C := (b.coord i₀) ∘ₗ ιₐ.toLinearMap
    have hg : Function.Surjective g := by
      intro t
      obtain ⟨c, hc⟩ := hιsurj (t • b i₀)
      refine ⟨c, ?_⟩
      show b.coord i₀ (ιₐ c) = t
      rw [hc, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul,
        mul_one]
    have hginj := OrzechProperty.injective_of_surjective_endomorphism g hg
    intro x y hxy
    apply hginj
    show b.coord i₀ (ιₐ x) = b.coord i₀ (ιₐ y)
    rw [hxy]

  let E : C ≃ₐ[C] ((C ⊗[R] O) ⧸ I) := AlgEquiv.ofBijective ιₐ ⟨hιinj, hιsurj⟩
  let σ : (C ⊗[R] O) →ₐ[C] C := (E.symm : ((C ⊗[R] O) ⧸ I) →ₐ[C] C).comp (Ideal.Quotient.mkₐ C I)
  have hEσ : ∀ d, E (σ d) = Ideal.Quotient.mk I d := fun d => E.apply_symm_apply _
  have hσ : ∀ d, residue C (σ d) = pbar d := by
    intro d
    rw [← hpL, ← hEσ]
    show _ = pL (ιₐ (σ d))
    exact (pL.commutes (σ d)).symm
  let ψ : O →ₐ[R] C := (σ.restrictScalars R).comp (Algebra.TensorProduct.includeRight (A := C))
  have hψ : ∀ o, residue C (ψ o) = q o := by
    intro o
    show residue C (σ (1 ⊗ₜ o)) = q o
    rw [hσ, hpbar, map_one, one_mul]
  refine ⟨ψ, ?_⟩

  haveI : IsArtinianRing (ResidueField R ⊗[R] C) := IsArtinianRing.of_finite (ResidueField R) _
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective (R := C) x
    exact ⟨1 ⊗ₜ c, by rw [hθ, map_one, one_mul]⟩
  have hnil : IsNilpotent (RingHom.ker (θ : ResidueField R ⊗[R] C →+* ResidueField C)) := by
    rw [ker_eq_maximalIdeal (θ : ResidueField R ⊗[R] C →+* ResidueField C) hθsurj,
      ← ringJacobson_eq_maximalIdeal]
    exact IsArtinianRing.isNilpotent_jacobson _
  apply Algebra.FormallyUnramified.ext' (θ : ResidueField R ⊗[R] C →+* ResidueField C) hnil
  intro z
  suffices hcomp : θ.comp ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R))
    ψ).restrictScalars R) =
      θ.comp (ψbar.restrictScalars R) from AlgHom.congr_fun hcomp z
  apply Algebra.TensorProduct.ext'
  intro a o
  have hz : a ⊗ₜ[R] o = algebraMap (ResidueField R) (ResidueField R ⊗[R] O) a * ((1 : ResidueField
    R) ⊗ₜ[R] o) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  show θ (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ (a ⊗ₜ[R] o)) =
    θ (ψbar (a ⊗ₜ[R] o))
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hθ, hψ, hz, map_mul, AlgHom.commutes,
    map_mul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hθ, map_one,
      mul_one]
  rfl

end Core

end H1Aux

namespace H1Aux

open IsLocalRing

section Assemble

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {O : Type v} [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
  {C : Type w} [CommRing C] [Algebra R C] [Module.Finite R C]

omit [HenselianLocalRing R] [Module.Finite R C] in
private theorem mul_mem_map_maximalIdeal_of_mk_mem [IsLocalRing R] (e c : C) (he : IsIdempotentElem
  e)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) c ∈
      (maximalIdeal R).map (algebraMap R (C ⧸ Ideal.span {1 - e}))) :
    c * e ∈ (maximalIdeal R).map (algebraMap R C) := by
  rw [IsScalarTower.algebraMap_eq R C (C ⧸ Ideal.span {1 - e}), ← Ideal.map_map,
    Ideal.Quotient.algebraMap_eq,
    Ideal.mem_map_span_singleton_iff_of_isIdempotentElem he.one_sub, sub_sub_cancel] at h
  rwa [mul_comm]

omit [Module.Finite R O] [Algebra.Etale R O] [Module.Finite R C] in
private theorem eq_zero_of_forall_map_mk_eq_zero {ι : Type*} [Fintype ι] (e : ι → C)
    (hce : CompleteOrthogonalIdempotents e) (z : ResidueField R ⊗[R] C)
    (hz : ∀ i, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R))
      (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := Algebra.TensorProduct.includeRight_surjective C residue_surjective z
  rw [Algebra.TensorProduct.includeRight_apply, one_tmul_eq_zero_iff]
  have hi : ∀ i, c * e i ∈ (maximalIdeal R).map (algebraMap R C) := by
    intro i
    have h := hz i
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Ideal.Quotient.mkₐ_eq_mk, one_tmul_eq_zero_iff] at h
    exact mul_mem_map_maximalIdeal_of_mk_mem (R := R) (e i) c (hce.idem i) h
  have hc : c = ∑ i, c * e i := by rw [← Finset.mul_sum, hce.complete, mul_one]
  rw [hc]
  exact Ideal.sum_mem _ fun i _ => hi i

private theorem exists_algHom
    (ψbar : ResidueField R ⊗[R] O →ₐ[ResidueField R] ResidueField R ⊗[R] C) :
    ∃ ψ : O →ₐ[R] C, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ =
      ψbar := by
  classical
  obtain ⟨hfin, e, hce, -, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_quotient
      (R := R) (S := C)

  let Cq : MaximalSpectrum C → Type w := fun m => C ⧸ Ideal.span {1 - e m}
  let π : (m : MaximalSpectrum C) → (C →ₐ[R] Cq m) :=
    fun m => Ideal.Quotient.mkₐ R (Ideal.span {1 - e m})
  have hψm : ∀ m, ∃ ψm : O →ₐ[R] Cq m,
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψm =
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) (π m)).comp ψbar
          := by
    intro m
    haveI : IsLocalRing (Cq m) := hloc m
    haveI : Module.Finite R (Cq m) := inferInstance
    exact exists_algHom_of_isLocalRing _
  choose ψm hψm using hψm

  let Φ : C →ₐ[R] ((m : MaximalSpectrum C) → Cq m) := AlgHom.pi π
  have hΦ : Function.Bijective Φ := by
    have := CompleteOrthogonalIdempotents.bijective_pi hce
    exact this
  let EΦ : C ≃ₐ[R] ((m : MaximalSpectrum C) → Cq m) := AlgEquiv.ofBijective Φ hΦ
  let ψ : O →ₐ[R] C := (EΦ.symm : ((m : MaximalSpectrum C) → Cq m) →ₐ[R] C).comp (AlgHom.pi ψm)
  have hπψ : ∀ m, (π m).comp ψ = ψm m := by
    intro m
    apply AlgHom.ext
    intro o
    show (Φ (EΦ.symm (AlgHom.pi ψm o))) m = ψm m o
    rw [show Φ (EΦ.symm (AlgHom.pi ψm o)) = AlgHom.pi ψm o from EΦ.apply_symm_apply _]
    rfl
  refine ⟨ψ, ?_⟩
  apply AlgHom.ext
  intro x
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_map_mk_eq_zero e hce
  intro m
  rw [map_sub, sub_eq_zero]
  show (Algebra.TensorProduct.map (AlgHom.id _ _) (π m)).comp
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ) x =
    (Algebra.TensorProduct.map (AlgHom.id _ _) (π m)).comp ψbar x
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, hπψ, hψm]

end Assemble

end H1Aux

namespace Algebra.Etale

/-- **Residue-field algebra maps out of finite étale algebras lift uniquely.** Over a
Henselian local ring `R`, a residue-field algebra map between the residue-field base
changes of a finite étale `R`-algebra `O` and a finite `R`-algebra `C` lifts to a
unique `R`-algebra map `O →ₐ[R] C`. The target `C` is not assumed étale or local. -/
theorem existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (O : Type v) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type w) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField
        R)) ψ = ψbar := by
  refine ⟨(H1Aux.exists_algHom ψbar).choose, (H1Aux.exists_algHom ψbar).choose_spec, ?_⟩
  intro ψ' hψ'
  exact H1Aux.algHom_eq_of_map_eq _ _ (hψ'.trans (H1Aux.exists_algHom ψbar).choose_spec.symm)

end Algebra.Etale
