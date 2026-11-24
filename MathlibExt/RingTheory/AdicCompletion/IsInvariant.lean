/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant.lean`
and
`P2M/Sol/S_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Filtration

/-!
# Adic completion of an invariant algebra

For a finite faithful algebra `S` over a Noetherian ring `A`, with a finite
group `G` acting on `S` so that the fixed points are exactly the image of
`A`, adic completion embeds the completion of `A` into that of `S`, and its
image is exactly the elements fixed by the completed action of `G`.
-/

@[expose] public section

namespace AdicCompletionInvariantAux

open LinearMap AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]

private theorem map_injective' [IsNoetherianRing R] [Module.Finite R N] {f : M →ₗ[R] N}
    (hf : Function.Injective f) : Function.Injective (AdicCompletion.map I f) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨42, fun n _ ↦ ⟨n + k, by lia, n, by lia, ?_⟩⟩
  rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M),
    Submodule.map_smul'', Submodule.map_top]
  apply (smul_mono_right _ inf_le_right : I ^ n • (I ^ k • ⊤ ⊓ (range f)) ≤ _)
  nth_rw 1 [show n = n + k - k by lia]
  rw [← hk (n + k) (show n + k ≥ k by lia)]
  exact ⟨by simpa using congrArg (fun x ↦ x.val (n + k)) hx, ⟨a (n + k), rfl⟩⟩

variable [IsNoetherianRing R] [Module.Finite R N]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)

section

variable {k : ℕ}
  (hkn : ∀ n ≥ k, I ^ n • ⊤ ⊓ LinearMap.range f = I ^ (n - k) • (I ^ k • ⊤ ⊓ LinearMap.range f))
  (x : AdicCauchySequence I N) (hker : ∀ (n : ℕ), g (x n) ∈ (I ^ n • ⊤ : Submodule R P))

private noncomputable def mapExactAuxDelta {n : ℕ} {d : N}
    (hdmem : d ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N)) {y yₙ : M}
    (hd : f y = x (k + n + 1) - d) (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N)) :
    { d : (I ^ n • ⊤ : Submodule R M)
      | f (yₙ + d) - x (k + n + 1) ∈ (I ^ (k + n + 1) • ⊤ : Submodule R N) } :=
  have h : f (y - yₙ) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
    simp only [map_sub, hd]
    convert_to x (k + n + 1) - x (k + n) - d - (f yₙ - x (k + n)) ∈ I ^ (k + n) • ⊤
    · abel
    · refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) hyₙ
      · rw [← Submodule.Quotient.eq]
        exact AdicCauchySequence.mk_eq_mk (by lia) _
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hdmem
  have hincl : I ^ (k + n - k) • (I ^ k • ⊤ ⊓ range f) ≤ I ^ (k + n - k) • (range f) :=
    smul_mono_right _ inf_le_right
  have hyyₙ : y - yₙ ∈ (I ^ n • ⊤ : Submodule R M) := by
    convert_to y - yₙ ∈ (I ^ (k + n - k) • ⊤ : Submodule R M)
    · simp
    · rw [← Submodule.comap_map_eq_of_injective hf (I ^ (k + n - k) • ⊤ : Submodule R M),
        Submodule.map_smul'', Submodule.map_top]
      apply hincl
      rw [← hkn (k + n) (by lia)]
      exact ⟨h, ⟨y - yₙ, rfl⟩⟩
  ⟨⟨y - yₙ, hyyₙ⟩, by simpa [hd, Nat.succ_eq_add_one, Nat.add_assoc]⟩

open Submodule

include hfg in
private noncomputable def mapExactAux :
    (n : ℕ) → { a : M | f a - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) }
  | .zero =>
    let d := (h2 0).choose
    let y := (h2 0).choose_spec.choose
    have hdy : f y = x (k + 0) - d := (h2 0).choose_spec.choose_spec.right
    have hdmem := (h2 0).choose_spec.choose_spec.left
    ⟨y, by simpa [hdy]⟩
  | .succ n =>
    let d := (h2 <| n + 1).choose
    let y := (h2 <| n + 1).choose_spec.choose
    have hdy : f y = x (k + (n + 1)) - d := (h2 <| n + 1).choose_spec.choose_spec.right
    have hdmem := (h2 <| n + 1).choose_spec.choose_spec.left
    let ⟨yₙ, (hyₙ : f yₙ - x (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N))⟩ :=
      mapExactAux n
    let ⟨d, hd⟩ := mapExactAuxDelta I hf hkn x hdmem hdy hyₙ
    ⟨yₙ + d, hd⟩
where
  h1 (n : ℕ) : g (x (k + n)) ∈ Submodule.map g (I ^ (k + n) • ⊤ : Submodule R N) := by
    rw [map_smul'', Submodule.map_top, range_eq_top.mpr hg]
    exact hker (k + n)
  h2 (n : ℕ) : ∃ (d : N) (y : M),
      d ∈ (I ^ (k + n) • ⊤ : Submodule R N) ∧ f y = x (k + n) - d := by
    obtain ⟨d, hdmem, hd⟩ := h1 n
    obtain ⟨y, hdy⟩ := (hfg (x (k + n) - d)).mp (by simp [hd])
    exact ⟨d, y, hdmem, hdy⟩

end

include hf hfg hg in
private theorem map_exact' : Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y ↦ ?_)
  · rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
    intro hz
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
    have hb (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R P) := by
      simpa using congrArg (fun x ↦ x.val n) hz
    let a := mapExactAux I hf hfg hg hk b hb
    refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M (fun n ↦ (a n : M)) ?_), ?_⟩
    · refine fun n ↦ SModEq.symm ?_
      simp [a, mapExactAux, SModEq]
    · ext n
      suffices h : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
            Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (k + n)) by
        simp [h, AdicCauchySequence.mk_eq_mk (show n ≤ k + n by lia)]
      rw [Submodule.Quotient.eq]
      have hle : (I ^ (k + n) • ⊤ : Submodule R N) ≤ (I ^ n • ⊤ : Submodule R N) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))
      exact hle (a n).property

omit [IsNoetherianRing R] [Module.Finite R N] in
private theorem map_sub_apply (f g : M →ₗ[R] N) (x : AdicCompletion I M) :
    AdicCompletion.map I (f - g) x = AdicCompletion.map I f x - AdicCompletion.map I g x := by
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  ext n
  simp

end AdicCompletionInvariantAux

namespace AdicCompletion

/-- The adic completion of a finite faithful invariant algebra embeds into
the completion of the algebra, with image exactly the invariants of the
completed finite-group action. -/
public theorem map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
    [Algebra.IsInvariant A S G] :
    Function.Injective (AdicCompletion.map I (Algebra.linearMap A S)) ∧
    ∀ x : AdicCompletion I S,
      x ∈ LinearMap.range (AdicCompletion.map I (Algebra.linearMap A S)) ↔
        ∀ g : G, AdicCompletion.map I (DistribSMul.toLinearMap A S g) x = x := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hι : Function.Injective (Algebra.linearMap A S) := FaithfulSMul.algebraMap_injective A S
  have hfix : ∀ g : G, DistribSMul.toLinearMap A S g ∘ₗ Algebra.linearMap A S =
      Algebra.linearMap A S := fun g ↦ by
    ext
    simp
  let δ : S →ₗ[A] (G → S) := LinearMap.pi fun g ↦ DistribSMul.toLinearMap A S g - LinearMap.id
  have hδ_apply : ∀ (s : S) (g : G), δ s g = g • s - s := fun s g ↦ rfl
  have hproj : ∀ g : G, LinearMap.proj g ∘ₗ δ = DistribSMul.toLinearMap A S g - LinearMap.id :=
    fun g ↦ rfl
  have hker : LinearMap.ker δ ≤ LinearMap.range (Algebra.linearMap A S) := by
    intro s hs
    have hs' : ∀ g : G, g • s = s := fun g ↦ by
      have := congrFun (LinearMap.mem_ker.mp hs) g
      rw [hδ_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) s hs'
    exact ⟨a, ha⟩
  have hrange : LinearMap.range (Algebra.linearMap A S) ≤ LinearMap.ker δ := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    funext g
    rw [hδ_apply, Pi.zero_apply, sub_eq_zero, Algebra.linearMap_apply]
    exact smul_algebraMap g a
  set W : Submodule A S := LinearMap.range (Algebra.linearMap A S) with hW
  let π : S →ₗ[A] S ⧸ W := W.mkQ
  let δ' : S ⧸ W →ₗ[A] (G → S) := W.liftQ δ hrange
  have hδ' : Function.Injective δ' :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot W δ hrange hker)
  have hδ'π : δ' ∘ₗ π = δ := Submodule.liftQ_mkQ W δ hrange
  have hπ : Function.Surjective π := Submodule.mkQ_surjective W
  have hexact : Function.Exact (Algebra.linearMap A S) π := LinearMap.exact_map_mkQ_range _
  have hE : Function.Exact (map I (Algebra.linearMap A S)) (map I π) :=
    AdicCompletionInvariantAux.map_exact' I hι hexact hπ
  have hinjδ' : Function.Injective (map I δ') := AdicCompletionInvariantAux.map_injective' I hδ'
  refine ⟨AdicCompletionInvariantAux.map_injective' I hι, fun x ↦ ?_⟩
  constructor
  · rintro ⟨a, rfl⟩ g
    rw [map_comp_apply, hfix]
  · intro hx
    have hδx : map I δ x = 0 := by
      apply (piEquivOfFintype I (fun _ : G ↦ S)).injective
      rw [_root_.map_zero]
      funext g
      simp only [piEquivOfFintype_apply, pi, LinearMap.pi_apply, Pi.zero_apply]
      rw [map_comp_apply, hproj, AdicCompletionInvariantAux.map_sub_apply, AdicCompletion.map_id,
        LinearMap.id_apply, hx g, sub_self]
    have hπx : map I π x = 0 := by
      apply hinjδ'
      rw [map_comp_apply, hδ'π, hδx, _root_.map_zero]
    exact (hE x).mp hπx

end AdicCompletion
