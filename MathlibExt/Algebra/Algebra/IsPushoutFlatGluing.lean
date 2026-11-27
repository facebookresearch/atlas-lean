/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_Algebra_IsPushout_exists_algEquiv_slice_eq_of_flat.lean`,
`P2M/Sol/S_Algebra_IsPushout_exists_algEquiv_slice_eq_of_flat.lean`,
`Theorems/Thm_Algebra_IsPushout_slice_ext_and_exists_of_flat.lean`
and
`P2M/Sol/S_Algebra_IsPushout_slice_ext_and_exists_of_flat.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct

import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace Algebra.IsPushout

private theorem slice_ext_and_exists_of_flat
    {B : Type u} {B₁ : Type v} {B' : Type w} {M : Type x} {N : Type y}
    [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B B'] [Algebra B M]
    [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N]
    [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (p : Fin 3 → (B' →ₐ[B] B))
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B,
      (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) →
        ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' N x) = algebraMap B M (p i x)) :
    (∀ n n' : N, (∀ i, e i n = e i n') → n = n') ∧
    (∀ m : Fin 3 → M,
      (∀ i j, m i - m j ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) →
        ∃ n : N, ∀ i, e i n = m i) := by
  classical
  have : Algebra.IsPushout B M B' N := Algebra.IsPushout.symm inferInstance
  let E : M ⊗[B] B' ≃ₐ[M] N := Algebra.IsPushout.equiv B M B' N
  let Pl : B' →ₗ[B] (Fin 3 → B) := LinearMap.pi fun i => (p i).toLinearMap
  let Ψ : M ⊗[B] B' →ₗ[B] (Fin 3 → M) :=
    (TensorProduct.piScalarRight B B M (Fin 3)).toLinearMap ∘ₗ
      LinearMap.lTensor M Pl
  have hΨ_tmul : ∀ (m : M) (b : B') (i : Fin 3), Ψ (m ⊗ₜ b) i = p i b • m := by
    intro m b i
    simp only [Ψ, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    rfl
  have hE : ∀ (x : M ⊗[B] B') (i : Fin 3), e i (E x) = Ψ x i := by
    intro x i
    induction x using TensorProduct.inductionOn with
    | tmul m b =>
      rw [hΨ_tmul]
      change e i (Algebra.IsPushout.equiv B M B' N (m ⊗ₜ b)) = _
      rw [Algebra.IsPushout.equiv_tmul, map_mul, heM, heB, Algebra.smul_def,
        mul_comm]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hPl : Function.Injective Pl := fun x y h => hinj x y (fun i => congrFun h i)
  have hΨinj : Function.Injective Ψ :=
    (TensorProduct.piScalarRight B B M (Fin 3)).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap Pl hPl)
  refine ⟨?_, ?_⟩
  · intro n n' h
    obtain ⟨x, rfl⟩ := E.surjective n
    obtain ⟨x', rfl⟩ := E.surjective n'
    have hxx : x = x' := hΨinj (funext fun i => by rw [← hE, ← hE, h i])
    rw [hxx]
  · have hsingle : ∀ (k : Fin 3) (d : M),
        d ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M) →
          ∃ n : N, ∀ i, e i n = (Pi.single k d : Fin 3 → M) i := by
      intro k d hd
      refine Submodule.span_induction
        (p := fun d _ => ∃ n : N, ∀ i, e i n = (Pi.single k d : Fin 3 → M) i)
        ?_ ?_ ?_ ?_ hd
      · rintro _ ⟨j, hj, rfl⟩
        have hj0 : algebraMap B B₁ j = 0 := hj
        obtain ⟨x, hx⟩ := hsurj (Pi.single k j : Fin 3 → B) (fun i i' => by
          simp only [Pi.single_apply]
          split_ifs <;> simp [hj0])
        refine ⟨algebraMap B' N x, fun i => ?_⟩
        rw [heB, hx, Pi.single_apply, Pi.single_apply]
        split_ifs <;> simp
      · exact ⟨0, fun i => by simp⟩
      · rintro d₁ d₂ _ _ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩
        exact ⟨n₁ + n₂, fun i => by
          rw [map_add, hn₁, hn₂, Pi.single_add, Pi.add_apply]⟩
      · rintro c d _ ⟨n, hn⟩
        refine ⟨algebraMap M N c * n, fun i => ?_⟩
        rw [map_mul, heM, hn, Pi.single_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp
    intro m hm
    obtain ⟨n₁, hn₁⟩ := hsingle 1 (m 1 - m 0) (hm 1 0)
    obtain ⟨n₂, hn₂⟩ := hsingle 2 (m 2 - m 0) (hm 2 0)
    refine ⟨algebraMap M N (m 0) + n₁ + n₂, fun i => ?_⟩
    rw [map_add, map_add, heM, hn₁, hn₂]
    fin_cases i <;> simp

/-- Flat base change preserves triple gluing of algebra automorphisms.

Given a pushout square with `M` flat over `B`, a comparison map
to `B₁`, and three slices `e i` of `N` over `M` compatible with three slices
`p i : B' → B` over `B₁` that identify `B'` with the triples in `B³` whose
images in `B₁` agree (the `p i` are jointly injective, and every such triple
is their value at some element of `B'`), every triple of automorphisms of `M`
that is trivial modulo the extension to `M` of the kernel of `B → B₁` glues
to a unique automorphism of `N` over `B'`. The glued automorphism is itself
trivial modulo the extension to `N` of the kernel of `B' → B₁`, and it is the
unique algebra map over `B'` with the prescribed slices. -/
public theorem exists_algEquiv_slice_eq_of_flat
    {B : Type u} {B₁ : Type v} {B' : Type w} {M : Type x} {N : Type y}
    [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M]
    [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N]
    [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B,
      (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) →
        ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' N x) = algebraMap B M (p i x))
    (t : Fin 3 → (M ≃ₐ[B] M))
    (ht : ∀ (i : Fin 3) (m : M),
      t i m - m ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) :
    ∃ σ : N ≃ₐ[B'] N,
      (∀ (i : Fin 3) (n : N), e i (σ n) = t i (e i n)) ∧
      (∀ n : N, σ n - n ∈ (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' N)) ∧
      (∀ σ' : N →ₐ[B'] N,
        (∀ (i : Fin 3) (n : N), e i (σ' n) = t i (e i n)) → ∀ n : N, σ' n = σ n) := by
  classical
  obtain ⟨hinjN, hsurjN⟩ := slice_ext_and_exists_of_flat
    (B := B) (B₁ := B₁) (B' := B') (M := M) (N := N)
    p hinj hsurj e heM heB
  let J : Ideal M := (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)
  let J' : Ideal N := (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' N)
  have ht' : ∀ (i : Fin 3) (m : M), (t i).symm m - m ∈ J := by
    intro i m
    have h := ht i ((t i).symm m)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [← neg_sub]
    exact J.neg_mem h
  have hcong : ∀ (n : N) (i j : Fin 3), e i n - e j n ∈ J := by
    have : Algebra.IsPushout B M B' N := Algebra.IsPushout.symm inferInstance
    intro n i j
    obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv B M B' N).surjective n
    induction x using TensorProduct.inductionOn with
    | tmul m b =>
      rw [Algebra.IsPushout.equiv_tmul, map_mul, map_mul, heM, heM, heB, heB,
        ← mul_sub, ← map_sub]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker, map_sub, hp, hp, sub_self]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact J.add_mem hx hy
  have hex : ∀ (s : Fin 3 → (M ≃ₐ[B] M)),
      (∀ i m, s i m - m ∈ J) →
        ∀ n : N, ∃ n' : N, ∀ i, e i n' = s i (e i n) := by
    intro s hs n
    refine hsurjN (fun i => s i (e i n)) (fun i j => ?_)
    have hdecomp : s i (e i n) - s j (e j n) =
        (s i (e i n) - e i n) + (e i n - e j n) - (s j (e j n) - e j n) := by ring
    rw [hdecomp]
    exact J.sub_mem (J.add_mem (hs i _) (hcong n i j)) (hs j _)
  have hmk : ∀ (s : Fin 3 → (M ≃ₐ[B] M)),
      (∀ i m, s i m - m ∈ J) →
        ∃ σ : N →ₐ[B'] N, ∀ i n, e i (σ n) = s i (e i n) := by
    intro s hs
    choose f hf using hex s hs
    let σ₀ : N →ₐ[B'] N :=
      { toFun := f
        map_one' := hinjN _ _ fun i => by rw [hf, map_one, map_one]
        map_mul' := fun x y =>
          hinjN _ _ fun i => by rw [hf, map_mul, map_mul, map_mul, hf, hf]
        map_zero' := hinjN _ _ fun i => by rw [hf, map_zero, map_zero]
        map_add' := fun x y =>
          hinjN _ _ fun i => by rw [hf, map_add, map_add, map_add, hf, hf]
        commutes' := fun x =>
          hinjN _ _ fun i => by rw [hf, heB, AlgEquiv.commutes] }
    exact ⟨σ₀, fun i n => hf n i⟩
  obtain ⟨σ, hσ⟩ := hmk t ht
  obtain ⟨σ', hσ'⟩ := hmk (fun i => (t i).symm) ht'
  have h1 : ∀ n, σ (σ' n) = n :=
    fun n => hinjN _ _ fun i => by rw [hσ, hσ', AlgEquiv.apply_symm_apply]
  have h2 : ∀ n, σ' (σ n) = n :=
    fun n => hinjN _ _ fun i => by rw [hσ', hσ, AlgEquiv.symm_apply_apply]
  refine ⟨AlgEquiv.ofAlgHom σ σ' (AlgHom.ext h1) (AlgHom.ext h2),
    fun i n => hσ i n, ?_, ?_⟩
  · have hsingle : ∀ (k : Fin 3) (d : M), d ∈ J →
        ∃ n : N, n ∈ J' ∧ ∀ i, e i n = (Pi.single k d : Fin 3 → M) i := by
      intro k d hd
      refine Submodule.span_induction
        (p := fun d _ => ∃ n : N, n ∈ J' ∧
          ∀ i, e i n = (Pi.single k d : Fin 3 → M) i) ?_ ?_ ?_ ?_ hd
      · rintro _ ⟨j, hj, rfl⟩
        have hj0 : algebraMap B B₁ j = 0 := hj
        obtain ⟨x, hx⟩ := hsurj (Pi.single k j : Fin 3 → B) (fun i i' => by
          simp only [Pi.single_apply]
          split_ifs <;> simp [hj0])
        refine ⟨algebraMap B' N x, Ideal.mem_map_of_mem _ ?_, fun i => ?_⟩
        · rw [RingHom.mem_ker, ← hp 0, hx, Pi.single_apply]
          split_ifs <;> simp [hj0]
        · rw [heB, hx, Pi.single_apply, Pi.single_apply]
          split_ifs <;> simp
      · exact ⟨0, J'.zero_mem, fun i => by simp⟩
      · rintro d₁ d₂ _ _ ⟨n₁, hn₁J, hn₁⟩ ⟨n₂, hn₂J, hn₂⟩
        exact ⟨n₁ + n₂, J'.add_mem hn₁J hn₂J, fun i => by
          rw [map_add, hn₁, hn₂, Pi.single_add, Pi.add_apply]⟩
      · rintro c d _ ⟨n, hnJ, hn⟩
        refine ⟨algebraMap M N c * n, J'.mul_mem_left _ hnJ, fun i => ?_⟩
        rw [map_mul, heM, hn, Pi.single_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp
    intro n
    change σ n - n ∈ J'
    obtain ⟨n₀, hn₀J, hn₀⟩ := hsingle 0 _ (ht 0 (e 0 n))
    obtain ⟨n₁, hn₁J, hn₁⟩ := hsingle 1 _ (ht 1 (e 1 n))
    obtain ⟨n₂, hn₂J, hn₂⟩ := hsingle 2 _ (ht 2 (e 2 n))
    have hsum : σ n - n = n₀ + n₁ + n₂ := hinjN _ _ fun i => by
      rw [map_sub, hσ, map_add, map_add, hn₀, hn₁, hn₂]
      fin_cases i <;> simp
    rw [hsum]
    exact J'.add_mem (J'.add_mem hn₀J hn₁J) hn₂J
  · intro σ'' hσ'' n
    exact hinjN _ _ fun i => by rw [hσ'']; exact (hσ i n).symm

end Algebra.IsPushout
