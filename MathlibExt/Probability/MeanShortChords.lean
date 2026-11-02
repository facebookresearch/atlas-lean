/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

private theorem block_map_inv (E : ℕ ≃ ℕ) (B : Finset ℕ) :
    (B.map E.toEmbedding).map E.symm.toEmbedding = B := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨x', ⟨x'', hx''B, rfl⟩, hx'⟩
    have hxeq : x = x'' := by
      calc x = E.symm.toEmbedding (E.toEmbedding x'') := hx'.symm
        _ = x'' := Equiv.symm_apply_apply E x''
    rw [hxeq]
    exact hx''B
  · intro hxB
    exact ⟨E.toEmbedding x, ⟨x, hxB, rfl⟩, Equiv.symm_apply_apply E x⟩

private theorem block_map_inv' (E : ℕ ≃ ℕ) (B : Finset ℕ) :
    (B.map E.symm.toEmbedding).map E.toEmbedding = B := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨x', ⟨x'', hx''B, rfl⟩, hx'⟩
    have hxeq : x = x'' := by
      calc x = E.toEmbedding (E.symm.toEmbedding x'') := hx'.symm
        _ = x'' := Equiv.apply_symm_apply E x''
    rw [hxeq]
    exact hx''B
  · intro hxB
    exact ⟨E.symm.toEmbedding x, ⟨x, hxB, rfl⟩, Equiv.apply_symm_apply E x⟩

private theorem block_map_injective (E : ℕ ≃ ℕ) :
    Function.Injective (fun B : Finset ℕ => B.map E.toEmbedding) := by
  intro B1 B2 h
  have h2 := congrArg (fun B => B.map E.symm.toEmbedding) h
  rw [block_map_inv, block_map_inv] at h2
  exact h2

private theorem range_map_symm_of (E : ℕ ≃ ℕ) (N : ℕ)
    (hR : (Finset.range N).map E.toEmbedding = Finset.range N) :
    (Finset.range N).map E.symm.toEmbedding = Finset.range N := by
  have h := congrArg (fun s => s.map E.symm.toEmbedding) hR
  rw [block_map_inv] at h
  exact h.symm

private theorem image_biUnion_id_map (E : ℕ ≃ ℕ) (D : Finset (Finset ℕ)) :
    (D.image fun B : Finset ℕ => B.map E.toEmbedding).biUnion id =
      (D.biUnion id).map E.toEmbedding := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_map, id_eq]
  constructor
  · rintro ⟨B, ⟨B', hB'D, rfl⟩, hx⟩
    rw [Finset.mem_map] at hx
    obtain ⟨y, hyB', hyE⟩ := hx
    exact ⟨y, ⟨B', hB'D, hyB'⟩, hyE⟩
  · rintro ⟨y, ⟨B', hB'D, hyB'⟩, hyE⟩
    refine ⟨B'.map E.toEmbedding, ⟨B', hB'D, rfl⟩, ?_⟩
    rw [Finset.mem_map]
    exact ⟨y, hyB', hyE⟩

private theorem image_mem_diagrams (F : ℕ ≃ ℕ) (N m k : ℕ) (D : Finset (Finset ℕ))
    (hR : (Finset.range N).map F.toEmbedding = Finset.range N)
    (hD : D ∈ (Finset.range N).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = m ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range N) :
    D.image (fun B : Finset ℕ => B.map F.toEmbedding) ∈
      (Finset.range N).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
        D.card = m ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range N := by
  classical
  rw [Finset.mem_filter] at hD ⊢
  obtain ⟨hDsub, hDcard, hDblock, hDunion⟩ := hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_powerset] at hDsub ⊢
    intro B hB
    rw [Finset.mem_image] at hB
    obtain ⟨B', hB'D, rfl⟩ := hB
    rw [Finset.mem_powerset]
    have hB'sub : B' ⊆ Finset.range N := by
      have hmem := hDsub hB'D
      rw [Finset.mem_powerset] at hmem
      exact hmem
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨z, hzB', hzE⟩ := hy
    rw [← hR]
    exact Finset.mem_map.mpr ⟨z, hB'sub hzB', hzE⟩
  · rw [Finset.card_image_of_injective _ (block_map_injective F)]
    exact hDcard
  · intro B hB
    rw [Finset.mem_image] at hB
    obtain ⟨B', hB'D, rfl⟩ := hB
    rw [Finset.card_map]
    exact hDblock B' hB'D
  · rw [image_biUnion_id_map, hDunion, hR]

private theorem image_image_eq (E : ℕ ≃ ℕ) (D : Finset (Finset ℕ)) :
    ((D.image fun B : Finset ℕ => B.map E.toEmbedding).image
      fun B : Finset ℕ => B.map E.symm.toEmbedding) = D := by
  ext B
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨B', ⟨B'', hB''D, rfl⟩, hB⟩
    have hBB : B'' = B := by
      have h2 : (B''.map E.toEmbedding).map E.symm.toEmbedding = B := hB
      rw [block_map_inv] at h2
      exact h2
    rw [hBB] at hB''D
    exact hB''D
  · intro hBD
    exact ⟨B.map E.toEmbedding, ⟨B, hBD, rfl⟩, block_map_inv E B⟩

private theorem fiber_card_eq_of_perm (N m k : ℕ) (S T : Finset ℕ) (E : ℕ ≃ ℕ)
    (hST : S.map E.toEmbedding = T)
    (hR : (Finset.range N).map E.toEmbedding = Finset.range N) :
    ((((Finset.range N).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = m ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range N)).filter
      fun D => S ∈ D).card =
    ((((Finset.range N).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = m ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range N)).filter
      fun D => T ∈ D).card := by
  classical
  have hRsymm : (Finset.range N).map E.symm.toEmbedding = Finset.range N :=
    range_map_symm_of E N hR
  have hTS : T.map E.symm.toEmbedding = S := by
    have h := congrArg (fun s => s.map E.symm.toEmbedding) hST
    rw [block_map_inv] at h
    exact h.symm
  have hSTmem : ∀ D : Finset (Finset ℕ), S ∈ D →
      T ∈ D.image fun B : Finset ℕ => B.map E.toEmbedding := by
    intro D hSD
    rw [Finset.mem_image]
    exact ⟨S, hSD, hST⟩
  have hTSmem : ∀ D : Finset (Finset ℕ), T ∈ D →
      S ∈ D.image fun B : Finset ℕ => B.map E.symm.toEmbedding := by
    intro D hTD
    rw [Finset.mem_image]
    exact ⟨T, hTD, hTS⟩
  apply Finset.card_bij (fun D _ => D.image fun B : Finset ℕ => B.map E.toEmbedding)
  · intro D hD
    rw [Finset.mem_filter] at hD ⊢
    obtain ⟨hDdiag, hSD⟩ := hD
    exact ⟨image_mem_diagrams E N m k D hR hDdiag, hSTmem D hSD⟩
  · intro D1 _ D2 _ h
    have h2 := congrArg
      (fun D => D.image fun B : Finset ℕ => B.map E.symm.toEmbedding) h
    rw [image_image_eq, image_image_eq] at h2
    exact h2
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    obtain ⟨hD'diag, hTD'⟩ := hD'
    refine ⟨D'.image (fun B : Finset ℕ => B.map E.symm.toEmbedding), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨image_mem_diagrams E.symm N m k D' hRsymm hD'diag, hTSmem D' hTD'⟩
    · have hinv2 := image_image_eq E.symm D'
      simp only [Equiv.symm_symm] at hinv2
      exact hinv2
private theorem exists_perm_map (N : ℕ) (S T : Finset ℕ)
    (hS : S ⊆ Finset.range N) (hT : T ⊆ Finset.range N)
    (hcard : S.card = T.card) :
    ∃ E : ℕ ≃ ℕ, S.map E.toEmbedding = T ∧
      (Finset.range N).map E.toEmbedding = Finset.range N := by
  classical
  let U : Finset ℕ := Finset.range N
  have hSU : ∀ x : ℕ, x ∈ S → x ∈ U := fun x hx => hS hx
  have hTU : ∀ x : ℕ, x ∈ T → x ∈ U := fun x hx => hT hx
  let equivS : { u : ↥U // u.val ∈ S } ≃ ↥S :=
    { toFun := fun u => ⟨u.val.val, u.prop⟩
      invFun := fun x => ⟨⟨x.val, hSU x.val x.prop⟩, x.prop⟩
      left_inv := fun u => by obtain ⟨⟨x, hx⟩, h⟩ := u; rfl
      right_inv := fun x => by obtain ⟨x, hx⟩ := x; rfl }
  let equivT : { u : ↥U // u.val ∈ T } ≃ ↥T :=
    { toFun := fun u => ⟨u.val.val, u.prop⟩
      invFun := fun x => ⟨⟨x.val, hTU x.val x.prop⟩, x.prop⟩
      left_inv := fun u => by obtain ⟨⟨x, hx⟩, h⟩ := u; rfl
      right_inv := fun x => by obtain ⟨x, hx⟩ := x; rfl }
  have hcard' : Fintype.card ↥S = Fintype.card ↥T := by
    rw [Fintype.card_coe, Fintype.card_coe, hcard]
  let e : { u : ↥U // u.val ∈ S } ≃ { u : ↥U // u.val ∈ T } :=
    equivS.trans ((Fintype.equivOfCardEq hcard').trans equivT.symm)
  let σ : Equiv.Perm ↥U := e.extendSubtype
  have hmem : ∀ (x : ℕ) (hxU : x ∈ U) (hxS : x ∈ S),
      (σ ⟨x, hxU⟩).val ∈ T :=
    fun x hxU hxS => Equiv.extendSubtype_mem e ⟨x, hxU⟩ hxS
  have hnot : ∀ (y : ℕ) (hyU : y ∈ U) (hyT : y ∈ T),
      (σ.symm ⟨y, hyU⟩).val ∈ S := by
    intro y hyU hyT
    by_contra hcon
    have h2 := Equiv.extendSubtype_not_mem e (σ.symm ⟨y, hyU⟩) hcon
    rw [Equiv.apply_symm_apply] at h2
    exact h2 hyT
  let f : ℕ → ℕ := fun x => if hx : x ∈ U then (σ ⟨x, hx⟩).val else x
  let g : ℕ → ℕ := fun y => if hy : y ∈ U then (σ.symm ⟨y, hy⟩).val else y
  have hf : ∀ x (hx : x ∈ U), f x = (σ ⟨x, hx⟩).val := fun x hx => dite_eq_left hx
  have hg : ∀ y (hy : y ∈ U), g y = (σ.symm ⟨y, hy⟩).val := fun y hy => dite_eq_left hy
  have hf_neg : ∀ x (hx : x ∉ U), f x = x := fun x hx => dite_eq_right hx
  have hg_neg : ∀ y (hy : y ∉ U), g y = y := fun y hy => dite_eq_right hy
  have hgf : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ U
    · have hmemU : (σ ⟨x, hx⟩).val ∈ U := (σ ⟨x, hx⟩).prop
      have e1 : f x = (σ ⟨x, hx⟩).val := hf x hx
      have e2 : g ((σ ⟨x, hx⟩).val) = (σ.symm ⟨(σ ⟨x, hx⟩).val, hmemU⟩).val :=
        hg _ hmemU
      have h3 : σ.symm ⟨(σ ⟨x, hx⟩).val, hmemU⟩ = (⟨x, hx⟩ : ↥U) :=
        σ.symm_apply_apply ⟨x, hx⟩
      change g (f x) = x
      rw [e1, e2, h3]
    · have e1 : f x = x := hf_neg x hx
      rw [e1]
      exact hg_neg x hx
  have hfg : Function.RightInverse g f := by
    intro y
    by_cases hy : y ∈ U
    · have hmemU : (σ.symm ⟨y, hy⟩).val ∈ U := (σ.symm ⟨y, hy⟩).prop
      have e1 : g y = (σ.symm ⟨y, hy⟩).val := hg y hy
      have e2 : f ((σ.symm ⟨y, hy⟩).val)
          = (σ ⟨(σ.symm ⟨y, hy⟩).val, hmemU⟩).val := dite_eq_left hmemU
      have h3 : σ ⟨(σ.symm ⟨y, hy⟩).val, hmemU⟩ = (⟨y, hy⟩ : ↥U) :=
        σ.apply_symm_apply ⟨y, hy⟩
      change f (g y) = y
      rw [e1, e2, h3]
    · have e1 : g y = y := hg_neg y hy
      rw [e1]
      exact hf_neg y hy
  set E0 : ℕ ≃ ℕ := ⟨f, g, hgf, hfg⟩ with hE0
  have hEsymm : ∀ y, E0.symm y = g y := fun y => rfl
  have hEapp : ∀ x, E0 x = f x := fun x => rfl
  have hEappE : ∀ x, E0.toEmbedding x = f x := fun x => rfl
  refine ⟨E0, ?_, ?_⟩
  · ext y
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨x, hxS, hxE⟩
      have hxU : x ∈ U := hSU x hxS
      have hyT := hmem x hxU hxS
      have hxE' : f x = y := hxE
      rw [hf x hxU] at hxE'
      exact hxE' ▸ hyT
    · intro hyT
      have hyU : y ∈ U := hTU y hyT
      have hmemS : E0.symm y ∈ S := by
        rw [hEsymm y, hg y hyU]
        exact hnot y hyU hyT
      refine ⟨E0.symm y, hmemS, ?_⟩
      exact Equiv.apply_symm_apply _ _
  · ext y
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨x, hxU, hxE⟩
      have hxU' : x ∈ U := hxU
      have hxE' : f x = y := hxE
      rw [hf x hxU'] at hxE'
      rw [← hxE']
      exact (σ ⟨x, hxU'⟩).prop
    · intro hyU
      have hyU' : y ∈ U := hyU
      have hmemU : (σ.symm ⟨y, hyU'⟩).val ∈ U := (σ.symm ⟨y, hyU'⟩).prop
      refine ⟨E0.symm y, ?_, Equiv.apply_symm_apply _ _⟩
      rw [hEsymm y, hg y hyU']
      exact hmemU

private theorem sum_filter_card_swap
    (Dset : Finset (Finset (Finset ℕ))) (I : Finset ℕ) (S : ℕ → Finset ℕ) :
    ∑ D ∈ Dset, ((I.filter fun i => S i ∈ D).card) =
      ∑ i ∈ I, ((Dset.filter fun D => S i ∈ D).card) := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

private theorem ico_card_of_lt (k n i : ℕ) (hi : i < k * n - (k - 1)) :
    (Finset.Ico i (i + k)).card = k := by
  rw [Nat.card_Ico]
  have : i + k ≤ k * n := by omega
  omega

private theorem ico_subset_range (k n i : ℕ) (hi : i < k * n - (k - 1)) :
    Finset.Ico i (i + k) ⊆ Finset.range (k * n) := by
  intro x hx
  simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
  have : i + k ≤ k * n := by omega
  omega

private theorem interval_fiber_eq (k n i j : ℕ) (_hk : 0 < k)
    (hi : i < k * n - (k - 1)) (hj : j < k * n - (k - 1)) :
    ((((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n))).filter
      fun D => Finset.Ico i (i + k) ∈ D).card =
    ((((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n))).filter
      fun D => Finset.Ico j (j + k) ∈ D).card := by
  classical
  obtain ⟨E, hEST, hER⟩ := exists_perm_map (k * n)
    (Finset.Ico i (i + k)) (Finset.Ico j (j + k))
    (ico_subset_range k n i hi) (ico_subset_range k n j hj)
    (by rw [ico_card_of_lt k n i hi, ico_card_of_lt k n j hj])
  exact fiber_card_eq_of_perm (k * n) n k _ _ E hEST hER

private theorem kfiber_eq_s0 (k n : ℕ) (_hk : 0 < k) (hn : 0 < n) (S : Finset ℕ)
    (hS : S ∈ (Finset.range (k * n)).powersetCard k) :
    ((((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n))).filter
      fun D => S ∈ D).card =
    ((((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n))).filter
      fun D => Finset.Ico 0 k ∈ D).card := by
  classical
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSsub, hScard⟩ := hS
  have hS0sub : Finset.Ico 0 k ⊆ Finset.range (k * n) := by
    intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    obtain ⟨_, hxk⟩ := hx
    calc x < k := hxk
      _ ≤ k * n := Nat.le_mul_of_pos_right k hn
  have hS0card : (Finset.Ico 0 k).card = k := by
    rw [Nat.card_Ico, Nat.sub_zero]
  obtain ⟨E, hEST, hER⟩ := exists_perm_map (k * n) S (Finset.Ico 0 k)
    hSsub hS0sub (by rw [hScard, hS0card])
  exact fiber_card_eq_of_perm (k * n) n k _ _ E hEST hER

private theorem sum_blocks_swap (Dset : Finset (Finset (Finset ℕ))) (K : Finset (Finset ℕ)) :
    ∑ D ∈ Dset, ((K.filter fun S => S ∈ D).card) =
      ∑ S ∈ K, ((Dset.filter fun D => S ∈ D).card) := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

private theorem block_mem_powersetCard (k n : ℕ) (D : Finset (Finset ℕ)) (B : Finset ℕ)
    (hD : D ∈ ((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n)))
    (hBD : B ∈ D) :
    B ∈ (Finset.range (k * n)).powersetCard k := by
  rw [Finset.mem_filter] at hD
  obtain ⟨hDsub, _, hDblock, _⟩ := hD
  rw [Finset.mem_powersetCard]
  have hDsub' : D ⊆ (Finset.range (k * n)).powerset := Finset.mem_powerset.mp hDsub
  exact ⟨Finset.mem_powerset.mp (hDsub' hBD), hDblock B hBD⟩

private theorem filter_blocks_eq (k n : ℕ) (D : Finset (Finset ℕ))
    (hD : D ∈ ((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n))) :
    (((Finset.range (k * n)).powersetCard k).filter fun S => S ∈ D).card = D.card := by
  classical
  have hall : ∀ B ∈ D, B ∈ (Finset.range (k * n)).powersetCard k :=
    fun B hBD => block_mem_powersetCard k n D B hD hBD
  have heq : ((Finset.range (k * n)).powersetCard k).filter (fun S => S ∈ D) = D := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hSD⟩; exact hSD
    · intro hSD; exact ⟨hall S hSD, hSD⟩
  rw [heq]

private theorem diag_card_eq (k n : ℕ) (D : Finset (Finset ℕ))
    (hD : D ∈ ((Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
      D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n))) :
    D.card = n := by
  rw [Finset.mem_filter] at hD
  exact hD.2.1

private theorem chunk_le (k n j : ℕ) (hj : j < n) : j * k + k ≤ k * n := by
  have h1 : j + 1 ≤ n := hj
  have h2 : (j + 1) * k ≤ n * k := Nat.mul_le_mul h1 (le_refl k)
  have h3 : (j + 1) * k = j * k + k := by ring
  have h4 : n * k = k * n := by ring
  omega

private theorem chunk_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun j => Finset.Ico (j * k) (j * k + k)) := by
  intro a b h
  have hmem : a * k ∈ Finset.Ico (a * k) (a * k + k) :=
    Finset.mem_Ico.mpr ⟨le_refl _, Nat.lt_add_of_pos_right hk⟩
  have hred : Finset.Ico (a * k) (a * k + k) = Finset.Ico (b * k) (b * k + k) := h
  have hmem2 : a * k ∈ Finset.Ico (b * k) (b * k + k) := by
    rw [← hred]; exact hmem
  rw [Finset.mem_Ico] at hmem2
  obtain ⟨hlo, hhi⟩ := hmem2
  have hba : b ≤ a := Nat.le_of_mul_le_mul_right hlo hk
  have hab : a ≤ b := by
    have h2 : a * k < (b + 1) * k := by
      have hbk : (b + 1) * k = b * k + k := by ring
      rw [hbk]; exact hhi
    have h3 : a < b + 1 := Nat.lt_of_mul_lt_mul_right h2
    omega
  exact le_antisymm hab hba

private theorem chunk_mem_diagrams (k n : ℕ) (hk : 0 < k) :
    (Finset.range n).image (fun j => Finset.Ico (j * k) (j * k + k)) ∈
      (Finset.range (k * n)).powerset.powerset.filter fun D : Finset (Finset ℕ) =>
        D.card = n ∧ (∀ B ∈ D, B.card = k) ∧ D.biUnion id = Finset.range (k * n) := by
  classical
  rw [Finset.mem_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro B hB
    rw [Finset.mem_image] at hB
    obtain ⟨j, hj, rfl⟩ := hB
    rw [Finset.mem_powerset]
    intro x hx
    simp only [Finset.mem_Ico] at hx
    rw [Finset.mem_range]
    obtain ⟨hlo, hhi⟩ := hx
    have hjlt : j < n := Finset.mem_range.mp hj
    have hle := chunk_le k n j hjlt
    omega
  · rw [Finset.card_image_of_injective _ (chunk_injective k hk), Finset.card_range]
  · intro B hB
    rw [Finset.mem_image] at hB
    obtain ⟨j, _, rfl⟩ := hB
    show (Finset.Ico (j * k) (j * k + k)).card = k
    rw [Nat.card_Ico]
    omega
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, id_eq]
    constructor
    · rintro ⟨B, ⟨j, hj, rfl⟩, hx⟩
      simp only [Finset.mem_Ico] at hx
      obtain ⟨hlo, hhi⟩ := hx
      have hle := chunk_le k n j hj
      omega
    · intro hx
      refine ⟨Finset.Ico ((x / k) * k) ((x / k) * k + k), ⟨x / k, ?_, rfl⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hk]
        have hx2 : x < n * k := by
          have hcomm : k * n = n * k := by ring
          omega
        exact hx2
      · simp only [Finset.mem_Ico]
        have hmod : x % k < k := Nat.mod_lt x hk
        have hdm : k * (x / k) + x % k = x := Nat.div_add_mod x k
        have hcomm : k * (x / k) = (x / k) * k := by ring
        omega

/--
**Mean number of short chords in linear $k$-chord diagrams.** Let $k \ge 1$ and $n \ge 0$ be
integers. A linear $k$-chord diagram of length $kn$ is a set of $n$ subsets of
$\{0, 1, \dots, kn - 1\}$, each with $k$ elements, whose union is $\{0, 1, \dots, kn - 1\}$; it
is therefore a partition of this set into $n$ blocks of size $k$, its chords. A chord is short
when it consists of $k$ consecutive integers $\{i, i + 1, \dots, i + k - 1\}$. The number of
short chords, averaged over all linear $k$-chord diagrams of length $kn$, equals
$$
\frac{n\,(kn - k + 1)}{\binom{kn}{k}},
$$
where for $n = 0$ the denominator $\binom{0}{k}$ is $0$ and the quotient is read as $0$, which
is the mean over the single empty diagram.

For $n \ge 1$ there are $kn - k + 1$ sets of $k$ consecutive integers in $\{0, \dots, kn - 1\}$.
This is the mean theorem, distinct from the same paper's asymptotic Poisson distribution of
short chords.

Proves `Wanted` entry `mean_short_chords_in_linear_k_chord_diagrams`.

Source: Donovan Young, "Linear k-Chord Diagrams," Journal of Integer
Sequences 23 (2020), Article 20.9.1, Theorem (label Thmmean), lines 208–214,
https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex
-/
theorem mean_short_chords_in_linear_k_chord_diagrams
    (k n : ℕ) (hk : 0 < k) :
    let diagrams :=
      ((Finset.range (k * n)).powerset.powerset.filter fun D =>
        D.card = n ∧
          (∀ B ∈ D, B.card = k) ∧
          D.biUnion id = Finset.range (k * n))
    (diagrams.sum fun D =>
        ((((Finset.range (k * n - (k - 1))).filter fun i =>
          Finset.Ico i (i + k) ∈ D).card : ℝ))) /
      diagrams.card =
        (Nat.choose (k * n) k : ℝ)⁻¹ * n * (k * n - (k - 1)) := by
  classical
  change (((((Finset.range (k * n)).powerset.powerset.filter fun D =>
        D.card = n ∧
          (∀ B ∈ D, B.card = k) ∧
          D.biUnion id = Finset.range (k * n))).sum fun D =>
        ((((Finset.range (k * n - (k - 1))).filter fun i =>
          Finset.Ico i (i + k) ∈ D).card : ℝ))) /
      (((Finset.range (k * n)).powerset.powerset.filter fun D =>
        D.card = n ∧
          (∀ B ∈ D, B.card = k) ∧
          D.biUnion id = Finset.range (k * n))).card =
        (Nat.choose (k * n) k : ℝ)⁻¹ * n * (k * n - (k - 1)))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hM0 : k * 0 - (k - 1) = 0 := by simp
    have hr0 : Finset.range (k * 0) = (∅ : Finset ℕ) := by simp
    have hdiag0 : ((Finset.range (k * 0)).powerset.powerset.filter fun D =>
        D.card = 0 ∧
          (∀ B ∈ D, B.card = k) ∧
          D.biUnion id = Finset.range (k * 0)) = {(∅ : Finset (Finset ℕ))} := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_hDsub, hDcard, _, _⟩
        rw [Finset.card_eq_zero] at hDcard
        exact hDcard
      · intro hD0
        subst hD0
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Finset.mem_powerset.mpr (Finset.empty_subset _)
        · exact Finset.card_empty
        · intro B hB
          exact absurd hB (Finset.notMem_empty B)
        · rw [Finset.biUnion_empty, hr0]
    have hterm : ((((Finset.range 0).filter fun i =>
        Finset.Ico i (i + k) ∈ (∅ : Finset (Finset ℕ))).card : ℝ)) = 0 := by
      have hempty : ((Finset.range 0).filter fun i =>
          Finset.Ico i (i + k) ∈ (∅ : Finset (Finset ℕ))) = ∅ := by
        rw [Finset.range_zero]
        ext i
        simp
      rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hsum : (({(∅ : Finset (Finset ℕ))} : Finset (Finset (Finset ℕ))).sum fun D =>
        ((((Finset.range 0).filter fun i => Finset.Ico i (i + k) ∈ D).card : ℝ))) = 0 := by
      rw [Finset.sum_singleton]
      exact hterm
    have hC0 : Nat.choose (k * 0) k = 0 :=
      Nat.choose_eq_zero_of_lt (by rw [Nat.mul_zero]; exact hk)
    rw [hdiag0, hM0, hsum, Finset.card_singleton, hC0]
    simp
  · set diagrams :=
      ((Finset.range (k * n)).powerset.powerset.filter fun D =>
        D.card = n ∧
          (∀ B ∈ D, B.card = k) ∧
          D.biUnion id = Finset.range (k * n)) with hdiagrams
    set f0 := (diagrams.filter fun D => Finset.Ico 0 k ∈ D).card with hf0
    have hkN : k ≤ k * n := Nat.le_mul_of_pos_right k hn
    have hMpos : 0 < k * n - (k - 1) := by omega
    have hdpos : 0 < diagrams.card := by
      rw [Finset.card_pos]
      refine ⟨(Finset.range n).image (fun j => Finset.Ico (j * k) (j * k + k)), ?_⟩
      rw [hdiagrams]
      exact chunk_mem_diagrams k n hk
    have hCpos : 0 < Nat.choose (k * n) k := Nat.choose_pos hkN
    have hKcard : ((Finset.range (k * n)).powersetCard k).card =
        Nat.choose (k * n) k := by
      rw [Finset.card_powersetCard, Finset.card_range]
    have hKconst : ∀ S ∈ (Finset.range (k * n)).powersetCard k,
        (diagrams.filter fun D => S ∈ D).card = f0 := by
      intro S hS
      have h := kfiber_eq_s0 k n hk hn S hS
      rw [hf0, hdiagrams]
      exact h
    have hblock : ∑ S ∈ (Finset.range (k * n)).powersetCard k,
        (diagrams.filter fun D => S ∈ D).card = n * diagrams.card := by
      have h1 : ∑ D ∈ diagrams,
          (((Finset.range (k * n)).powersetCard k).filter fun S => S ∈ D).card =
          ∑ S ∈ (Finset.range (k * n)).powersetCard k,
            ((diagrams.filter fun D => S ∈ D).card) :=
        sum_blocks_swap diagrams ((Finset.range (k * n)).powersetCard k)
      have h2 : ∑ D ∈ diagrams,
          (((Finset.range (k * n)).powersetCard k).filter fun S => S ∈ D).card =
          n * diagrams.card := by
        have h3 : ∀ D ∈ diagrams,
            (((Finset.range (k * n)).powersetCard k).filter fun S => S ∈ D).card = n := by
          intro D hD
          rw [hdiagrams] at hD
          calc (((Finset.range (k * n)).powersetCard k).filter fun S => S ∈ D).card
              = D.card := filter_blocks_eq k n D hD
            _ = n := diag_card_eq k n D hD
        calc ∑ D ∈ diagrams,
                (((Finset.range (k * n)).powersetCard k).filter fun S => S ∈ D).card
            = ∑ _ ∈ diagrams, n := Finset.sum_congr rfl h3
          _ = n * diagrams.card := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]
      exact h1.symm.trans h2
    have hKf0 : ((Finset.range (k * n)).powersetCard k).card * f0 =
        n * diagrams.card := by
      have h4 : ∑ S ∈ (Finset.range (k * n)).powersetCard k,
          (diagrams.filter fun D => S ∈ D).card =
          ((Finset.range (k * n)).powersetCard k).card * f0 :=
        calc ∑ S ∈ (Finset.range (k * n)).powersetCard k,
                (diagrams.filter fun D => S ∈ D).card
            = ∑ _ ∈ (Finset.range (k * n)).powersetCard k, f0 :=
              Finset.sum_congr rfl hKconst
          _ = ((Finset.range (k * n)).powersetCard k).card * f0 := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]
      exact h4.symm.trans hblock
    have hint : ∑ D ∈ diagrams,
        (((Finset.range (k * n - (k - 1))).filter fun i =>
          Finset.Ico i (i + k) ∈ D).card) =
        (Finset.range (k * n - (k - 1))).card * f0 := by
      have h5 : ∑ D ∈ diagrams,
          (((Finset.range (k * n - (k - 1))).filter fun i =>
            Finset.Ico i (i + k) ∈ D).card) =
          ∑ i ∈ Finset.range (k * n - (k - 1)),
            ((diagrams.filter fun D => Finset.Ico i (i + k) ∈ D).card) :=
        sum_filter_card_swap diagrams (Finset.range (k * n - (k - 1)))
          (fun i => Finset.Ico i (i + k))
      have h6 : ∀ i ∈ Finset.range (k * n - (k - 1)),
          (diagrams.filter fun D => Finset.Ico i (i + k) ∈ D).card = f0 := by
        intro i hi
        rw [Finset.mem_range] at hi
        have h := interval_fiber_eq k n i 0 hk hi hMpos
        have h00 : Finset.Ico 0 (0 + k) = Finset.Ico 0 k := by rw [Nat.zero_add]
        rw [h00] at h
        rw [hf0, hdiagrams]
        exact h
      calc ∑ D ∈ diagrams,
              (((Finset.range (k * n - (k - 1))).filter fun i =>
                Finset.Ico i (i + k) ∈ D).card)
          = ∑ _ ∈ Finset.range (k * n - (k - 1)), f0 :=
            h5.trans (Finset.sum_congr rfl h6)
        _ = (Finset.range (k * n - (k - 1))).card * f0 := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]
    have hIcard : (Finset.range (k * n - (k - 1))).card = k * n - (k - 1) :=
      Finset.card_range _
    have hnumR : (diagrams.sum fun D =>
        ((((Finset.range (k * n - (k - 1))).filter fun i =>
          Finset.Ico i (i + k) ∈ D).card : ℝ))) =
        ((((Finset.range (k * n - (k - 1))).card * f0 : ℕ)) : ℝ) := by
      rw [← Nat.cast_sum, hint]
    have h1 : (Nat.choose (k * n) k : ℝ) * (f0 : ℝ) =
        (n : ℝ) * diagrams.card := by
      have h := congrArg (Nat.cast : ℕ → ℝ) hKf0
      rw [Nat.cast_mul, Nat.cast_mul, hKcard] at h
      exact h
    have hC : (Nat.choose (k * n) k : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < Nat.choose (k * n) k := by exact_mod_cast hCpos
      exact ne_of_gt hpos
    have hd : ((diagrams.card : ℕ) : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < diagrams.card := by exact_mod_cast hdpos
      exact ne_of_gt hpos
    have hfd : (f0 : ℝ) / diagrams.card =
        (n : ℝ) / (Nat.choose (k * n) k : ℝ) := by
      rw [div_eq_div_iff hd hC]
      linear_combination h1
    have hcast : ((k * n - (k - 1) : ℕ) : ℝ) =
        (k : ℝ) * (n : ℝ) - ((k : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : k - 1 ≤ k * n), Nat.cast_mul,
        Nat.cast_sub (show 1 ≤ k from hk), Nat.cast_one]
    have hfin : (((((Finset.range (k * n - (k - 1))).card * f0 : ℕ)) : ℝ)) /
        diagrams.card =
        (Nat.choose (k * n) k : ℝ)⁻¹ * n * (k * n - (k - 1)) := by
      rw [Nat.cast_mul, hIcard, mul_div_assoc, hfd, div_eq_mul_inv, hcast]
      ring
    rw [hnumR]
    exact hfin

end MetaMathlibExt
