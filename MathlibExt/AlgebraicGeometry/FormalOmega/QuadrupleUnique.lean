/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf`
`CF_DrinfeldDatum_IsQuadrupleOf_isIsomorphic_of_N_eq`
`CF_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic`
`CF_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd
import MathlibExt.AlgebraicGeometry.FormalOmega.InvertibleModule
import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeEdge
import MathlibExt.AlgebraicGeometry.FormalOmega.EdgeChart
import MathlibExt.AlgebraicGeometry.FormalOmega.EdgeNondegUnique
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleUniqueAux

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.QuadrupleUnique

section Iota

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

private def ιB (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
    (N : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B N →ₗ[B] latticeBaseChange 𝒪 K A N where
  toFun := LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap
  map_add' a b := map_add _ a b
  map_smul' b p := by
    rw [rTensor_smul_left (IsScalarTower.toAlgHom 𝒪 B A) N b p, IsScalarTower.toAlgHom_apply,
      algebraMap_smul]
    rfl

private theorem ιB_one_tmul (N : FullLattice 𝒪 K) (v : ↥N.1) :
    ιB A N ((1 : B) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] v :=
  rTensor_one_tmul _ N v

private theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A]
    (N : FullLattice 𝒪 K) : IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

end Iota

section Sat

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem mem_smul_top_of_smul_mem {L : Type} [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (x : PrimeSpectrum B) {s : B} (hs : s ∉ x.asIdeal) {l : L}
    (h : s • l ∈ (x.asIdeal • ⊤ : Submodule B L)) : l ∈ (x.asIdeal • ⊤ : Submodule B L) := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (TensorProduct.quotTensorEquivQuotSMul L x.asIdeal).symm.map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  have h1 : (1 : B ⧸ x.asIdeal) ⊗ₜ[B] (s • l) = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero]
    exact h
  have h2 : (Ideal.Quotient.mk x.asIdeal s) • ((1 : B ⧸ x.asIdeal) ⊗ₜ[B] l) = 0 := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← h1, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  have hs' : Ideal.Quotient.mk x.asIdeal s ≠ 0 := fun h0 =>
    hs (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have : Module.IsTorsionFree (B ⧸ x.asIdeal) ((B ⧸ x.asIdeal) ⊗[B] L) :=
    Module.Flat.isTorsionFree
  exact (smul_eq_zero_iff_right hs').mp h2

private theorem mem_line_sup_of_smul_mem (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K)
    (x : PrimeSpectrum B) {s : B} (hs : s ∉ x.asIdeal) {p : latticeBaseChange 𝒪 K B M}
    (h : s • p ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    p ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  have := d.invertible M
  have key : ∀ q : latticeBaseChange 𝒪 K B M,
      q ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) ↔
        (d.line M).mkQ q ∈
          (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M ⧸ d.line M)) := by
    intro q
    rw [← Submodule.range_mkQ (d.line M), LinearMap.range_eq_map, ← Submodule.map_smul'',
      ← Submodule.mem_comap, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm]
  rw [key] at h ⊢
  rw [map_smul] at h
  exact mem_smul_top_of_smul_mem x hs h

end Sat

section Core

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem map_mem_smul_top {T : Type} [AddCommGroup T] [Module B T] {T' : Type}
    [AddCommGroup T'] [Module B T'] (P : T →ₗ[B] T') (x : PrimeSpectrum B)
    (h : LinearMap.range P ≤ x.asIdeal • (⊤ : Submodule B T')) (m : stalk B x T) :
    LocalizedModule.map x.asIdeal.primeCompl P m ∈
      (x.asIdeal • ⊤ : Submodule B (stalk B x T')) := by
  have closed : ∀ (c : locRing B x) (n : stalk B x T'),
      n ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T')) →
        c • n ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T')) := by
    intro c n hn
    induction hn using Submodule.smul_induction_on' with
    | smul r hr n _ => rw [smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    | add a _ b _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [LocalizedModule.map_mk]
    have e : LocalizedModule.mk (P t) s =
        Localization.mk 1 s • LocalizedModule.mk (P t) (1 : x.asIdeal.primeCompl) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [e]
    apply closed
    have aux : ∀ n : T', n ∈ x.asIdeal • (⊤ : Submodule B T') →
        LocalizedModule.mk n (1 : x.asIdeal.primeCompl) ∈
          (x.asIdeal • ⊤ : Submodule B (stalk B x T')) := by
      intro n hn
      induction hn using Submodule.smul_induction_on' with
      | smul r hr n _ =>
        rw [← LocalizedModule.smul'_mk]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      | add a _ b _ ha hb =>
        rw [show LocalizedModule.mk (a + b) (1 : x.asIdeal.primeCompl) =
            LocalizedModule.mk a 1 + LocalizedModule.mk b 1 from
          (map_add (LocalizedModule.mkLinearMap x.asIdeal.primeCompl T') a b)]
        exact Submodule.add_mem _ ha hb
    exact aux _ (h ⟨t, rfl⟩)

private theorem notMem_one (x : PrimeSpectrum B) : (1 : B) ∉ x.asIdeal := fun h1 =>
  x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem exists_smul_eq_ιB (M : FullLattice 𝒪 K) (x : PrimeSpectrum B)
    (D : Submodule B (latticeBaseChange 𝒪 K B M)) (m : latticeBaseChange 𝒪 K (locRing B x) M)
    (hm : m ∈ (lineBaseChange (toLocRing B x) M D).restrictScalars B ⊔
      (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M))) :
    ∃ s : B, s ∉ x.asIdeal ∧ ∃ p ∈ D ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
      s • m = ιB (locRing B x) M p := by
  have := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B x) x.asIdeal.primeCompl M
  obtain ⟨ℓ, hℓ, q, hq, rfl⟩ := Submodule.mem_sup.mp hm
  have Hℓ : ∀ ℓ' ∈ lineBaseChange (toLocRing B x) M D,
      ∃ s : B, s ∉ x.asIdeal ∧ ∃ p ∈ D, s • ℓ' = ιB (locRing B x) M p := by
    intro ℓ' hℓ'
    induction hℓ' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨1, notMem_one x, p, hp, by rw [one_smul]; rfl⟩
    | zero => exact ⟨1, notMem_one x, 0, D.zero_mem, by simp⟩
    | add y _ z _ hy hz =>
      obtain ⟨s, hs, p, hp, hsp⟩ := hy
      obtain ⟨t, ht, p', hp', htp⟩ := hz
      refine ⟨s * t, fun h => (x.isPrime.mem_or_mem h).elim hs ht, t • p + s • p',
        D.add_mem (D.smul_mem _ hp) (D.smul_mem _ hp'), ?_⟩
      rw [smul_add, map_add, map_smul, map_smul, ← hsp, ← htp, smul_smul, smul_smul, mul_comm s t]
    | smul c y _ hy =>
      obtain ⟨s, hs, p, hp, hsp⟩ := hy
      obtain ⟨⟨b, t⟩, hc⟩ := IsLocalization.surj x.asIdeal.primeCompl c
      dsimp only at hc
      refine ⟨t * s, fun h => (x.isPrime.mem_or_mem h).elim t.2 hs, b • p, D.smul_mem _ hp, ?_⟩
      rw [map_smul, ← hsp, smul_smul, ← algebraMap_smul (locRing B x) (↑t * s), map_mul,
        smul_smul,
        show algebraMap B (locRing B x) ↑t * algebraMap B (locRing B x) s * c =
            algebraMap B (locRing B x) (b * s) by
          rw [mul_right_comm, mul_comm _ c, hc, ← map_mul],
        algebraMap_smul]
  have Hq : ∀ q' ∈ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M)),
      ∃ s : B, s ∉ x.asIdeal ∧
        ∃ p ∈ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)),
          s • q' = ιB (locRing B x) M p := by
    intro q' hq'
    induction hq' using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      obtain ⟨⟨p, s⟩, hsp⟩ := IsLocalizedModule.surj x.asIdeal.primeCompl (ιB (locRing B x) M) n
      refine ⟨s, s.2, r • p, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
      rw [smul_comm, ← Submonoid.smul_def, hsp, map_smul]
    | add y _ z _ hy hz =>
      obtain ⟨s, hs, p, hp, hsp⟩ := hy
      obtain ⟨t, ht, p', hp', htp⟩ := hz
      refine ⟨s * t, fun h => (x.isPrime.mem_or_mem h).elim hs ht, t • p + s • p',
        Submodule.add_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hp'), ?_⟩
      rw [smul_add, map_add, map_smul, map_smul, ← hsp, ← htp, smul_smul, smul_smul, mul_comm s t]
  obtain ⟨s, hs, p, hp, hsp⟩ := Hℓ ℓ hℓ
  obtain ⟨t, ht, p', hp', htp⟩ := Hq q hq
  refine ⟨s * t, fun h => (x.isPrime.mem_or_mem h).elim hs ht, t • p + s • p',
    Submodule.add_mem _ (Submodule.mem_sup_left (D.smul_mem _ hp))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hp')), ?_⟩
  rw [smul_add, map_add, map_smul, map_smul, ← hsp, ← htp, smul_smul, smul_smul, mul_comm s t]

private theorem tmul_mem_line_sup_of_apply_mem (d : DeligneDatum (K := K) π B)
    (M : FullLattice 𝒪 K) (x : PrimeSpectrum B) {T : Type} [AddCommGroup T] [Module B T]
    (u : latticeBaseChange 𝒪 K (locRing B x) M →ₗ[locRing B x] stalk B x T)
    (hu : Function.Surjective u) (hker : LinearMap.ker u = (d.map π (toLocRing B x)).line M)
    (p : ↥M.1) (hp : u ((1 : locRing B x) ⊗ₜ[𝒪] p) ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T))) :
    (1 : B) ⊗ₜ[𝒪] p ∈ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  have := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B x) x.asIdeal.primeCompl M
  have hsurj : Function.Surjective (u.restrictScalars B) := hu
  have himg : (x.asIdeal • ⊤ : Submodule B (stalk B x T)) =
      ((x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M))).map
        (u.restrictScalars B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  rw [himg] at hp
  obtain ⟨q, hq, hqe⟩ := hp
  have hk : (1 : locRing B x) ⊗ₜ[𝒪] p - q ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact hqe.symm
  rw [hker] at hk
  have hm : (1 : locRing B x) ⊗ₜ[𝒪] p ∈
      (lineBaseChange (toLocRing B x) M (d.line M)).restrictScalars B ⊔
        (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K (locRing B x) M)) := by
    have : (1 : locRing B x) ⊗ₜ[𝒪] p = ((1 : locRing B x) ⊗ₜ[𝒪] p - q) + q := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hk) (Submodule.mem_sup_right hq)
  obtain ⟨s, hs, p', hp', hsp⟩ := exists_smul_eq_ιB M x (d.line M) _ hm
  rw [← ιB_one_tmul (B := B) (A := locRing B x) M p, ← map_smul, eq_comm, ← sub_eq_zero,
    ← map_sub, IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl (ιB (locRing B x) M)] at hsp
  obtain ⟨c, hc⟩ := hsp
  rw [smul_sub, sub_eq_zero, Submonoid.smul_def, Submonoid.smul_def, smul_smul] at hc
  apply mem_line_sup_of_smul_mem d M x (s := ↑c * s)
    (fun h => (x.isPrime.mem_or_mem h).elim (fun h1 => c.2 h1) hs)
  rw [← hc]
  exact Submodule.smul_mem _ _ hp'

end Core

section Quad

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem inclBaseChange_one_tmul (A : Type) [CommRing A] [Algebra 𝒪 A]
    {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) (v : ↥M'.1) :
    inclBaseChange A h ((1 : A) ⊗ₜ[𝒪] v) =
      (1 : A) ⊗ₜ[𝒪] (⟨(v : Fin 2 → K), h v.2⟩ : ↥M.1) := by
  unfold inclBaseChange
  rw [LinearMap.baseChange_tmul]
  rfl

private theorem smulInto_baseChange_one_tmul (A : Type) [CommRing A] [Algebra 𝒪 A]
    {N N' : Submodule 𝒪 (Fin 2 → K)} (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈ N') (v : ↥N) :
    (smulInto π h).baseChange A ((1 : A) ⊗ₜ[𝒪] v) =
      (1 : A) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • (v : Fin 2 → K), h v v.2⟩ : ↥N') := by
  rw [LinearMap.baseChange_tmul]
  rfl

private theorem tmul_mem_line_L₁_sup (Q : DrinfeldDatum (K := K) π B)
    (d : DeligneDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d) (x : PrimeSpectrum B)
    (hx : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁))
    (v : Fin 2 → K) (hv : v ∈ Q.N₀ x) :
    (1 : B) ⊗ₜ[𝒪] (⟨v, Q.le x hv⟩ : ↥(Q.N₁ x)) ∈
      d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x))) := by
  apply tmul_mem_line_sup_of_apply_mem d (Q.L₁ x) x (Q.u₁ x) (Q.u₁_surjective x) (hQ x).2.2
  have h1 := Q.u₁_incl x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x)))
  have h2 := inclBaseChange_one_tmul (locRing B x) (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x) ⟨v, hv⟩
  rw [h2] at h1
  rw [h1]
  exact map_mem_smul_top Q.Pi₀ x hx _

private theorem tmul_smul_mem_line_L₀_sup (Q : DrinfeldDatum (K := K) π B)
    (d : DeligneDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d) (x : PrimeSpectrum B)
    (hx : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀))
    (w : Fin 2 → K) (hw : w ∈ Q.N₁ x) :
    (1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • w, Q.smul_le x w hw⟩ : ↥(Q.N₀ x)) ∈
      d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x))) := by
  apply tmul_mem_line_sup_of_apply_mem d (Q.L₀ x) x (Q.u₀ x) (Q.u₀_surjective x) (hQ x).2.1
  have h1 := Q.u₀_smul x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥(Q.N₁ x)))
  rw [smulInto_baseChange_one_tmul] at h1
  rw [h1]
  exact map_mem_smul_top Q.Pi₁ x hx _

end Quad

section Lattice

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

private theorem latticeMap_scalarGL_comm (c c' : Kˣ) (N : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL c') N) =
      latticeMap (scalarGL c') (latticeMap (scalarGL c) N) := by
  rw [← latticeMap_mul, ← latticeMap_mul, ← scalarGL_mul, ← scalarGL_mul, mul_comm]

private theorem latticeMap_scalarGL_inv_mul (c c' : Kˣ) (N : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (c⁻¹ * c')) (latticeMap (scalarGL c) N) =
      latticeMap (scalarGL c') N := by
  rw [← latticeMap_mul, ← scalarGL_mul, mul_assoc, mul_comm c' c, ← mul_assoc, inv_mul_cancel,
    one_mul]

private theorem eq_latticeMap_scalarGL_of_forall {N₀ N₁ : Submodule 𝒪 (Fin 2 → K)} (c : Kˣ)
    (h1 : ∀ v ∈ N₀, ∃ w ∈ N₁, v = (c : K) • w) (h2 : ∀ w ∈ N₁, (c : K) • w ∈ N₀) :
    N₀ = latticeMap (scalarGL c) N₁ := by
  ext v
  rw [mem_latticeMap_scalarGL]
  constructor
  · intro hv; obtain ⟨w, hw, rfl⟩ := h1 v hv; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact h2 w hw

end Lattice

section Types

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem algebraMap_ne_zero (hπ : Irreducible π) : algebraMap 𝒪 K π ≠ 0 := fun h =>
  hπ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h)

private def πu (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (algebraMap 𝒪 K π) (algebraMap_ne_zero (K := K) hπ)

variable (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
  (hQ : Q.IsQuadrupleOf d) (x : PrimeSpectrum B) (hπx : algebraMap 𝒪 B π ∈ x.asIdeal)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
include hπx in
private theorem stratum_cover :
    LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁) ∨
      LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀) := by
  have hfg : Q.Pi₁ ∘ₗ Q.Pi₀ = algebraMap 𝒪 B π • LinearMap.id := LinearMap.ext fun t => by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Q.Pi₁_Pi₀]
  exact Module.Invertible.range_le_smul_top_or_of_comp_eq_smul Q.Pi₀ Q.Pi₁ _ hfg x hπx

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem N₀_eq_of_not_S₁
    (hS1 : ¬ LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀)) :
    Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x) := by
  have hbij := Module.Invertible.bijective_localizedModule_map_of_not_range_le Q.Pi₁ x hS1
  apply eq_latticeMap_scalarGL_of_forall
  · intro v hv
    obtain ⟨w, hw, hvw⟩ := Q.injective₀ x ⟨v, hv⟩ (Submodule.mem_sup_left (by
      rw [Submodule.restrictScalars_mem, LinearMap.range_eq_top.mpr hbij.2]; trivial))
    exact ⟨w, hw, hvw⟩
  · intro w hw; exact Q.smul_le x w hw

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
private theorem N₀_eq_of_not_S₀
    (hS0 : ¬ LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁)) :
    Q.N₀ x = Q.N₁ x := by
  have hbij := Module.Invertible.bijective_localizedModule_map_of_not_range_le Q.Pi₀ x hS0
  refine le_antisymm (Q.le x) fun v hv => ?_
  exact Q.injective₁ x ⟨v, hv⟩ (Submodule.mem_sup_left (by
    rw [Submodule.restrictScalars_mem, LinearMap.range_eq_top.mpr hbij.2]; trivial))

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
include hQ in
private theorem vertexNondegAt_L₁_of_V0
    (h : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x)) :
    d.VertexNondegAt π x.asIdeal (Q.L₁ x) := by
  intro v hnot
  apply (hQ x).1.2.2.1 v
  intro hv0
  change (v : Fin 2 → K) ∈ Q.N₀ x at hv0
  rw [h, mem_latticeMap_scalarGL] at hv0
  obtain ⟨w, hw, hwv⟩ := hv0
  exact hnot ⟨⟨w, hw⟩, by rw [← hwv]; rfl⟩

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
include hQ in
private theorem vertexNondegAt_L₀_of_V1 (h : Q.N₀ x = Q.N₁ x) :
    d.VertexNondegAt π x.asIdeal (Q.L₀ x) := by
  intro v' hnot
  apply (hQ x).1.2.2.2 v'
  rintro ⟨w, hw⟩
  exact hnot ⟨⟨w, by change (w : Fin 2 → K) ∈ Q.N₀ x; rw [h]; exact w.2⟩, hw⟩

end Types

section Edge

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

variable (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
  (hQ : Q.IsQuadrupleOf d) (x : PrimeSpectrum B)
  (hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁))
  (hS1 : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀))

private theorem not_even_one_aux {e : ℤ} (h : Even e) (he : e = 1 ∨ e = -1) : False := by
  obtain ⟨k, hk⟩ := h; rcases he with rfl | rfl <;> omega

include hπ hS0 hS1 in
private theorem N₀_ne_N₁_of_E : Q.N₀ x ≠ Q.N₁ x := by
  intro h
  have h0 := Q.hasDetIndex₀ x hS0
  have h1 := Q.hasDetIndex₁ x hS1
  refine not_even_one_aux (HasDetIndex.even_sub_of_latticeMap_scalarGL hπ (Q.N₁ x) 1 (-1) 0
    h1 (by rw [scalarGL_one, latticeMap_one, ← h]; exact h0)) (Or.inr (by norm_num))

include hπ hS0 hS1 in
private theorem exists_mem_N₀_not_smul_of_E :
    ∃ v ∈ Q.N₀ x, ¬ ∃ w ∈ Q.N₁ x, v = algebraMap 𝒪 K π • w := by
  by_contra hne
  push Not at hne
  have heq : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x) :=
    eq_latticeMap_scalarGL_of_forall _ (fun v hv => by
      obtain ⟨w, hw, hvw⟩ := hne v hv; exact ⟨w, hw, hvw⟩) (fun w hw => Q.smul_le x w hw)
  have h0 := Q.hasDetIndex₀ x hS0
  have h1 := Q.hasDetIndex₁ x hS1
  rw [heq] at h0
  exact not_even_one_aux (HasDetIndex.even_sub_of_latticeMap_scalarGL hπ (Q.N₁ x) _ (-1) 0
    h1 h0) (Or.inr (by norm_num))

include hπ hQ hS0 hS1 in
private theorem not_vertexNondegAt_L₁_of_E : ¬ d.VertexNondegAt π x.asIdeal (Q.L₁ x) := by
  intro hV
  obtain ⟨v, hv0, hnot⟩ := exists_mem_N₀_not_smul_of_E hπ Q x hS0 hS1
  exact hV ⟨v, Q.le x hv0⟩ (fun ⟨w, hw⟩ => hnot ⟨w, w.2, hw⟩)
    (tmul_mem_line_L₁_sup Q d hQ x hS0 v hv0)

include hπ hQ hS0 hS1 in
private theorem not_vertexNondegAt_L₀_of_E : ¬ d.VertexNondegAt π x.asIdeal (Q.L₀ x) := by
  intro hV
  obtain ⟨w, hw1, hw0⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_le_of_ne (Q.le x) (N₀_ne_N₁_of_E hπ Q x hS0 hS1))
  refine hV ⟨algebraMap 𝒪 K π • w, Q.smul_le x w hw1⟩ ?_
    (tmul_smul_mem_line_L₀_sup Q d hQ x hS1 w hw1)
  rintro ⟨w', hw'⟩
  have : w = (w' : Fin 2 → K) :=
    smul_right_injective (Fin 2 → K) (algebraMap_ne_zero (K := K) hπ) hw'
  exact hw0 (this ▸ w'.2)

include hπ hQ hS0 hS1 in
private theorem false_of_vertexNondegAt_of_E (M : FullLattice 𝒪 K)
    (hM : d.VertexNondegAt π x.asIdeal M) (c : Kˣ)
    (hc : latticeMap (scalarGL c) M.1 = (Q.L₀ x).1 ∨ latticeMap (scalarGL c) M.1 = (Q.L₁ x).1) :
    False := by
  have hVc := (DeligneDatum.vertexNondegAt_act_scalarGL_iff π d x.asIdeal c M).mpr hM
  rcases hc with hc | hc
  · have : FullLattice.act (scalarGL c) M = Q.L₀ x := Subtype.ext hc
    rw [this] at hVc
    exact not_vertexNondegAt_L₀_of_E hπ Q d hQ x hS0 hS1 hVc
  · have : FullLattice.act (scalarGL c) M = Q.L₁ x := Subtype.ext hc
    rw [this] at hVc
    exact not_vertexNondegAt_L₁_of_E hπ Q d hQ x hS0 hS1 hVc

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
include hQ in
private theorem mem_N₀_of_tmul_mem (v : Fin 2 → K) (hv1 : v ∈ Q.N₁ x)
    (h : (1 : B) ⊗ₜ[𝒪] (⟨v, hv1⟩ : ↥(Q.N₁ x)) ∈
      d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x)))) :
    v ∈ Q.N₀ x := by
  by_contra hv0
  exact (hQ x).1.2.2.1 ⟨v, hv1⟩ hv0 h

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
include hQ in
private theorem exists_of_tmul_mem (v : Fin 2 → K) (hv0 : v ∈ Q.N₀ x)
    (h : (1 : B) ⊗ₜ[𝒪] (⟨v, hv0⟩ : ↥(Q.N₀ x)) ∈
      d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x)))) :
    ∃ w ∈ Q.N₁ x, v = algebraMap 𝒪 K π • w := by
  by_contra hne
  push Not at hne
  exact (hQ x).1.2.2.2 ⟨v, hv0⟩ (fun ⟨w, hw⟩ => hne w w.2 hw) h

end Edge

section Transport

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem tmul_mem_of_eq (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B)
    {L L' : FullLattice 𝒪 K} (hL : L = L') (v : Fin 2 → K) (hv : v ∈ L.1) (hv' : v ∈ L'.1)
    (h : (1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥L.1) ∈
      d.line L ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L))) :
    (1 : B) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥L'.1) ∈
      d.line L' ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L')) := by
  subst hL; exact h

end Transport

section Compare

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]

variable (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B)
  (hπx : algebraMap 𝒪 B π ∈ x.asIdeal)
  (Q : DrinfeldDatum (K := K) π B) (hQ : Q.IsQuadrupleOf d)
  (Q' : DrinfeldDatum (K := K) π B) (hQ' : Q'.IsQuadrupleOf d)

local notation "S0" R =>
  LinearMap.range (DrinfeldDatum.Pi₀ R) ≤ x.asIdeal • (⊤ : Submodule B (DrinfeldDatum.T₁ R))
local notation "S1" R =>
  LinearMap.range (DrinfeldDatum.Pi₁ R) ≤ x.asIdeal • (⊤ : Submodule B (DrinfeldDatum.T₀ R))

include hπ hπx hQ' in
private theorem false_of_vertex_edge (M : FullLattice 𝒪 K) (hM : d.VertexNondegAt π x.asIdeal M)
    (hS0' : S0 Q') (hS1' : S1 Q') : False := by
  obtain ⟨c, hc⟩ := DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx M (Q'.L₀ x) (Q'.L₁ x) hM (hQ' x).1
  exact false_of_vertexNondegAt_of_E hπ Q' d hQ' x hS0' hS1' M hM c hc

include hπ hπx hQ hQ' in
private theorem eq_of_V0_V0 (hS0 : S0 Q)
    (h0 : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x))
    (hS0' : S0 Q') (h0' : Q'.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q'.N₁ x)) :
    Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  have hV := vertexNondegAt_L₁_of_V0 hπ Q d hQ x h0
  obtain ⟨c, hc⟩ := DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx (Q.L₁ x) (Q'.L₀ x) (Q'.L₁ x) hV (hQ' x).1
  obtain ⟨c', hc'⟩ : ∃ c' : Kˣ, latticeMap (scalarGL c') (Q.N₁ x) = Q'.N₁ x := by
    rcases hc with hc | hc
    · refine ⟨(πu (K := K) hπ)⁻¹ * c, ?_⟩
      change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₀ x at hc
      rw [h0'] at hc
      rw [scalarGL_mul, latticeMap_mul, hc, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel,
        scalarGL_one, latticeMap_one]
    · exact ⟨c, hc⟩
  have idx0 := Q.hasDetIndex₀ x hS0
  have idx0' := Q'.hasDetIndex₀ x hS0'
  have hN0' : Q'.N₀ x = latticeMap (scalarGL c') (Q.N₀ x) := by
    rw [h0', ← hc', h0, latticeMap_scalarGL_comm]
  have key : latticeMap (scalarGL c') (Q.N₀ x) = Q.N₀ x :=
    latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c' 0 idx0 (hN0' ▸ idx0')
  refine ⟨by rw [hN0', key], ?_⟩
  rw [← hc']
  apply latticeMap_injective (scalarGL (πu (K := K) hπ))
  rw [← latticeMap_scalarGL_comm, ← h0, key]

include hπ hπx hQ hQ' in
private theorem eq_of_V1_V1 (hS1 : S1 Q) (h1 : Q.N₀ x = Q.N₁ x) (hS1' : S1 Q')
    (h1' : Q'.N₀ x = Q'.N₁ x) : Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  have hV := vertexNondegAt_L₀_of_V1 Q d hQ x h1
  obtain ⟨c, hc⟩ := DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx (Q.L₀ x) (Q'.L₀ x) (Q'.L₁ x) hV (hQ' x).1
  have hc1 : latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₁ x := by
    rcases hc with hc | hc
    · change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₀ x at hc; rwa [h1, h1'] at hc
    · change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₁ x at hc; rwa [h1] at hc
  have idx1 := Q.hasDetIndex₁ x hS1
  have idx1' := Q'.hasDetIndex₁ x hS1'
  have key : latticeMap (scalarGL c) (Q.N₁ x) = Q.N₁ x :=
    latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c (-1) idx1 (hc1.symm ▸ idx1')
  have hN1 : Q.N₁ x = Q'.N₁ x := by rw [← hc1, key]
  exact ⟨by rw [h1, h1', hN1], hN1⟩

include hπ hπx hQ hQ' in
private theorem false_of_V0_V1 (hS0 : S0 Q)
    (h0 : Q.N₀ x = latticeMap (scalarGL (πu (K := K) hπ)) (Q.N₁ x))
    (hS1' : S1 Q') (h1' : Q'.N₀ x = Q'.N₁ x) : False := by
  have hV := vertexNondegAt_L₁_of_V0 hπ Q d hQ x h0
  obtain ⟨c, hc⟩ := DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    hπ d x.asIdeal hπx (Q.L₁ x) (Q'.L₀ x) (Q'.L₁ x) hV (hQ' x).1
  have hc1 : latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₁ x := by
    rcases hc with hc | hc
    · change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₀ x at hc; rwa [h1'] at hc
    · exact hc
  have idx0 := Q.hasDetIndex₀ x hS0
  have idx1' := Q'.hasDetIndex₁ x hS1'
  rw [h0] at idx0
  rw [← hc1, ← latticeMap_scalarGL_inv_mul (πu (K := K) hπ) c] at idx1'
  exact not_even_one_aux (HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ _ 0 (-1) idx0 idx1')
    (Or.inl (by norm_num))

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
include hπ hQ hQ' in
private theorem N₁_le_of_E_E (hS1 : S1 Q) (hN0 : Q.N₀ x = Q'.N₀ x) : Q.N₁ x ≤ Q'.N₁ x := by
  intro w hw
  have hmem := tmul_smul_mem_line_L₀_sup Q d hQ x hS1 w hw
  have hL : Q.L₀ x = Q'.L₀ x := Subtype.ext hN0
  have hmem' := tmul_mem_of_eq d x hL _ (Q.smul_le x w hw)
    (by change _ ∈ Q'.N₀ x; rw [← hN0]; exact Q.smul_le x w hw) hmem
  obtain ⟨w', hw', hww'⟩ := exists_of_tmul_mem Q' d hQ' x _ _ hmem'
  have : w = w' := smul_right_injective (Fin 2 → K) (algebraMap_ne_zero (K := K) hπ) hww'
  exact this ▸ hw'

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
include hQ hQ' in
private theorem N₀_le_of_E_E (hS0 : S0 Q) (hN1 : Q.N₁ x = Q'.N₁ x) : Q.N₀ x ≤ Q'.N₀ x := by
  intro v hv
  have hmem := tmul_mem_line_L₁_sup Q d hQ x hS0 v hv
  have hL : Q.L₁ x = Q'.L₁ x := Subtype.ext hN1
  have hmem' := tmul_mem_of_eq d x hL _ (Q.le x hv)
    (by change _ ∈ Q'.N₁ x; rw [← hN1]; exact Q.le x hv) hmem
  exact mem_N₀_of_tmul_mem Q' d hQ' x v _ hmem'

include hπ hπx hQ hQ' in
private theorem eq_of_E_E (hS0 : S0 Q) (hS1 : S1 Q) (hS0' : S0 Q') (hS1' : S1 Q') :
    Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  obtain ⟨c, X, Y, hX, hY, hXY⟩ :=
    DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt hπ d x.asIdeal
      hπx (Q.L₀ x) (Q.L₁ x) (Q'.L₀ x) (Q'.L₁ x) (hQ x).1 (hQ' x).1
  have idx0 := Q.hasDetIndex₀ x hS0
  have idx1 := Q.hasDetIndex₁ x hS1
  have idx0' := Q'.hasDetIndex₀ x hS0'
  have idx1' := Q'.hasDetIndex₁ x hS1'
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₀ x at hXY
    have key :=
      latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c 0 idx0 (hXY.symm ▸ idx0')
    have hN0 : Q.N₀ x = Q'.N₀ x := by rw [← hXY, key]
    exact ⟨hN0, le_antisymm (N₁_le_of_E_E hπ d x Q hQ Q' hQ' hS1 hN0)
      (N₁_le_of_E_E hπ d x Q' hQ' Q hQ hS1' hN0.symm)⟩
  · change latticeMap (scalarGL c) (Q.N₀ x) = Q'.N₁ x at hXY
    exact (not_even_one_aux (HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ c 0 (-1) idx0
      (hXY.symm ▸ idx1')) (Or.inl (by norm_num))).elim
  · change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₀ x at hXY
    exact (not_even_one_aux (HasDetIndex.even_sub_of_latticeMap_scalarGL hπ _ c (-1) 0 idx1
      (hXY.symm ▸ idx0')) (Or.inr (by norm_num))).elim
  · change latticeMap (scalarGL c) (Q.N₁ x) = Q'.N₁ x at hXY
    have key :=
      latticeMap_scalarGL_eq_self_of_hasDetIndex hπ _ c (-1) idx1 (hXY.symm ▸ idx1')
    have hN1 : Q.N₁ x = Q'.N₁ x := by rw [← hXY, key]
    exact ⟨le_antisymm (N₀_le_of_E_E d x Q hQ Q' hQ' hS0 hN1)
      (N₀_le_of_E_E d x Q' hQ' Q hQ hS0' hN1.symm), hN1⟩

end Compare

end CerednikDrinfeld.FormalOmega.QuadrupleUnique

open CerednikDrinfeld.FormalOmega.QuadrupleUnique in
/-- Two Drinfeld quadruples of the same Deligne datum over a ring in which `π` is nilpotent have
the same lattices `N₀` and `N₁` at every point. -/
theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) (h' : Q'.IsQuadrupleOf d) :
    ∀ x : PrimeSpectrum B, Q.N₀ x = Q'.N₀ x ∧ Q.N₁ x = Q'.N₁ x := by
  intro x
  have hπx : algebraMap 𝒪 B π ∈ x.asIdeal := by
    obtain ⟨n, hn⟩ := hB
    exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
  have cov := stratum_cover Q x hπx
  have cov' := stratum_cover Q' x hπx
  by_cases hS0 : LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁) <;>
  by_cases hS1 : LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀) <;>
  by_cases hS0' : LinearMap.range Q'.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q'.T₁) <;>
  by_cases hS1' : LinearMap.range Q'.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q'.T₀)
  · exact eq_of_E_E hπ d x hπx Q h Q' h' hS0 hS1 hS0' hS1'
  · exact (false_of_vertex_edge hπ d x hπx Q h (Q'.L₁ x)
      (vertexNondegAt_L₁_of_V0 hπ Q' d h' x (N₀_eq_of_not_S₁ hπ Q' x hS1')) hS0 hS1).elim
  · exact (false_of_vertex_edge hπ d x hπx Q h (Q'.L₀ x)
      (vertexNondegAt_L₀_of_V1 Q' d h' x (N₀_eq_of_not_S₀ Q' x hS0')) hS0 hS1).elim
  · exact (cov'.elim hS0' hS1').elim
  · exact (false_of_vertex_edge hπ d x hπx Q' h' (Q.L₁ x)
      (vertexNondegAt_L₁_of_V0 hπ Q d h x (N₀_eq_of_not_S₁ hπ Q x hS1)) hS0' hS1').elim
  · exact eq_of_V0_V0 hπ d x hπx Q h Q' h' hS0 (N₀_eq_of_not_S₁ hπ Q x hS1) hS0'
      (N₀_eq_of_not_S₁ hπ Q' x hS1')
  · exact (false_of_V0_V1 hπ d x hπx Q h Q' h' hS0 (N₀_eq_of_not_S₁ hπ Q x hS1) hS1'
      (N₀_eq_of_not_S₀ Q' x hS0')).elim
  · exact (cov'.elim hS0' hS1').elim
  · exact (false_of_vertex_edge hπ d x hπx Q' h' (Q.L₀ x)
      (vertexNondegAt_L₀_of_V1 Q d h x (N₀_eq_of_not_S₀ Q x hS0)) hS0' hS1').elim
  · exact (false_of_V0_V1 hπ d x hπx Q' h' Q h hS0' (N₀_eq_of_not_S₁ hπ Q' x hS1') hS1
      (N₀_eq_of_not_S₀ Q x hS0)).elim
  · exact eq_of_V1_V1 hπ d x hπx Q h Q' h' hS1 (N₀_eq_of_not_S₀ Q x hS0) hS1'
      (N₀_eq_of_not_S₀ Q' x hS0')
  · exact (cov'.elim hS0' hS1').elim
  · exact (cov.elim hS0 hS1).elim
  · exact (cov.elim hS0 hS1).elim
  · exact (cov.elim hS0 hS1).elim
  · exact (cov.elim hS0 hS1).elim


namespace CerednikDrinfeld.FormalOmega.QuadrupleUnique

section IsoInv

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem ker_eq_map_transport {C : Type} [CommRing C] [Algebra 𝒪 C]
    {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1) {P₁ P₂ : Type} [AddCommGroup P₁] [Module C P₁]
    [AddCommGroup P₂] [Module C P₂] (u₁ : latticeBaseChange 𝒪 K C M₁ →ₗ[C] P₁)
    (u₂ : latticeBaseChange 𝒪 K C M₂ →ₗ[C] P₂) (φ : P₁ →ₗ[C] P₂) (hφ : Function.Injective φ)
    (hcomm : ∀ z, u₂ (transportEquiv C h z) = φ (u₁ z)) :
    LinearMap.ker u₂ = (LinearMap.ker u₁).map (transportEquiv C h).toLinearMap := by
  ext z
  constructor
  · intro hz
    refine ⟨(transportEquiv C h).symm z, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [LinearMap.mem_ker] at hz
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply hφ
    rw [← hcomm, LinearEquiv.apply_symm_apply, hz, map_zero]
  · rintro ⟨w, hw, rfl⟩
    have hw' : u₁ w = 0 := hw
    rw [LinearMap.mem_ker, LinearEquiv.coe_coe, hcomm, hw', map_zero]

private theorem ext_one_tmul {C : Type} [CommRing C] [Algebra 𝒪 C] {M : FullLattice 𝒪 K}
    {P : Type} [AddCommGroup P] [Module C P] (u u' : latticeBaseChange 𝒪 K C M →ₗ[C] P)
    (h : ∀ v : ↥M.1, u ((1 : C) ⊗ₜ[𝒪] v) = u' ((1 : C) ⊗ₜ[𝒪] v)) : u = u' := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul c v =>
    have hc : (c ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K C M) = c • ((1 : C) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, h]

private theorem ker_transfer (x : PrimeSpectrum B) {N N' : Submodule 𝒪 (Fin 2 → K)}
    (hN : Submodule.IsFullLattice K N) (hN' : Submodule.IsFullLattice K N') (hNN' : N = N')
    {T T' : Type} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T'] (τ : T ≃ₗ[B] T')
    (u : latticeBaseChange 𝒪 K (locRing B x) ⟨N, hN⟩ →ₗ[locRing B x] stalk B x T)
    (u' : latticeBaseChange 𝒪 K (locRing B x) ⟨N', hN'⟩ →ₗ[locRing B x] stalk B x T')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N) (hv' : v ∈ N'),
      u' ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N')) =
        LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap
          (u ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N))))
    (dloc : DeligneDatum (K := K) π (locRing B x)) (hker : LinearMap.ker u = dloc.line ⟨N, hN⟩) :
    LinearMap.ker u' = dloc.line ⟨N', hN'⟩ := by
  have h1 : (⟨N, hN⟩ : FullLattice 𝒪 K).1 = (⟨N', hN'⟩ : FullLattice 𝒪 K).1 := hNN'
  rw [DeligneDatum.line_transport π dloc h1, ← hker]
  refine ker_eq_map_transport h1 u u'
    ((LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap).restrictScalars (locRing B x))
    ?_ ?_
  · exact LocalizedModule.map_injective _ _ τ.injective
  · intro z
    have key : u' ∘ₗ (transportEquiv (locRing B x) h1).toLinearMap =
        ((LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap).restrictScalars
          (locRing B x)) ∘ₗ u := by
      apply ext_one_tmul
      intro v
      have ht := transportEquiv_tmul (locRing B x) h1 1 v
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ht,
        LinearMap.restrictScalars_apply]
      have hv' : (v : Fin 2 → K) ∈ N' := hNN' ▸ v.2
      have hofEq : (LinearEquiv.ofEq _ _ h1 v : ↥(⟨N', hN'⟩ : FullLattice 𝒪 K).1) = ⟨v, hv'⟩ :=
        Subtype.ext rfl
      rw [hofEq, hu v v.2 hv']
    exact congrArg (fun F : latticeBaseChange 𝒪 K (locRing B x) ⟨N, hN⟩ →ₗ[locRing B x]
      stalk B x T' => F z) key

private theorem map_symm_map {T T' : Type} [AddCommGroup T] [Module B T] [AddCommGroup T']
    [Module B T'] (x : PrimeSpectrum B) (τ : T ≃ₗ[B] T') (y : stalk B x T) :
    LocalizedModule.map x.asIdeal.primeCompl τ.symm.toLinearMap
      (LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap y) = y := by
  induction y using LocalizedModule.induction_on with
  | h m s => simp [LocalizedModule.map_mk]

private def isoSymm {Q Q' : DrinfeldDatum (K := K) π B} (e : Q.Iso Q') : Q'.Iso Q where
  N₀_eq x := (e.N₀_eq x).symm
  N₁_eq x := (e.N₁_eq x).symm
  τ₀ := e.τ₀.symm
  τ₁ := e.τ₁.symm
  τ₁_Pi₀ t := by
    apply e.τ₁.injective
    rw [LinearEquiv.apply_symm_apply, e.τ₁_Pi₀, LinearEquiv.apply_symm_apply]
  τ₀_Pi₁ t := by
    apply e.τ₀.injective
    rw [LinearEquiv.apply_symm_apply, e.τ₀_Pi₁, LinearEquiv.apply_symm_apply]
  τ₀_u₀ x v hv hv' := by rw [e.τ₀_u₀ x v hv' hv, map_symm_map]
  τ₁_u₁ x v hv hv' := by rw [e.τ₁_u₁ x v hv' hv, map_symm_map]

end IsoInv

end CerednikDrinfeld.FormalOmega.QuadrupleUnique

open CerednikDrinfeld.FormalOmega.QuadrupleUniqueAux in
set_option linter.unusedVariables false in
/-- Two Drinfeld quadruples of the same Deligne datum with the same lattices `N₀` and `N₁` at
every point are isomorphic. -/
theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) (h' : Q'.IsQuadrupleOf d)
    (h₀ : ∀ x : PrimeSpectrum B, Q.N₀ x = Q'.N₀ x)
    (h₁ : ∀ x : PrimeSpectrum B, Q.N₁ x = Q'.N₁ x) :
    Q'.IsIsomorphic Q := by
  classical
  obtain ⟨N₀', N₁', full₀', full₁', le', sle', o₀', o₁', T₀', T₁', inv₀', inv₁',
    Pi₀', Pi₁', hPP₁, hPP₀, u₀', u₁', ui', us', su₀, su₁, uc₀, uc₁, lc₀, lc₁, inj₀, inj₁, det₀,
    det₁⟩ := Q'
  have e₀ : N₀' = Q.N₀ := funext fun x => (h₀ x).symm
  have e₁ : N₁' = Q.N₁ := funext fun x => (h₁ x).symm
  subst e₀ e₁
  obtain ⟨τ₀, hτ₀⟩ := exists_linearEquiv_map_comp_eq Q.N₀ Q.full₀ Q.T₀ T₀' Q.u₀ u₀'
    Q.u₀_surjective su₀ (fun x => ((h' x).2.1).trans ((h x).2.1).symm) Q.u₀_continuous uc₀
  obtain ⟨τ₁, hτ₁⟩ := exists_linearEquiv_map_comp_eq Q.N₁ Q.full₁ Q.T₁ T₁' Q.u₁ u₁'
    Q.u₁_surjective su₁ (fun x => ((h' x).2.2).trans ((h x).2.2).symm) Q.u₁_continuous uc₁
  have loc_eq : ∀ {M : Type} [AddCommGroup M] [Module B M] (m m' : M),
      (∀ x : PrimeSpectrum B, (LocalizedModule.mk m 1 : stalk B x M) = LocalizedModule.mk m' 1) →
        m = m' := by
    intro M _ _ m m' hx
    refine Module.eq_of_localization_maximal (R := B)
      (fun (P : Ideal B) (_ : P.IsMaximal) => LocalizedModule P.primeCompl M)
      (fun (P : Ideal B) (_ : P.IsMaximal) => LocalizedModule.mkLinearMap P.primeCompl M) m m'
      fun P hP => ?_
    exact hx ⟨P, hP.isPrime⟩
  refine ⟨⟨fun _ => rfl, fun _ => rfl, τ₀, τ₁, fun t => ?_, fun t => ?_, fun x v hv hv' => ?_,
    fun x v hv hv' => ?_⟩⟩
  · refine loc_eq _ _ fun x => ?_
    obtain ⟨w, hw⟩ := su₀ x (LocalizedModule.mk t 1)
    have h1 : (LocalizedModule.mk (τ₁ (Pi₀' t)) 1 : stalk B x Q.T₁) =
        LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap
          (LocalizedModule.map x.asIdeal.primeCompl Pi₀' (LocalizedModule.mk t 1)) := by
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk]; rfl
    have h2 : (LocalizedModule.mk (Q.Pi₀ (τ₀ t)) 1 : stalk B x Q.T₁) =
        LocalizedModule.map x.asIdeal.primeCompl Q.Pi₀
          (LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap (LocalizedModule.mk t 1)) := by
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk]; rfl
    rw [h1, h2, ← hw, ← ui', hτ₁, Q.u₁_incl, hτ₀]
  · refine loc_eq _ _ fun x => ?_
    obtain ⟨w, hw⟩ := su₁ x (LocalizedModule.mk t 1)
    have h1 : (LocalizedModule.mk (τ₀ (Pi₁' t)) 1 : stalk B x Q.T₀) =
        LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap
          (LocalizedModule.map x.asIdeal.primeCompl Pi₁' (LocalizedModule.mk t 1)) := by
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk]; rfl
    have h2 : (LocalizedModule.mk (Q.Pi₁ (τ₁ t)) 1 : stalk B x Q.T₀) =
        LocalizedModule.map x.asIdeal.primeCompl Q.Pi₁
          (LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap (LocalizedModule.mk t 1)) := by
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk]; rfl
    rw [h1, h2, ← hw, ← us', hτ₀, Q.u₀_smul, hτ₁]
  · exact (hτ₀ x _).symm
  · exact (hτ₁ x _).symm

open CerednikDrinfeld.FormalOmega.QuadrupleUnique in
/-- Being a quadruple of a Deligne datum is invariant under isomorphism of Drinfeld data. -/
theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {Q Q' : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (e : Q.IsIsomorphic Q') : Q'.IsQuadrupleOf d := by
  obtain ⟨e⟩ := e
  intro x
  obtain ⟨hedge, hk₀, hk₁⟩ := h x
  have hL₀ : Q'.L₀ x = Q.L₀ x := Subtype.ext (e.N₀_eq x).symm
  have hL₁ : Q'.L₁ x = Q.L₁ x := Subtype.ext (e.N₁_eq x).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hL₀, hL₁]; exact hedge
  · exact ker_transfer x (Q.full₀ x) (Q'.full₀ x) (e.N₀_eq x) e.τ₀ (Q.u₀ x) (Q'.u₀ x)
      (fun v hv hv' => e.τ₀_u₀ x v hv hv') _ hk₀
  · exact ker_transfer x (Q.full₁ x) (Q'.full₁ x) (e.N₁_eq x) e.τ₁ (Q.u₁ x) (Q'.u₁ x)
      (fun v hv hv' => e.τ₁_u₁ x v hv hv') _ hk₁

open CerednikDrinfeld.FormalOmega.QuadrupleUnique in
/-- Over a ring in which `π` is nilpotent, the quadruples of the Deligne datum `d` are exactly the
Drinfeld data isomorphic to a given quadruple `Q` of `d`. -/
theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) : Q'.IsQuadrupleOf d ↔ Q'.IsIsomorphic Q := by
  constructor
  · intro h'
    exact DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq hπ hB h Q' h'
      (fun x => (DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf hπ hB h Q' h' x).1)
      (fun x => (DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf hπ hB h Q' h' x).2)
  · rintro ⟨e⟩
    exact DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic h ⟨isoSymm e⟩

end
