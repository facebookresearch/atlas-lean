/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Submodule_exists_isPerfPair_dotProduct_of_saturated.lean`
and
`P2M/Sol/S_Submodule_exists_isPerfPair_dotProduct_of_saturated.lean`
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

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Perfect dot-product pairings from saturated sublattices

Given two saturated, mutually orthogonal sublattices `B` and `E` of `ι → ℤ` and two linear maps
`f X : L →ₗ[ℤ] (ι → ℤ)` satisfying the orthogonality, injectivity and saturation conditions of
`Submodule.exists_isPerfPair_dotProduct_of_saturated`, the pairing `(x, y) ↦ X x ⬝ᵥ f y`
is a perfect pairing on `L`.
-/

set_option linter.unusedSectionVars false

namespace DotProductPairingAux

open Module

attribute [-instance] AddCommGroup.toIntModule

variable {ι : Type*} [Fintype ι]

private def dotL : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v ⬝ᵥ w) (fun _ _ _ => add_dotProduct _ _ _)
    (fun c v w => by change (c • v) ⬝ᵥ w = c • (v ⬝ᵥ w); rw [smul_dotProduct])
    (fun _ _ _ => dotProduct_add _ _ _)
    (fun c v w => by change v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w); rw [dotProduct_smul])

@[scoped simp] private theorem dotL_apply (v w : ι → ℤ) : dotL v w = v ⬝ᵥ w := rfl

private theorem exists_eq_dotL (Λ : (ι → ℤ) →ₗ[ℤ] ℤ) : ∃ w : ι → ℤ, ∀ v, Λ v = w ⬝ᵥ v := by
  classical
  refine ⟨fun i => Λ (Pi.single i 1), fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (v i) = v i • (Pi.single i (1 : ℤ) : ι → ℤ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

private def perp (N : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) where
  carrier := {v | ∀ n ∈ N, v ⬝ᵥ n = 0}
  zero_mem' := fun n _ => zero_dotProduct n
  add_mem' := by
    intro v w hv hw n hn
    rw [add_dotProduct, hv n hn, hw n hn, add_zero]
  smul_mem' := by
    intro c v hv n hn
    rw [smul_dotProduct, hv n hn, smul_zero]

private theorem mem_perp {N : Submodule ℤ (ι → ℤ)} {v : ι → ℤ} : v ∈ perp N ↔ ∀ n ∈ N, v ⬝ᵥ n = 0 :=
  Iff.rfl

private def Saturated (N : Submodule ℤ (ι → ℤ)) : Prop := ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ N
    → v ∈ N

private theorem saturated_perp (N : Submodule ℤ (ι → ℤ)) : Saturated (perp N) := by
  intro n v hn hv m hm
  have := hv m hm
  rw [smul_dotProduct, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hn

section Sat

variable (N : Submodule ℤ (ι → ℤ)) (hN : Saturated N)

private theorem bM_mem {n : ℕ} (snf : Module.Basis.SmithNormalForm N ι n) (hN : Saturated N) (i :
    Fin n) :
    snf.bM (snf.f i) ∈ N := by
  have h1 : ((snf.bN i : N) : ι → ℤ) ∈ N := (snf.bN i).2
  rw [snf.snf] at h1
  have ha : snf.a i ≠ 0 := by
    intro h0
    have h2 : ((snf.bN i : N) : ι → ℤ) = 0 := by rw [snf.snf, h0, zero_smul]
    exact snf.bN.ne_zero i (Subtype.ext h2)
  exact hN _ _ ha h1

include hN in
private theorem exists_projection : ∃ π : (ι → ℤ) →ₗ[ℤ] (ι → ℤ), (∀ v, π v ∈ N) ∧ ∀ n ∈ N, π n = n
    := by
  classical
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun ℤ ι) N
  set g : ι → ι → ℤ := fun j => if j ∈ Set.range snf.f then snf.bM j else 0 with hg
  have hgN : ∀ j, g j ∈ N := by
    intro j
    simp only [hg]
    split_ifs with hj
    · obtain ⟨i, rfl⟩ := hj
      exact bM_mem N snf hN i
    · exact N.zero_mem
  refine ⟨snf.bM.constr ℤ g, fun v => ?_, fun m hm => ?_⟩
  · rw [Module.Basis.constr_apply]
    exact Submodule.sum_mem N fun j _ => N.smul_mem _ (hgN j)
  · rw [Module.Basis.constr_apply]
    conv_rhs => rw [← snf.bM.linearCombination_repr m, Finsupp.linearCombination_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ Set.range snf.f
    · simp only [hg, ite_eq_left hj]
    · simp only [snf.repr_eq_zero_of_notMem_range ⟨m, hm⟩ hj, zero_smul]

include hN in
private theorem exists_dot_eq (μ : N →ₗ[ℤ] ℤ) : ∃ w : ι → ℤ, ∀ n : N, w ⬝ᵥ n = μ n := by
  obtain ⟨π, hπ, hπN⟩ := exists_projection N hN
  set Λ : (ι → ℤ) →ₗ[ℤ] ℤ := μ ∘ₗ LinearMap.codRestrict N π hπ with hΛ
  obtain ⟨w, hw⟩ := exists_eq_dotL Λ
  refine ⟨w, fun n => ?_⟩
  rw [← hw]
  simp only [hΛ, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  simp [hπN n n.2]

include hN in
private theorem perp_perp : perp (perp N) = N := by
  classical
  refine le_antisymm ?_ ?_
  · intro v hv
    by_contra hvN
    obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun ℤ ι) N
    have hex : ∃ j, j ∉ Set.range snf.f ∧ snf.bM.repr v j ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hvN
      rw [← snf.bM.linearCombination_repr v, Finsupp.linearCombination_apply]
      refine Submodule.sum_mem N fun j _ => ?_
      by_cases hj : j ∈ Set.range snf.f
      · obtain ⟨i, rfl⟩ := hj
        exact N.smul_mem _ (bM_mem N snf hN i)
      · simp only [hall j hj, zero_smul]
        exact N.zero_mem
    obtain ⟨j, hj, hvj⟩ := hex
    obtain ⟨w, hw⟩ := exists_eq_dotL (snf.bM.coord j)
    have hwN : w ∈ perp N := by
      intro m hm
      rw [← hw]
      exact snf.le_ker_coord_of_notMem_range hj hm
    have h0 := hv w hwN
    rw [dotProduct_comm, ← hw] at h0
    exact hvj h0
  · intro n hn v hv
    rw [dotProduct_comm]
    exact hv n hn

end Sat

section Rank

private theorem finrank_perp_add (N : Submodule ℤ (ι → ℤ)) (hN : Saturated N) :
    finrank ℤ (perp N) + finrank ℤ N = Fintype.card ι := by
  set ρ : (ι → ℤ) →ₗ[ℤ] Module.Dual ℤ N := (dotL (ι := ι)).domRestrict₂ N with hρ
  have hker : LinearMap.ker ρ = perp N := by
    ext v
    simp only [LinearMap.mem_ker, mem_perp]
    constructor
    · intro h n hn
      have := LinearMap.congr_fun h ⟨n, hn⟩
      simp [hρ] at this
      exact this
    · intro h
      ext n
      have h__af := h n n.2
      simp [hρ] at h__af ⊢
      exact h__af
  have hsurj : Function.Surjective ρ := by
    intro μ
    obtain ⟨w, hw⟩ := exists_dot_eq N hN μ
    refine ⟨w, ?_⟩
    ext n
    have h__af := hw n
    simp [hρ] at h__af ⊢
    exact h__af
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker ρ)
  have h1' : finrank ℤ ((ι → ℤ) ⧸ LinearMap.ker ρ) = finrank ℤ (Module.Dual ℤ N) := by
    rw [(LinearMap.quotKerEquivRange ρ).finrank_eq, LinearMap.range_eq_top.mpr hsurj, finrank_top]
  rw [h1', hker] at h1
  haveI : Module.Free ℤ N := Module.free_of_finite_type_torsion_free'
  have h2 : finrank ℤ (Module.Dual ℤ N) = finrank ℤ N := by
    have b := Module.Free.chooseBasis ℤ N
    rw [finrank_eq_card_basis b, finrank_eq_card_basis b.dualBasis]
  rw [h2] at h1
  rw [← Module.finrank_fintype_fun_eq_card ℤ, ← h1, add_comm]

private theorem finrank_sup_add_finrank_inf (s t : Submodule ℤ (ι → ℤ)) :
    finrank ℤ ↥(s ⊔ t) + finrank ℤ ↥(s ⊓ t) = finrank ℤ s + finrank ℤ t := by
  have h := Submodule.rank_sup_add_rank_inf_eq s t
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
  exact_mod_cast h

private theorem eq_of_le_of_finrank_eq {N M : Submodule ℤ (ι → ℤ)} (hle : N ≤ M)
    (hrank : finrank ℤ N = finrank ℤ M)
    (hsat : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → v ∈ M → n • v ∈ N → v ∈ N) : N = M := by
  refine le_antisymm hle fun v hv => ?_
  set N' : Submodule ℤ M := N.comap M.subtype with hN'
  have hq : finrank ℤ (M ⧸ N') = 0 := by
    have h := Submodule.finrank_quotient_add_finrank N'
    have hN'r : finrank ℤ N' = finrank ℤ N := by
      have e : N' ≃ₗ[ℤ] N := Submodule.comapSubtypeEquivOfLe hle
      exact e.finrank_eq
    omega
  have htors := (Module.finrank_eq_zero_iff_isTorsion (R := ℤ) (M := M ⧸ N')).mp hq
  obtain ⟨⟨a, ha⟩, hav⟩ := htors (x := Submodule.Quotient.mk ⟨v, hv⟩)
  have ha0 : (a : ℤ) ≠ 0 := nonZeroDivisors.ne_zero ha
  rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN',
    Submodule.mem_comap] at hav
  exact hsat a v ha0 hv (by simpa using hav)

end Rank

section Main

variable {L : Type*} [AddCommGroup L] [Module ℤ L]
variable (B E : Submodule ℤ (ι → ℤ)) (hB : Saturated B) (hE : Saturated E)
variable (hBE : ∀ b ∈ B, ∀ e ∈ E, b ⬝ᵥ e = 0)
variable (f X : L →ₗ[ℤ] (ι → ℤ))
variable (hf : ∀ y, ∀ e ∈ E, f y ⬝ᵥ e = 0) (hX : ∀ x, ∀ b ∈ B, X x ⬝ᵥ b = 0)
variable (hfB : ∀ y, f y ∈ B → y = 0) (hXE : ∀ x, X x ∈ E → x = 0)
variable (hZ : ∀ v : ι → ℤ, (∀ e ∈ E, v ⬝ᵥ e = 0) → ∃ y, v - f y ∈ B)
variable (hsat : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → (∃ x, n • v - X x ∈ E) → ∃ x, v - X x ∈ E)

private def pr : L →ₗ[ℤ] L →ₗ[ℤ] ℤ := ((dotL (ι := ι)).comp X).compl₂ f

@[scoped simp] private theorem pr_apply (x y : L) : pr f X x y = X x ⬝ᵥ f y := rfl

include hfB in
private theorem f_injective : Function.Injective f := by
  intro y y' h
  have : f (y - y') ∈ B := by rw [map_sub, h, sub_self]; exact B.zero_mem
  exact sub_eq_zero.mp (hfB _ this)

include hXE in
private theorem X_injective : Function.Injective X := by
  intro y y' h
  have : X (y - y') ∈ E := by rw [map_sub, h, sub_self]; exact E.zero_mem
  exact sub_eq_zero.mp (hXE _ this)

include hfB in
private theorem finite_L : Module.Finite ℤ L := Module.Finite.of_injective f (f_injective B f hfB)

include hfB in
private theorem free_L : Module.Free ℤ L := by
  haveI := finite_L B f hfB
  haveI : Module.IsTorsionFree ℤ L :=
    Function.Injective.moduleIsTorsionFree f (f_injective B f hfB) (fun r m => LinearMap.map_smul f
        r m)
  exact Module.free_of_finite_type_torsion_free'

include hBE hf hZ hfB in
private theorem perp_E_eq : perp E = LinearMap.range f ⊔ B := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨y, hy⟩ := hZ v hv
    rw [Submodule.mem_sup]
    exact ⟨f y, ⟨y, rfl⟩, v - f y, hy, by abel⟩
  · rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, rfl⟩ e he
      exact hf y e he
    · intro b hb e he
      exact hBE b hb e he

include hfB in
private theorem range_f_inf_B : LinearMap.range f ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨y, rfl⟩, hyB⟩
  rw [Submodule.mem_bot, hfB y hyB, map_zero]

include hXE in
private theorem range_X_inf_E : LinearMap.range X ⊓ E = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨y, rfl⟩, hyE⟩
  rw [Submodule.mem_bot, hXE y hyE, map_zero]

include hB hE hBE hf hX hfB hXE hZ hsat in
private theorem perp_B_eq : perp B = LinearMap.range X ⊔ E := by
  symm
  have hle : LinearMap.range X ⊔ E ≤ perp B := by
    rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩ b hb
      exact hX x b hb
    · intro e he b hb
      rw [dotProduct_comm]
      exact hBE b hb e he
  refine eq_of_le_of_finrank_eq hle ?_ ?_
  · have hZ' := perp_E_eq B E hBE f hf hfB hZ
    have h1 := finrank_perp_add E hE
    have h2 := finrank_perp_add B hB
    have h3 := finrank_sup_add_finrank_inf (LinearMap.range f) B
    have h4 := finrank_sup_add_finrank_inf (LinearMap.range X) E
    rw [range_f_inf_B B f hfB, finrank_bot, add_zero, ← hZ'] at h3
    rw [range_X_inf_E E X hXE, finrank_bot, add_zero] at h4
    have h5 : finrank ℤ (LinearMap.range f) = finrank ℤ (LinearMap.range X) := by
      haveI := finite_L B f hfB
      rw [LinearMap.finrank_range_of_inj (f_injective B f hfB),
        LinearMap.finrank_range_of_inj (X_injective E X hXE)]
    omega
  · intro n v hn _ hnv
    rw [Submodule.mem_sup] at hnv ⊢
    obtain ⟨_, ⟨x, rfl⟩, e, he, hxe⟩ := hnv
    obtain ⟨x', hx'⟩ := hsat n v hn ⟨x, by rw [← hxe]; simpa using he⟩
    exact ⟨X x', ⟨x', rfl⟩, v - X x', hx', by abel⟩

include hB hE hBE hf hX hfB hXE hZ hsat in
private theorem pr_injective : Function.Injective (pr f X) := by
  intro x x' h
  rw [← sub_eq_zero]
  apply hXE
  rw [← perp_perp E hE]
  rw [perp_E_eq B E hBE f hf hfB hZ]
  intro v hv
  rw [Submodule.mem_sup] at hv
  obtain ⟨_, ⟨y, rfl⟩, b, hb, rfl⟩ := hv
  rw [dotProduct_add, hX _ b hb, add_zero, map_sub, sub_dotProduct]
  have := LinearMap.congr_fun h y
  simp only [pr_apply] at this
  rw [this, sub_self]

include hB hE hBE hf hX hfB hXE hZ hsat in
private theorem pr_surjective : Function.Surjective (pr f X) := by
  intro μ
  classical
  have hZmem : ∀ z : perp E, ∃ y : L, (z : ι → ℤ) - f y ∈ B := fun z => hZ z z.2
  choose sec hsec using hZmem
  have hsec_unique : ∀ (z : perp E) (y : L), (z : ι → ℤ) - f y ∈ B → sec z = y := by
    intro z y hy
    have : f (y - sec z) ∈ B := by
      have := B.sub_mem (hsec z) hy
      rw [map_sub]
      convert this using 1
      abel
    have := hfB _ this
    exact (sub_eq_zero.mp this).symm
  set secL : perp E →ₗ[ℤ] L :=
    { toFun := sec
      map_add' := fun z z' => by
        apply hsec_unique
        rw [Submodule.coe_add, map_add]
        have := B.add_mem (hsec z) (hsec z')
        convert this using 1
        abel
      map_smul' := fun c z => by
        apply hsec_unique
        rw [LinearMap.map_smul, RingHom.id_apply, Submodule.coe_smul, ← smul_sub]
        exact B.smul_mem c (hsec z) } with hsecL
  have hsecL_apply : ∀ z, secL z = sec z := fun z => rfl
  obtain ⟨w, hw⟩ := exists_dot_eq (perp E) (saturated_perp E) (μ ∘ₗ secL)
  have hwB : w ∈ perp B := by
    intro b hb
    have hbZ : b ∈ perp E := fun e he => hBE b hb e he
    have := hw ⟨b, hbZ⟩
    rw [this, LinearMap.comp_apply, hsecL_apply, hsec_unique ⟨b, hbZ⟩ 0 (by simpa using hb),
      map_zero]
  rw [perp_B_eq B E hB hE hBE f X hf hX hfB hXE hZ hsat, Submodule.mem_sup] at hwB
  obtain ⟨_, ⟨x, rfl⟩, e, he, hxe⟩ := hwB
  refine ⟨x, ?_⟩
  ext y
  rw [pr_apply]
  have hfyZ : f y ∈ perp E := fun e' he' => hf y e' he'
  have h1 := hw ⟨f y, hfyZ⟩
  rw [LinearMap.comp_apply, hsecL_apply, hsec_unique ⟨f y, hfyZ⟩ y (by simp)]
    at h1
  rw [← h1, ← hxe, add_dotProduct, dotProduct_comm e, hf y e he, add_zero]

include hB hE hBE hf hX hfB hXE hZ hsat in
private theorem isPerfPair_pr : (pr f X).IsPerfPair := by
  haveI := finite_L B f hfB
  haveI := free_L B f hfB
  exact LinearMap.IsPerfPair.of_bijective _
    ⟨pr_injective B E hB hE hBE f X hf hX hfB hXE hZ hsat,
      pr_surjective B E hB hE hBE f X hf hX hfB hXE hZ hsat⟩

end Main

end DotProductPairingAux

open DotProductPairingAux in
/-- Under the saturation and orthogonality hypotheses, `(x, y) ↦ X x ⬝ᵥ f y` is a perfect
pairing on `L`. -/
public theorem Submodule.exists_isPerfPair_dotProduct_of_saturated {ι : Type*} [Fintype ι]
    {L : Type*} [AddCommGroup L] [Module ℤ L]
    (B E : Submodule ℤ (ι → ℤ))
    (hB : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ B → v ∈ B)
    (hE : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ E → v ∈ E)
    (hBE : ∀ b ∈ B, ∀ e ∈ E, b ⬝ᵥ e = 0)
    (f X : L →ₗ[ℤ] (ι → ℤ))
    (hf : ∀ y, ∀ e ∈ E, f y ⬝ᵥ e = 0) (hX : ∀ x, ∀ b ∈ B, X x ⬝ᵥ b = 0)
    (hfB : ∀ y, f y ∈ B → y = 0) (hXE : ∀ x, X x ∈ E → x = 0)
    (hZ : ∀ v : ι → ℤ, (∀ e ∈ E, v ⬝ᵥ e = 0) → ∃ y, v - f y ∈ B)
    (hsat : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → (∃ x, n • v - X x ∈ E) → ∃ x, v - X x ∈ E) :
    ∃ p : L →ₗ[ℤ] L →ₗ[ℤ] ℤ, (∀ x y, p x y = X x ⬝ᵥ f y) ∧ p.IsPerfPair :=
  ⟨pr f X, pr_apply f X, isPerfPair_pr B E hB hE hBE f X hf hX hfB hXE hZ hsat⟩
