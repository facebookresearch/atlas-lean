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
`CF_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt`
`CF_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt`
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
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd
public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeEdge
import MathlibExt.AlgebraicGeometry.FormalOmega.EdgeNondegUniqueAux

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.EdgeNondegUnique

section Generation

variable {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q]

private theorem eq_top_of_mem_of_forall_not_mem_smul_top [Module.Invertible R Q]
    (N : Submodule R Q) (q : Q) (hqN : q ∈ N)
    (hq : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → q ∉ (𝔪 • ⊤ : Submodule R Q)) : N = ⊤ := by
  set A : Ideal R := N.colon (Set.univ : Set Q) with hA_def
  by_cases hA : A = ⊤
  · have h1 : (1 : R) ∈ A := by rw [hA]; exact Submodule.mem_top
    rw [hA_def, Submodule.mem_colon] at h1
    refine eq_top_iff.mpr fun m _ => ?_
    have := h1 m (Set.mem_univ m)
    rwa [one_smul] at this
  · exfalso
    obtain ⟨𝔪, h𝔪, hA𝔪⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem 𝔪 q (hq 𝔪 h𝔪)
    obtain ⟨c, hc⟩ := (Module.Invertible.toModuleEnd_bijective R Q).2 (LinearMap.smulRight φ q)
    have hc' : ∀ x : Q, c • x = φ x • q := fun x => by
      have := congrArg (fun f : Module.End R Q => f x) hc
      simp only [LinearMap.smulRight_apply] at this
      exact this
    have hcA : c ∈ A := by
      rw [hA_def, Submodule.mem_colon]
      intro m _
      rw [hc' m]
      exact N.smul_mem _ hqN
    have hkey : (φ q - c) * φ q = 0 := by
      have h := congrArg φ (hc' q)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
      rw [sub_mul, ← h, sub_self]
    have hmem : (φ q - c) * φ q ∈ 𝔪 := by rw [hkey]; exact 𝔪.zero_mem
    rcases h𝔪.isPrime.mem_or_mem hmem with h1 | h1
    · apply hφ
      have : φ q = (φ q - c) + c := by ring
      rw [this]
      exact 𝔪.add_mem h1 (hA𝔪 hcA)
    · exact hφ h1

private theorem mem_sup_smul_top_of_mkQ_mem {V : Type} [AddCommGroup V] [Module R V]
    (N : Submodule R V) (I : Ideal R) (x : V)
    (hx : N.mkQ x ∈ (I • ⊤ : Submodule R (V ⧸ N))) : x ∈ N ⊔ (I • ⊤ : Submodule R V) := by
  have : x ∈ ((I • ⊤ : Submodule R V).map N.mkQ).comap N.mkQ := by
    rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    exact hx
  rwa [Submodule.comap_map_mkQ] at this

end Generation

section Transitions

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem line_le_comap (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K}
    (h : M₁.1 ≤ M₂.1) : d.line M₁ ≤ (d.line M₂).comap (inclBaseChange B h) :=
  Submodule.map_le_iff_le_comap.mp (d.mono h)

private def transition (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K}
    (h : M₁.1 ≤ M₂.1) :
    (latticeBaseChange 𝒪 K B M₁ ⧸ d.line M₁) →ₗ[B] (latticeBaseChange 𝒪 K B M₂ ⧸ d.line M₂) :=
  Submodule.mapQ _ _ (inclBaseChange B h) (line_le_comap π d h)

private theorem transition_mk (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K}
    (h : M₁.1 ≤ M₂.1) (x : latticeBaseChange 𝒪 K B M₁) :
    transition π d h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (inclBaseChange B h x) :=
  Submodule.mapQ_apply _ _ _ x

private theorem inclBaseChange_tmul' {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) (b : B)
    (v : ↥M₁.1) : inclBaseChange B h (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) :=
  rfl

private theorem transition_bijective_of_generator (d : DeligneDatum (K := K) π B)
    {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) (v : ↥M₁.1)
    (hv : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → (1 : B) ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) ∉
      d.line M₂ ⊔ (𝔪 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M₂))) :
    Function.Bijective (transition π d h) := by
  have := d.invertible M₁
  have := d.invertible M₂
  have hsurj : Function.Surjective (transition π d h) := by
    rw [← LinearMap.range_eq_top]
    apply eq_top_of_mem_of_forall_not_mem_smul_top _
      ((d.line M₂).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1)))
    · refine ⟨(d.line M₁).mkQ ((1 : B) ⊗ₜ[𝒪] v), ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, transition_mk, inclBaseChange_tmul']
    · intro 𝔪 h𝔪 hmem
      exact hv 𝔪 h𝔪 (mem_sup_smul_top_of_mkQ_mem _ _ _ hmem)
  exact Module.Invertible.bijective_of_surjective hsurj

end Transitions

section Vertex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem vertexNondegAt_map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) {𝔭 : Ideal B} (M : FullLattice 𝒪 K)
    (hd : d.VertexNondegAt π 𝔭 M) (𝔮 : Ideal B') (h𝔮 : 𝔮.IsPrime)
    (hle : Ideal.comap f 𝔮 ≤ 𝔭) : (d.map π f).VertexNondegAt π 𝔮 M := by
  intro v hv
  rw [← rTensor_one_tmul f M v]
  refine rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔮 _
    fun hmem => hd v hv ?_
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  exact Submodule.mem_sup.mpr ⟨y, hy, z, Submodule.smul_mono_left hle hz, hyz⟩

private theorem vertexNondegAt_act (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ)
    (L : FullLattice 𝒪 K) (h : d.VertexNondegAt π 𝔭 L) :
    d.VertexNondegAt π 𝔭 (FullLattice.act (scalarGL c) L) := by
  intro v hv hmem
  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp v.2
  have hv_eq : v = latticeMapEquiv (scalarGL c) L.1 ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [coe_latticeMapEquiv_apply, ← hwv, scalarGL_mulVec]
  apply h ⟨w, hw⟩
  · rintro ⟨w', hw'⟩
    apply hv
    refine ⟨latticeMapEquiv (scalarGL c) L.1 w', ?_⟩
    rw [hv_eq, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, hw', Matrix.mulVec_smul]
  · rw [d.homothety c L] at hmem
    have key : actBaseChange B (scalarGL c) L ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥L.1)) =
        (1 : B) ⊗ₜ[𝒪] v := by
      rw [hv_eq]; rfl
    rw [← key] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    refine Submodule.mem_sup.mpr ⟨y₀, hy₀, (actBaseChange B (scalarGL c) L).symm z, ?_, ?_⟩
    · have : z ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)).map
          (actBaseChange B (scalarGL c) L).toLinearMap := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]; exact hz
      obtain ⟨z₀, hz₀, rfl⟩ := this
      rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]; exact hz₀
    · apply (actBaseChange B (scalarGL c) L).injective
      rw [map_add, LinearEquiv.apply_symm_apply, ← hyz, LinearEquiv.coe_coe]

private theorem edgeNondegAt_map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) {𝔭 : Ideal B} (M' M : FullLattice 𝒪 K)
    (hd : d.EdgeNondegAt π 𝔭 M' M) (𝔮 : Ideal B') (h𝔮 : 𝔮.IsPrime)
    (hle : Ideal.comap f 𝔮 ≤ 𝔭) : (d.map π f).EdgeNondegAt π 𝔮 M' M := by
  obtain ⟨hMM, hπ, h1, h2⟩ := hd
  have hmono : ∀ (L : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B L),
      x ∈ d.line L ⊔ (Ideal.comap f 𝔮 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) →
      x ∈ d.line L ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
    intro L x hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    exact Submodule.mem_sup.mpr ⟨y, hy, z, Submodule.smul_mono_left hle hz, hyz⟩
  refine ⟨hMM, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔮 _
      fun h => h1 v hv (hmono M _ h)
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') 𝔮 _
      fun h => h2 v' hv' (hmono M' _ h)

end Vertex

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
  [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

private theorem eq_of_vertexNondegAt_of_generator (hπ : Irreducible π)
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    {L M : FullLattice 𝒪 K} (hLM : L.1 ≤ M.1) (u : ↥L.1)
    (hu : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → (1 : B) ⊗ₜ[𝒪] (⟨u, hLM u.2⟩ : ↥M.1) ∉
      d.line M ⊔ (𝔪 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)))
    (hL : d.VertexNondegAt π 𝔭 L) : L.1 = M.1 := by
  by_contra hne
  have := d.invertible L
  have := d.invertible M
  have hbij : Function.Bijective (transition π d hLM) :=
    transition_bijective_of_generator π d hLM u hu
  obtain ⟨v, hvL, ⟨w, hwM, hvw⟩, hvπL⟩ := exists_mem_smul_not_mem_smul hπ L.2 hLM hne
  apply hL ⟨v, hvL⟩
  · rintro ⟨w', hw'⟩
    exact hvπL ⟨w', w'.2, hw'⟩
  apply mem_sup_smul_top_of_mkQ_mem
  have hT : transition π d hLM ((d.line L).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvL⟩ : ↥L.1))) =
      algebraMap 𝒪 B π • (d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨w, hwM⟩ : ↥M.1)) := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, transition_mk, inclBaseChange_tmul',
      ← Submodule.Quotient.mk_smul]
    congr 1
    have : (⟨v, hLM hvL⟩ : ↥M.1) = π • (⟨w, hwM⟩ : ↥M.1) := by
      apply Subtype.ext
      change v = π • w
      rw [hvw, algebraMap_smul]
    rw [this, TensorProduct.tmul_smul, algebraMap_smul]
  have hmemM : transition π d hLM ((d.line L).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvL⟩ : ↥L.1))) ∈
      (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M ⧸ d.line M)) := by
    rw [hT]
    exact Submodule.smul_mem_smul h𝔭 Submodule.mem_top
  have hrange : (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M ⧸ d.line M)) =
      (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ d.line L)).map
        (transition π d hLM) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hbij.2]
  rw [hrange] at hmemM
  obtain ⟨y, hy, hyeq⟩ := hmemM
  rw [← hbij.1 hyeq]
  exact hy

end Main

section ShareVertex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

private abbrev tgt (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A : FullLattice 𝒪 K) :
    Submodule B (latticeBaseChange 𝒪 K B A) :=
  d.line A ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A))

private def W (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A : FullLattice 𝒪 K) :
    Submodule 𝒪 (Fin 2 → K) where
  carrier := {v | ∃ hv : v ∈ A.1, (1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥A.1) ∈ tgt d 𝔭 A}
  zero_mem' := ⟨A.1.zero_mem, by
    have : (⟨0, A.1.zero_mem⟩ : ↥A.1) = 0 := rfl
    rw [this, TensorProduct.tmul_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨A.1.add_mem hv hw, ?_⟩
    have : (⟨v + w, A.1.add_mem hv hw⟩ : ↥A.1) = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
    rw [this, TensorProduct.tmul_add]; exact Submodule.add_mem _ hv' hw'
  smul_mem' := by
    rintro r v ⟨hv, hv'⟩
    refine ⟨A.1.smul_mem r hv, ?_⟩
    have : (⟨r • v, A.1.smul_mem r hv⟩ : ↥A.1) = r • ⟨v, hv⟩ := rfl
    rw [this, TensorProduct.tmul_smul, ← algebraMap_smul B r]
    exact Submodule.smul_mem _ _ hv'

private theorem mem_W {d : DeligneDatum (K := K) π B} {𝔭 : Ideal B} {A : FullLattice 𝒪 K}
    {v : Fin 2 → K} :
    v ∈ W d 𝔭 A ↔ ∃ hv : v ∈ A.1, (1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥A.1) ∈ tgt d 𝔭 A := Iff.rfl

private theorem mem_W_of_mem {d : DeligneDatum (K := K) π B} {𝔭 : Ideal B}
    {A : FullLattice 𝒪 K} (v : ↥A.1) (h : (1 : B) ⊗ₜ[𝒪] v ∈ tgt d 𝔭 A) :
    (v : Fin 2 → K) ∈ W d 𝔭 A := ⟨v.2, h⟩

private theorem tmul_mem_of_mem_W {d : DeligneDatum (K := K) π B} {𝔭 : Ideal B}
    {A : FullLattice 𝒪 K} (v : ↥A.1) (h : (v : Fin 2 → K) ∈ W d 𝔭 A) :
    (1 : B) ⊗ₜ[𝒪] v ∈ tgt d 𝔭 A := by
  obtain ⟨hv, h⟩ := h; exact h

private theorem W_le (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A : FullLattice 𝒪 K) :
    W d 𝔭 A ≤ A.1 :=
  fun _ ⟨hv, _⟩ => hv

private theorem pi_smul_mem_W (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭) (A : FullLattice 𝒪 K) (v : Fin 2 → K) (hv : v ∈ A.1) :
    algebraMap 𝒪 K π • v ∈ W d 𝔭 A := by
  have hmem : algebraMap 𝒪 K π • v ∈ A.1 := by rw [algebraMap_smul]; exact A.1.smul_mem π hv
  refine ⟨hmem, ?_⟩
  have : (⟨algebraMap 𝒪 K π • v, hmem⟩ : ↥A.1) = π • ⟨v, hv⟩ := by
    apply Subtype.ext; simp [algebraMap_smul]
  rw [this, TensorProduct.tmul_smul, ← algebraMap_smul B π]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul h𝔭 Submodule.mem_top)

private theorem W_ne (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime]
    (A : FullLattice 𝒪 K) : W d 𝔭 A ≠ A.1 := by
  intro hW
  have := d.invertible A
  have htop : tgt d 𝔭 A = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul b v =>
      have hv : (v : Fin 2 → K) ∈ W d 𝔭 A := by rw [hW]; exact v.2
      have h1 := tmul_mem_of_mem_W v hv
      have : b ⊗ₜ[𝒪] v = b • ((1 : B) ⊗ₜ[𝒪] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ h1
  have hQ : (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A ⧸ d.line A)) = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (d.line A) q
    have hx : x ∈ tgt d 𝔭 A := by rw [htop]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy0 : (d.line A).mkQ y = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hy
    rw [map_add, hy0, zero_add]
    have : (d.line A).mkQ z ∈
        ((𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A))).map (d.line A).mkQ :=
      Submodule.mem_map_of_mem hz
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
  have hfg : (⊤ : Submodule B (latticeBaseChange 𝒪 K B A ⧸ d.line A)).FG := Module.Finite.fg_top
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔭 ⊤ hfg (by rw [hQ])
  have hr0 : r = 0 := by
    have hinj :=
      (Module.Invertible.toModuleEnd_bijective B (latticeBaseChange 𝒪 K B A ⧸ d.line A)).1
    apply hinj
    refine LinearMap.ext fun q => ?_
    rw [map_zero, LinearMap.zero_apply]
    exact hr q Submodule.mem_top
  rw [hr0, zero_sub] at hr1
  exact (Ideal.IsPrime.ne_top ‹𝔭.IsPrime›)
    ((Ideal.eq_top_iff_one _).mpr (by simpa using 𝔭.neg_mem hr1))

private theorem not_W_le_of_not_vertexNondegAt [IsDomain 𝒪] [IsFractionRing 𝒪 K]
    (hπ : Irreducible π) (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B)
    (A : FullLattice 𝒪 K) (hV : ¬ d.VertexNondegAt π 𝔭 A) :
    ¬ (W d 𝔭 A ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) A.1) := by
  intro hle
  apply hV
  intro v hv hmem
  have hW : (v : Fin 2 → K) ∈ W d 𝔭 A := mem_W_of_mem v hmem
  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp (hle hW)
  exact hv ⟨⟨w, hw⟩, by rw [← hwv, unitOfNeZero_coe]⟩

private theorem W_mono (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (A A' : FullLattice 𝒪 K)
    (h : A'.1 ≤ A.1) : W d 𝔭 A' ≤ W d 𝔭 A := by
  rintro v ⟨hv, hv'⟩
  refine ⟨h hv, ?_⟩
  have himg : inclBaseChange B h ((1 : B) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥A'.1)) =
      (1 : B) ⊗ₜ[𝒪] (⟨v, h hv⟩ : ↥A.1) := rfl
  rw [← himg]
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv'
  rw [← hyz, map_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (d.mono h (Submodule.mem_map_of_mem hy)))
    (Submodule.mem_sup_right ?_)
  have : inclBaseChange B h z ∈
      ((𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B A'))).map (inclBaseChange B h) :=
    Submodule.mem_map_of_mem hz
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono (le_refl 𝔭) le_top this

private theorem W_act_scalarGL (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (c : Kˣ)
    (A : FullLattice 𝒪 K) :
    W d 𝔭 (FullLattice.act (scalarGL c) A) = latticeMap (scalarGL c) (W d 𝔭 A) := by
  set e := actBaseChange B (scalarGL c) A with he
  have htgt : tgt d 𝔭 (FullLattice.act (scalarGL c) A) = (tgt d 𝔭 A).map e.toLinearMap := by
    change d.line (FullLattice.act (scalarGL c) A) ⊔ _ = _
    rw [d.homothety c A, Submodule.map_sup, Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range]
  have hcoe : ∀ (w : ↥A.1),
      ((latticeMapEquiv (scalarGL c) A.1 w : ↥(latticeMap (scalarGL c) A.1)) : Fin 2 → K) =
        (c : K) • (w : Fin 2 → K) := fun w => by
    rw [coe_latticeMapEquiv_apply, scalarGL_mulVec]
  ext v
  rw [mem_W, mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨hv, hmem⟩
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
    refine ⟨w, ⟨hw, ?_⟩, hwv⟩
    have hsub : (⟨v, hv⟩ : ↥(FullLattice.act (scalarGL c) A).1) =
        latticeMapEquiv (scalarGL c) A.1 ⟨w, hw⟩ := by
      apply Subtype.ext; rw [hcoe]; exact hwv.symm
    rw [hsub] at hmem
    change e ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥A.1)) ∈ tgt d 𝔭 (FullLattice.act (scalarGL c) A)
      at hmem
    rw [htgt, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hmem
    exact hmem
  · rintro ⟨w, ⟨hw, hmem⟩, hwv⟩
    have hv : v ∈ (FullLattice.act (scalarGL c) A).1 := mem_latticeMap_scalarGL.mpr ⟨w, hw, hwv⟩
    refine ⟨hv, ?_⟩
    have hsub : (⟨v, hv⟩ : ↥(FullLattice.act (scalarGL c) A).1) =
        latticeMapEquiv (scalarGL c) A.1 ⟨w, hw⟩ := by
      apply Subtype.ext; rw [hcoe]; exact hwv.symm
    rw [hsub]
    change e ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥A.1)) ∈ tgt d 𝔭 (FullLattice.act (scalarGL c) A)
    rw [htgt, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    exact hmem

private theorem edge_read [IsDomain 𝒪] [IsFractionRing 𝒪 K] (hπ : Irreducible π)
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (M' M : FullLattice 𝒪 K)
    (h : d.EdgeNondegAt π 𝔭 M' M) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 ∧ M'.1 ≤ M.1 ∧
      W d 𝔭 M ≤ M'.1 ∧
      W d 𝔭 M' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 := by
  obtain ⟨hle, hπM, h3, h4⟩ := h
  refine ⟨?_, hle, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [unitOfNeZero_coe]; exact hπM ⟨w, hw⟩
  · rintro v ⟨hv, hmem⟩
    by_contra hnot
    exact h3 ⟨v, hv⟩ hnot hmem
  · rintro v ⟨hv, hmem⟩
    by_contra hnot
    refine h4 ⟨v, hv⟩ ?_ hmem
    rintro ⟨w, hww⟩
    exact hnot (mem_latticeMap_scalarGL.mpr
      ⟨w, w.2, by rw [unitOfNeZero_coe]; exact hww.symm⟩)

private theorem latticeMap_scalarGL_of_eq_of_eq
    {P X Y : Submodule 𝒪 (Fin 2 → K)} {c c' : Kˣ}
    (hX : latticeMap (scalarGL c) P = X) (hY : latticeMap (scalarGL c') P = Y) :
    latticeMap (scalarGL (c' * c⁻¹)) X = Y := by
  rw [← hX, ← hY, ← latticeMap_mul, ← scalarGL_mul, mul_assoc, inv_mul_cancel, mul_one]

private theorem sc_le (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) X ≤ X := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hv
  rw [hc, algebraMap_smul]
  exact X.smul_mem π hw

private theorem smul_mem_sc (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {X : Submodule 𝒪 (Fin 2 → K)} {v : Fin 2 → K} (hv : v ∈ X) :
    algebraMap 𝒪 K π • v ∈ latticeMap (scalarGL c) X :=
  mem_latticeMap_scalarGL.2 ⟨v, hv, by rw [hc]⟩

private theorem forall_ne_of_not_mem_sc (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {X : Submodule 𝒪 (Fin 2 → K)} {v : Fin 2 → K} (hv : v ∉ latticeMap (scalarGL c) X) :
    ∀ w ∈ X, v ≠ algebraMap 𝒪 K π • w := by
  intro w hw h
  exact hv (mem_latticeMap_scalarGL.2 ⟨w, hw, by rw [hc, h]⟩)

private theorem sc_sup (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (X Y : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap g (X ⊔ Y) = latticeMap g X ⊔ latticeMap g Y :=
  Submodule.map_sup _ _ _

private theorem sc_comm (c c' : Kˣ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL c') X) =
      latticeMap (scalarGL c') (latticeMap (scalarGL c) X) := by
  rw [← latticeMap_mul, ← latticeMap_mul, ← scalarGL_mul, ← scalarGL_mul, mul_comm]

private theorem sc_pow_pow (c : Kˣ) (a b : ℕ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ a)) (latticeMap (scalarGL (c ^ b)) X) =
      latticeMap (scalarGL (c ^ (a + b))) X := by
  rw [← latticeMap_mul, ← scalarGL_mul, ← pow_add]

private theorem sc_pow_one (c : Kˣ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL c) X = latticeMap (scalarGL (c ^ 1)) X := by
  rw [pow_one]

private theorem sc_pow_le (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (j : ℕ)
    (X : Submodule 𝒪 (Fin 2 → K)) : latticeMap (scalarGL (c ^ j)) X ≤ X := by
  induction j with
  | zero => rw [pow_zero, scalarGL_one, latticeMap_one]
  | succ j ih =>
    rw [pow_succ', scalarGL_mul, latticeMap_mul]
    exact (latticeMap_mono _ ih).trans (sc_le c hc X)

private theorem pow_le_of_pow_le (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {X Y : Submodule 𝒪 (Fin 2 → K)} {j : ℕ} (h : latticeMap (scalarGL (c ^ j)) X ≤ Y) (i : ℕ) :
    latticeMap (scalarGL (c ^ (i + j))) X ≤ Y := by
  induction i with
  | zero => rwa [zero_add]
  | succ i ih =>
    rw [Nat.succ_add, pow_succ', scalarGL_mul, latticeMap_mul]
    exact (latticeMap_mono _ ih).trans (sc_le c hc Y)

private theorem absorb (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π) (X Y : Submodule 𝒪 (Fin 2 → K))
    (h : Y ≤ X ⊔ latticeMap (scalarGL c) Y) (j : ℕ) :
    Y ≤ X ⊔ latticeMap (scalarGL (c ^ j)) (latticeMap (scalarGL c) Y) := by
  induction j with
  | zero => rwa [pow_zero, scalarGL_one, latticeMap_one]
  | succ j ih =>
    have h1 : latticeMap (scalarGL c) Y ≤
        X ⊔ latticeMap (scalarGL (c ^ (j + 1))) (latticeMap (scalarGL c) Y) := by
      refine (latticeMap_mono (scalarGL c) ih).trans ?_
      rw [sc_sup, pow_succ', scalarGL_mul, latticeMap_mul]
      exact sup_le ((sc_le c hc X).trans le_sup_left) le_sup_right
    exact h.trans (sup_le le_sup_left h1)

private theorem isFullLattice_sup [IsFractionRing 𝒪 K] (L : FullLattice 𝒪 K)
    (Y : Submodule 𝒪 (Fin 2 → K)) (hY : Y.FG) : Submodule.IsFullLattice K (L.1 ⊔ Y) :=
  have := L.2
  Submodule.IsFullLattice.of_le_of_fg K le_sup_left ((Submodule.IsLattice.fg K L.1).sup hY)

private def P1 [IsFractionRing 𝒪 K] (c : Kˣ) (N A : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
  have := A.2
  ⟨N.1 ⊔ latticeMap (scalarGL c) A.1, isFullLattice_sup N _ ((Submodule.IsLattice.fg K A.1).map _)⟩

private theorem P1_val [IsFractionRing 𝒪 K] (c : Kˣ) (N A : FullLattice 𝒪 K) :
    (P1 c N A).1 = N.1 ⊔ latticeMap (scalarGL c) A.1 := rfl

end ShareVertex

private theorem lattice_walk
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    (W : FullLattice 𝒪 K → Submodule 𝒪 (Fin 2 → K))
    (hW_le : ∀ A : FullLattice 𝒪 K, W A ≤ A.1)
    (hW_ne : ∀ A : FullLattice 𝒪 K, W A ≠ A.1)
    (hπW : ∀ (A : FullLattice 𝒪 K) (v : Fin 2 → K), v ∈ A.1 → algebraMap 𝒪 K π • v ∈ W A)
    (hW_not : ∀ A : FullLattice 𝒪 K,
      ¬ (W A ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) A.1))
    (hW_mono : ∀ A A' : FullLattice 𝒪 K, A'.1 ≤ A.1 → W A' ≤ W A)
    (hW_hom : ∀ (c : Kˣ) (A : FullLattice 𝒪 K),
      W (FullLattice.act (scalarGL c) A) = latticeMap (scalarGL c) (W A))
    (M' M L' L : FullLattice 𝒪 K)
    (hM₂ : M'.1 ≤ M.1) (hM₃ : W M ≤ M'.1)
    (hM₄ : W M' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1)
    (hL₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) L.1 ≤ L'.1)
    (hL₂ : L'.1 ≤ L.1) (hL₃ : W L ≤ L'.1)
    (hL₄ : W L' ≤ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) L.1) :
    ∃ (c : Kˣ) (X Y : FullLattice 𝒪 K), (X = M' ∨ X = M) ∧ (Y = L' ∨ Y = L) ∧
      latticeMap (scalarGL c) X.1 = Y.1 := by
  classical
  set u : Kˣ := unitOfNeZero (K := K) hπ.ne_zero with hu_def
  have hu : (u : K) = algebraMap 𝒪 K π := by rw [hu_def, unitOfNeZero_coe]
  have two_step : ∀ (A : FullLattice 𝒪 K) (R₁ R₂ : Submodule 𝒪 (Fin 2 → K)),
      (∀ v ∈ A.1, algebraMap 𝒪 K π • v ∈ R₁) → R₁ ≤ R₂ → R₂ ≤ A.1 →
      (∃ v ∈ R₁, v ∉ latticeMap (scalarGL u) A.1) → R₂ ≠ A.1 → R₁ = R₂ := by
    intro A R₁ R₂ h1 h2 h3 h4 h5
    obtain ⟨v, hv, hv'⟩ := h4
    exact LT.LatticeTree.FullLattice.eq_of_forall_smul_mem_of_le_of_le π hπ A R₁ R₂ h1 h2 h3
      ⟨v, hv, forall_ne_of_not_mem_sc u hu hv'⟩ h5
  have hW_ex : ∀ A : FullLattice 𝒪 K, ∃ v ∈ W A, v ∉ latticeMap (scalarGL u) A.1 := fun A =>
    IsConcreteLE.not_le_iff_exists.mp (hW_not A)
  have strict : ∀ A' A : FullLattice 𝒪 K, W A ≤ A'.1 → W A' ≤ latticeMap (scalarGL u) A.1 →
      A'.1 ≠ A.1 ∧ latticeMap (scalarGL u) A.1 ≠ A'.1 := by
    intro A' A h3 h4
    constructor
    · intro h
      apply hW_not A
      have hAA : A' = A := Subtype.ext h
      rw [hAA] at h4
      exact h4
    · intro h
      apply hW_not A
      rw [h]
      exact h3
  have mono_lemma : ∀ P Q : FullLattice 𝒪 K, latticeMap (scalarGL u) P.1 ≤ Q.1 → Q.1 ≤ P.1 →
      latticeMap (scalarGL u) P.1 ≠ Q.1 → Q.1 ≠ P.1 →
      W Q = latticeMap (scalarGL u) P.1 ∨ W P = Q.1 := by
    intro P Q hPQ hQP hne1 hne2
    by_cases h : W Q ≤ latticeMap (scalarGL u) P.1
    · left
      exact two_step Q (W Q) _ (hπW Q) h hPQ (hW_ex Q) hne1
    · right
      obtain ⟨v, hvW, hv⟩ := IsConcreteLE.not_le_iff_exists.mp h
      have hvP : v ∈ W P := hW_mono P Q hQP hvW
      have hvQ : v ∈ Q.1 := hW_le Q hvW
      have hin : ∀ w ∈ P.1, algebraMap 𝒪 K π • w ∈ W P ⊓ Q.1 := fun w hw =>
        Submodule.mem_inf.mpr ⟨hπW P w hw, hPQ (smul_mem_sc u hu hw)⟩
      have e1 : W P ⊓ Q.1 = W P :=
        two_step P (W P ⊓ Q.1) (W P) hin inf_le_left (hW_le P)
          ⟨v, Submodule.mem_inf.mpr ⟨hvP, hvQ⟩, hv⟩ (hW_ne P)
      have e2 : W P ⊓ Q.1 = Q.1 :=
        two_step P (W P ⊓ Q.1) Q.1 hin inf_le_right hQP
          ⟨v, Submodule.mem_inf.mpr ⟨hvP, hvQ⟩, hv⟩ hne2
      rw [← e1, e2]
  have core : ∀ (N' N : FullLattice 𝒪 K), N.1 ≤ M.1 → ¬ N.1 ≤ latticeMap (scalarGL u) M.1 →
      latticeMap (scalarGL u) N.1 ≤ N'.1 → N'.1 ≤ N.1 → W N ≤ N'.1 →
      W N' ≤ latticeMap (scalarGL u) N.1 →
      N.1 = M.1 ∨ N'.1 = latticeMap (scalarGL u) M.1 := by
    intro N' N hNM hN_not hN₁ hN₂ hN₃ hN₄
    by_cases hNM' : N.1 = M.1
    · exact Or.inl hNM'
    right
    obtain ⟨k, hk⟩ := exists_sc_pow_le hπ N.2 M.2
    have hkM : latticeMap (scalarGL (u ^ k)) M.1 ≤ N.1 := hk
    have walk : ∀ (k : ℕ) (A : FullLattice 𝒪 K), N.1 ≤ A.1 →
        ¬ N.1 ≤ latticeMap (scalarGL u) A.1 →
        latticeMap (scalarGL (u ^ k)) A.1 ≤ N.1 → N.1 ≠ A.1 →
        W (P1 u N A) = latticeMap (scalarGL u) A.1 → N'.1 = latticeMap (scalarGL u) A.1 := by
      intro k
      induction k with
      | zero =>
        intro A h1 _ h3 h4 _
        exfalso
        apply h4
        rw [pow_zero, scalarGL_one, latticeMap_one] at h3
        exact le_antisymm h1 h3
      | succ k ih =>
        intro A hNA hNA_not hkA hNA_ne hWP
        have hNP_le : N.1 ≤ (P1 u N A).1 := le_sup_left
        by_cases hNP : N.1 = (P1 u N A).1
        · have hP : P1 u N A = N := (Subtype.ext hNP).symm
          rw [hP] at hWP
          symm
          refine two_step N (latticeMap (scalarGL u) A.1) N'.1 ?_ ?_ hN₂ ?_
            (strict N' N hN₃ hN₄).1
          · intro v hv
            exact smul_mem_sc u hu (hNA hv)
          · rw [← hWP]
            exact hN₃
          · by_contra hcon
            push Not at hcon
            exact hNA_ne (le_antisymm hNA
              (le_of_latticeMap_le (scalarGL u) (fun v hv => hcon v hv)))
        · exfalso
          have hscP_le : latticeMap (scalarGL u) (P1 u N A).1 ≤ latticeMap (scalarGL u) A.1 := by
            rw [P1_val, sc_sup]
            exact sup_le (latticeMap_mono _ hNA) (sc_le u hu _)
          have hN_not_P : ¬ N.1 ≤ latticeMap (scalarGL u) (P1 u N A).1 := fun h =>
            hNA_not (h.trans hscP_le)
          have hkP : latticeMap (scalarGL (u ^ k)) (P1 u N A).1 ≤ N.1 := by
            rw [P1_val, sc_sup, sc_pow_one u A.1, sc_pow_pow]
            exact sup_le (sc_pow_le u hu k N.1) hkA
          have hedge1 : latticeMap (scalarGL u) (P1 u N A).1 ≠ (P1 u N (P1 u N A)).1 := by
            intro h
            apply hN_not_P
            rw [h]
            exact le_sup_left
          have hedge2 : (P1 u N (P1 u N A)).1 ≠ (P1 u N A).1 := by
            intro h
            apply hNP
            apply le_antisymm hNP_le
            refine sup_le le_rfl ?_
            have h1 : latticeMap (scalarGL u) A.1 ≤
                N.1 ⊔ latticeMap (scalarGL u) (latticeMap (scalarGL u) A.1) := by
              have h0 : latticeMap (scalarGL u) A.1 ≤ (P1 u N (P1 u N A)).1 := by
                rw [h]
                exact le_sup_right
              refine h0.trans ?_
              rw [P1_val, P1_val, sc_sup]
              exact sup_le le_sup_left (sup_le ((sc_le u hu _).trans le_sup_left) le_sup_right)
            refine (absorb u hu N.1 _ h1 k).trans (sup_le le_rfl ?_)
            rw [sc_pow_one u A.1, sc_pow_one u (latticeMap (scalarGL (u ^ 1)) A.1), sc_pow_pow,
              sc_pow_pow]
            rw [show k + (1 + 1) = 1 + (k + 1) by omega]
            exact pow_le_of_pow_le u hu hkA 1
          have hWP₂ : W (P1 u N (P1 u N A)) = latticeMap (scalarGL u) (P1 u N A).1 := by
            rcases mono_lemma (P1 u N A) (P1 u N (P1 u N A)) le_sup_right
                (sup_le hNP_le (sc_le u hu _)) hedge1 hedge2 with h | h
            · exact h
            · exfalso
              apply hNA_not
              rw [hWP] at h
              rw [h]
              exact le_sup_left
          have hih := ih (P1 u N A) hNP_le hN_not_P hkP hNP hWP₂
          have hN'eq : N' = FullLattice.act (scalarGL u) (P1 u N A) := Subtype.ext hih
          have hWN' : W N' = latticeMap (scalarGL u) (latticeMap (scalarGL u) A.1) := by
            rw [hN'eq, hW_hom, hWP]
          apply hNP
          apply le_antisymm hNP_le (sup_le le_rfl ?_)
          apply le_of_latticeMap_le (scalarGL u)
          rw [← hWN']
          exact hN₄
    have hMne : M'.1 ≠ M.1 ∧ latticeMap (scalarGL u) M.1 ≠ M'.1 := strict M' M hM₃ hM₄
    have hWM : W M = M'.1 := two_step M (W M) M'.1 (hπW M) hM₃ hM₂ (hW_ex M) hMne.1
    have hP1_ne1 : latticeMap (scalarGL u) M.1 ≠ (P1 u N M).1 := by
      intro h
      apply hN_not
      rw [h]
      exact le_sup_left
    have hP1_ne2 : (P1 u N M).1 ≠ M.1 := by
      intro h
      apply hNM'
      apply le_antisymm hNM
      have h1 : M.1 ≤ N.1 ⊔ latticeMap (scalarGL u) M.1 := by
        rw [← P1_val, h]
      refine (absorb u hu N.1 M.1 h1 k).trans (sup_le le_rfl ?_)
      rw [sc_pow_one u M.1, sc_pow_pow]
      rw [show k + 1 = 1 + k by omega]
      exact pow_le_of_pow_le u hu hkM 1
    have hWP1 : W (P1 u N M) = latticeMap (scalarGL u) M.1 := by
      rcases mono_lemma M (P1 u N M) le_sup_right (sup_le hNM (sc_le u hu _)) hP1_ne1
          hP1_ne2 with h | h
      · exact h
      · have hM'P : M' = P1 u N M := Subtype.ext (hWM ▸ h)
        refine two_step (P1 u N M) _ _ (hπW _) ?_ le_sup_right (hW_ex _) hP1_ne1
        rw [← hM'P]
        exact hM₄
    exact walk k M hNM hN_not hkM hNM' hWP1
  obtain ⟨c, hLcM, hLc_not⟩ := exists_sc_le_not_le hπ L.2 M.2
  have hLcM : (FullLattice.act (scalarGL c) L).1 ≤ M.1 := hLcM
  have hLc_not : ¬ (FullLattice.act (scalarGL c) L).1 ≤ latticeMap (scalarGL u) M.1 := hLc_not
  have hL₁' : latticeMap (scalarGL u) (FullLattice.act (scalarGL c) L).1 ≤
      (FullLattice.act (scalarGL c) L').1 := by
    change latticeMap (scalarGL u) (latticeMap (scalarGL c) L.1) ≤ latticeMap (scalarGL c) L'.1
    rw [sc_comm]
    exact latticeMap_mono _ hL₁
  have hL₂' : (FullLattice.act (scalarGL c) L').1 ≤ (FullLattice.act (scalarGL c) L).1 :=
    latticeMap_mono _ hL₂
  have hL₃' : W (FullLattice.act (scalarGL c) L) ≤ (FullLattice.act (scalarGL c) L').1 := by
    rw [hW_hom]
    exact latticeMap_mono _ hL₃
  have hL₄' : W (FullLattice.act (scalarGL c) L') ≤
      latticeMap (scalarGL u) (FullLattice.act (scalarGL c) L).1 := by
    rw [hW_hom]
    change latticeMap (scalarGL c) (W L') ≤ latticeMap (scalarGL u) (latticeMap (scalarGL c) L.1)
    rw [sc_comm u c]
    exact latticeMap_mono _ hL₄
  rcases core _ _ hLcM hLc_not hL₁' hL₂' hL₃' hL₄' with h | h
  · refine ⟨c⁻¹, M, L, Or.inr rfl, Or.inr rfl, ?_⟩
    change latticeMap (scalarGL c) L.1 = M.1 at h
    rw [← h, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]
  · refine ⟨c⁻¹ * u, M, L', Or.inr rfl, Or.inl rfl, ?_⟩
    change latticeMap (scalarGL c) L'.1 = latticeMap (scalarGL u) M.1 at h
    rw [scalarGL_mul, latticeMap_mul, ← h, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel,
      scalarGL_one, latticeMap_one]

end CerednikDrinfeld.FormalOmega.EdgeNondegUnique

open CerednikDrinfeld.FormalOmega.EdgeNondegUnique

namespace CerednikDrinfeld.FormalOmega.DeligneDatum

/-- If a Deligne datum is vertex nondegenerate at `M` and edge nondegenerate at `A₀ ⊆ A₁` at a
prime containing `π`, then a homothety carries `M` onto `A₀` or onto `A₁`. -/
theorem exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    (M A₀ A₁ : FullLattice 𝒪 K) (hM : d.VertexNondegAt π 𝔭 M) (hA : d.EdgeNondegAt π 𝔭 A₀ A₁) :
    ∃ c : Kˣ, latticeMap (scalarGL c) M.1 = A₀.1 ∨ latticeMap (scalarGL c) M.1 = A₁.1 := by
  obtain ⟨c, hcA, hcπA⟩ := exists_sc_le_not_le (K := K) hπ M.2 A₁.2
  refine ⟨c, ?_⟩
  set L₁ : FullLattice 𝒪 K := FullLattice.act (scalarGL c) M with hL₁
  change L₁.1 = A₀.1 ∨ L₁.1 = A₁.1
  let B' := Localization.AtPrime 𝔭
  let f : B →ₐ[𝒪] B' := IsScalarTower.toAlgHom 𝒪 B B'
  have hcomap : ∀ 𝔮 : Ideal B', 𝔮.IsPrime → Ideal.comap f 𝔮 ≤ 𝔭 := by
    intro 𝔮 h𝔮 s hs
    by_contra hsx
    apply h𝔮.ne_top
    apply Ideal.eq_top_of_isUnit_mem 𝔮 (Ideal.mem_comap.mp hs)
    exact IsLocalization.map_units B' (⟨s, hsx⟩ : 𝔭.primeCompl)
  have h𝔭' : algebraMap 𝒪 B' π ∈ IsLocalRing.maximalIdeal B' := by
    rw [IsScalarTower.algebraMap_apply 𝒪 B B']
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff B' 𝔭 _).mpr h𝔭
  have hL' : (d.map π f).VertexNondegAt π (IsLocalRing.maximalIdeal B') L₁ :=
    vertexNondegAt_map π f d L₁ (vertexNondegAt_act π d 𝔭 c M hM) _ inferInstance
      (hcomap _ inferInstance)
  have hA' : ∀ 𝔪 : Ideal B', 𝔪.IsMaximal → (d.map π f).EdgeNondegAt π 𝔪 A₀ A₁ := fun 𝔪 h𝔪 =>
    edgeNondegAt_map π f d A₀ A₁ hA 𝔪 h𝔪.isPrime (hcomap 𝔪 h𝔪.isPrime)
  obtain ⟨hA₀₁, hπA, -, -⟩ := hA
  by_cases hcase : L₁.1 ≤ A₀.1
  · left
    obtain ⟨u, huL, huπ⟩ := Set.not_subset.mp hcπA
    refine eq_of_vertexNondegAt_of_generator hπ (d.map π f) (IsLocalRing.maximalIdeal B') h𝔭'
      hcase ⟨u, huL⟩ (fun 𝔪 h𝔪 => ?_) hL'
    obtain ⟨-, -, -, h2⟩ := hA' 𝔪 h𝔪
    apply h2 ⟨u, hcase huL⟩
    rintro ⟨w, hw⟩
    apply huπ
    exact mem_latticeMap_scalarGL.mpr ⟨w, w.2, by rw [piU_coe]; exact hw.symm⟩
  · right
    obtain ⟨u, huL, huA⟩ := Set.not_subset.mp hcase
    refine eq_of_vertexNondegAt_of_generator hπ (d.map π f) (IsLocalRing.maximalIdeal B') h𝔭'
      hcA ⟨u, huL⟩ (fun 𝔪 h𝔪 => ?_) hL'
    obtain ⟨-, -, h1, -⟩ := hA' 𝔪 h𝔪
    exact h1 ⟨u, hcA huL⟩ huA

/-- If a Deligne datum is edge nondegenerate at `M' ⊆ M` and at `L' ⊆ L` at a prime containing
`π`, then a homothety carries one of `M'`, `M` onto one of `L'`, `L`. -/
theorem exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    (M' M L' L : FullLattice 𝒪 K) (hM : d.EdgeNondegAt π 𝔭 M' M) (hL : d.EdgeNondegAt π 𝔭 L' L) :
    ∃ (c : Kˣ) (X Y : FullLattice 𝒪 K), (X = M' ∨ X = M) ∧ (Y = L' ∨ Y = L) ∧
      latticeMap (scalarGL c) X.1 = Y.1 := by
  classical
  by_cases hVex : ∃ P : FullLattice 𝒪 K, d.VertexNondegAt π 𝔭 P
  · obtain ⟨P, hP⟩ := hVex
    obtain ⟨c, hc⟩ :=
      exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt hπ d 𝔭 h𝔭 P M' M hP hM
    obtain ⟨c', hc'⟩ :=
      exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt hπ d 𝔭 h𝔭 P L' L hP hL
    refine ⟨c' * c⁻¹, ?_⟩
    rcases hc with hX | hX <;> rcases hc' with hY | hY
    · exact ⟨M', L', Or.inl rfl, Or.inl rfl, latticeMap_scalarGL_of_eq_of_eq hX hY⟩
    · exact ⟨M', L, Or.inl rfl, Or.inr rfl, latticeMap_scalarGL_of_eq_of_eq hX hY⟩
    · exact ⟨M, L', Or.inr rfl, Or.inl rfl, latticeMap_scalarGL_of_eq_of_eq hX hY⟩
    · exact ⟨M, L, Or.inr rfl, Or.inr rfl, latticeMap_scalarGL_of_eq_of_eq hX hY⟩
  · push Not at hVex
    obtain ⟨-, hM₂, hM₃, hM₄⟩ := edge_read hπ d 𝔭 M' M hM
    obtain ⟨hL₁, hL₂, hL₃, hL₄⟩ := edge_read hπ d 𝔭 L' L hL
    exact lattice_walk hπ (W d 𝔭) (W_le d 𝔭) (W_ne d 𝔭) (pi_smul_mem_W d 𝔭 h𝔭)
      (fun A => not_W_le_of_not_vertexNondegAt hπ d 𝔭 A (hVex A)) (W_mono d 𝔭)
      (W_act_scalarGL d 𝔭) M' M L' L hM₂ hM₃ hM₄ hL₁ hL₂ hL₃ hL₄

end CerednikDrinfeld.FormalOmega.DeligneDatum

end
