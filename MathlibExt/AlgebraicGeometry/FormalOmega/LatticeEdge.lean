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
`Definitions/Def_LatticeTreeOrbital.lean`,
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice`
`CF_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt`
`CF_exists_fullLattice_lt_and_lt`
`LT_LatticeTree_FullLattice_eq_of_forall_smul_mem_of_le_of_le`
`CF_latticeMap_scalarGL_eq_self_of_hasDetIndex`
`CF_HasDetIndex_even_sub_of_latticeMap_scalarGL`
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
import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeOrbital
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.Lattice.Full
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace LT.LatticeTree

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

private theorem mulVec_tri (a b d : K) (w : Fin 2 → K) :
    (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) K) *ᵥ w = ![a * w 0 + b * w 1, d * w 1] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem exists_scalarGL_le_stdLattice (L : Submodule R (Fin 2 → K))
    (hL : Submodule.IsFullLattice K L) :
    ∃ d : R, ∃ hd : d ≠ 0,
      latticeMap (scalarGL (unitOfNeZero (K := K) hd)) L ≤ stdLattice R K := by
  classical
  obtain ⟨S, hS⟩ := Submodule.IsLattice.fg K L
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (S ×ˢ (Finset.univ : Finset (Fin 2))) (fun p : (Fin 2 → K) × Fin 2 => p.1 p.2)
  have hb0 : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  refine ⟨b, hb0, ?_⟩
  rw [← hS]
  unfold latticeMap
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  intro i
  have := hb (v, i) (Finset.mem_product.mpr ⟨hv, Finset.mem_univ i⟩)
  rw [Algebra.smul_def] at this
  change IsLocalization.IsInteger R
    ((mulVecLinR (R := R) (scalarGL (unitOfNeZero (K := K) hb0)) v) i)
  rw [mulVecLinR_apply, scalarGL_mulVec, Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]
  exact this

private theorem exists_eq_latticeMap_of_le_stdLattice (ϖ : R) (hϖ : Irreducible ϖ)
    (L : Submodule R (Fin 2 → K)) (hL : Submodule.IsFullLattice K L) (hle : L ≤ stdLattice R K) :
    ∃ (a b : ℕ) (β' : K) (g' : Matrix.GeneralLinearGroup (Fin 2) K),
      (g' : Matrix (Fin 2) (Fin 2) K) =
        !![algebraMap R K ϖ ^ a, β'; 0, algebraMap R K ϖ ^ b] ∧
      L = latticeMap g' (stdLattice R K) := by
  classical
  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))
  let I₁ : Ideal R :=
    { carrier := {r | ∃ v ∈ L, v 1 = algebraMap R K r}
      add_mem' := by
        rintro r s ⟨v, hv, hvr⟩ ⟨w, hw, hws⟩
        exact ⟨v + w, L.add_mem hv hw, by simp [hvr, hws]⟩
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro c r ⟨v, hv, hvr⟩
        exact ⟨c • v, L.smul_mem c hv, by simp [hvr, Algebra.smul_def]⟩ }
  let e : R → (Fin 2 → K) := fun r => ![algebraMap R K r, 0]
  have e_add : ∀ r s, e (r + s) = e r + e s := fun r s => by
    ext i; fin_cases i <;> simp [e]
  have e_smul : ∀ c r, e (c * r) = c • e r := fun c r => by
    ext i; fin_cases i <;> simp [e, Algebra.smul_def]
  have e_zero : e 0 = 0 := by ext i; fin_cases i <;> simp [e]
  let I₀ : Ideal R :=
    { carrier := {r | e r ∈ L}
      add_mem' := fun {r s} hr hs => by
        change e (r + s) ∈ L; rw [e_add]; exact L.add_mem hr hs
      zero_mem' := by change e 0 ∈ L; rw [e_zero]; exact L.zero_mem
      smul_mem' := fun c {r} hr => by
        change e (c * r) ∈ L; rw [e_smul]; exact L.smul_mem c hr }
  have hI₁ : I₁ ≠ ⊥ := by
    intro h
    have hzero : ∀ v ∈ L, v 1 = 0 := by
      intro v hv
      obtain ⟨r, hr⟩ := hle hv 1
      have : r ∈ I₁ := ⟨v, hv, hr.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [← hr, this, map_zero]
    have hsub : Submodule.span K (L : Set (Fin 2 → K)) ≤
        LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin 2 => K) 1) := by
      rw [Submodule.span_le]; intro v hv; exact hzero v hv
    have hmem : (Pi.single (1 : Fin 2) (1 : K) : Fin 2 → K) ∈
        Submodule.span K (L : Set (Fin 2 → K)) := by
      rw [hL.2]; exact Submodule.mem_top
    have := hsub hmem
    simp at this
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI₁ hϖ
  have hwb : ϖ ^ b ∈ I₁ := by rw [hb]; exact Ideal.mem_span_singleton_self _
  obtain ⟨w, hwL, hw1⟩ := hwb
  have hcoord1 : ∀ v ∈ L, ∃ s : R, v 1 = algebraMap R K (ϖ ^ b * s) := by
    intro v hv
    obtain ⟨r, hr⟩ := hle hv 1
    have : r ∈ I₁ := ⟨v, hv, hr.symm⟩
    rw [hb, Ideal.mem_span_singleton] at this
    obtain ⟨s, rfl⟩ := this
    exact ⟨s, hr.symm⟩
  have hdecomp : ∀ v ∈ L, ∃ s t : R,
      v 1 = algebraMap R K (ϖ ^ b * s) ∧ t ∈ I₀ ∧ v = s • w + e t := by
    intro v hv
    obtain ⟨s, hs⟩ := hcoord1 v hv
    have hu : v - s • w ∈ L := L.sub_mem hv (L.smul_mem s hwL)
    obtain ⟨t, ht⟩ := hle hu 0
    have hu1 : (v - s • w) 1 = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [Algebra.smul_def, hs, hw1, map_mul, map_pow]; ring
    have ht0 : e t = v - s • w := by
      ext i; fin_cases i
      · simpa [e] using ht
      · simpa [e] using hu1.symm
    refine ⟨s, t, hs, ?_, ?_⟩
    · change e t ∈ L; rw [ht0]; exact hu
    · rw [ht0]; abel
  have hI₀ : I₀ ≠ ⊥ := by
    intro h
    have hline : ∀ v ∈ L, ∃ s : R, v = s • w := by
      intro v hv
      obtain ⟨s, t, -, ht, hv'⟩ := hdecomp v hv
      rw [h, Ideal.mem_bot] at ht
      refine ⟨s, ?_⟩
      rw [hv', ht, e_zero, add_zero]
    have hsub : Submodule.span K (L : Set (Fin 2 → K)) ≤ Submodule.span K {w} := by
      rw [Submodule.span_le]
      intro v hv
      obtain ⟨s, rfl⟩ := hline v hv
      rw [← algebraMap_smul K s w]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    have hw10 : w 1 ≠ 0 := by rw [hw1, map_pow]; exact pow_ne_zero _ hϖ0
    have hmem : (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) ∈ Submodule.span K {w} := by
      apply hsub; rw [hL.2]; exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrFun hk 1
    have h0 := congrFun hk 0
    simp only [Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), Pi.single_eq_same] at h1 h0
    rcases mul_eq_zero.mp h1 with hk0 | hw0
    · rw [hk0, zero_mul] at h0; exact zero_ne_one h0
    · exact hw10 hw0
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI₀ hϖ
  have hea : e (ϖ ^ a) ∈ L := by
    change ϖ ^ a ∈ I₀; rw [ha]; exact Ideal.mem_span_singleton_self _
  let A : Matrix (Fin 2) (Fin 2) K := !![algebraMap R K ϖ ^ a, w 0; 0, algebraMap R K ϖ ^ b]
  have hdet : A.det ≠ 0 := by
    simp only [A, Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_ne_zero (pow_ne_zero _ hϖ0) (pow_ne_zero _ hϖ0)
  refine ⟨a, b, w 0, Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, rfl, ?_⟩
  have hAv : ∀ u : Fin 2 → K, A *ᵥ u =
      ![algebraMap R K ϖ ^ a * u 0 + w 0 * u 1, algebraMap R K ϖ ^ b * u 1] :=
    fun u => mulVec_tri _ _ _ u
  have hw_eq : w = ![w 0, algebraMap R K (ϖ ^ b)] := by
    ext i; fin_cases i <;> simp [hw1]
  ext v
  rw [mem_latticeMap]
  constructor
  · intro hv
    obtain ⟨s, t, hs, ht, hv'⟩ := hdecomp v hv
    rw [ha, Ideal.mem_span_singleton] at ht
    obtain ⟨r, rfl⟩ := ht
    refine ⟨![algebraMap R K r, algebraMap R K s], ?_, ?_⟩
    · intro i; fin_cases i; exacts [⟨r, rfl⟩, ⟨s, rfl⟩]
    · change A *ᵥ _ = v
      rw [hAv, hv', hw_eq]
      ext i; fin_cases i <;> simp [e, Algebra.smul_def, map_mul, map_pow] <;> ring
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨r, hr⟩ := hu 0
    obtain ⟨s, hs⟩ := hu 1
    change A *ᵥ u ∈ L
    rw [hAv]
    have : (![algebraMap R K ϖ ^ a * u 0 + w 0 * u 1, algebraMap R K ϖ ^ b * u 1] :
        Fin 2 → K) = s • w + r • e (ϖ ^ a) := by
      rw [hw_eq]
      ext i; fin_cases i <;> simp [e, Algebra.smul_def, ← hr, ← hs, map_pow] <;> ring
    rw [this]
    exact L.add_mem (L.smul_mem s hwL) (L.smul_mem r hea)

end LT.LatticeTree

/-- Every full lattice in `K²` is the image of the standard lattice under a scalar matrix times
an upper-triangular matrix `!![ϖ ^ n, β; 0, 1]`. -/
theorem LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (L : Submodule R (Fin 2 → K)) (hL : Submodule.IsFullLattice K L) :
    ∃ (c : Kˣ) (n : ℤ) (β : K) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ ^ n, β; 0, 1] ∧
      L = latticeMap (scalarGL c * g) (stdLattice R K) := by
  obtain ⟨d, hd, hle⟩ := exists_scalarGL_le_stdLattice (K := K) L hL
  have hL' : Submodule.IsFullLattice K (latticeMap (scalarGL (unitOfNeZero (K := K) hd)) L) :=
    IsFullLattice.map hL _
  obtain ⟨a, b, β', g', hg', hLg'⟩ := exists_eq_latticeMap_of_le_stdLattice ϖ hϖ
    (latticeMap (scalarGL (unitOfNeZero (K := K) hd)) L) hL' hle
  have hL1 : L = latticeMap ((scalarGL (unitOfNeZero (K := K) hd))⁻¹ * g')
      (stdLattice R K) := by
    rw [latticeMap_mul, ← hLg', latticeMap_inv_latticeMap]
  have hϖ0 : algebraMap R K ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))
  set ϖK : K := algebraMap R K ϖ with hϖK
  set c₀ : Kˣ := unitOfNeZero (K := K) hd with hc₀
  let G : Matrix (Fin 2) (Fin 2) K := !![ϖK ^ ((a : ℤ) - b), β' / ϖK ^ b; 0, 1]
  have hG : G.det ≠ 0 := by
    simp only [G, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
    exact zpow_ne_zero _ hϖ0
  refine ⟨c₀⁻¹ * Units.mk0 (ϖK ^ b) (pow_ne_zero _ hϖ0), (a : ℤ) - b, β' / ϖK ^ b,
    Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, rfl, ?_⟩
  rw [hL1]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg', scalarGL_coe]
  change (((c₀⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 2) (Fin 2) K)) *
      !![algebraMap R K ϖ ^ a, β'; 0, algebraMap R K ϖ ^ b] =
    (((c₀⁻¹ * Units.mk0 (ϖK ^ b) (pow_ne_zero _ hϖ0) : Kˣ) : K) •
      (1 : Matrix (Fin 2) (Fin 2) K)) * G
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, Units.val_mul,
    Units.val_mk0, ← hϖK]
  have hpow : ϖK ^ b * ϖK ^ ((a : ℤ) - b) = ϖK ^ a := by
    rw [← zpow_natCast, ← zpow_add₀ hϖ0, ← zpow_natCast]; congr 1; ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [G, mul_assoc, hpow]
  · simp [G, mul_div_cancel₀ _ (pow_ne_zero b hϖ0), mul_assoc]
  · simp [G]
  · simp [G]


namespace LT.LatticeTree

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable [IsFractionRing R K]

private theorem latticeMap_scalarGL_lt_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  refine lt_of_le_of_ne ?_ fun h => ?_
  · intro v hv
    rw [mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at hv
    rw [mem_latticeMap_diagSnd_stdLattice]
    obtain ⟨w0, hw0, hw0'⟩ := hv 0
    obtain ⟨w1, hw1, hw1'⟩ := hv 1
    refine ⟨?_, w1, hw1, by rw [unitOfNeZero_coe]; exact hw1'⟩
    rw [← hw0']
    exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw0
  · have he0 := single_zero_one_mem_latticeMap_diagSnd
      (R := R) (unitOfNeZero (K := K) hϖ.ne_zero)
    rw [← h, mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at he0
    obtain ⟨w, hw, hweq⟩ := he0 0
    rw [Pi.single_eq_same] at hweq
    exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

end LT.LatticeTree

namespace CerednikDrinfeld.FormalOmega

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type}
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
private theorem coords_of_mem_stdLattice {v : Fin 2 → K} (hv : v ∈ stdLattice 𝒪 K) :
    ∃ x y : 𝒪, algebraMap 𝒪 K x = v 0 ∧ algebraMap 𝒪 K y = v 1 := by
  obtain ⟨x, hx⟩ := ((mem_stdLattice 𝒪 K).1 hv) 0
  obtain ⟨y, hy⟩ := ((mem_stdLattice 𝒪 K).1 hv) 1
  exact ⟨x, y, hx, hy⟩

private theorem isUnit_of_not_dvd {π : 𝒪} (hπ : Irreducible π) {a : 𝒪} (h : ¬ π ∣ a) :
    IsUnit a := by
  by_contra hu
  apply h
  have : a ∈ IsLocalRing.maximalIdeal 𝒪 :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ] at this
  exact Ideal.mem_span_singleton.1 this

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
private theorem latticeMap_diag_stdLattice {π : 𝒪} (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) :
    latticeMap g (stdLattice 𝒪 K) = interLattice 𝒪 K π 0 1 := by
  ext v
  rw [mem_latticeMap, mem_interLattice]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := (mem_stdLattice 𝒪 K).1 hw
    have h0 : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 0 = algebraMap 𝒪 K π * w 0 := by
      rw [hg, Matrix.mulVec_diagonal]; simp
    have h1 : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 1 = w 1 := by
      rw [hg, Matrix.mulVec_diagonal]; simp
    refine ⟨?_, w 0, hw' 0, ?_⟩
    · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · rw [h0]; exact IsLocalization.isInteger_mul ⟨π, rfl⟩ (hw' 0)
      · rw [h1]; exact hw' 1
    · rw [h0, h1, map_one, map_zero, one_mul, zero_mul, sub_zero]
  · rintro ⟨hv, w, hw, hvw⟩
    rw [map_one, map_zero, one_mul, zero_mul, sub_zero] at hvw
    refine ⟨![w, v 1], ?_, ?_⟩
    · rw [mem_stdLattice]
      intro i
      fin_cases i
      · simpa using hw
      · simpa using hv 1
    · rw [hg]
      funext i
      rw [Matrix.mulVec_diagonal]
      fin_cases i
      · simp [hvw]
      · simp

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
private theorem latticeMap_map_stdLattice (π : 𝒪) (M : Matrix.GeneralLinearGroup (Fin 2) 𝒪) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M) (stdLattice 𝒪 K) =
      stdLattice 𝒪 K := by
  rw [← interLattice_zero_zero (R := 𝒪) (K := K) π, latticeMap_map_interLattice]
  simp

private theorem exists_eq_interLattice {π : 𝒪} (hπ : Irreducible π)
    {L : Submodule 𝒪 (Fin 2 → K)}
    (h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) < L)
    (h₂ : L < stdLattice 𝒪 K) :
    ∃ a b : 𝒪, (IsUnit a ∨ IsUnit b) ∧ L = interLattice 𝒪 K π a b := by
  obtain ⟨-, v, hvL, hvπ⟩ := IsConcreteLE.lt_iff_le_and_exists.1 h₁
  have hvstd : v ∈ stdLattice 𝒪 K := h₂.le hvL
  obtain ⟨a, b, ha, hb⟩ := coords_of_mem_stdLattice hvstd
  have hunit : IsUnit a ∨ IsUnit b := by
    by_contra hne
    push Not at hne
    obtain ⟨hna, hnb⟩ := hne
    apply hvπ
    rw [mem_latticeMap_scalarGL_stdLattice hπ.ne_zero]
    have hda : π ∣ a := by by_contra h; exact hna (isUnit_of_not_dvd hπ h)
    have hdb : π ∣ b := by by_contra h; exact hnb (isUnit_of_not_dvd hπ h)
    obtain ⟨a', rfl⟩ := hda
    obtain ⟨b', rfl⟩ := hdb
    intro i
    fin_cases i
    · exact ⟨algebraMap 𝒪 K a', ⟨a', rfl⟩, by rw [← map_mul]; exact ha⟩
    · exact ⟨algebraMap 𝒪 K b', ⟨b', rfl⟩, by rw [← map_mul]; exact hb⟩
  refine ⟨a, b, hunit, le_antisymm ?_ ?_⟩
  · intro u hu
    by_contra huI
    have hustd : u ∈ stdLattice 𝒪 K := h₂.le hu
    obtain ⟨x, y, hx, hy⟩ := coords_of_mem_stdLattice hustd
    have hndvd : ¬ π ∣ b * x - a * y := by
      intro hd
      apply huI
      obtain ⟨w, hw, hweq⟩ := (exists_isInteger_eq_algebraMap_mul_iff_dvd (K := K)).2 hd
      refine ⟨(mem_stdLattice 𝒪 K).1 hustd, w, hw, ?_⟩
      rw [← hx, ← hy, ← map_mul, ← map_mul, ← map_sub]
      exact hweq
    obtain ⟨δ, hδ⟩ := isUnit_of_not_dvd hπ hndvd
    have hδinv : (b * x - a * y) * ((δ⁻¹ : 𝒪ˣ) : 𝒪) = 1 := by rw [← hδ, Units.mul_inv]
    have hstd : stdLattice 𝒪 K ≤ L := by
      intro s hs
      obtain ⟨σ₀, σ₁, hσ₀, hσ₁⟩ := coords_of_mem_stdLattice hs
      set lam : 𝒪 := -(σ₀ * y - σ₁ * x) * ((δ⁻¹ : 𝒪ˣ) : 𝒪) with hlam
      set mu : 𝒪 := (b * σ₀ - a * σ₁) * ((δ⁻¹ : 𝒪ˣ) : 𝒪) with hmu
      have hcomb : s = lam • v + mu • u := by
        funext i
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
        fin_cases i
        · change s 0 = algebraMap 𝒪 K lam * v 0 + algebraMap 𝒪 K mu * u 0
          rw [← hσ₀, ← ha, ← hx, ← map_mul, ← map_mul, ← map_add]
          congr 1
          rw [hlam, hmu]
          linear_combination (-σ₀) * hδinv
        · change s 1 = algebraMap 𝒪 K lam * v 1 + algebraMap 𝒪 K mu * u 1
          rw [← hσ₁, ← hb, ← hy, ← map_mul, ← map_mul, ← map_add]
          congr 1
          rw [hlam, hmu]
          linear_combination (-σ₁) * hδinv
      rw [hcomb]
      exact L.add_mem (L.smul_mem lam hvL) (L.smul_mem mu hu)
    exact absurd (le_antisymm h₂.le hstd) h₂.ne
  · rintro u ⟨hu, w, hw, hwu⟩
    obtain ⟨x, y, hx, hy⟩ := coords_of_mem_stdLattice ((mem_stdLattice 𝒪 K).2 hu)
    obtain ⟨ω, rfl⟩ := hw
    rw [← hx, ← hy, ← map_mul, ← map_mul, ← map_sub, ← map_mul] at hwu
    have hwu' : b * x - a * y = π * ω := IsFractionRing.injective 𝒪 K hwu
    have hπL : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) ≤ L :=
      h₁.le
    have key : ∀ t r₀ r₁ : 𝒪, x - t * a = π * r₀ → y - t * b = π * r₁ → u ∈ L := by
      intro t r₀ r₁ h0 h1
      have hr : u - t • v ∈
          latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) := by
        rw [mem_latticeMap_scalarGL_stdLattice hπ.ne_zero]
        intro i
        fin_cases i
        · refine ⟨algebraMap 𝒪 K r₀, ⟨r₀, rfl⟩, ?_⟩
          change algebraMap 𝒪 K π * algebraMap 𝒪 K r₀ = (u - t • v) 0
          rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, ← hx, ← ha, ← map_mul, ← map_mul,
            ← map_sub, ← h0]
        · refine ⟨algebraMap 𝒪 K r₁, ⟨r₁, rfl⟩, ?_⟩
          change algebraMap 𝒪 K π * algebraMap 𝒪 K r₁ = (u - t • v) 1
          rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, ← hy, ← hb, ← map_mul, ← map_mul,
            ← map_sub, ← h1]
      have : u = t • v + (u - t • v) := by abel
      rw [this]
      exact L.add_mem (L.smul_mem t hvL) (hπL hr)
    rcases hunit with ⟨ai, hai⟩ | ⟨bi, hbi⟩
    · have hinv : ((ai⁻¹ : 𝒪ˣ) : 𝒪) * a = 1 := by rw [← hai, Units.inv_mul]
      refine key (x * ((ai⁻¹ : 𝒪ˣ) : 𝒪)) 0 (-(((ai⁻¹ : 𝒪ˣ) : 𝒪) * ω)) ?_ ?_
      · linear_combination (-x) * hinv
      · linear_combination (-(((ai⁻¹ : 𝒪ˣ) : 𝒪))) * hwu' + (-y) * hinv
    · have hinv : ((bi⁻¹ : 𝒪ˣ) : 𝒪) * b = 1 := by rw [← hbi, Units.inv_mul]
      refine key (y * ((bi⁻¹ : 𝒪ˣ) : 𝒪)) (((bi⁻¹ : 𝒪ˣ) : 𝒪) * ω) 0 ?_ ?_
      · linear_combination (((bi⁻¹ : 𝒪ˣ) : 𝒪)) * hwu' + (-x) * hinv
      · linear_combination (-y) * hinv

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem exists_gl_snd_col {a b : 𝒪} (h : IsUnit a ∨ IsUnit b) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) 𝒪,
      (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 = a ∧ (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 = b := by
  rcases h with ha | hb
  · have hdet : IsUnit (!![0, a; -1, b] : Matrix (Fin 2) (Fin 2) 𝒪).det := by
      rw [Matrix.det_fin_two_of]; simpa using ha
    obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
    exact ⟨M, by rw [hM]; rfl, by rw [hM]; rfl⟩
  · have hdet : IsUnit (!![1, a; 0, b] : Matrix (Fin 2) (Fin 2) 𝒪).det := by
      rw [Matrix.det_fin_two_of]; simpa using hb
    obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
    exact ⟨M, by rw [hM]; rfl, by rw [hM]; rfl⟩

end CerednikDrinfeld.FormalOmega

/-- Any edge `π M < M' < M` of the lattice tree is a translate of the standard edge
`diag(π, 1) 𝒪² < 𝒪²`. -/
theorem CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (M' M : FullLattice 𝒪 K)
    (h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1)
    (h₂ : M'.1 < M.1) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
      FullLattice.act h (stdFullLattice K) = M ∧
        FullLattice.act h (FullLattice.act g (stdFullLattice K)) = M' := by
  obtain ⟨c, n, β, g₁, -, hM⟩ :=
    LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice 𝒪 K π hπ M.1 M.2
  set k : Matrix.GeneralLinearGroup (Fin 2) K := scalarGL c * g₁ with hk
  set L : Submodule 𝒪 (Fin 2 → K) := latticeMap k⁻¹ M'.1 with hL
  have hπk : ∀ N : Submodule 𝒪 (Fin 2 → K),
      latticeMap k⁻¹ (latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) N) =
        latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (latticeMap k⁻¹ N) := by
    intro N; rw [← latticeMap_mul, ← scalarGL_mul_comm, latticeMap_mul]
  have hL₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) < L := by
    have := (latticeMap_lt_latticeMap_iff k⁻¹).2 h₁
    rwa [hπk, hM, latticeMap_inv_latticeMap] at this
  have hL₂ : L < stdLattice 𝒪 K := by
    have := (latticeMap_lt_latticeMap_iff k⁻¹).2 h₂
    rwa [hM, latticeMap_inv_latticeMap] at this
  obtain ⟨a, b, hab, hLI⟩ := exists_eq_interLattice hπ hL₁ hL₂
  obtain ⟨M₀, h01, h11⟩ := exists_gl_snd_col hab
  have hM₀I : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀)
      (interLattice 𝒪 K π 0 1) = interLattice 𝒪 K π a b := by
    rw [latticeMap_map_interLattice]
    simp [h01, h11]
  refine ⟨k * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀, Subtype.ext ?_, Subtype.ext ?_⟩
  · change latticeMap (k * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀)
      (stdLattice 𝒪 K) = M.1
    rw [latticeMap_mul, latticeMap_map_stdLattice π, hM]
  · change latticeMap (k * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀)
      (latticeMap g (stdLattice 𝒪 K)) = M'.1
    rw [latticeMap_mul, latticeMap_diag_stdLattice g hg, hM₀I, ← hLI, hL,
      latticeMap_latticeMap_inv]

/-- Every full lattice `M` has a neighbour `M'` with `π M < M' < M`. -/
theorem CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (M : FullLattice 𝒪 K) :
    ∃ M' : FullLattice 𝒪 K,
      latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1 := by
  obtain ⟨c, n, β, g₁, -, hM⟩ :=
    LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice 𝒪 K π hπ M.1 M.2
  refine ⟨⟨latticeMap (scalarGL c * g₁)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K)),
    IsFullLattice.map (IsFullLattice.map (isFullLattice_stdLattice (R := 𝒪) (K := K)) _) _⟩, ?_, ?_⟩
  · change latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 <
      latticeMap (scalarGL c * g₁)
        (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K))
    rw [hM, ← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, latticeMap_lt_latticeMap_iff]
    exact latticeMap_scalarGL_lt_latticeMap_diagSnd hπ
  · change latticeMap (scalarGL c * g₁)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K)) < M.1
    conv_rhs => rw [hM]
    rw [latticeMap_lt_latticeMap_iff]
    exact latticeMap_diagSnd_lt_stdLattice hπ


namespace LT.LatticeTree

private theorem sandwich_repr_add_smul {𝒪 : Type*} [CommRing 𝒪] {M : Type*} [AddCommGroup M]
    [Module 𝒪 M] (b : Module.Basis (Fin 2) 𝒪 M) (a c : 𝒪) (v u : M) (i : Fin 2) :
    b.repr (a • v + c • u) i = a * b.repr v i + c * b.repr u i := by
  simp [map_add, map_smul]

private theorem sandwich_exists_eq_smul_add_smul_of_mem {𝒪 : Type*} [CommRing 𝒪] {M : Type*}
    [AddCommGroup M] [Module 𝒪 M] (π : 𝒪) (hπ : ∀ x : 𝒪, ¬ IsUnit x → π ∣ x)
    (b : Module.Basis (Fin 2) 𝒪 M) (N : Submodule 𝒪 M) (hπN : ∀ m : M, π • m ∈ N)
    (v : M) (hv : v ∈ N) (hvπ : ∀ m : M, v ≠ π • m) (u : M) (hu : u ∉ N) :
    ∀ w ∈ N, ∃ (a : 𝒪) (m : M), w = a • v + π • m := by
  classical
  have hdecomp : ∀ x : M, x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    rw [Fin.sum_univ_two]
  have hmkπ : ∀ x : M, π ∣ b.repr x 0 → π ∣ b.repr x 1 → ∃ m : M, x = π • m := by
    rintro x ⟨y₀, hy₀⟩ ⟨y₁, hy₁⟩
    refine ⟨y₀ • b 0 + y₁ • b 1, ?_⟩
    rw [hdecomp x, hy₀, hy₁, smul_add, smul_smul, smul_smul]
  have hmemN : ∀ (a : 𝒪) (m : M), a • v + π • m ∈ N := fun a m =>
    N.add_mem (N.smul_mem a hv) (hπN m)
  have hvunit : IsUnit (b.repr v 0) ∨ IsUnit (b.repr v 1) := by
    by_contra h
    obtain ⟨m, hm⟩ :=
      hmkπ v (hπ _ fun h0 => h (Or.inl h0)) (hπ _ fun h1 => h (Or.inr h1))
    exact hvπ m hm
  have hD : IsUnit (b.repr v 0 * b.repr u 1 - b.repr v 1 * b.repr u 0) := by
    by_contra hDn
    obtain ⟨D', hD'⟩ := hπ _ hDn
    apply hu
    rcases hvunit with h0 | h1
    · obtain ⟨vi, hvi⟩ := h0.exists_right_inv
      obtain ⟨m, hm⟩ : ∃ m : M, u - (b.repr u 0 * vi) • v = π • m := by
        apply hmkπ
        · refine ⟨0, ?_⟩
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          linear_combination (-(b.repr u 0)) * hvi
        · refine ⟨vi * D', ?_⟩
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          linear_combination (-(b.repr u 1)) * hvi + vi * hD'
      have : u = (b.repr u 0 * vi) • v + π • m := by rw [← hm]; abel
      rw [this]; exact hmemN _ _
    · obtain ⟨vi, hvi⟩ := h1.exists_right_inv
      obtain ⟨m, hm⟩ : ∃ m : M, u - (b.repr u 1 * vi) • v = π • m := by
        apply hmkπ
        · refine ⟨-(vi * D'), ?_⟩
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          linear_combination (-(b.repr u 0)) * hvi + (-vi) * hD'
        · refine ⟨0, ?_⟩
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          linear_combination (-(b.repr u 1)) * hvi
      have : u = (b.repr u 1 * vi) • v + π • m := by rw [← hm]; abel
      rw [this]; exact hmemN _ _
  obtain ⟨Di, hDi⟩ := hD.exists_right_inv
  intro w hw
  have hw' : w = (Di * (b.repr w 0 * b.repr u 1 - b.repr w 1 * b.repr u 0)) • v +
      (Di * (b.repr v 0 * b.repr w 1 - b.repr v 1 * b.repr w 0)) • u := by
    refine b.ext_elem_iff.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [sandwich_repr_add_smul]
      linear_combination (-(b.repr w 0)) * hDi
    · rw [sandwich_repr_add_smul]
      linear_combination (-(b.repr w 1)) * hDi
  obtain ⟨a, c, rfl⟩ : ∃ a c : 𝒪, w = a • v + c • u := ⟨_, _, hw'⟩
  have hcu : c • u ∈ N := by
    have := N.sub_mem hw (N.smul_mem a hv)
    rwa [add_sub_cancel_left] at this
  have hc : ¬ IsUnit c := by
    intro hcU
    obtain ⟨ci, hci⟩ := hcU.exists_left_inv
    apply hu
    have := N.smul_mem ci hcu
    rwa [smul_smul, hci, one_smul] at this
  obtain ⟨c', hc'⟩ := hπ c hc
  exact ⟨a, c' • u, by rw [hc', ← smul_smul]⟩

end LT.LatticeTree

/-- If `π M ≤ R₁ ≤ R₂ ≤ M` with `R₁ ≠ π M` and `R₂ ≠ M`, then `R₁ = R₂`: the lattices strictly
between `π M` and `M` form an antichain. -/
theorem LT.LatticeTree.FullLattice.eq_of_forall_smul_mem_of_le_of_le
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (M : FullLattice 𝒪 K) (R₁ R₂ : Submodule 𝒪 (Fin 2 → K))
    (hπM : ∀ v ∈ M.1, (algebraMap 𝒪 K π) • v ∈ R₁) (h₁₂ : R₁ ≤ R₂) (h₂M : R₂ ≤ M.1)
    (hne₁ : ∃ v ∈ R₁, ∀ w ∈ M.1, v ≠ (algebraMap 𝒪 K π) • w) (hne₂ : R₂ ≠ M.1) :
    R₁ = R₂ := by
  classical
  have hLat : Submodule.IsFullLattice K M.1 := M.2
  have := Submodule.IsLattice.free K M.1
  have := Submodule.IsLattice.finite K M.1
  have hrank : Module.finrank 𝒪 ↥M.1 = 2 :=
    (Submodule.IsFullLattice.finrank_eq K M.1).trans (Module.finrank_fin_fun K)
  let b : Module.Basis (Fin 2) 𝒪 ↥M.1 := Module.finBasisOfFinrankEq 𝒪 ↥M.1 hrank
  have hπdvd : ∀ x : 𝒪, ¬ IsUnit x → π ∣ x := fun x hx => by
    have hmem : x ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal x).mpr hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.mem_span_singleton] at hmem
    exact hmem
  obtain ⟨v, hvR₁, hvπ⟩ := hne₁
  obtain ⟨u, huM, huR₂⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne h₂M hne₂)
  have hvM : v ∈ M.1 := h₂M (h₁₂ hvR₁)
  have hπsmul : ∀ m : ↥M.1,
      ((π • m : ↥M.1) : Fin 2 → K) = (algebraMap 𝒪 K π) • (m : Fin 2 → K) := fun m => by
    rw [Submodule.coe_smul, algebraMap_smul]
  have key := sandwich_exists_eq_smul_add_smul_of_mem π hπdvd b (R₂.comap M.1.subtype)
    (fun m => by
      change ((π • m : ↥M.1) : Fin 2 → K) ∈ R₂
      rw [hπsmul]; exact h₁₂ (hπM _ m.2))
    ⟨v, hvM⟩ (show v ∈ R₂ from h₁₂ hvR₁)
    (fun m hm => hvπ m m.2 (by rw [← hπsmul, ← hm]))
    ⟨u, huM⟩ (show u ∉ R₂ from huR₂)
  refine le_antisymm h₁₂ (fun w hw => ?_)
  obtain ⟨a, m, hm⟩ := key ⟨w, h₂M hw⟩ (show w ∈ R₂ from hw)
  have hw' : w = a • v + (algebraMap 𝒪 K π) • (m : Fin 2 → K) := by
    have := congrArg Subtype.val hm
    rw [Submodule.coe_add, Submodule.coe_smul, hπsmul] at this
    exact this
  rw [hw']
  exact R₁.add_mem (R₁.smul_mem a hvR₁) (hπM _ m.2)

namespace CerednikDrinfeld.FormalOmega

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

private theorem latticeMap_scalarGL_stdLattice_of_isUnit (a : 𝒪) (ha : IsUnit a) (c : Kˣ)
    (hc : algebraMap 𝒪 K a = (c : K)) :
    latticeMap (scalarGL c) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
  obtain ⟨b, hab⟩ := ha.exists_right_inv
  have hcinv : ((c⁻¹ : Kˣ) : K) = algebraMap 𝒪 K b := by
    have h1 : (c : K) * algebraMap 𝒪 K b = 1 := by
      rw [← hc, ← map_mul, hab, map_one]
    calc ((c⁻¹ : Kˣ) : K) = ((c⁻¹ : Kˣ) : K) * ((c : K) * algebraMap 𝒪 K b) := by
          rw [h1, mul_one]
      _ = algebraMap 𝒪 K b := by rw [← mul_assoc, Units.inv_mul, one_mul]
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [mem_stdLattice] at hw ⊢
    intro i
    rw [Pi.smul_apply, smul_eq_mul, ← hc]
    obtain ⟨y, hy⟩ := hw i
    exact ⟨a * y, by rw [map_mul, hy]⟩
  · intro v hv
    rw [mem_stdLattice] at hv
    refine mem_latticeMap_scalarGL.mpr ⟨((c⁻¹ : Kˣ) : K) • v, ?_, ?_⟩
    · rw [mem_stdLattice]
      intro i
      rw [Pi.smul_apply, smul_eq_mul, hcinv]
      obtain ⟨y, hy⟩ := hv i
      exact ⟨b * y, by rw [map_mul, hy]⟩
    · rw [smul_smul, Units.mul_inv, one_smul]

omit [CommRing 𝒪] [Algebra 𝒪 K] in
private theorem val_det_scalarGL (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.det (scalarGL c) : Kˣ) : K) = (c : K) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K]

private theorem exists_unit_mul_zpow_of_ne_zero {π : 𝒪} (hπ : Irreducible π) {x : K}
    (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : 𝒪ˣ), x = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨i, ua, hua⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hπ
  obtain ⟨j, ub, hub⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ
  refine ⟨(i : ℤ) - j, ua⁻¹ * ub, ?_⟩
  have ha : algebraMap 𝒪 K a = algebraMap 𝒪 K π ^ i * algebraMap 𝒪 K (ua⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hua, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hb' : algebraMap 𝒪 K b = algebraMap 𝒪 K π ^ j * algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) := by
    rw [← map_pow, ← hub, map_mul, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hBi : algebraMap 𝒪 K (ub⁻¹ : 𝒪ˣ) = (algebraMap 𝒪 K (ub : 𝒪ˣ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [ha, hb', hBi, zpow_sub₀ hπK, zpow_natCast, zpow_natCast, Units.val_mul, map_mul]
  field_simp

private theorem zpow_eq_algebraMap_unit {π : 𝒪} (hπ : Irreducible π) (m : ℤ) (u : 𝒪ˣ)
    (h : algebraMap 𝒪 K π ^ m = algebraMap 𝒪 K u) : m = 0 := by
  have hinj := IsFractionRing.injective 𝒪 K
  have key : ∀ n : ℕ, IsUnit (π ^ n) → n = 0 := fun n hn => by
    by_contra h0
    exact hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π h0) hn)
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, ← map_pow] at h
    have := key n (hinj h ▸ u.isUnit)
    simp [this]
  · have hu0 : algebraMap 𝒪 K u ≠ 0 := fun h0 => u.ne_zero (hinj (by rw [h0, map_zero]))
    rw [zpow_neg, zpow_natCast, ← map_pow, inv_eq_iff_eq_inv] at h
    have h1 : algebraMap 𝒪 K (π ^ n * u) = algebraMap 𝒪 K 1 := by
      rw [map_mul, h, inv_mul_cancel₀ hu0, map_one]
    have := key n (IsUnit.of_mul_eq_one _ (hinj h1))
    simp [this]

private theorem zpow_exp_unique {π : 𝒪} (hπ : Irreducible π) (a b : ℤ) (w₁ w₂ : 𝒪ˣ)
    (h : algebraMap 𝒪 K w₁ * algebraMap 𝒪 K π ^ a =
      algebraMap 𝒪 K w₂ * algebraMap 𝒪 K π ^ b) : a = b := by
  have hinj := IsFractionRing.injective 𝒪 K
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h0 => hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have hw1 : algebraMap 𝒪 K w₁ ≠ 0 := fun h0 => w₁.ne_zero (hinj (by rw [h0, map_zero]))
  have key : algebraMap 𝒪 K π ^ (a - b) = algebraMap 𝒪 K ((w₂ * w₁⁻¹ : 𝒪ˣ)) := by
    rw [zpow_sub₀ hπK, div_eq_iff (zpow_ne_zero _ hπK), Units.val_mul, map_mul, map_units_inv,
      mul_assoc, mul_comm ((algebraMap 𝒪 K ↑w₁)⁻¹), ← mul_assoc, ← h]
    field_simp
  have := zpow_eq_algebraMap_unit hπ _ _ key
  omega

end CerednikDrinfeld.FormalOmega

/-- A homothety that preserves a lattice's determinant index fixes the lattice. -/
theorem CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e) :
    latticeMap (scalarGL c) N = N := by
  obtain ⟨g, hg, u, hu⟩ := h
  obtain ⟨g', hg', u', hu'⟩ := h'
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h0 => hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have hfix : latticeMap (g'⁻¹ * (scalarGL c * g)) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, latticeMap_mul, hg, ← hg', latticeMap_inv_latticeMap]
  obtain ⟨k, hk⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix
  have hdet : algebraMap 𝒪 K ((Matrix.GeneralLinearGroup.det k : 𝒪ˣ) : 𝒪) *
      ((Matrix.GeneralLinearGroup.det g' : Kˣ) : K) =
      (c : K) ^ 2 * ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) := by
    have h1 : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) k) =
        Matrix.GeneralLinearGroup.det (g'⁻¹ * (scalarGL c * g)) := by rw [hk]
    rw [Matrix.GeneralLinearGroup.map_det, map_mul, map_mul, map_inv] at h1
    have h2 := congrArg
      (fun x : Kˣ => ((Matrix.GeneralLinearGroup.det g' * x : Kˣ) : K)) h1
    rw [← mul_assoc, mul_inv_cancel, one_mul, Units.val_mul, Units.val_mul, Units.coe_map,
      val_det_scalarGL] at h2
    rw [mul_comm]
    exact h2
  set w : 𝒪ˣ := Matrix.GeneralLinearGroup.det k * u' * u⁻¹ with hw
  have hc2 : (c : K) ^ 2 = algebraMap 𝒪 K ((w : 𝒪ˣ) : 𝒪) := by
    have hπe : (algebraMap 𝒪 K π) ^ e ≠ 0 := zpow_ne_zero e hπK
    rw [hu', hu] at hdet
    have huK : algebraMap 𝒪 K ((u : 𝒪ˣ) : 𝒪) ≠ 0 := by
      intro h0; exact (u.isUnit.map (algebraMap 𝒪 K)).ne_zero h0
    have key : (c : K) ^ 2 * algebraMap 𝒪 K ((u : 𝒪ˣ) : 𝒪) =
        algebraMap 𝒪 K ((Matrix.GeneralLinearGroup.det k : 𝒪ˣ) : 𝒪) *
          algebraMap 𝒪 K ((u' : 𝒪ˣ) : 𝒪) := by
      apply mul_right_cancel₀ hπe
      rw [mul_assoc, mul_assoc]; exact hdet.symm
    have hwval : ((w : 𝒪ˣ) : 𝒪) * ((u : 𝒪ˣ) : 𝒪) =
        ((Matrix.GeneralLinearGroup.det k : 𝒪ˣ) : 𝒪) * ((u' : 𝒪ˣ) : 𝒪) := by
      rw [hw, Units.val_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    apply mul_right_cancel₀ huK
    rw [key, ← map_mul, ← map_mul, hwval]
  obtain ⟨a, ha⟩ : ∃ a : 𝒪, algebraMap 𝒪 K a = (c : K) := by
    refine IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (n := 2) (by norm_num) ?_
    rw [hc2]; exact isIntegral_algebraMap
  have haunit : IsUnit a := by
    have h2 : a * a = ((w : 𝒪ˣ) : 𝒪) := hinj (by rw [map_mul, ha, ← sq, hc2])
    exact isUnit_of_mul_isUnit_left (h2 ▸ w.isUnit)
  have hstd : latticeMap (scalarGL c) (stdLattice 𝒪 K) = stdLattice 𝒪 K :=
    latticeMap_scalarGL_stdLattice_of_isUnit a haunit c ha
  calc latticeMap (scalarGL c) N = latticeMap (scalarGL c * g) (stdLattice 𝒪 K) := by
        rw [latticeMap_mul, hg]
    _ = latticeMap (g * scalarGL c) (stdLattice 𝒪 K) := by rw [scalarGL_mul_comm]
    _ = N := by rw [latticeMap_mul, hstd, hg]

/-- Homothetic lattices have determinant indices of the same parity. -/
theorem CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e e' : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e') :
    Even (e - e') := by
  obtain ⟨g, hg, u, hu⟩ := h
  obtain ⟨g', hg', u', hu'⟩ := h'
  have hfix : latticeMap ((scalarGL c * g)⁻¹ * g') (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, hg', ← hg, ← latticeMap_mul, ← latticeMap_mul, mul_assoc,
      inv_mul_cancel, latticeMap_one]
  obtain ⟨M, hM⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix
  have hdet : (Matrix.GeneralLinearGroup.det g' : Kˣ) =
      Matrix.GeneralLinearGroup.det (scalarGL c) * Matrix.GeneralLinearGroup.det g *
        Matrix.GeneralLinearGroup.det ((scalarGL c * g)⁻¹ * g') := by
    conv_lhs => rw [← mul_inv_cancel_left (scalarGL c * g) g']
    rw [map_mul, map_mul]
  have hdetk : ((Matrix.GeneralLinearGroup.det ((scalarGL c * g)⁻¹ * g') : Kˣ) : K) =
      algebraMap 𝒪 K (Matrix.GeneralLinearGroup.det M : 𝒪ˣ) := by
    rw [← hM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    change ((M : Matrix (Fin 2) (Fin 2) 𝒪).map (algebraMap 𝒪 K)).det = _
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  obtain ⟨n, v, hv⟩ := exists_unit_mul_zpow_of_ne_zero hπ hc0
  have hπK : algebraMap 𝒪 K π ≠ 0 :=
    fun h0 => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h0, map_zero]))
  have heq : algebraMap 𝒪 K u' * algebraMap 𝒪 K π ^ e' =
      (algebraMap 𝒪 K v * algebraMap 𝒪 K π ^ n) ^ 2 *
        (algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ e) *
        algebraMap 𝒪 K (Matrix.GeneralLinearGroup.det M : 𝒪ˣ) := by
    rw [← hu', ← hv, ← val_det_scalarGL, ← hu, ← hdetk, hdet, Units.val_mul, Units.val_mul]
  have heq' : algebraMap 𝒪 K u' * algebraMap 𝒪 K π ^ e' =
      algebraMap 𝒪 K ((v * v * u * Matrix.GeneralLinearGroup.det M : 𝒪ˣ)) *
        algebraMap 𝒪 K π ^ (2 * n + e) := by
    rw [heq, zpow_add₀ hπK, two_mul, zpow_add₀ hπK, Units.val_mul, Units.val_mul,
      Units.val_mul, map_mul, map_mul, map_mul]
    ring
  have := zpow_exp_unique hπ _ _ _ _ heq'
  exact ⟨-n, by omega⟩

end
