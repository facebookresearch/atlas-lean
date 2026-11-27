/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from:

`Theorems/Thm_AlgebraicCurve_absLogHeight_root_le_coeff.lean`,
`P2M/Sol/S_AlgebraicCurve_absLogHeight_root_le_coeff.lean`,
`Theorems/Thm_AlgebraicCurve_sum_absLogHeight_roots_le_coeff.lean`,
`P2M/Sol/S_AlgebraicCurve_sum_absLogHeight_roots_le_coeff.lean`, and
`Definitions/Def_ModularCurve_JZeroHeightForm.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.RingTheory.Polynomial.GaussNorm
import MathlibExt.NumberTheory.Height.LogHeightAlgebraMap

@[expose] public section

namespace AlgebraicCurve

private theorem finiteDimensional_adjoin_range {ι : Type*} [Finite ι]
    (x : ι → AlgebraicClosure ℚ) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
  IntermediateField.finiteDimensional_adjoin fun y _ =>
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral

/-- **Absolute logarithmic height of a tuple.** The absolute logarithmic height of a tuple of
algebraic numbers: the logarithmic height of the tuple in the field it generates, normalised by
the degree of that field over `ℚ`. -/
public noncomputable def absLogHeight {ι : Type*} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) : ℝ :=
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  haveI : NumberField (IntermediateField.adjoin ℚ (Set.range x)) := {}
  (Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) : ℝ)⁻¹ *
    Height.logHeight fun i =>
      (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range x))

private theorem absLogHeight_eq_of_mem {ι : Type*} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField L] (hx : ∀ i, x i ∈ L) :
    absLogHeight x
      = (Module.finrank ℚ L : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : L)) := by
  classical
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
    finiteDimensional_adjoin_range x
  have : NumberField (IntermediateField.adjoin ℚ (Set.range x)) := {}
  have : NumberField L := {}
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (Set.range_subset_iff.mpr hx)
  let : Algebra (IntermediateField.adjoin ℚ (Set.range x)) L :=
    (IntermediateField.inclusion hle).toAlgebra
  have htup : (fun i => (⟨x i, hx i⟩ : L))
      = fun i => algebraMap (IntermediateField.adjoin ℚ (Set.range x)) L
          (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
            IntermediateField.adjoin ℚ (Set.range x)) := by
    funext i
    rfl
  rw [htup, Height.logHeight_algebraMap]
  have htower : Module.finrank ℚ L
      = Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x))
        * Module.finrank (IntermediateField.adjoin ℚ (Set.range x)) L :=
    (Module.finrank_mul_finrank ℚ _ L).symm
  have hdK : (0 : ℝ) < (Module.finrank ℚ
      (IntermediateField.adjoin ℚ (Set.range x)) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hdKL : (0 : ℝ) < (Module.finrank
      (IntermediateField.adjoin ℚ (Set.range x)) L : ℝ) := by
    exact_mod_cast Module.finrank_pos
  unfold absLogHeight
  rw [htower, Nat.cast_mul, mul_inv]
  field_simp



private theorem mwb1_absLogHeight_nonneg {ι : Type*} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
    finiteDimensional_adjoin_range x
  have : NumberField (IntermediateField.adjoin ℚ (Set.range x)) := {}
  unfold absLogHeight
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
  exact Height.logHeight_nonneg (fun i =>
    (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range x)))

private lemma mwb1_iSup_coeff_eq_gaussNorm {M : Type*} [Field M] (v : AbsoluteValue M ℝ)
    {n : ℕ} {f : Polynomial M} (hdeg : f.natDegree ≤ n) :
    (⨆ k : Fin (n + 1), v (f.coeff k)) = f.gaussNorm v 1 := by
  refine le_antisymm (ciSup_le fun k ↦ ?_) ?_
  · simpa using f.le_gaussNorm v zero_le_one k
  · obtain ⟨i, hi⟩ := f.exists_eq_gaussNorm v 1
    rcases le_or_gt i n with hin | hin
    · rw [hi]
      have := Finite.le_ciSup (fun k : Fin (n + 1) ↦ v (f.coeff ↑k)) ⟨i, Nat.lt_succ_of_le hin⟩
      simpa using this
    · rw [hi, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hin)]
      simpa using Real.iSup_nonneg_of_nonnegHomClass v fun k : Fin (n + 1) ↦ f.coeff ↑k

private lemma mwb1_gaussNorm_X_sub_C {M : Type*} [Field M] (v : AbsoluteValue M ℝ) (a : M) :
    (Polynomial.X - Polynomial.C a).gaussNorm v 1 = max (v a) 1 := by
  have hc0 : (Polynomial.X - Polynomial.C a).coeff 0 = -a := by simp
  have hc1 : (Polynomial.X - Polynomial.C a).coeff 1 = 1 := by simp
  have hdeg : (Polynomial.X - Polynomial.C a).natDegree ≤ 1 := by
    simp
  rw [← mwb1_iSup_coeff_eq_gaussNorm v hdeg]
  refine le_antisymm (ciSup_le fun k ↦ ?_) ?_
  · fin_cases k
    · change v ((Polynomial.X - Polynomial.C a).coeff 0) ≤ max (v a) 1
      rw [hc0, v.map_neg]
      exact le_max_left _ _
    · change v ((Polynomial.X - Polynomial.C a).coeff 1) ≤ max (v a) 1
      rw [hc1, v.map_one]
      exact le_max_right _ _
  · have h0 : v ((Polynomial.X - Polynomial.C a).coeff ((0 : Fin 2) : ℕ)) = v a := by
      rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, hc0, v.map_neg]
    have h1 : v ((Polynomial.X - Polynomial.C a).coeff ((1 : Fin 2) : ℕ)) = 1 := by
      rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, hc1, v.map_one]
    rcases max_cases (v a) 1 with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
    · exact h0 ▸ Finite.le_ciSup (fun k : Fin 2 ↦ v ((Polynomial.X - Polynomial.C a).coeff ↑k)) 0
    · exact h1 ▸ Finite.le_ciSup (fun k : Fin 2 ↦ v ((Polynomial.X - Polynomial.C a).coeff ↑k)) 1

private lemma mwb1_gaussNorm_prod {M : Type*} [Field M] {ι : Type*} {v : AbsoluteValue M ℝ}
    (hv : IsNonarchimedean (⇑v)) (t : Finset ι) (α : ι → M) (m : ι → ℕ) :
    (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).gaussNorm v 1
      = ∏ i ∈ t, max (v (α i)) 1 ^ m i := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [show (1 : Polynomial M) = Polynomial.C 1 from (Polynomial.C_1).symm,
      Polynomial.gaussNorm_C, map_one]
  | insert a t ha ih =>
    have := Polynomial.gaussNorm_isAbsoluteValue hv one_pos
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Polynomial.gaussNorm_mul (hna := hv) (hc := one_pos),
      IsAbsoluteValue.abv_pow (Polynomial.gaussNorm v 1), mwb1_gaussNorm_X_sub_C, ih]

open Real in
private lemma mwb1_arch_prod_le {M : Type*} [Field M] [NumberField M] {ι : Type*}
    (w : NumberField.InfinitePlace M) (t : Finset ι) (α : ι → M) (m : ι → ℕ) {n : ℕ}
    (hdegp : (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).natDegree ≤ n) :
    (∏ i ∈ t, max (w (α i)) 1 ^ m i)
      ≤ Real.sqrt (n + 1) * ⨆ k : Fin (n + 1),
          w ((∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k) := by
  classical
  set p : Polynomial M := ∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i with hpdef
  set φ : M →+* ℂ := w.embedding with hφ
  have hp : p.Monic := Polynomial.monic_prod_of_monic _ _
    fun i _ => (Polynomial.monic_X_sub_C (α i)).pow _
  have hp0 : p ≠ 0 := hp.ne_zero
  have hP0 : p.map φ ≠ 0 := (Polynomial.map_eq_zero_iff φ.injective).not.mpr hp0
  have hPdeg : (p.map φ).natDegree ≤ n := by
    rw [Polynomial.natDegree_map_eq_of_injective φ.injective]
    exact hdegp
  have hmap : p.map φ = ∏ i ∈ t, (Polynomial.X - Polynomial.C (φ (α i))) ^ m i := by
    rw [hpdef, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hM : (p.map φ).mahlerMeasure = ∏ i ∈ t, max (w (α i)) 1 ^ m i := by
    rw [hmap, Finset.prod_eq_multiset_prod, Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod,
      Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Function.comp_apply, ← Multiset.prod_replicate,
      Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod, Multiset.map_replicate,
      Multiset.prod_replicate, Polynomial.mahlerMeasure_X_sub_C, w.norm_embedding_eq, max_comm]
  have hsup : (p.map φ).supNorm ≤ ⨆ k : Fin (n + 1), w (p.coeff k) := by
    rw [Polynomial.supNorm_def', dite_eq_left (Polynomial.support_nonempty.mpr hP0)]
    refine Finset.sup'_le _ _ fun i hi ↦ ?_
    have hin : i < n + 1 :=
      Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_mem_supp i hi).trans hPdeg)
    have hcoe : ‖(p.map φ).coeff i‖ = w (p.coeff i) := by
      rw [Polynomial.coeff_map, w.norm_embedding_eq]
    calc (norm ∘ (p.map φ).coeff) i = w (p.coeff i) := by
          simpa [Function.comp_apply] using hcoe
      _ ≤ ⨆ k : Fin (n + 1), w (p.coeff ↑k) :=
          Finite.le_ciSup (fun k : Fin (n + 1) ↦ w (p.coeff ↑k)) ⟨i, hin⟩
  have hml : (p.map φ).mahlerMeasure ≤ Real.sqrt (n + 1) * (p.map φ).supNorm := by
    refine (Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _).trans ?_
    have hnn : ((p.map φ).natDegree : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hPdeg
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hnn) (p.map φ).supNorm_nonneg
  calc (∏ i ∈ t, max (w (α i)) 1 ^ m i) = (p.map φ).mahlerMeasure := hM.symm
    _ ≤ Real.sqrt (n + 1) * (p.map φ).supNorm := hml
    _ ≤ Real.sqrt (n + 1) * ⨆ k : Fin (n + 1), w (p.coeff k) :=
        mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)

open Real in
private lemma mwb1_srh_mul {M : Type*} [Field M] [NumberField M] {ι : Type*}
    (t : Finset ι) (α : ι → M) (m : ι → ℕ) {n : ℕ}
    (hdeg : ∑ i ∈ t, m i ≤ n) :
    ∏ i ∈ t, Height.mulHeight₁ (α i) ^ m i
      ≤ Real.sqrt (n + 1) ^ Height.totalWeight M *
          Height.mulHeight (fun k : Fin (n + 1) =>
            (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k) := by
  classical
  set p : Polynomial M := ∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i with hpdef
  have hp : p.Monic := Polynomial.monic_prod_of_monic _ _
    fun i _ => (Polynomial.monic_X_sub_C (α i)).pow _
  have hdegp : p.natDegree ≤ n := by
    rw [hpdef, Polynomial.natDegree_prod_of_monic _ _
      fun i _ => (Polynomial.monic_X_sub_C (α i)).pow _]
    calc (∑ i ∈ t, ((Polynomial.X - Polynomial.C (α i)) ^ m i).natDegree)
        = ∑ i ∈ t, m i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      _ ≤ n := hdeg
  have htp : (fun k : Fin (n + 1) => p.coeff k) ≠ 0 := by
    refine Function.ne_iff.mpr ⟨⟨p.natDegree, Nat.lt_succ_of_le hdegp⟩, ?_⟩
    simp [hp.coeff_natDegree]
  have hmax : ∀ i : ι, Function.HasFiniteMulSupport
      (fun v : NumberField.FinitePlace M => max (v (α i)) 1) := by
    intro i
    rcases eq_or_ne (α i) 0 with h | h
    · simp only [h, map_zero, zero_le_one, max_eq_right]
      exact Function.hasFiniteMulSupport_fun_one
    · exact (NumberField.FinitePlace.hasFiniteMulSupport h).max
        Function.hasFiniteMulSupport_fun_one
  have hroot : ∀ i ∈ t, Height.mulHeight₁ (α i) ^ m i
      = (∏ w : NumberField.InfinitePlace M, (max (w (α i)) 1 ^ m i) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace M, max (v (α i)) 1 ^ m i := by
    intro i _
    rw [NumberField.mulHeight₁_eq, mul_pow]
    congr 1
    · rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← pow_mul, ← pow_mul, mul_comm (m i) w.mult]
    · exact finprod_pow (hmax i) _
  have hsplit : ∏ i ∈ t, Height.mulHeight₁ (α i) ^ m i
      = (∏ w : NumberField.InfinitePlace M, (∏ i ∈ t, max (w (α i)) 1 ^ m i) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace M, ∏ i ∈ t, max (v (α i)) 1 ^ m i := by
    rw [Finset.prod_congr rfl hroot, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← Finset.prod_pow]
    · exact prod_finprod_comm t _ fun i _ => (hmax i).pow _
  rw [hsplit]
  have hfin : (∏ᶠ v : NumberField.FinitePlace M, ∏ i ∈ t, max (v (α i)) 1 ^ m i)
      = ∏ᶠ v : NumberField.FinitePlace M, ⨆ k : Fin (n + 1), v (p.coeff k) := by
    refine finprod_congr fun v => ?_
    have hna : IsNonarchimedean (⇑(v.val) : M → ℝ) := by
      intro a b
      simpa only [NumberField.FinitePlace.coe_apply] using v.add_le a b
    have h1 := mwb1_gaussNorm_prod (v := v.val) hna t α m
    have h2 := mwb1_iSup_coeff_eq_gaussNorm (v := v.val) hdegp
    have h3 : ∀ x : M, v.val x = v x := fun x => by
      rw [NumberField.FinitePlace.coe_apply]
    calc (∏ i ∈ t, max (v (α i)) 1 ^ m i)
        = ∏ i ∈ t, max (v.val (α i)) 1 ^ m i := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [h3]
      _ = (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).gaussNorm v.val 1 := h1.symm
      _ = ⨆ k : Fin (n + 1), v.val (p.coeff k) := by rw [← hpdef, ← h2]
      _ = ⨆ k : Fin (n + 1), v (p.coeff k) := by
          refine iSup_congr fun k => ?_
          rw [h3]
  rw [hfin]
  have harch : (∏ w : NumberField.InfinitePlace M, (∏ i ∈ t, max (w (α i)) 1 ^ m i) ^ w.mult)
      ≤ ∏ w : NumberField.InfinitePlace M,
          (Real.sqrt (n + 1) * ⨆ k : Fin (n + 1), w (p.coeff k)) ^ w.mult := by
    refine Finset.prod_le_prod₀ (fun w _ ↦ ?_) (fun w _ ↦ ?_)
    · exact pow_nonneg (Finset.prod_nonneg fun i _ =>
        pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) _
    · refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ =>
        pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) ?_ _
      rw [hpdef]
      exact mwb1_arch_prod_le w t α m hdegp
  calc (∏ w : NumberField.InfinitePlace M, (∏ i ∈ t, max (w (α i)) 1 ^ m i) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace M, ⨆ k : Fin (n + 1), v (p.coeff k)
      ≤ (∏ w : NumberField.InfinitePlace M,
          (Real.sqrt (n + 1) * ⨆ k : Fin (n + 1), w (p.coeff k)) ^ w.mult) *
          ∏ᶠ v : NumberField.FinitePlace M, ⨆ k : Fin (n + 1), v (p.coeff k) := by
        refine mul_le_mul_of_nonneg_right harch ?_
        exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v _
    _ = Real.sqrt (n + 1) ^ Height.totalWeight M *
          ((∏ w : NumberField.InfinitePlace M,
            (⨆ k : Fin (n + 1), w (p.coeff k)) ^ w.mult) *
            ∏ᶠ v : NumberField.FinitePlace M, ⨆ k : Fin (n + 1), v (p.coeff k)) := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          ← NumberField.totalWeight_eq_sum_mult, mul_assoc]
    _ = Real.sqrt (n + 1) ^ Height.totalWeight M *
          Height.mulHeight (fun k : Fin (n + 1) => p.coeff k) := by
        rw [← NumberField.mulHeight_eq htp]

open Real in
private theorem mwb1_srh_abs {ι : Type*} (t : Finset ι) (α : ι → AlgebraicClosure ℚ)
    (m : ι → ℕ) {n : ℕ} (hdeg : ∑ i ∈ t, m i ≤ n) :
    ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1]
      ≤ absLogHeight (fun k : Fin (n + 1) =>
          (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
        + Real.log (Real.sqrt (n + 1)) := by
  classical
  set S : Set (AlgebraicClosure ℚ) := ↑(t.image α) with hS
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  set M := IntermediateField.adjoin ℚ S with hM
  have : NumberField M := {}
  have hmem_α : ∀ i ∈ t, α i ∈ M := fun i hi =>
    IntermediateField.subset_adjoin ℚ S (by
      rw [hS]
      exact_mod_cast Finset.mem_image_of_mem α hi)
  set p' : Polynomial M := ∏ j ∈ t.attach, (Polynomial.X - Polynomial.C
    (⟨α j.val, hmem_α j.val j.property⟩ : M)) ^ m j.val with hp'def
  have hmap : Polynomial.map (algebraMap M (AlgebraicClosure ℚ)) p'
      = ∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i := by
    rw [hp'def, Polynomial.map_prod]
    rw [← Finset.prod_attach t fun i => (Polynomial.X - Polynomial.C (α i)) ^ m i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hcoeff_mem : ∀ k : Fin (n + 1),
      (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k ∈ M := by
    intro k
    rw [← hmap, Polynomial.coeff_map]
    exact (p'.coeff k).property
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := M)
  have hd0 : (0 : ℝ) < (Module.finrank ℚ M : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hcoeff_eq : absLogHeight (fun k : Fin (n + 1) =>
      (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
      = (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight fun k : Fin (n + 1) => p'.coeff k := by
    rw [absLogHeight_eq_of_mem _ M hcoeff_mem]
    congr 1
    refine congrArg _ (funext fun k => ?_)
    refine Subtype.ext ?_
    change (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k
      = ((p'.coeff k : M) : AlgebraicClosure ℚ)
    rw [← hmap, Polynomial.coeff_map]
    rfl
  have hroot_eq : ∀ i (hi : i ∈ t), absLogHeight ![α i, 1]
      = (Module.finrank ℚ M : ℝ)⁻¹ *
          Height.logHeight₁ (⟨α i, hmem_α i hi⟩ : M) := by
    intro i hi
    have hmem : ∀ k : Fin 2, (![α i, 1] : Fin 2 → AlgebraicClosure ℚ) k ∈ M := by
      intro k
      fin_cases k
      · exact hmem_α i hi
      · exact one_mem M
    rw [absLogHeight_eq_of_mem _ M hmem]
    congr 1
    have htup : (fun k : Fin 2 => (⟨(![α i, 1] : Fin 2 → AlgebraicClosure ℚ) k, hmem k⟩ : M))
        = ![(⟨α i, hmem_α i hi⟩ : M), 1] := by
      funext k
      fin_cases k
      · rfl
      · exact Subtype.ext (by simp)
    rw [htup, ← Height.logHeight₁_eq_logHeight]
  have hsum : ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1]
      = (Module.finrank ℚ M : ℝ)⁻¹ * ∑ j ∈ t.attach,
          (m j.val : ℝ) * Height.logHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M) := by
    rw [Finset.mul_sum, ← Finset.sum_attach t fun i => (m i : ℝ) * absLogHeight ![α i, 1]]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hroot_eq j.val j.property]
    ring
  have hdeg' : ∑ j ∈ t.attach, m j.val ≤ n := by
    rw [Finset.sum_attach t m]
    exact hdeg
  have hmulsrh := mwb1_srh_mul (M := M) t.attach
    (fun j => (⟨α j.val, hmem_α j.val j.property⟩ : M)) (fun j => m j.val) hdeg'
  have hp'eq : (∏ j ∈ t.attach, (Polynomial.X - Polynomial.C
      (⟨α j.val, hmem_α j.val j.property⟩ : M)) ^ m j.val) = p' := hp'def.symm
  rw [hp'eq] at hmulsrh
  have hlogsrh : ∑ j ∈ t.attach,
      (m j.val : ℝ) * Height.logHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M)
      ≤ (Height.totalWeight M : ℝ) * Real.log (Real.sqrt (n + 1))
        + Height.logHeight fun k : Fin (n + 1) => p'.coeff k := by
    have hpos : ∀ j ∈ t.attach, (0 : ℝ) <
        Height.mulHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M) ^ m j.val :=
      fun j _ => pow_pos (lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight₁ _)) _
    have hlhs : ∑ j ∈ t.attach,
        (m j.val : ℝ) * Height.logHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M)
        = Real.log (∏ j ∈ t.attach,
            Height.mulHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M) ^ m j.val) := by
      rw [Real.log_prod fun j hj => (hpos j hj).ne']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Real.log_pow, Height.logHeight₁_eq_log_mulHeight₁]
    rw [hlhs]
    have hrhs_pos : (0 : ℝ) < Real.sqrt (n + 1) ^ Height.totalWeight M *
        Height.mulHeight (fun k : Fin (n + 1) => p'.coeff k) := by
      refine mul_pos (pow_pos ?_ _) (Height.mulHeight_pos _)
      rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
      exact Real.sqrt_lt_sqrt le_rfl (by positivity)
    calc Real.log (∏ j ∈ t.attach,
          Height.mulHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M) ^ m j.val)
        ≤ Real.log (Real.sqrt (n + 1) ^ Height.totalWeight M *
            Height.mulHeight (fun k : Fin (n + 1) => p'.coeff k)) :=
          Real.log_le_log (Finset.prod_pos hpos) hmulsrh
      _ = (Height.totalWeight M : ℝ) * Real.log (Real.sqrt (n + 1))
          + Height.logHeight fun k : Fin (n + 1) => p'.coeff k := by
          rw [Real.log_mul (by positivity) (Height.mulHeight_pos _).ne',
            Real.log_pow, Height.logHeight_eq_log_mulHeight]
  rw [hsum, hcoeff_eq]
  rw [NumberField.totalWeight_eq_finrank] at hlogsrh
  have h := mul_le_mul_of_nonneg_left hlogsrh (inv_nonneg.mpr hd0.le)
  calc (Module.finrank ℚ M : ℝ)⁻¹ * ∑ j ∈ t.attach,
        (m j.val : ℝ) * Height.logHeight₁ (⟨α j.val, hmem_α j.val j.property⟩ : M)
      ≤ (Module.finrank ℚ M : ℝ)⁻¹ * ((Module.finrank ℚ M : ℝ) * Real.log (Real.sqrt (n + 1))
          + Height.logHeight fun k : Fin (n + 1) => p'.coeff k) := h
    _ = (Module.finrank ℚ M : ℝ)⁻¹ *
          (Height.logHeight fun k : Fin (n + 1) => p'.coeff k)
          + Real.log (Real.sqrt (n + 1)) := by
        field_simp
        ring


/-- The source's form of the root height bound, through the pair height `absLogHeight ![z, 1]`;
`absLogHeight₁_root_le_coeff` is its public statement. -/
private theorem absLogHeight_root_le_coeff {p : Polynomial (AlgebraicClosure ℚ)}
    (hmonic : p.Monic) {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) := by
  classical
  have hχ0 : p ≠ 0 := hmonic.ne_zero
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hprod : p = (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    hsplits.eq_prod_roots_of_monic hmonic
  have hfactor : (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod
      = ∏ r ∈ p.roots.toFinset,
          (Polynomial.X - Polynomial.C r) ^ p.roots.count r :=
    Finset.prod_multiset_map_count _ _
  have hdeg : (∑ r ∈ p.roots.toFinset, p.roots.count r) ≤ p.natDegree := by
    rw [Multiset.toFinset_sum_count_eq]
    exact_mod_cast (Polynomial.card_roots' p)
  have hsrh := mwb1_srh_abs p.roots.toFinset id (fun r => p.roots.count r) hdeg
  have hzr : z ∈ p.roots := by
    rw [Polynomial.mem_roots hχ0]
    exact hroot
  have hz1 : 1 ≤ p.roots.count z := Multiset.one_le_count_iff_mem.mpr hzr
  have hsingle : absLogHeight ![z, 1]
      ≤ ∑ r ∈ p.roots.toFinset, (p.roots.count r : ℝ) * absLogHeight ![id r, 1] := by
    have hmem : z ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hzr
    calc absLogHeight ![z, 1]
        = absLogHeight ![id z, 1] := rfl
      _ ≤ (p.roots.count z : ℝ) * absLogHeight ![id z, 1] := by
          have h1 : (1 : ℝ) ≤ (p.roots.count z : ℝ) := by exact_mod_cast hz1
          have h2 := mwb1_absLogHeight_nonneg (![id z, 1])
          nlinarith
      _ ≤ _ := Finset.single_le_sum
          (f := fun r => (p.roots.count r : ℝ) * absLogHeight ![id r, 1])
          (fun r _ => mul_nonneg (by positivity) (mwb1_absLogHeight_nonneg _)) hmem
  refine hsingle.trans (hsrh.trans ?_)
  have hpoly : (∏ r ∈ p.roots.toFinset,
      (Polynomial.X - Polynomial.C (id r)) ^ p.roots.count r) = p := by
    simp only [id]
    rw [← hfactor, ← hprod]
  rw [hpoly]

/-- **Pair height and the canonical height.** The absolute logarithmic height of the pair
`![z, 1]` is the canonical absolute logarithmic height `NumberField.absLogHeight₁ z`. -/
public theorem absLogHeight_pair_eq_absLogHeight₁ (z : AlgebraicClosure ℚ) :
    absLogHeight ![z, 1] = NumberField.absLogHeight₁ z := by
  classical
  have hz : IsIntegral ℚ z := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z}) :=
    IntermediateField.adjoin.finiteDimensional hz
  have : NumberField (IntermediateField.adjoin ℚ {z}) := {}
  have hmem : ∀ i, ![z, (1 : AlgebraicClosure ℚ)] i ∈
      IntermediateField.adjoin ℚ {z} := by
    intro i
    fin_cases i
    · exact IntermediateField.subset_adjoin ℚ {z} (Set.mem_singleton z)
    · exact one_mem _
  rw [absLogHeight_eq_of_mem ![z, 1] (IntermediateField.adjoin ℚ {z}) hmem,
    NumberField.absLogHeight₁, NumberField.absMulHeight₁, dite_eq_left hz,
    Real.log_rpow (Height.mulHeight₁_pos _),
    ← Height.logHeight₁_eq_log_mulHeight₁, Height.logHeight₁_eq_logHeight]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- **Height of a root bounded by its coefficients.** Let $p$ be a monic polynomial of degree $d$
over the algebraic closure of $\mathbb{Q}$, with coefficients $a_0, \dots, a_d$, and let $z$ be a
root of $p$. Then the absolute logarithmic height of $z$ is at most the absolute logarithmic
height of the coefficient tuple plus $\log \sqrt{d + 1}$:

$$h(z) \le h(a_0, \dots, a_d) + \log \sqrt{d + 1}.$$
-/
public theorem absLogHeight₁_root_le_coeff {p : Polynomial (AlgebraicClosure ℚ)}
    (hmonic : p.Monic) {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    NumberField.absLogHeight₁ z
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) := by
  rw [← absLogHeight_pair_eq_absLogHeight₁]
  exact absLogHeight_root_le_coeff hmonic hroot

end AlgebraicCurve
