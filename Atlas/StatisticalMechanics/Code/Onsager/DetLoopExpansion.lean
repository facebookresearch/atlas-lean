/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators
open Polynomial
open Set FiniteDimensional Module

namespace StatMech.Onsager





theorem trace_pow_endo {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (φ : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (φ ^ k) = (φ.charpoly.roots.map (fun α => α ^ k)).sum := by
  classical
  have h_comm : Commute φ (φ ^ k) := (Commute.refl φ).pow_right k
  have hf : ∀ μ, MapsTo (φ ^ k)
      (φ.maxGenEigenspace μ : Submodule ℂ V) (φ.maxGenEigenspace μ) :=
    fun μ => φ.mapsTo_maxGenEigenspace_of_comm h_comm μ
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    φ.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top φ)
  have h_fin : {μ | φ.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep φ.independent_maxGenEigenspace
  
  have block : ∀ μ : ℂ, LinearMap.trace ℂ (φ.maxGenEigenspace μ) ((φ ^ k).restrict (hf μ))
      = μ ^ k * (Module.finrank ℂ (φ.maxGenEigenspace μ) : ℂ) := by
    intro μ
    have hφ : ∀ x ∈ (φ.maxGenEigenspace μ : Submodule ℂ V), φ x ∈ φ.maxGenEigenspace μ :=
      φ.mapsTo_maxGenEigenspace_of_comm (Commute.refl φ) μ
    have hnil : IsNilpotent
        (φ.restrict hφ - algebraMap ℂ (Module.End ℂ (φ.maxGenEigenspace μ)) μ) := by
      have h0 := φ.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
      have heq : φ.restrict hφ - algebraMap ℂ (Module.End ℂ (φ.maxGenEigenspace μ)) μ
          = (φ - algebraMap ℂ (Module.End ℂ V) μ).restrict
              (φ.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes φ μ) μ) := by
        refine LinearMap.ext (fun x => Subtype.ext ?_)
        simp [LinearMap.sub_apply, Module.algebraMap_end_apply]
      rw [heq]; exact h0
    have hpr : ((φ ^ k).restrict (hf μ)) = (φ.restrict hφ) ^ k :=
      (Module.End.pow_restrict k hφ).symm
    rw [hpr]
    have blockpow : ∀ m : ℕ, LinearMap.trace ℂ (φ.maxGenEigenspace μ) ((φ.restrict hφ) ^ m)
        = μ ^ m * (Module.finrank ℂ (φ.maxGenEigenspace μ) : ℂ) := by
      intro m
      induction m with
      | zero => simp [LinearMap.trace_one]
      | succ m ih =>
        have hc : Commute ((φ.restrict hφ) ^ m) (φ.restrict hφ) :=
          (Commute.refl (φ.restrict hφ)).pow_left m
        rw [pow_succ, Module.End.mul_eq_comp,
          LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ hc hnil, ih]
        ring
    exact blockpow k
  
  have hfinset : h_fin.toFinset = φ.charpoly.roots.toFinset := by
    ext μ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [show (φ.maxGenEigenspace μ ≠ ⊥) ↔ (Module.finrank ℂ (φ.maxGenEigenspace μ) ≠ 0) from
          not_congr Submodule.finrank_eq_zero.symm,
        LinearMap.finrank_maxGenEigenspace_eq, ← Polynomial.count_roots, ne_eq,
        Multiset.count_eq_zero, not_not]
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hf,
    Finset.sum_congr rfl (fun μ _ => block μ), Finset.sum_multiset_map_count, ← hfinset]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [LinearMap.finrank_maxGenEigenspace_eq, Polynomial.count_roots, nsmul_eq_mul, mul_comm]








theorem ons_det_loop_expansion_of_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : Matrix ι ι ℂ)
    (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1)
    (htrace : ∀ n : ℕ,
        (Λ ^ (n + 1)).trace = (Λ.charpoly.roots.map (fun α => α ^ (n + 1))).sum) :
    (1 - Λ).det = Complex.exp (- ∑' n : ℕ, (Λ ^ (n + 1)).trace / (n + 1)) := by
  
  have hsumm_root : ∀ α : ℂ, ‖α‖ < 1 →
      Summable (fun n : ℕ => α ^ (n + 1) / ((n : ℂ) + 1)) := by
    intro α ha
    have h := (Complex.hasSum_taylorSeries_neg_log ha).summable
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr (fun n => ?_)
    push_cast
    ring
  
  have htsum_root : ∀ α : ℂ, ‖α‖ < 1 →
      (∑' n : ℕ, α ^ (n + 1) / ((n : ℂ) + 1)) = - Complex.log (1 - α) := by
    intro α ha
    have hHS : HasSum (fun n : ℕ => α ^ n / (n : ℂ)) (- Complex.log (1 - α)) :=
      Complex.hasSum_taylorSeries_neg_log ha
    have h0 := hHS.summable.tsum_eq_zero_add
    rw [hHS.tsum_eq] at h0
    simp only [pow_zero, Nat.cast_zero, div_zero, zero_add] at h0
    rw [h0]
    refine tsum_congr (fun n => ?_)
    push_cast
    ring
  
  have hsumm_multiset : ∀ t : Multiset ℂ, (∀ α ∈ t, ‖α‖ < 1) →
      Summable (fun n : ℕ => (t.map (fun α => α ^ (n + 1) / ((n : ℂ) + 1))).sum) := by
    intro t
    refine Multiset.induction ?_ ?_ t
    · intro _; simp
    · intro a t ih ht
      have ha : ‖a‖ < 1 := ht a (Multiset.mem_cons_self a t)
      have ht' : ∀ α ∈ t, ‖α‖ < 1 := fun α hα => ht α (Multiset.mem_cons_of_mem hα)
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (hsumm_root a ha).add (ih ht')
  
  have key : ∀ t : Multiset ℂ, (∀ α ∈ t, ‖α‖ < 1) →
      (∑' n : ℕ, (t.map (fun α => α ^ (n + 1) / ((n : ℂ) + 1))).sum)
        = (t.map (fun α => ∑' n : ℕ, α ^ (n + 1) / ((n : ℂ) + 1))).sum := by
    intro t
    refine Multiset.induction ?_ ?_ t
    · intro _; simp
    · intro a t ih ht
      have ha : ‖a‖ < 1 := ht a (Multiset.mem_cons_self a t)
      have ht' : ∀ α ∈ t, ‖α‖ < 1 := fun α hα => ht α (Multiset.mem_cons_of_mem hα)
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [Summable.tsum_add (hsumm_root a ha) (hsumm_multiset t ht'), ih ht']
  
  have hne1 : ∀ α ∈ Λ.charpoly.roots, (1 : ℂ) - α ≠ 0 := by
    intro α hα h
    have hlt := hspec α hα
    rw [sub_eq_zero] at h
    rw [← h] at hlt
    simp at hlt
  
  have hcard : Λ.charpoly.roots.card = Λ.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits Λ.charpoly)
  have hprod : (Λ.charpoly.roots.map (fun a => X - C a)).prod = Λ.charpoly :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq Λ.charpoly_monic hcard
  have h1 : (1 - Λ).det = Λ.charpoly.eval 1 := by
    rw [Matrix.eval_charpoly, map_one]
  have h2 : Λ.charpoly.eval 1 = (Λ.charpoly.roots.map (fun α => 1 - α)).prod := by
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun a _ => ?_))
    simp
  have hdet : (1 - Λ).det = (Λ.charpoly.roots.map (fun α => 1 - α)).prod := h1.trans h2
  
  have hexp : Complex.exp ((Λ.charpoly.roots.map (fun α => Complex.log (1 - α))).sum)
      = (Λ.charpoly.roots.map (fun α => 1 - α)).prod := by
    rw [Complex.exp_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun α hα => ?_))
    exact Complex.exp_log (hne1 α hα)
  
  have hchain : (∑' n : ℕ, (Λ ^ (n + 1)).trace / ((n : ℂ) + 1))
      = - (Λ.charpoly.roots.map (fun α => Complex.log (1 - α))).sum := by
    have e1 : ∀ n : ℕ, (Λ ^ (n + 1)).trace / ((n : ℂ) + 1)
        = (Λ.charpoly.roots.map (fun α => α ^ (n + 1) / ((n : ℂ) + 1))).sum := by
      intro n
      rw [htrace n, ← Multiset.sum_map_div]
    rw [tsum_congr e1, key Λ.charpoly.roots hspec]
    have hmap : (Λ.charpoly.roots.map (fun α => ∑' n : ℕ, α ^ (n + 1) / ((n : ℂ) + 1)))
          = (Λ.charpoly.roots.map (fun α => Complex.log (1 - α))).map Neg.neg := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl (fun α hα => htsum_root α (hspec α hα))
    rw [hmap, Multiset.sum_map_neg']
  have hlogsum : - (∑' n : ℕ, (Λ ^ (n + 1)).trace / ((n : ℂ) + 1))
      = (Λ.charpoly.roots.map (fun α => Complex.log (1 - α))).sum := by
    rw [hchain, neg_neg]
  rw [hdet, ← hexp, hlogsum]




theorem ons_det_loop_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : Matrix ι ι ℂ)
    (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
    (1 - Λ).det = Complex.exp (- ∑' n : ℕ, (Λ ^ (n + 1)).trace / (n + 1)) := by
  
  have htoLin_pow : ∀ m : ℕ, (Λ ^ m).toLin' = (Λ.toLin') ^ m := by
    intro m
    induction m with
    | zero => simp [Matrix.toLin'_one, Module.End.one_eq_id]
    | succ m ih => rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]
  
  have htrace : ∀ n : ℕ,
      (Λ ^ (n + 1)).trace = (Λ.charpoly.roots.map (fun α => α ^ (n + 1))).sum := by
    intro n
    rw [← Matrix.trace_toLin'_eq, htoLin_pow, trace_pow_endo, Matrix.charpoly_toLin']
  exact ons_det_loop_expansion_of_trace Λ hspec htrace

end StatMech.Onsager
