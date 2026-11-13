/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FiniteBoundarySourceLaw
import Code.FrontierB.BoundaryCurrentTail

open scoped BigOperators

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem interiorSpinSum_monomial_insert
    (interior A : Finset V) (hA : A ⊆ interior)
    (n : Sharpness.Current V) :
    (∑ s : ConfigSpace ↑interior,
      spinProd A (extendInteriorPlus interior s) *
        ∏ e ∈ G.edgeFinset,
          bond (extendInteriorPlus interior s) e ^ n e) =
      if (sources G n) ∩ interior = A then
        (2 : ℝ) ^ interior.card else 0 := by
  classical
  have hrewrite : ∀ s : ConfigSpace ↑interior,
      spinProd A (extendInteriorPlus interior s) *
          (∏ e ∈ G.edgeFinset,
            bond (extendInteriorPlus interior s) e ^ n e) =
        ∏ v : ↑interior,
          spin s v ^ ((if v.1 ∈ A then 1 else 0) + incidentFlux G n v.1) := by
    intro s
    have hinsert := prod_spin_extendInteriorPlus interior s
      (fun v => if v ∈ A then 1 else 0)
    have hinsert' : spinProd A (extendInteriorPlus interior s) =
        ∏ v : ↑interior, spin s v ^ (if v.1 ∈ A then 1 else 0) := by
      rw [← hinsert]
      simp [spinProd]
    rw [prod_bond_pow_eq_prod_spin_pow,
      prod_spin_extendInteriorPlus interior s (incidentFlux G n),
      hinsert', ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    rw [← pow_add]
  simp_rw [hrewrite, spin_eq_spinB]
  rw [← Fintype.prod_sum
    (fun v : ↑interior => fun b : Bool =>
      spinB b ^ ((if v.1 ∈ A then 1 else 0) + incidentFlux G n v.1))]
  simp_rw [sum_spinB_pow]
  by_cases hsrc : (sources G n) ∩ interior = A
  · rw [if_pos hsrc]
    have heven : ∀ v : ↑interior,
        Even ((if v.1 ∈ A then 1 else 0) + incidentFlux G n v.1) := by
      intro v
      have hviff : v.1 ∈ sources G n ↔ v.1 ∈ A := by
        have := Finset.ext_iff.mp hsrc v.1
        simpa [v.2] using this
      by_cases hvA : v.1 ∈ A
      · have hodd : Odd (incidentFlux G n v.1) :=
          (mem_sources G).1 (hviff.mpr hvA)
        simp only [hvA, if_true]
        exact hodd.one_add
      · have hnotSource : v.1 ∉ sources G n := fun hs => hvA (hviff.mp hs)
        have hev : Even (incidentFlux G n v.1) :=
          Nat.not_odd_iff_even.mp (fun ho => hnotSource ((mem_sources G).2 ho))
        simpa [hvA] using hev
    have hall :
        (∏ v : ↑interior,
          if Even ((if v.1 ∈ A then 1 else 0) + incidentFlux G n v.1)
            then (2 : ℝ) else 0) =
          ∏ _v : ↑interior, (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [if_pos (heven v)]
    rw [hall]
    simp
  · rw [if_neg hsrc]
    have hmismatch : ∃ v : V, v ∈ interior ∧
        ((v ∈ sources G n ∧ v ∉ A) ∨ (v ∈ A ∧ v ∉ sources G n)) := by
      by_contra hnone
      apply hsrc
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hvsrc, hvint⟩
        by_contra hvA
        exact hnone ⟨v, hvint, Or.inl ⟨hvsrc, hvA⟩⟩
      · intro hvA
        have hvint := hA hvA
        refine ⟨?_, hvint⟩
        by_contra hvsrc
        exact hnone ⟨v, hvint, Or.inr ⟨hvA, hvsrc⟩⟩
    obtain ⟨v, hvint, hmismatch⟩ := hmismatch
    apply Finset.prod_eq_zero
      (Finset.mem_univ (⟨v, hvint⟩ : ↑interior))
    rw [if_neg]
    rcases hmismatch with ⟨hvsrc, hvA⟩ | ⟨hvA, hvsrc⟩
    · simpa [hvA] using (mem_sources G).1 hvsrc
    · have hev : Even (incidentFlux G n v) :=
        Nat.not_odd_iff_even.mp (fun ho => hvsrc ((mem_sources G).2 ho))
      simpa [hvA] using hev.one_add



theorem boundarySpinNumerator_eq_boundarySourceCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior A : Finset V) (hA : A ⊆ interior) :
    (∑ s : ConfigSpace ↑interior,
      spinProd A (extendInteriorPlus interior s) *
        boltzmannJ G beta J (extendInteriorPlus interior s)) =
      (2 : ℝ) ^ interior.card *
        boundarySourceCurrentSum G beta J interior A := by
  classical
  have hstep : ∀ s : ConfigSpace ↑interior,
      spinProd A (extendInteriorPlus interior s) *
          boltzmannJ G beta J (extendInteriorPlus interior s) =
        ∑' m : EdgeCurrent G,
          weight G beta J (ofEdgeFun G m) *
            (spinProd A (extendInteriorPlus interior s) *
              ∏ e : G.edgeFinset,
                bond (extendInteriorPlus interior s) e.1 ^ m e) := by
    intro s
    rw [boltzmannJ_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  simp_rw [hstep]
  rw [← Summable.tsum_finsetSum
    (s := (Finset.univ : Finset (ConfigSpace ↑interior)))
    (f := fun s (m : EdgeCurrent G) =>
      weight G beta J (ofEdgeFun G m) *
        (spinProd A (extendInteriorPlus interior s) *
          ∏ e : G.edgeFinset,
            bond (extendInteriorPlus interior s) e.1 ^ m e))
    (fun s _ => by
      have hs := summable_weight_bond G beta J (extendInteriorPlus interior s)
      exact (hs.mul_left (spinProd A (extendInteriorPlus interior s))).congr
        (fun m => by ring))]
  have hinner : ∀ m : EdgeCurrent G,
      (∑ s : ConfigSpace ↑interior,
        weight G beta J (ofEdgeFun G m) *
          (spinProd A (extendInteriorPlus interior s) *
            ∏ e : G.edgeFinset,
              bond (extendInteriorPlus interior s) e.1 ^ m e)) =
        if sources G (ofEdgeFun G m) ∩ interior = A then
          weight G beta J (ofEdgeFun G m) * (2 : ℝ) ^ interior.card else 0 := by
    intro m
    rw [← Finset.mul_sum]
    have hbonds : ∀ s : ConfigSpace ↑interior,
        (∏ e : G.edgeFinset,
          bond (extendInteriorPlus interior s) e.1 ^ m e) =
          ∏ e ∈ G.edgeFinset,
            bond (extendInteriorPlus interior s) e ^ (ofEdgeFun G m) e :=
      fun s => (prod_bond_pow_ofEdgeFun G (extendInteriorPlus interior s) m).symm
    simp_rw [hbonds]
    rw [interiorSpinSum_monomial_insert G interior A hA (ofEdgeFun G m)]
    split <;> simp_all
  simp_rw [hinner]
  unfold boundarySourceCurrentSum
  rw [mul_comm ((2 : ℝ) ^ interior.card), ← tsum_mul_right]
  apply tsum_congr
  intro m
  split <;> simp_all



theorem boundarySourceCurrentSum_div_boundaryCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior A : Finset V) (hA : A ⊆ interior) :
    boundarySourceCurrentSum G beta J interior A /
        boundaryCurrentSum G beta J interior =
      (∑ s : ConfigSpace ↑interior,
        spinProd A (extendInteriorPlus interior s) *
          boltzmannJ G beta J (extendInteriorPlus interior s)) /
        boundaryPartitionJ G beta J interior := by
  rw [boundarySpinNumerator_eq_boundarySourceCurrentSum G beta J interior A hA,
    boundaryPartitionJ_eq_boundaryCurrentSum]
  have hp : (2 : ℝ) ^ interior.card ≠ 0 := by positivity
  field_simp

end StatMech.FrontierB
