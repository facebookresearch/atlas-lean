/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Ising.KWSelfDuality
import Code.Sharpness.CurrentRep
import Code.Sharpness.BackbonePropsFull
import Code.Sharpness.SimonLieb

open Finset
open scoped BigOperators

namespace StatMech
namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def HasOddBoundary (F : Finset (Sym2 V)) (A : Finset V) : Prop :=
  ∀ v : V, Odd (incCount F v) ↔ v ∈ A

instance (F : Finset (Sym2 V)) (A : Finset V) : Decidable (HasOddBoundary F A) :=
  Fintype.decidableForallFintype

omit [Fintype V] in
@[simp]
theorem hasOddBoundary_empty (F : Finset (Sym2 V)) :
    HasOddBoundary F ∅ ↔ IsEvenSubgraph F := by
  simp only [HasOddBoundary, IsEvenSubgraph, Finset.notMem_empty, iff_false,
    Nat.not_odd_iff_even]



theorem sum_spinProd_prod_bond_subgraph (A : Finset V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∑ s : ConfigSpace V, spinProd A s * ∏ e ∈ F, bond s e)
      = if HasOddBoundary F A then (2 : ℝ) ^ Fintype.card V else 0 := by
  have hint : ∀ s : ConfigSpace V,
      spinProd A s * ∏ e ∈ F, bond s e =
        ∏ v : V, (spin s v) ^ (incCount F v + if v ∈ A then 1 else 0) := by
    intro s
    rw [spinProd_eq_prod_pow, prod_bond_eq_prod_pow_incCount s F hF,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _ => by rw [pow_add]; ring)
  simp_rw [hint]
  rw [sum_prod_spin_pow]
  simp_rw [sum_spinB_pow]
  by_cases hbd : HasOddBoundary F A
  · rw [if_pos hbd]
    have heven : ∀ v : V, Even (incCount F v + if v ∈ A then 1 else 0) := by
      intro v
      by_cases hv : v ∈ A
      · rw [if_pos hv, Nat.even_add_one, Nat.not_even_iff_odd]
        exact (hbd v).2 hv
      · rw [if_neg hv, add_zero]
        exact Nat.not_odd_iff_even.mp (fun hodd => hv ((hbd v).1 hodd))
    simp_rw [if_pos (heven _)]
    rw [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hbd]
    have hex : ∃ v : V, ¬ (Odd (incCount F v) ↔ v ∈ A) := by
      simpa only [HasOddBoundary, not_forall] using hbd
    obtain ⟨v, hv⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [if_neg]
    by_cases hvmem : v ∈ A
    · rw [if_pos hvmem, Nat.even_add_one, Nat.not_even_iff_odd]
      simpa [hvmem] using hv
    · rw [if_neg hvmem, add_zero, Nat.not_even_iff_odd]
      simpa [hvmem] using hv



theorem spinProd_weight_high_temp_expansion (beta : ℝ) (A : Finset V) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G beta 0 s)
      = (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card
        * ∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
            (Real.tanh beta) ^ F.card := by
  have hweight : ∀ s : ConfigSpace V,
      isingWeight G beta 0 s =
        (Real.cosh beta) ^ G.edgeFinset.card
          * ∏ e ∈ G.edgeFinset, (1 + Real.tanh beta * bond s e) := by
    intro s
    rw [isingWeight_field_free_eq_prod, prod_exp_bond_eq]
  simp_rw [hweight]
  have hexpand : ∀ s : ConfigSpace V,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh beta * bond s e)) =
        ∑ F ∈ G.edgeFinset.powerset,
          ∏ e ∈ F, (Real.tanh beta * bond s e) := by
    intro s
    exact Finset.prod_one_add _
  simp_rw [hexpand]
  have hswap : (∑ s : ConfigSpace V,
        spinProd A s * ((Real.cosh beta) ^ G.edgeFinset.card *
          ∑ F ∈ G.edgeFinset.powerset,
            ∏ e ∈ F, (Real.tanh beta * bond s e))) =
      (Real.cosh beta) ^ G.edgeFinset.card *
        ∑ F ∈ G.edgeFinset.powerset,
          ∑ s : ConfigSpace V, spinProd A s *
            ∏ e ∈ F, (Real.tanh beta * bond s e) := by
    calc
      _ = (Real.cosh beta) ^ G.edgeFinset.card *
          ∑ s : ConfigSpace V, spinProd A s *
            (∑ F ∈ G.edgeFinset.powerset,
              ∏ e ∈ F, (Real.tanh beta * bond s e)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = (Real.cosh beta) ^ G.edgeFinset.card *
          ∑ s : ConfigSpace V, ∑ F ∈ G.edgeFinset.powerset,
            spinProd A s * ∏ e ∈ F, (Real.tanh beta * bond s e) := by
            congr 1
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_filter]
  rw [show (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card *
      (∑ F ∈ G.edgeFinset.powerset,
        if HasOddBoundary F A then (Real.tanh beta) ^ F.card else 0) =
      (Real.cosh beta) ^ G.edgeFinset.card *
        ((2 : ℝ) ^ Fintype.card V *
          ∑ F ∈ G.edgeFinset.powerset,
            if HasOddBoundary F A then (Real.tanh beta) ^ F.card else 0) by ring]
  apply congrArg ((Real.cosh beta) ^ G.edgeFinset.card * ·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull : ∀ s : ConfigSpace V,
      spinProd A s * ∏ e ∈ F, (Real.tanh beta * bond s e) =
        (Real.tanh beta) ^ F.card *
          (spinProd A s * ∏ e ∈ F, bond s e) := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  simp_rw [hpull, ← Finset.mul_sum]
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF he)
  rw [sum_spinProd_prod_bond_subgraph A F hnd]
  by_cases hbd : HasOddBoundary F A
  · rw [if_pos hbd, if_pos hbd]
    ring
  · rw [if_neg hbd, if_neg hbd]
    ring


theorem expectation_spinProd_high_temp_ratio (beta : ℝ) (A : Finset V) :
    isingExpectation G beta 0 (spinProd A) =
      (∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
          (Real.tanh beta) ^ F.card) /
        (∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
          (Real.tanh beta) ^ F.card) := by
  unfold isingExpectation isingProb
  rw [show (∑ s : ConfigSpace V, isingWeight G beta 0 s / isingZ G beta 0 * spinProd A s) =
      (∑ s : ConfigSpace V, spinProd A s * isingWeight G beta 0 s) / isingZ G beta 0 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  rw [spinProd_weight_high_temp_expansion G beta A, isingZ_high_temp_expansion G beta]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcosh : (Real.cosh beta) ^ G.edgeFinset.card ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (Real.cosh_pos beta))
  field_simp









noncomputable def highTempSubgraphWeight (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) : ℝ :=
  ∏ e ∈ F, Real.tanh (beta * J e)



theorem boltzmannJ_high_temp_factor (beta : ℝ) (J : Sym2 V → ℝ)
    (s : ConfigSpace V) :
    boltzmannJ G beta J s =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        ∏ e ∈ G.edgeFinset,
          (1 + Real.tanh (beta * J e) * bond s e) := by
  unfold boltzmannJ
  rw [Finset.mul_sum, Real.exp_sum]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [show beta * (J e * bond s e) = (beta * J e) * bond s e by ring]
  exact exp_mul_eq_cosh_mul (beta * J e) (bond s e)
    (bond_eq_one_or_neg_one s e)



theorem spinProd_boltzmannJ_high_temp_expansion (beta : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) :
    (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G beta J s) =
      (2 : ℝ) ^ Fintype.card V *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        ∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
          highTempSubgraphWeight beta J F := by
  simp_rw [boltzmannJ_high_temp_factor G beta J]
  have hexpand : ∀ s : ConfigSpace V,
      (∏ e ∈ G.edgeFinset,
          (1 + Real.tanh (beta * J e) * bond s e)) =
        ∑ F ∈ G.edgeFinset.powerset,
          ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) := by
    intro s
    exact Finset.prod_one_add _
  simp_rw [hexpand]
  have hswap :
      (∑ s : ConfigSpace V,
        spinProd A s *
          ((∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
            ∑ F ∈ G.edgeFinset.powerset,
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e))) =
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ F ∈ G.edgeFinset.powerset,
            ∑ s : ConfigSpace V, spinProd A s *
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) := by
    calc
      _ = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ s : ConfigSpace V, spinProd A s *
            (∑ F ∈ G.edgeFinset.powerset,
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ s : ConfigSpace V, ∑ F ∈ G.edgeFinset.powerset,
            spinProd A s *
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) := by
            congr 1
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap, Finset.sum_filter]
  rw [show
      (2 : ℝ) ^ Fintype.card V *
          (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          (∑ F ∈ G.edgeFinset.powerset,
            if HasOddBoundary F A then highTempSubgraphWeight beta J F else 0) =
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ((2 : ℝ) ^ Fintype.card V *
            ∑ F ∈ G.edgeFinset.powerset,
              if HasOddBoundary F A then highTempSubgraphWeight beta J F else 0) by
        ring]
  apply congrArg ((∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * ·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull : ∀ s : ConfigSpace V,
      spinProd A s *
          ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) =
        highTempSubgraphWeight beta J F *
          (spinProd A s * ∏ e ∈ F, bond s e) := by
    intro s
    unfold highTempSubgraphWeight
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hpull, ← Finset.mul_sum]
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF he)
  rw [sum_spinProd_prod_bond_subgraph A F hnd]
  by_cases hbd : HasOddBoundary F A
  · rw [if_pos hbd, if_pos hbd]
    ring
  · rw [if_neg hbd, if_neg hbd]
    ring


theorem expectationJ_high_temp_ratio (beta : ℝ) (J : Sym2 V → ℝ)
    (A : Finset V) :
    expectationJ G beta J A =
      (∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
          highTempSubgraphWeight beta J F) /
        (∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
          highTempSubgraphWeight beta J F) := by
  unfold expectationJ partitionJ
  rw [spinProd_boltzmannJ_high_temp_expansion G beta J A]
  rw [show (∑ s : ConfigSpace V, boltzmannJ G beta J s) =
      ∑ s : ConfigSpace V, spinProd (∅ : Finset V) s *
        boltzmannJ G beta J s by
      apply Finset.sum_congr rfl
      intro s _
      simp]
  rw [spinProd_boltzmannJ_high_temp_expansion G beta J ∅]
  simp_rw [hasOddBoundary_empty]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcosh : (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e _
    exact ne_of_gt (Real.cosh_pos (beta * J e))
  field_simp




noncomputable def edgeIndicatorCurrent (F : Finset (Sym2 V)) : Current V :=
  fun e => if e ∈ F then 1 else 0



theorem incidentFlux_edgeIndicatorCurrent (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) (v : V) :
    incidentFlux G (edgeIndicatorCurrent F) v = incCount F v := by
  unfold incidentFlux edgeIndicatorCurrent incCount
  rw [Finset.card_eq_sum_ones]
  symm
  calc
    ∑ e ∈ F.filter (fun e => v ∈ e), 1 =
        ∑ e ∈ F.filter (fun e => v ∈ e), if e ∈ F then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          rw [if_pos (Finset.mem_filter.mp he).1]
    _ = ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), if e ∈ F then 1 else 0 := by
      apply Finset.sum_subset
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨hF he.1, he.2⟩
      · intro e heG heF
        rw [if_neg]
        intro he
        apply heF
        exact Finset.mem_filter.mpr ⟨he, (Finset.mem_filter.mp heG).2⟩



theorem sources_edgeIndicatorCurrent (F : Finset (Sym2 V)) (A : Finset V)
    (hF : F ⊆ G.edgeFinset) (hbd : HasOddBoundary F A) :
    sources G (edgeIndicatorCurrent F) = A := by
  ext v
  rw [mem_sources, incidentFlux_edgeIndicatorCurrent G F hF v]
  exact hbd v



theorem hasOddBoundary_backbone (F : Finset (Sym2 V)) {o z : V}
    (hF : F ⊆ G.edgeFinset) (hoz : o ≠ z)
    (hbd : HasOddBoundary F {o, z}) :
    Nonempty (IsBackbonePath G (edgeIndicatorCurrent F) o z) := by
  apply shb_backbone_exists G (edgeIndicatorCurrent F) hoz
  exact sources_edgeIndicatorCurrent G F {o, z} hF hbd




theorem hasOddBoundary_firstExit (F : Finset (Sym2 V)) {o z : V}
    (hF : F ⊆ G.edgeFinset) (hoz : o ≠ z)
    (hbd : HasOddBoundary F {o, z}) (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, s(x, y) ∈ F := by
  let p := (hasOddBoundary_backbone G F hF hoz hbd).some
  obtain ⟨k, _, _, hx, hy, _, hodd, _, _⟩ := backbone_firstExit G p S ho hz
  refine ⟨p.1.getVert (k - 1), hx, p.1.getVert k, hy, ?_⟩
  by_contra hnot
  simp [edgeIndicatorCurrent, hnot] at hodd

end Sharpness
end StatMech
