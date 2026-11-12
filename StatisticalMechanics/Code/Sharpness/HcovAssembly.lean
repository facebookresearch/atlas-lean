/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Sharpness.DeltaRewriteDichotomy
import Code.Sharpness.FluxEdgeCopyDischarge
import Code.Sharpness.GhostCurrentRep
import Code.Sharpness.FieldGhostDict
import Code.Ising.CorrelationRatio

open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace StatMech
namespace Sharpness
namespace HcovAssembly

open StatMech.Sharpness (ofEdgeFun weight currentSum)
open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_switching_gap)
open StatMech.Sharpness.RandomCurrent (connK switching_disconnect_card)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]






noncomputable def hca_gap (m : ↥H.edgeFinset → ℕ) (A : Finset V) (u v : V) : ℝ :=
  if RandomCurrent.sources (endsM H m) univ = A then
    ((#((univ : Finset (Copy H m)).powerset.filter
        (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ)
      - #((univ : Finset (Copy H m)).powerset.filter
        (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v})))
   else 0




theorem hca_gap_disconn (m : ↥H.edgeFinset → ℕ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    hca_gap H m A u v
      = (if ¬ connK (endsM H m) univ u v then (1 : ℝ) else 0) * hca_gap H m A u v := by
  classical
  unfold hca_gap
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · rw [if_pos hAm]
    have hsw := switching_disconnect_card (endsM H m) (univ : Finset (Copy H m))
      (fun i _ => endsM_not_isDiag H m i) A hAm huv
    by_cases hC : connK (endsM H m) univ u v
    · 
      rw [if_neg (not_not.mpr hC)] at hsw
      have hgapR : ((#((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ)
            - #((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v}))) = 0 := by
        have hz : ((#((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℤ)
            - #((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v}))) = 0 := by omega
        exact_mod_cast hz
      rw [hgapR, if_neg (not_not.mpr hC), zero_mul]
    · rw [if_pos hC, one_mul]
  · rw [if_neg hAm, mul_zero]











noncomputable def hca_pairSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (P : (↥H.edgeFinset → ℕ) → Prop) : ℝ :=
  ∑' m : ↥H.edgeFinset → ℕ,
    (if P m then (1 : ℝ) else 0) * hca_gap H m A u v * weight H β J (ofEdgeFun H m)












theorem hca_gap_mul_weight_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (m : ↥H.edgeFinset → ℕ) :
    hca_gap H m A u v * weight H β J (ofEdgeFun H m)
      = (∑ S : Finset (Copy H m),
            (if RandomCurrent.sources (endsM H m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM H m) (univ \ S) = (∅ : Finset V) then 1 else 0))
          * weight H β J (ofEdgeFun H m)
        - (∑ S : Finset (Copy H m),
            (if RandomCurrent.sources (endsM H m) S = A ∆ {u, v} then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM H m) (univ \ S) = ({u, v} : Finset V) then 1 else 0))
          * weight H β J (ofEdgeFun H m) := by
  classical
  rw [GhostCurrentRep.gcr_pairCount_empty H m A,
    GhostCurrentRep.gcr_pairCount_pair H m A u v]
  unfold hca_gap
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · simp only [if_pos hAm, one_mul]; ring
  · simp only [if_neg hAm, zero_mul]; ring



theorem hca_summable_gap (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V) :
    Summable (fun m : ↥H.edgeFinset → ℕ =>
      hca_gap H m A u v * weight H β J (ofEdgeFun H m)) := by
  classical
  have hsum := (GhostCurrentRep.gcr_summable_edgecopy H β J A ∅).sub
    (GhostCurrentRep.gcr_summable_edgecopy H β J (A ∆ {u, v}) {u, v})
  refine hsum.congr (fun m => ?_)
  rw [hca_gap_mul_weight_eq H β J A u v m]



theorem hca_summable_pairSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (P : (↥H.edgeFinset → ℕ) → Prop) :
    Summable (fun m : ↥H.edgeFinset → ℕ =>
      (if P m then (1 : ℝ) else 0) * hca_gap H m A u v * weight H β J (ofEdgeFun H m)) := by
  classical
  refine Summable.of_norm ?_
  refine ((hca_summable_gap H β J A u v).norm).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun m => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hP : P m
  · rw [if_pos hP, one_mul]
  · rw [if_neg hP, zero_mul, zero_mul, abs_zero]; positivity







theorem hca_pairSum_add (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (P₁ P₂ : (↥H.edgeFinset → ℕ) → Prop)
    (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
    hca_pairSum H β J A u v (fun m => P₁ m ∨ P₂ m)
      = hca_pairSum H β J A u v P₁ + hca_pairSum H β J A u v P₂ := by
  classical
  unfold hca_pairSum
  rw [← Summable.tsum_add (hca_summable_pairSum H β J A u v P₁)
    (hca_summable_pairSum H β J A u v P₂)]
  refine tsum_congr (fun m => ?_)
  by_cases h1 : P₁ m <;> by_cases h2 : P₂ m
  · exact absurd ⟨h1, h2⟩ (hdisj m)
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]









theorem hca_pairSum_disconn_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    hca_pairSum H β J A u v (fun m => ¬ connK (endsM H m) univ u v)
      = sourcePairDisconnSum H β J A ∅ u v := by
  classical
  rw [sourcePairDisconnSum_eq_switching_gap H β J A u v huv]
  unfold hca_pairSum
  refine tsum_congr (fun m => ?_)
  simp only []
  
  congr 1
  
  rw [show (if RandomCurrent.sources (endsM H m) univ = A then
        ((#((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ)
          - #((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v})))
       else 0) = hca_gap H m A u v from rfl]
  convert (hca_gap_disconn H m A huv).symm using 3



theorem hca_gap_srcGate (m : ↥H.edgeFinset → ℕ) (A : Finset V) (u v : V) :
    hca_gap H m A u v
      = (if RandomCurrent.sources (endsM H m) univ = A then (1 : ℝ) else 0) * hca_gap H m A u v := by
  classical
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · rw [if_pos hAm, one_mul]
  · conv_lhs => unfold hca_gap
    rw [if_neg hAm, if_neg hAm, zero_mul]






theorem hca_pairSum_disconn_conj_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    hca_pairSum H β J A u v
        (fun m => RandomCurrent.sources (endsM H m) univ = A ∧ ¬ connK (endsM H m) univ u v)
      = sourcePairDisconnSum H β J A ∅ u v := by
  classical
  rw [← hca_pairSum_disconn_eq H β J A huv]
  unfold hca_pairSum
  refine tsum_congr (fun m => ?_)
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · 
    by_cases hC : connK (endsM H m) univ u v <;> simp [hAm, hC]
  · 
    have hg0 : hca_gap H m A u v = 0 := by unfold hca_gap; rw [if_neg hAm]
    rw [hg0]; ring
























theorem hca_sourcePairDisconn_deltaRewrite (β : ℝ) (J : Sym2 V → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    sourcePairDisconnSum H β J ({o, x, y, g} : Finset V) ∅ o g
      = hca_pairSum H β J ({o, x, y, g} : Finset V) o g
          (fun m => (RandomCurrent.sources (endsM H m) univ = {o, x, y, g}
              ∧ ¬ connK (endsM H m) univ o g)
            ∧ (connK (endsM H m) univ o x ∧ connK (endsM H m) univ y g))
        + hca_pairSum H β J ({o, x, y, g} : Finset V) o g
            (fun m => (RandomCurrent.sources (endsM H m) univ = {o, x, y, g}
                ∧ ¬ connK (endsM H m) univ o g)
              ∧ (connK (endsM H m) univ o y ∧ connK (endsM H m) univ x g)) := by
  classical
  rw [← hca_pairSum_disconn_conj_eq H β J ({o, x, y, g} : Finset V) hog]
  refine sdr_deltaRewrite_perEdge
    (hca_pairSum H β J ({o, x, y, g} : Finset V) o g
      (fun m => RandomCurrent.sources (endsM H m) univ = {o, x, y, g} ∧ ¬ connK (endsM H m) univ o g))
    (hca_pairSum H β J ({o, x, y, g} : Finset V) o g)
    (fun P₁ P₂ _ _ _ hdisj => hca_pairSum_add H β J ({o, x, y, g} : Finset V) o g P₁ P₂ hdisj)
    (disconn := fun m =>
      RandomCurrent.sources (endsM H m) univ = {o, x, y, g} ∧ ¬ connK (endsM H m) univ o g)
    (caseA := fun m => connK (endsM H m) univ o x ∧ connK (endsM H m) univ y g)
    (caseB := fun m => connK (endsM H m) univ o y ∧ connK (endsM H m) univ x g)
    rfl ?_
  
  rintro m ⟨hsrc, hdisc⟩
  exact RandomCurrent.disconnect_dichotomy_prop (endsM H m) univ
    (fun i _ => endsM_not_isDiag H m i) hox hoy hog hxy hxg hyg hsrc hdisc









open StatMech.Ising (isingExpectation spinProd)
open StatMech.Sharpness.FieldGhostDict (ghostCoupling someEmb
  fgd_ghostCurrentRep_unconditional fgd_isingExpectation_eq_currentSum_ratio
  fgd_isingExpectation_eq_currentSum_ratio_odd someEmb_apply)

variable (G : SimpleGraph V) [DecidableRel G.Adj]











noncomputable def hcaBondSource (o : V) : Sym2 V -> Finset (Option V) :=
  Sym2.lift <| by
    refine ⟨fun x y => insert none ((({o} : Finset V) ∆ {x, y}).map someEmb), ?_⟩
    intro x y
    simp [Finset.pair_comm]

@[simp] theorem hcaBondSource_mk (o x y : V) :
    hcaBondSource o s(x, y) = insert none ((({o} : Finset V) ∆ {x, y}).map someEmb) := rfl


noncomputable def hcaBondDelta (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
    (hcaBondSource o e) ∅ (some o) none


noncomputable def hcaFieldSource (o z : V) : Finset (Option V) :=
  ((({o} : Finset V) ∆ {z}).map someEmb)


noncomputable def hcaFieldDelta (β h : ℝ) (o z : V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
    (hcaFieldSource o z) ∅ (some o) none

private theorem odd_card_singleton_symmDiff_pair (o x y : V) (hxy : x ≠ y) :
    Odd ((({o} : Finset V) ∆ {x, y}).card) := by
  classical
  by_cases hox : o = x
  · subst x
    have heq : ({o} : Finset V) ∆ {o, y} = {y} := by
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      aesop
    rw [heq]
    simp
  · by_cases hoy : o = y
    · subst y
      have heq : ({o} : Finset V) ∆ {x, o} = {x} := by
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        aesop
      rw [heq]
      simp
    · have heq : ({o} : Finset V) ∆ {x, y} = {o, x, y} := by
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        aesop
      rw [heq, Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      decide

private theorem even_card_singleton_symmDiff_singleton (o z : V) :
    Even ((({o} : Finset V) ∆ {z}).card) := by
  classical
  by_cases hoz : o = z
  · subst z
    simp
  · have heq : ({o} : Finset V) ∆ {z} = {o, z} := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      aesop
    rw [heq, Finset.card_insert_of_notMem (by simp [hoz]), Finset.card_singleton]
    decide



theorem hca_bond_covariance_sourcePair (β h : ℝ) (o x y : V) (hxy : x ≠ y)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h
              (spinProd (({o} : Finset V) ∆ {x, y}))
            - isingExpectation G β h (spinProd ({x, y} : Finset V))
              * isingExpectation G β h (spinProd ({o} : Finset V)))
      = hcaBondDelta G β h o s(x, y) := by
  classical
  let S : Finset V := ({o} : Finset V) ∆ {x, y}
  let A : Finset (Option V) := insert none (S.map someEmb)
  have hSodd : Odd S.card := odd_card_singleton_symmDiff_pair o x y hxy
  have hpair : Even (({x, y} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    decide
  have hsingle : Odd (({o} : Finset V).card) := by simp
  have hrepS := fgd_isingExpectation_eq_currentSum_ratio_odd G β h S hSodd
  have hrepPair := fgd_isingExpectation_eq_currentSum_ratio G β h
    ({x, y} : Finset V) hpair
  have hrepO := fgd_isingExpectation_eq_currentSum_ratio_odd G β h
    ({o} : Finset V) hsingle
  have hdiff : A ∆ {some o, none} = ({x, y} : Finset V).map someEmb := by
    ext z
    cases z with
    | none => simp [A, Finset.mem_symmDiff, someEmb]
    | some w =>
        simp only [A, S, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_map, someEmb_apply,
          Option.some.injEq, Option.some_ne_none, false_or]
        simp only [exists_eq_right]
        tauto
  have hpairSource : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext z
    simp [someEmb]
    aesop
  change isingExpectation G β h (spinProd S) =
    currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) A /
      currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ at hrepS
  rw [← hdiff] at hrepPair
  rw [← hpairSource] at hrepO
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β (fun _ => 1)) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    (isingExpectation G β h (spinProd S))
    (isingExpectation G β h (spinProd ({x, y} : Finset V)))
    (isingExpectation G β h (spinProd ({o} : Finset V)))
    rfl hZne hrepS hrepPair hrepO
  simpa [hcaBondDelta, hcaBondSource, A, S] using hgcr



theorem hca_field_covariance_sourcePair (β h : ℝ) (o z : V)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h
              (spinProd (({o} : Finset V) ∆ {z}))
            - isingExpectation G β h (spinProd ({z} : Finset V))
              * isingExpectation G β h (spinProd ({o} : Finset V)))
      = hcaFieldDelta G β h o z := by
  classical
  let S : Finset V := ({o} : Finset V) ∆ {z}
  let A : Finset (Option V) := S.map someEmb
  have hSeven : Even S.card := even_card_singleton_symmDiff_singleton o z
  have hsingleZ : Odd (({z} : Finset V).card) := by simp
  have hsingleO : Odd (({o} : Finset V).card) := by simp
  have hrepS := fgd_isingExpectation_eq_currentSum_ratio G β h S hSeven
  have hrepZ := fgd_isingExpectation_eq_currentSum_ratio_odd G β h
    ({z} : Finset V) hsingleZ
  have hrepO := fgd_isingExpectation_eq_currentSum_ratio_odd G β h
    ({o} : Finset V) hsingleO
  have hdiff : A ∆ {some o, none} =
      insert none (({z} : Finset V).map someEmb) := by
    ext w
    cases w with
    | none => simp [A, Finset.mem_symmDiff, someEmb]
    | some v =>
        simp only [A, S, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_map, someEmb_apply,
          Option.some.injEq, Option.some_ne_none, false_or]
        simp only [exists_eq_right]
        tauto
  have hpairSource : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext w
    simp [someEmb]
    aesop
  change isingExpectation G β h (spinProd S) =
    currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) A /
      currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ at hrepS
  rw [← hdiff] at hrepZ
  rw [← hpairSource] at hrepO
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β (fun _ => 1)) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    (isingExpectation G β h (spinProd S))
    (isingExpectation G β h (spinProd ({z} : Finset V)))
    (isingExpectation G β h (spinProd ({o} : Finset V)))
    rfl hZne hrepS hrepZ hrepO
  simpa [hcaFieldDelta, hcaFieldSource, A, S] using hgcr

private theorem spin_mul_bond_eq_spinProd (o x y : V) (hxy : x ≠ y) :
    (fun s : ConfigSpace V => Ising.spin s o * Ising.bond s s(x, y)) =
      spinProd (({o} : Finset V) ∆ {x, y}) := by
  funext s
  rw [show Ising.spin s o = spinProd ({o} : Finset V) s by simp [spinProd],
    show Ising.bond s s(x, y) = spinProd ({x, y} : Finset V) s by
      rw [Ising.bond_mk, spinProd, Finset.prod_pair hxy],
    Ising.spinProd_mul_self]

private theorem bond_eq_spinProd (x y : V) (hxy : x ≠ y) :
    (fun s : ConfigSpace V => Ising.bond s s(x, y)) = spinProd ({x, y} : Finset V) := by
  funext s
  rw [Ising.bond_mk, spinProd, Finset.prod_pair hxy]

private theorem spin_mul_spin_eq_spinProd (o z : V) :
    (fun s : ConfigSpace V => Ising.spin s o * Ising.spin s z) =
      spinProd (({o} : Finset V) ∆ {z}) := by
  funext s
  rw [show Ising.spin s o = spinProd ({o} : Finset V) s by simp [spinProd],
    show Ising.spin s z = spinProd ({z} : Finset V) s by simp [spinProd],
    Ising.spinProd_mul_self]

private theorem spin_eq_spinProd (z : V) :
    (fun s : ConfigSpace V => Ising.spin s z) = spinProd ({z} : Finset V) := by
  funext s
  simp [spinProd]


theorem hca_bond_covariance_eq_delta (β h : ℝ) (o : V) (e : Sym2 V)
    (he : e ∈ G.edgeFinset)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h (fun s => Ising.spin s o * Ising.bond s e)
            - isingExpectation G β h (fun s => Ising.bond s e)
              * isingExpectation G β h (fun s => Ising.spin s o))
      = hcaBondDelta G β h o e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : G.Adj x y := by simpa using (SimpleGraph.mem_edgeFinset.mp he)
      have hxy : x ≠ y := G.ne_of_adj hadj
      rw [spin_mul_bond_eq_spinProd o x y hxy, bond_eq_spinProd x y hxy,
        spin_eq_spinProd o]
      exact hca_bond_covariance_sourcePair G β h o x y hxy hZne



theorem hca_field_covariance_eq_delta (β h : ℝ) (o z : V)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h (fun s => Ising.spin s o * Ising.spin s z)
            - isingExpectation G β h (fun s => Ising.spin s z)
              * isingExpectation G β h (fun s => Ising.spin s o))
      = hcaFieldDelta G β h o z := by
  rw [spin_mul_spin_eq_spinProd o z, spin_eq_spinProd z, spin_eq_spinProd o]
  exact hca_field_covariance_sourcePair G β h o z hZne






theorem hca_deriv_magnetization_eq_currentDelta (β h : ℝ) (o : V) :
    HasDerivAt (fun β => isingExpectation G β h (fun s => Ising.spin s o))
      ((1 / (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2) *
        ((∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e)
          + h * ∑ z, hcaFieldDelta G β h o z)) β := by
  classical
  let Z : ℝ := currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅
  let bondCov : Sym2 V -> ℝ := fun e =>
    isingExpectation G β h (fun s => Ising.spin s o * Ising.bond s e)
      - isingExpectation G β h (fun s => Ising.spin s o)
        * isingExpectation G β h (fun s => Ising.bond s e)
  let fieldCov : V -> ℝ := fun z =>
    isingExpectation G β h (fun s => Ising.spin s o * Ising.spin s z)
      - isingExpectation G β h (fun s => Ising.spin s o)
        * isingExpectation G β h (fun s => Ising.spin s z)
  have hZpos : 0 < Z := Ising.acr_currentSum_empty_pos (withGhost G) β
    (ghostCoupling h β (fun _ => 1))
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hbond (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      Z ^ 2 * bondCov e = hcaBondDelta G β h o e := by
    simpa [Z, bondCov, mul_comm] using hca_bond_covariance_eq_delta G β h o e he hZne
  have hfield (z : V) : Z ^ 2 * fieldCov z = hcaFieldDelta G β h o z := by
    simpa [Z, fieldCov, mul_comm] using hca_field_covariance_eq_delta G β h o z hZne
  have hbondSum :
      Z ^ 2 * (∑ e ∈ G.edgeFinset, bondCov e) =
        ∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hbond
  have hfieldSum :
      Z ^ 2 * (∑ z, fieldCov z) = ∑ z, hcaFieldDelta G β h o z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hfield z)
  have hscaled :
      Z ^ 2 * ((∑ e ∈ G.edgeFinset, bondCov e) + h * ∑ z, fieldCov z) =
        (∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e)
          + h * ∑ z, hcaFieldDelta G β h o z := by
    calc
      Z ^ 2 * ((∑ e ∈ G.edgeFinset, bondCov e) + h * ∑ z, fieldCov z) =
          Z ^ 2 * (∑ e ∈ G.edgeFinset, bondCov e)
            + h * (Z ^ 2 * ∑ z, fieldCov z) := by ring
      _ = (∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e)
            + h * ∑ z, hcaFieldDelta G β h o z := by rw [hbondSum, hfieldSum]
  have hvalue :
      (∑ e ∈ G.edgeFinset, bondCov e) + h * ∑ z, fieldCov z =
        (1 / Z ^ 2) * ((∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e)
          + h * ∑ z, hcaFieldDelta G β h o z) := by
    rw [← hscaled]
    field_simp
  have hd := sdr_deriv_magnetization_eq_bondCov G β h o
  change HasDerivAt (fun β => isingExpectation G β h (fun s => Ising.spin s o))
    ((1 / Z ^ 2) * ((∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e)
      + h * ∑ z, hcaFieldDelta G β h o z)) β
  rw [← hvalue]
  simpa [bondCov, fieldCov] using hd










theorem hca_odd_bond_covariance_sourcePair (β h : ℝ)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h (spinProd ({o, x, y} : Finset V))
            - isingExpectation G β h (spinProd ({x, y} : Finset V))
              * isingExpectation G β h (spinProd ({o} : Finset V)))
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V)) ∅ (some o) none := by
  classical
  have htriple : Odd (({o, x, y} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    decide
  have hpair : Even (({x, y} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    decide
  have hsingle : Odd (({o} : Finset V).card) := by simp
  have hrep3 := fgd_isingExpectation_eq_currentSum_ratio_odd G β h
    ({o, x, y} : Finset V) htriple
  have hrep1 := fgd_isingExpectation_eq_currentSum_ratio G β h
    ({x, y} : Finset V) hpair
  have hrep2 := fgd_isingExpectation_eq_currentSum_ratio_odd G β h
    ({o} : Finset V) hsingle
  let A : Finset (Option V) := insert none (({o, x, y} : Finset V).map someEmb)
  have hA : A = ({some o, some x, some y, none} : Finset (Option V)) := by
    ext z
    simp [A, someEmb]
    aesop
  have hdiff : A ∆ {some o, none} =
      (({x, y} : Finset V).map someEmb) := by
    rw [hA]
    have hsox : (some o : Option V) ≠ some x := by simpa using hox
    have hsoy : (some o : Option V) ≠ some y := by simpa using hoy
    have hsxy : (some x : Option V) ≠ some y := by simpa using hxy
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_map, someEmb_apply]
    aesop
  have hsingleMap : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext z
    simp [someEmb]
    aesop
  change isingExpectation G β h (spinProd ({o, x, y} : Finset V)) =
    currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) A /
      currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ at hrep3
  rw [← hdiff] at hrep1
  rw [← hsingleMap] at hrep2
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β (fun _ => 1)) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    (isingExpectation G β h (spinProd ({o, x, y} : Finset V)))
    (isingExpectation G β h (spinProd ({x, y} : Finset V)))
    (isingExpectation G β h (spinProd ({o} : Finset V)))
    rfl hZne hrep3 hrep1 hrep2
  rwa [hA] at hgcr





theorem hca_odd_bond_covariance_deltaRewrite (β h : ℝ)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h (spinProd ({o, x, y} : Finset V))
            - isingExpectation G β h (spinProd ({x, y} : Finset V))
              * isingExpectation G β h (spinProd ({o} : Finset V)))
      = hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V)) (some o) none
          (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ
                = {some o, some x, some y, none}
              ∧ ¬ connK (endsM (withGhost G) m) univ (some o) none)
            ∧ (connK (endsM (withGhost G) m) univ (some o) (some x)
                ∧ connK (endsM (withGhost G) m) univ (some y) none))
        + hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            ({some o, some x, some y, none} : Finset (Option V)) (some o) none
            (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ
                  = {some o, some x, some y, none}
                ∧ ¬ connK (endsM (withGhost G) m) univ (some o) none)
              ∧ (connK (endsM (withGhost G) m) univ (some o) (some y)
                  ∧ connK (endsM (withGhost G) m) univ (some x) none)) := by
  rw [hca_odd_bond_covariance_sourcePair G β h hox hoy hxy hZne]
  exact hca_sourcePairDisconn_deltaRewrite (withGhost G) β
    (ghostCoupling h β (fun _ => 1))
    (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp)

























theorem hca_covariance_deltaRewrite (β h : ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h (spinProd ({o, x, y, g} : Finset V))
            - isingExpectation G β h (spinProd ({x, y} : Finset V))
              * isingExpectation G β h (spinProd ({o, g} : Finset V)))
      = hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, some g} : Finset (Option V)) (some o) (some g)
          (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ
                = {some o, some x, some y, some g}
              ∧ ¬ connK (endsM (withGhost G) m) univ (some o) (some g))
            ∧ (connK (endsM (withGhost G) m) univ (some o) (some x)
                ∧ connK (endsM (withGhost G) m) univ (some y) (some g)))
        + hca_pairSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            ({some o, some x, some y, some g} : Finset (Option V)) (some o) (some g)
            (fun m => (RandomCurrent.sources (endsM (withGhost G) m) univ
                  = {some o, some x, some y, some g}
                ∧ ¬ connK (endsM (withGhost G) m) univ (some o) (some g))
              ∧ (connK (endsM (withGhost G) m) univ (some o) (some y)
                  ∧ connK (endsM (withGhost G) m) univ (some x) (some g))) := by
  classical
  
  have hsox : (some o : Option V) ≠ some x := fun hc => hox (Option.some_injective V hc)
  have hsoy : (some o : Option V) ≠ some y := fun hc => hoy (Option.some_injective V hc)
  have hsog : (some o : Option V) ≠ some g := fun hc => hog (Option.some_injective V hc)
  have hsxy : (some x : Option V) ≠ some y := fun hc => hxy (Option.some_injective V hc)
  have hsxg : (some x : Option V) ≠ some g := fun hc => hxg (Option.some_injective V hc)
  have hsyg : (some y : Option V) ≠ some g := fun hc => hyg (Option.some_injective V hc)
  
  
  
  have hAeven : Even (({o, x, y, g} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hox, hoy, hog]),
      Finset.card_insert_of_notMem (by simp [hxy, hxg]),
      Finset.card_insert_of_notMem (by simp [hyg]), Finset.card_singleton]
    decide
  have hdiff : ({o, x, y, g} : Finset V) ∆ {o, g} = {x, y} := by
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rcases h1 with rfl | rfl | rfl | rfl
        · exact absurd (Or.inl rfl) h2
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd (Or.inr rfl) h2
      · rcases h1 with rfl | rfl <;> simp_all
    · rintro (rfl | rfl)
      · exact Or.inl ⟨Or.inr (Or.inl rfl), by simp [hox.symm, hxg]⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), by simp [hoy.symm, hyg]⟩
  have hAuvEven : Even ((({o, x, y, g} : Finset V) ∆ {o, g}).card) := by
    rw [hdiff, Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    decide
  have huvEven : Even (({o, g} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hog]), Finset.card_singleton]
    decide
  have hfgd := fgd_ghostCurrentRep_unconditional G β h ({o, x, y, g} : Finset V)
    hog hAeven hAuvEven huvEven hZne
  
  rw [hdiff] at hfgd
  
  have hmap : ({o, x, y, g} : Finset V).map someEmb
      = ({some o, some x, some y, some g} : Finset (Option V)) := by
    ext z; simp [someEmb]
  rw [hmap] at hfgd
  rw [hfgd]
  
  exact hca_sourcePairDisconn_deltaRewrite (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hsox hsoy hsog hsxy hsxg hsyg















theorem hca_pairSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJnn : ∀ e, 0 ≤ J e)
    (A : Finset V) {u v : V} (huv : u ≠ v)
    (P : (↥H.edgeFinset → ℕ) → Prop) (hP : ∀ m, P m → ¬ connK (endsM H m) univ u v) :
    0 ≤ hca_pairSum H β J A u v P := by
  classical
  unfold hca_pairSum
  refine tsum_nonneg (fun m => ?_)
  
  have hw : 0 ≤ weight H β J (ofEdgeFun H m) := by
    unfold weight
    refine Finset.prod_nonneg (fun e _ => ?_)
    have hbJ : 0 ≤ β * J e := mul_nonneg hβ (hJnn e)
    positivity
  
  by_cases hPm : P m
  · 
    rw [if_pos hPm, one_mul]
    refine mul_nonneg ?_ hw
    have hdisc := hP m hPm
    rw [hca_gap_disconn H m A huv, if_pos hdisc, one_mul]
    unfold hca_gap
    by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
    · rw [if_pos hAm]
      
      have hsw := switching_disconnect_card (endsM H m) (univ : Finset (Copy H m))
        (fun i _ => endsM_not_isDiag H m i) A hAm huv
      rw [if_pos hdisc] at hsw
      have heq : ((#((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ)
          - #((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v})))
          = (#((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ) := by
        exact_mod_cast hsw
      rw [heq]; positivity
    · rw [if_neg hAm]
  · rw [if_neg hPm, zero_mul, zero_mul]

private theorem ghostCoupling_one_nonneg (β h : ℝ) (hh : 0 ≤ h) :
    ∀ e : Sym2 (Option V), 0 ≤ ghostCoupling h β (fun _ => 1) e := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      cases a <;> cases b <;> simp [ghostCoupling, hh]



theorem hcaBondDelta_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (e : Sym2 V) : 0 ≤ hcaBondDelta G β h o e := by
  rw [hcaBondDelta, ← hca_pairSum_disconn_eq (withGhost G) β
    (ghostCoupling h β (fun _ => 1)) (hcaBondSource o e) (by simp)]
  exact hca_pairSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hβ (ghostCoupling_one_nonneg β h hh) (hcaBondSource o e) (by simp)
    (fun m => ¬ connK (endsM (withGhost G) m) univ (some o) none) (fun _ hm => hm)



theorem hcaFieldDelta_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o z : V) : 0 ≤ hcaFieldDelta G β h o z := by
  rw [hcaFieldDelta, ← hca_pairSum_disconn_eq (withGhost G) β
    (ghostCoupling h β (fun _ => 1)) (hcaFieldSource o z) (by simp)]
  exact hca_pairSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hβ (ghostCoupling_one_nonneg β h hh) (hcaFieldSource o z) (by simp)
    (fun m => ¬ connK (endsM (withGhost G) m) univ (some o) none) (fun _ hm => hm)


theorem hca_currentDelta_derivative_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) :
    0 ≤ (1 / (currentSum (withGhost G) β
          (ghostCoupling h β (fun _ => 1)) ∅) ^ 2) *
      ((∑ e ∈ G.edgeFinset, hcaBondDelta G β h o e)
        + h * ∑ z, hcaFieldDelta G β h o z) := by
  have hZpos := Ising.acr_currentSum_empty_pos (withGhost G) β
    (ghostCoupling h β (fun _ => 1))
  refine mul_nonneg (by positivity) (add_nonneg ?_ (mul_nonneg hh ?_))
  · exact Finset.sum_nonneg (fun e _ => hcaBondDelta_nonneg G β h hβ hh o e)
  · exact Finset.sum_nonneg (fun z _ => hcaFieldDelta_nonneg G β h hβ hh o z)









theorem hca_sourcePairDisconn_deltaRewrite_nonvacuous :
    sourcePairDisconnSum (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1)
        ({0, 1, 2, 3} : Finset (Fin 4)) ∅ 0 3
      = hca_pairSum (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({0, 1, 2, 3} : Finset (Fin 4)) 0 3
          (fun m => (RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 4)) m) univ = {0, 1, 2, 3}
              ∧ ¬ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 3)
            ∧ (connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 1
                ∧ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 2 3))
        + hca_pairSum (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1) ({0, 1, 2, 3} : Finset (Fin 4)) 0 3
            (fun m => (RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 4)) m) univ = {0, 1, 2, 3}
                ∧ ¬ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 3)
              ∧ (connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 0 2
                  ∧ connK (endsM (⊤ : SimpleGraph (Fin 4)) m) univ 1 3)) :=
  hca_sourcePairDisconn_deltaRewrite (⊤ : SimpleGraph (Fin 4)) 1 (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end HcovAssembly
end Sharpness
end StatMech
