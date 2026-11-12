/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib
import Code.Sharpness.Claim1IsingFull
import Code.Sharpness.ClaimIsingFull
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.Simon
import Code.Ising.CorrelationRatio

open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech
namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





theorem symmDiff_eq_symmDiff_iff_of_separated (S X Y A B : Finset V)
    (hXS : X ⊆ S) (hYS : Y ⊆ Sᶜ) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ) :
    X ∆ Y = A ∆ B ↔ X = A ∧ Y = B := by
  constructor
  · intro h
    constructor <;> ext v
    · have hv := Finset.ext_iff.mp h v
      by_cases hs : v ∈ S
      · have hny : v ∉ Y := fun hy => (Finset.mem_compl.mp (hYS hy)) hs
        have hnb : v ∉ B := fun hb => (Finset.mem_compl.mp (hBS hb)) hs
        simp only [Finset.mem_symmDiff] at hv
        simpa [hny, hnb] using hv
      · have hnx : v ∉ X := fun hx => hs (hXS hx)
        have hna : v ∉ A := fun ha => hs (hAS ha)
        simp [hnx, hna]
    · have hv := Finset.ext_iff.mp h v
      by_cases hs : v ∈ S
      · have hny : v ∉ Y := fun hy => (Finset.mem_compl.mp (hYS hy)) hs
        have hnb : v ∉ B := fun hb => (Finset.mem_compl.mp (hBS hb)) hs
        simp [hny, hnb]
      · have hnx : v ∉ X := fun hx => hs (hXS hx)
        have hna : v ∉ A := fun ha => hs (hAS ha)
        simp only [Finset.mem_symmDiff] at hv
        simpa [hnx, hna] using hv
  · rintro ⟨rfl, rfl⟩
    rfl


theorem sources_reEdge_eq_symmDiff_iff (S A B : Finset V)
    (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ)
    (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)
    (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V)) :
    sources G (ofEdgeFun G (reEdge G S (a, b))) = A ∆ B ↔
      sources G (ofEdgeFun G (aFull G S a)) = A ∧
        sources G (ofEdgeFun G (bFull G S b)) = B := by
  rw [sources_reEdge_split]
  exact symmDiff_eq_symmDiff_iff_of_separated S _ _ A B
    (sources_aFull_subset G S a) (sources_bFull_subset_compl G S b hcross) hAS hBS




noncomputable def claim1Context (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V)
    (bd : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) : ℝ :=
  (if sources G (ofEdgeFun G (bFull G S bd.1)) = B
      then weight G β J (ofEdgeFun G (bFull G S bd.1)) else 0) *
    (if sources G (ofEdgeFun G (bFull G S bd.2)) = D
      then weight G β J (ofEdgeFun G (bFull G S bd.2)) else 0) *
    (if P (fun e => ofEdgeFun G (bFull G S bd.1) e +
        ofEdgeFun G (bFull G S bd.2) e) then 1 else 0)



noncomputable def pairCutEquiv (S : Finset V) :
    ((({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) ×
      (({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ))) ≃
    ((({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // isIn G S i} → ℕ)) ×
      (({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ))) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv := by rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩; rfl


theorem claim1_summand_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A B C D : Finset V) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (hCS : C ⊆ S) (hDS : D ⊆ Sᶜ)
    (a c : {i : ↥G.edgeFinset // isIn G S i} → ℕ)
    (b d : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) :
    (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A ∆ B
        then weight G β J (ofEdgeFun G (reEdge G S (a, b))) else 0) *
      (if sources G (ofEdgeFun G (reEdge G S (c, d))) = C ∆ D
        then weight G β J (ofEdgeFun G (reEdge G S (c, d))) else 0) *
      (if P (fun e => ofEdgeFun G (reEdge G S (a, b)) e +
          ofEdgeFun G (reEdge G S (c, d)) e) then 1 else 0)
    = factorSummand G β J S A a * factorSummand G β J S C c *
        claim1Context G β J S P B D (b, d) := by
  let m : Current V := fun e => ofEdgeFun G (reEdge G S (a, b)) e +
    ofEdgeFun G (reEdge G S (c, d)) e
  let m' : Current V := fun e => ofEdgeFun G (bFull G S b) e +
    ofEdgeFun G (bFull G S d) e
  have hP : P m ↔ P m' := by
    apply H2
    intro i _ hi
    have hab : ofEdgeFun G (reEdge G S (a, b)) i = ofEdgeFun G (bFull G S b) i := by
      unfold ofEdgeFun
      by_cases he : i ∈ G.edgeFinset
      · rw [dif_pos he, dif_pos he, reEdge_eq_add, aFull, dif_neg (by unfold isIn; exact hi), zero_add]
      · rw [dif_neg he, dif_neg he]
    have hcd : ofEdgeFun G (reEdge G S (c, d)) i = ofEdgeFun G (bFull G S d) i := by
      unfold ofEdgeFun
      by_cases he : i ∈ G.edgeFinset
      · rw [dif_pos he, dif_pos he, reEdge_eq_add, aFull, dif_neg (by unfold isIn; exact hi), zero_add]
      · rw [dif_neg he, dif_neg he]
    exact congrArg₂ (· + ·) hab hcd
  by_cases hev : P m'
  · have hnc : NoCrossing G m S := H1 m (hP.mpr hev)
    have hbCross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V) := by
      intro i hipos
      have hsuper : 1 ≤ m i.1 := by
        have hle : bFull G S b i ≤ ofEdgeFun G (reEdge G S (a, b)) i.1 := by
          rw [show ofEdgeFun G (reEdge G S (a, b)) i.1 = reEdge G S (a, b) i from by
            unfold ofEdgeFun; rw [dif_pos i.2], reEdge_eq_add]
          omega
        simp only [m]; omega
      rcases hnc i.1 i.2 hsuper with hi | hi
      · exfalso
        have hni : ¬ isIn G S i := by
          intro his
          unfold bFull at hipos
          rw [dif_pos his] at hipos
          omega
        exact hni hi
      · exact hi
    have hdCross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S d i → edgeInside Sᶜ (i : Sym2 V) := by
      intro i hipos
      have hsuper : 1 ≤ m i.1 := by
        have hle : bFull G S d i ≤ ofEdgeFun G (reEdge G S (c, d)) i.1 := by
          rw [show ofEdgeFun G (reEdge G S (c, d)) i.1 = reEdge G S (c, d) i from by
            unfold ofEdgeFun; rw [dif_pos i.2], reEdge_eq_add]
          omega
        simp only [m]; omega
      rcases hnc i.1 i.2 hsuper with hi | hi
      · exfalso
        have hni : ¬ isIn G S i := by
          intro his
          unfold bFull at hipos
          rw [dif_pos his] at hipos
          omega
        exact hni hi
      · exact hi
    have hsrc1 := sources_reEdge_eq_symmDiff_iff G S A B hAS hBS a b hbCross
    have hsrc2 := sources_reEdge_eq_symmDiff_iff G S C D hCS hDS c d hdCross
    unfold factorSummand claim1Context
    change P (fun e => ofEdgeFun G (bFull G S b) e +
      ofEdgeFun G (bFull G S d) e) at hev
    have hevFull : P (fun e => ofEdgeFun G (reEdge G S (a, b)) e +
        ofEdgeFun G (reEdge G S (c, d)) e) := hP.mpr hev
    rw [if_pos hev, if_pos hevFull]
    simp only [weight_reEdge_split]
    by_cases ha : sources G (ofEdgeFun G (aFull G S a)) = A <;>
      by_cases hb : sources G (ofEdgeFun G (bFull G S b)) = B <;>
      by_cases hc : sources G (ofEdgeFun G (aFull G S c)) = C <;>
      by_cases hd : sources G (ofEdgeFun G (bFull G S d)) = D <;>
      simp [hsrc1, hsrc2, ha, hb, hc, hd] <;> ring
  · have hnfull : ¬ P m := fun h => hev (hP.mp h)
    unfold claim1Context
    change ¬ P (fun e => ofEdgeFun G (bFull G S b) e +
      ofEdgeFun G (bFull G S d) e) at hev
    change ¬ P (fun e => ofEdgeFun G (reEdge G S (a, b)) e +
      ofEdgeFun G (reEdge G S (c, d)) e) at hnfull
    rw [if_neg hev, if_neg hnfull]
    ring



theorem norm_claim1Context_le (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V)
    (bd : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) :
    ‖claim1Context G β J S P B D bd‖ ≤
      ‖weight G β J (ofEdgeFun G (bFull G S bd.1))‖ *
        ‖weight G β J (ofEdgeFun G (bFull G S bd.2))‖ :=
  norm_triple_le _ _ _ _ _

theorem summable_claim1Context (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V) :
    Summable (claim1Context G β J S P B D) := by
  have hdom : Summable (fun bd :
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) =>
      ‖weight G β J (ofEdgeFun G (bFull G S bd.1))‖ *
        ‖weight G β J (ofEdgeFun G (bFull G S bd.2))‖) :=
    Summable.mul_of_nonneg (summable_norm_weight_bFull G β J S)
      (summable_norm_weight_bFull G β J S) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_claim1Context_le G β J S P B D))

theorem summable_claim1Interior (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (A C : Finset V) :
    Summable (fun ac :
      ({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // isIn G S i} → ℕ) =>
      factorSummand G β J S A ac.1 * factorSummand G β J S C ac.2) :=
  summable_mul_of_summable_norm
    ((summable_factorSummand G β J S A).norm)
    ((summable_factorSummand G β J S C).norm)



theorem claim1_pairSum_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A B C D : Finset V) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (hCS : C ⊆ S) (hDS : D ⊆ Sᶜ) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      (if sources G (ofEdgeFun G pq.1) = A ∆ B then weight G β J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = C ∆ D then weight G β J (ofEdgeFun G pq.2) else 0) *
        (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0))
    = currentSum G β (couplingIn J S) A * currentSum G β (couplingIn J S) C *
        (∑' bd, claim1Context G β J S P B D bd) := by
  let E := Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ : ↥G.edgeFinset => ℕ)
  let E2 := E.prodCongr E
  rw [← E2.symm.tsum_eq]
  have hsummand : ∀ q,
      ((if sources G (ofEdgeFun G (E2.symm q).1) = A ∆ B
          then weight G β J (ofEdgeFun G (E2.symm q).1) else 0) *
        (if sources G (ofEdgeFun G (E2.symm q).2) = C ∆ D
          then weight G β J (ofEdgeFun G (E2.symm q).2) else 0) *
        (if P (fun e => ofEdgeFun G (E2.symm q).1 e + ofEdgeFun G (E2.symm q).2 e)
          then 1 else 0)) =
      factorSummand G β J S A q.1.1 * factorSummand G β J S C q.2.1 *
        claim1Context G β J S P B D (q.1.2, q.2.2) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    exact claim1_summand_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS a c b d
  rw [tsum_congr hsummand]
  have hgroup : ∀ q,
      factorSummand G β J S A q.1.1 * factorSummand G β J S C q.2.1 *
          claim1Context G β J S P B D (q.1.2, q.2.2) =
        (fun r =>
          (factorSummand G β J S A r.1.1 * factorSummand G β J S C r.1.2) *
            claim1Context G β J S P B D r.2) (pairCutEquiv G S q) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  rw [tsum_congr hgroup]
  rw [(pairCutEquiv G S).tsum_eq (fun r =>
    (factorSummand G β J S A r.1.1 * factorSummand G β J S C r.1.2) *
      claim1Context G β J S P B D r.2)]
  have hi := summable_claim1Interior G β J S A C
  have he := summable_claim1Context G β J S P B D
  have hie := summable_mul_of_summable_norm hi.norm he.norm
  rw [← Summable.tsum_mul_tsum hi he hie]
  rw [← Summable.tsum_mul_tsum (summable_factorSummand G β J S A)
    (summable_factorSummand G β J S C) (summable_claim1Interior G β J S A C)]
  rw [currentSum_couplingIn_eq, currentSum_couplingIn_eq]
  ac_rfl



open FluxEdgeCopy


noncomputable def gatedSourcePairSum (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P] : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) *
      (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) *
      (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)

namespace FluxEdgeCopy



theorem sources_univ_eq_symmDiff (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) :
    RandomCurrent.sources (endsM G m) (univ : Finset (Copy G m)) =
      RandomCurrent.sources (endsM G m) K ∆
        RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) := by
  rw [← RandomCurrent.sources_symmDiff]
  congr 1
  ext i
  simp


theorem edgecopy_sourcePair_switching (m : ↥G.edgeFinset → ℕ) (A : Finset V)
    {u v : V} (huv : u ≠ v) :
    (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) = {u, v}
            then 1 else 0))
      = ∑ K : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
            (if RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) = ∅
              then 1 else 0) *
            (if RandomCurrent.connK (endsM G m) univ u v then 1 else 0) := by
  let U : Finset (Copy G m) := univ
  by_cases hU : RandomCurrent.sources (endsM G m) U = A
  · have hleft : ∀ K : Finset (Copy G m),
        RandomCurrent.sources (endsM G m) K = A ∆ {u, v} →
          RandomCurrent.sources (endsM G m) (U \ K) = {u, v} := by
      intro K hK
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hU, hK] at hs
      ext z
      have hz := Finset.ext_iff.mp hs z
      simp only [Finset.mem_symmDiff] at hz ⊢
      tauto
    have hright : ∀ K : Finset (Copy G m),
        RandomCurrent.sources (endsM G m) K = A →
          RandomCurrent.sources (endsM G m) (U \ K) = ∅ := by
      intro K hK
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hU, hK] at hs
      ext z
      have hz := Finset.ext_iff.mp hs z
      simp only [Finset.mem_symmDiff, Finset.notMem_empty] at hz ⊢
      tauto
    have hsw := RandomCurrent.switching_lemma (endsM G m) U
      (fun i _ => endsM_not_isDiag G m i) A hU huv (fun _ => (1 : ℝ))
    have hL : (∑ K : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
            (if RandomCurrent.sources (endsM G m) (U \ K) = {u, v} then 1 else 0)) =
        ∑ _K ∈ U.powerset.filter
          (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}), (1 : ℝ) := by
      rw [Finset.sum_filter]
      simp only [U, Finset.mem_powerset, Finset.subset_univ, if_true]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A ∆ {u, v}
      · rw [if_pos hK, if_pos (by simpa [U] using hleft K hK)]
        norm_num
      · simp [hK]
    have hR : (∑ K : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
            (if RandomCurrent.sources (endsM G m) (U \ K) = ∅ then 1 else 0) *
            (if RandomCurrent.connK (endsM G m) U u v then 1 else 0)) =
        ∑ _K ∈ U.powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A),
          (1 : ℝ) * (if RandomCurrent.connK (endsM G m) U u v then 1 else 0) := by
      rw [Finset.sum_filter]
      simp only [U, Finset.mem_powerset, Finset.subset_univ, if_true]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A
      · rw [if_pos hK, if_pos (by simpa [U] using hright K hK), one_mul]
        simp [hK]
      · simp [hK]
    rw [show (univ : Finset (Copy G m)) = U from rfl, hL, hR]
    exact hsw
  · have hzero : ∀ K : Finset (Copy G m),
        ¬ (RandomCurrent.sources (endsM G m) K = A ∆ {u, v} ∧
          RandomCurrent.sources (endsM G m) (U \ K) = {u, v}) := by
      rintro K ⟨hK, hC⟩
      apply hU
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hK, hC] at hs
      ext z
      have hz := Finset.ext_iff.mp hs z
      simp only [Finset.mem_symmDiff] at hz ⊢
      tauto
    have hzero' : ∀ K : Finset (Copy G m),
        ¬ (RandomCurrent.sources (endsM G m) K = A ∧
          RandomCurrent.sources (endsM G m) (U \ K) = ∅) := by
      rintro K ⟨hK, hC⟩
      apply hU
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hK, hC] at hs
      calc
        RandomCurrent.sources (endsM G m) U = A ∆ (∅ : Finset V) := hs
        _ = A := by ext z; simp [Finset.mem_symmDiff]
    have hLzero : (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = {u, v} then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A ∆ {u, v}
      · have hC : RandomCurrent.sources (endsM G m) (U \ K) ≠ {u, v} :=
          fun h => hzero K ⟨hK, h⟩
        simp [hK, hC]
      · simp [hK]
    have hRzero : (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = ∅ then 1 else 0) *
          (if RandomCurrent.connK (endsM G m) U u v then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A
      · have hC : RandomCurrent.sources (endsM G m) (U \ K) ≠ ∅ :=
          fun h => hzero' K ⟨hK, h⟩
        simp [hK, hC]
      · simp [hK]
    change (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = {u, v} then 1 else 0)) =
      ∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = ∅ then 1 else 0) *
          (if RandomCurrent.connK (endsM G m) U u v then 1 else 0)
    rw [hLzero, hRzero]

end FluxEdgeCopy



theorem gatedSourcePairSum_switching (β : ℝ) (J : Sym2 V → ℝ)
    (A : Finset V) {u v : V} (huv : u ≠ v)
    (P : Current V → Prop) [DecidablePred P] :
    gatedSourcePairSum G β J (A ∆ {u, v}) {u, v} P =
      gatedSourcePairSum G β J A ∅
        (fun m => P m ∧ CurrentConnected G m u v) := by
  unfold gatedSourcePairSum
  rw [FluxEdgeCopy.sourcePairSum_conv_factor G β J (A ∆ {u, v}) {u, v}
      (fun m => if P (ofEdgeFun G m) then 1 else 0)
      (fun m => by by_cases h : P (ofEdgeFun G m) <;> simp [h])]
  rw [FluxEdgeCopy.sourcePairSum_conv_factor G β J A ∅
      (fun m => if P (ofEdgeFun G m) ∧ CurrentConnected G (ofEdgeFun G m) u v then 1 else 0)
      (fun m => by
        by_cases hP : P (ofEdgeFun G m) <;>
          by_cases hC : CurrentConnected G (ofEdgeFun G m) u v <;> simp [hP, hC])]
  refine tsum_congr (fun m => ?_)
  rw [FluxEdgeCopy.sourcePair_superposition_bridge G β J (A ∆ {u, v}) {u, v} m,
    FluxEdgeCopy.sourcePair_superposition_bridge G β J A ∅ m]
  rw [FluxEdgeCopy.edgecopy_sourcePair_switching G m A huv]
  have hconn := FluxEdgeCopy.connK_univ_iff G m u v
  by_cases hP : P (ofEdgeFun G m) <;>
    by_cases hC : CurrentConnected G (ofEdgeFun G m) u v <;>
    simp [hP, hC, hconn]




def edgesIn (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (edgeInside S)



theorem expectationJ_eq_expJ (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G β J A =
      expJ G.edgeFinset (fun e => β * J e) (fun _ => 0) (Ising.spinProd A) := by
  have hw : ∀ s : ConfigSpace V,
      boltzmannJ G β J s = wJ G.edgeFinset (fun e => β * J e) (fun _ => 0) s := by
    intro s
    unfold boltzmannJ wJ
    congr 1
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold expectationJ expJ partitionJ ZJ
  simp_rw [hw]



theorem expectationJ_couplingIn_eq_expJ (β : ℝ) (J : Sym2 V → ℝ)
    (S A : Finset V) :
    expectationJ G β (couplingIn J S) A =
      expJ (edgesIn G S) (fun e => β * J e) (fun _ => 0) (Ising.spinProd A) := by
  have hw : ∀ s : ConfigSpace V,
      boltzmannJ G β (couplingIn J S) s =
        wJ (edgesIn G S) (fun e => β * J e) (fun _ => 0) s := by
    intro s
    unfold boltzmannJ wJ couplingIn edgesIn
    congr 1
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : edgeInside S e <;> simp [hi] <;> ring
  unfold expectationJ expJ partitionJ ZJ
  simp_rw [hw]



theorem expectationJ_couplingIn_le (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (S A : Finset V) :
    expectationJ G β (couplingIn J S) A ≤ expectationJ G β J A := by
  rw [expectationJ_couplingIn_eq_expJ, expectationJ_eq_expJ]
  apply griffiths_mono (edgesIn G S) G.edgeFinset (fun e => β * J e) (fun _ => 0)
  · intro e he
    exact (Finset.mem_filter.mp he).1
  · intro e _
    exact mul_nonneg hβ (hJ e)
  · intro x
    exact le_rfl
  · intro e he _
    exact G.not_isDiag_of_mem_edgeFinset he


theorem gatedSourcePairSum_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A B C D : Finset V) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (hCS : C ⊆ S) (hDS : D ⊆ Sᶜ) :
    gatedSourcePairSum G β J (A ∆ B) (C ∆ D) P =
      currentSum G β (couplingIn J S) A * currentSum G β (couplingIn J S) C *
        (∑' bd, claim1Context G β J S P B D bd) := by
  unfold gatedSourcePairSum
  simpa only [ofEdgeFun_add] using
    claim1_pairSum_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS


theorem claim1Context_nonneg (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V) :
    0 ≤ ∑' bd, claim1Context G β J S P B D bd := by
  apply tsum_nonneg
  rintro ⟨b, d⟩
  unfold claim1Context
  by_cases hb : sources G (ofEdgeFun G (bFull G S b)) = B <;>
    by_cases hd : sources G (ofEdgeFun G (bFull G S d)) = D <;>
    by_cases hp : P (fun e => ofEdgeFun G (bFull G S b) e +
      ofEdgeFun G (bFull G S d) e) <;> simp [hb, hd, hp]
  exact mul_nonneg
    (Ising.acw_weight_nonneg G β J hβ hJ (ofEdgeFun G (bFull G S b)))
    (Ising.acw_weight_nonneg G β J hβ hJ (ofEdgeFun G (bFull G S d)))










theorem claim1_ising_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) (mΛ : ℝ)
    (hgriff : expectationJ G β (couplingIn J S) {y, g} ≤ mΛ) :
    mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
        (fun m => notConnComp G m o = S) ≥
      gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
  let P : Current V → Prop := fun m => notConnComp G m o = S
  have H1 : ∀ m, P m → NoCrossing G m S := fun m hm =>
    noCrossing_of_event G m S o ho hm
  have H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m') := by
    intro m m' heq
    constructor
    · intro hm
      exact notConnComp_congr G m m' S o ho hm heq
    · intro hm'
      exact notConnComp_congr G m' m S o ho hm' (fun i hi hni => (heq i hi hni).symm)
  have hA : ({y, g} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hB : ({o, x} : Finset V) ⊆ Sᶜ := by
    intro z hz
    rw [Finset.mem_compl]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hE : (∅ : Finset V) ⊆ S := Finset.empty_subset _
  have hEc : (∅ : Finset V) ⊆ Sᶜ := Finset.empty_subset _
  let cA := currentSum G β (couplingIn J S) ({y, g} : Finset V)
  let c0 := currentSum G β (couplingIn J S) ∅
  let C := ∑' bd, claim1Context G β J S P ({o, x} : Finset V) ∅ bd
  have hcA : cA = expectationJ G β (couplingIn J S) {y, g} * c0 := by
    exact Ising.acr_eq15_insertion' G β (couplingIn J S) {y, g}
  have heS : 0 ≤ expectationJ G β (couplingIn J S) {y, g} :=
    Ising.acr_expectationJ_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) {y, g}
  have hc0 : 0 ≤ c0 :=
    Ising.acr_currentSum_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) ∅
  have hlocal : mΛ * cA * c0 ≥ cA * cA := by
    rw [hcA]
    have hm := mul_le_mul_of_nonneg_right hgriff (mul_nonneg heS (sq_nonneg c0))
    nlinarith
  have hC : 0 ≤ C := claim1Context_nonneg G β J hβ hJ S P {o, x} ∅
  have htheta := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) {o, x} ∅ ∅ hA hB hE hEc
  have hpre := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) {o, x} {y, g} ∅ hA hB hA hEc
  have hee : (∅ : Finset V) ∆ ∅ = ∅ := by ext z; simp [Finset.mem_symmDiff]
  have ha0 : ({y, g} : Finset V) ∆ ∅ = {y, g} := by
    ext z; simp [Finset.mem_symmDiff]
  rw [hee] at htheta
  rw [ha0] at hpre
  have hmul := mul_le_mul_of_nonneg_right hlocal hC
  have hswitch := gatedSourcePairSum_switching G β J ({o, x} : Finset V) hyg P
  change mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅ P ≥ _
  rw [htheta]
  rw [← hswitch]
  rw [show ({o, x} : Finset V) ∆ {y, g} = {y, g} ∆ {o, x} by
    apply symmDiff_comm]
  rw [hpre]
  nlinarith


theorem claim1_ising (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) (mΛ : ℝ) (hmΛ : 0 < mΛ)
    (hgriff : expectationJ G β (couplingIn J S) {y, g} ≤ mΛ) :
    gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
        (fun m => notConnComp G m o = S) ≥
      mΛ⁻¹ * gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
  have h := claim1_ising_cleared G β J hβ hJ S o x y g ho hx hy hg hyg mΛ hgriff
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hmΛ.le)
  calc
    mΛ⁻¹ * gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g)
      ≤ mΛ⁻¹ * (mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
          (fun m => notConnComp G m o = S)) := hm
    _ = gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
          (fun m => notConnComp G m o = S) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmΛ), one_mul]


theorem claim1_ising_unconditional_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) :
    expectationJ G β J {y, g} *
        gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
          (fun m => notConnComp G m o = S) ≥
      gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) :=
  claim1_ising_cleared G β J hβ hJ S o x y g ho hx hy hg hyg
    (expectationJ G β J {y, g})
    (expectationJ_couplingIn_le G β J hβ hJ S {y, g})



theorem claim1_ising_self_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o y g : V)
    (ho : o ∉ S) (hy : y ∈ S) (hg : g ∈ S) (hyg : y ≠ g) :
    expectationJ G β J {y, g} *
        gatedSourcePairSum G β J {y, g} ∅
          (fun m => notConnComp G m o = S) ≥
      gatedSourcePairSum G β J ∅ ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
  let P : Current V → Prop := fun m => notConnComp G m o = S
  have H1 : ∀ m, P m → NoCrossing G m S := fun m hm =>
    noCrossing_of_event G m S o ho hm
  have H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m') := by
    intro m m' heq
    constructor
    · intro hm
      exact notConnComp_congr G m m' S o ho hm heq
    · intro hm'
      exact notConnComp_congr G m' m S o ho hm'
        (fun i hi hni => (heq i hi hni).symm)
  have hA : ({y, g} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hE : (∅ : Finset V) ⊆ S := Finset.empty_subset _
  have hEc : (∅ : Finset V) ⊆ Sᶜ := Finset.empty_subset _
  let cA := currentSum G β (couplingIn J S) ({y, g} : Finset V)
  let c0 := currentSum G β (couplingIn J S) ∅
  let C := ∑' bd, claim1Context G β J S P ∅ ∅ bd
  have hcA : cA = expectationJ G β (couplingIn J S) {y, g} * c0 :=
    Ising.acr_eq15_insertion' G β (couplingIn J S) {y, g}
  have heS : 0 ≤ expectationJ G β (couplingIn J S) {y, g} :=
    Ising.acr_expectationJ_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) {y, g}
  have hc0 : 0 ≤ c0 :=
    Ising.acr_currentSum_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) ∅
  have hgriff := expectationJ_couplingIn_le G β J hβ hJ S {y, g}
  have hlocal : expectationJ G β J {y, g} * cA * c0 ≥ cA * cA := by
    rw [hcA]
    have hm := mul_le_mul_of_nonneg_right hgriff (mul_nonneg heS (sq_nonneg c0))
    calc
      (expectationJ G β (couplingIn J S) {y, g} * c0) *
          (expectationJ G β (couplingIn J S) {y, g} * c0) =
          expectationJ G β (couplingIn J S) {y, g} *
            (expectationJ G β (couplingIn J S) {y, g} * c0 ^ 2) := by ring
      _ ≤ expectationJ G β J {y, g} *
            (expectationJ G β (couplingIn J S) {y, g} * c0 ^ 2) := hm
      _ = expectationJ G β J {y, g} *
            (expectationJ G β (couplingIn J S) {y, g} * c0) * c0 := by ring
  have hC : 0 ≤ C := claim1Context_nonneg G β J hβ hJ S P ∅ ∅
  have htheta := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) ∅ ∅ ∅ hA hEc hE hEc
  have hpre := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) ∅ ({y, g} : Finset V) ∅ hA hEc hA hEc
  have hee : (∅ : Finset V) ∆ ∅ = ∅ := by ext z; simp [Finset.mem_symmDiff]
  have ha0 : ({y, g} : Finset V) ∆ ∅ = {y, g} := by
    ext z; simp [Finset.mem_symmDiff]
  have h0a : (∅ : Finset V) ∆ {y, g} = {y, g} := by
    ext z; simp [Finset.mem_symmDiff]
  rw [hee] at htheta
  rw [ha0] at htheta
  rw [ha0] at hpre
  have hmul := mul_le_mul_of_nonneg_right hlocal hC
  have hswitch := gatedSourcePairSum_switching G β J (∅ : Finset V) hyg P
  rw [h0a] at hswitch
  change expectationJ G β J {y, g} *
      gatedSourcePairSum G β J {y, g} ∅ P ≥ _
  rw [htheta]
  rw [← hswitch]
  rw [hpre]
  simpa only [mul_assoc] using hmul



theorem claim1_ising_unconditional (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) (hm : 0 < expectationJ G β J {y, g}) :
    gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
        (fun m => notConnComp G m o = S) ≥
      (expectationJ G β J {y, g})⁻¹ * gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) :=
  claim1_ising G β J hβ hJ S o x y g ho hx hy hg hyg
    (expectationJ G β J {y, g}) hm
    (expectationJ_couplingIn_le G β J hβ hJ S {y, g})

end Sharpness
end StatMech
