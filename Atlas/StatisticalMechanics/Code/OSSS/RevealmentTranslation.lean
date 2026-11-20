/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.OSSS.RevealmentConstruction
import Code.Lattice.PathVisitsRow
import Code.OSSS.RevealmentSum
import Code.OSSS.ReachBoxCrossing

open Set Finset SimpleGraph

namespace StatMech
namespace OSSS
namespace RevealmentTranslation

open Lattice
open RevealmentConstruction


def siteRadius {d : ℕ} (x : Site d) : ℕ :=
  Finset.univ.sup (fun i => (x i).natAbs)


def centeredRadius {d : ℕ} (u x : Site d) : ℕ :=
  siteRadius (fun i => x i - u i)



def centeredBoundary {d : ℕ} (u : Site d) (n : ℕ) : Set (Site d) :=
  {x | centeredRadius u x = n}

lemma siteRadius_le_iff {d n : ℕ} {x : Site d} :
    siteRadius x ≤ n ↔ ∀ i, (x i).natAbs ≤ n := by
  unfold siteRadius
  rw [Finset.sup_le_iff]
  simp

lemma mem_box_iff_siteRadius_le {d n : ℕ} {x : Site d} :
    x ∈ box d n ↔ siteRadius x ≤ n := by
  rw [mem_box, siteRadius_le_iff]

lemma siteRadius_eq_of_mem_vertexBoundary {d k : ℕ} {x : Site d}
    (hx : x ∈ vertexBoundary d k) : siteRadius x = k := by
  have hle : siteRadius x ≤ k := (mem_box_iff_siteRadius_le.mp hx.1)
  have hnle : ¬ siteRadius x ≤ k - 1 := by
    intro h
    exact hx.2 (mem_box_iff_siteRadius_le.mpr h)
  omega

lemma centeredRadius_self {d : ℕ} (u : Site d) : centeredRadius u u = 0 := by
  unfold centeredRadius siteRadius
  simp

lemma centeredRadius_comm {d : ℕ} (u v : Site d) :
    centeredRadius u v = centeredRadius v u := by
  unfold centeredRadius siteRadius
  apply congrArg (Finset.univ.sup ·)
  funext i
  change (v i - u i).natAbs = (u i - v i).natAbs
  rw [← Int.natAbs_neg, neg_sub]

lemma siteRadius_triangle {d : ℕ} (x y : Site d) :
    siteRadius x ≤ siteRadius y + centeredRadius y x := by
  rw [siteRadius_le_iff]
  intro i
  have hy : (y i).natAbs ≤ siteRadius y :=
    Finset.le_sup (f := fun j => (y j).natAbs) (Finset.mem_univ i)
  have hxy : (x i - y i).natAbs ≤ centeredRadius y x :=
    Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ i)
  calc
    (x i).natAbs = ((x i - y i) + y i).natAbs := by ring_nf
    _ ≤ (x i - y i).natAbs + (y i).natAbs := Int.natAbs_add_le _ _
    _ ≤ centeredRadius y x + siteRadius y := Nat.add_le_add hxy hy
    _ = siteRadius y + centeredRadius y x := Nat.add_comm _ _

lemma centeredRadius_step_le {d : ℕ} (u x y : Site d)
    (hxy : (hypercubicLattice d).Adj x y) :
    centeredRadius u y ≤ centeredRadius u x + 1 := by
  unfold centeredRadius
  rw [siteRadius_le_iff]
  intro i
  have hstep : (y i - x i).natAbs ≤ 1 := by
    have h := Lattice.pvr_adj_coord_diff_le_one hxy i
    rw [← Int.natAbs_neg, neg_sub]
    exact h
  have hx : (x i - u i).natAbs ≤ centeredRadius u x :=
    Finset.le_sup (f := fun j => (x j - u j).natAbs) (Finset.mem_univ i)
  calc
    (y i - u i).natAbs = ((y i - x i) + (x i - u i)).natAbs := by ring_nf
    _ ≤ (y i - x i).natAbs + (x i - u i).natAbs := Int.natAbs_add_le _ _
    _ ≤ 1 + centeredRadius u x := Nat.add_le_add hstep hx
    _ = centeredRadius u x + 1 := Nat.add_comm _ _



lemma nat_discrete_ivt (f : ℕ → ℕ) :
    ∀ n, f 0 = 0 → (∀ i, i < n → f (i + 1) ≤ f i + 1) →
      ∀ m, m ≤ f n → ∃ i ≤ n, f i = m := by
  intro n
  induction n with
  | zero =>
      intro hf0 _ m hm
      exact ⟨0, le_rfl, by omega⟩
  | succ n ih =>
      intro hf0 hstep m hm
      by_cases hmn : m ≤ f n
      · obtain ⟨i, hi, hfi⟩ := ih hf0 (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) m hmn
        exact ⟨i, Nat.le_succ_of_le hi, hfi⟩
      · refine ⟨n + 1, le_rfl, ?_⟩
        have hs := hstep n (Nat.lt_succ_self n)
        omega

lemma openWalk_hits_centeredBoundary {d : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {u v : Site d}
    (w : (openSubgraph d ω).Walk u v) {m : ℕ}
    (hm : m ≤ centeredRadius u v) :
    ∃ z ∈ centeredBoundary u m, Connected d ω u z := by
  let f : ℕ → ℕ := fun i => centeredRadius u (w.getVert i)
  have hf0 : f 0 = 0 := by simp [f, centeredRadius_self]
  have hstep : ∀ i, i < w.length → f (i + 1) ≤ f i + 1 := by
    intro i hi
    apply centeredRadius_step_le
    exact openSubgraph_le ω (w.adj_getVert_succ hi)
  have hm' : m ≤ f w.length := by simpa [f] using hm
  obtain ⟨i, hi, hfi⟩ := nat_discrete_ivt f w.length hf0 hstep m hm'
  refine ⟨w.getVert i, ?_, (w.take i).reachable⟩
  exact hfi



theorem connectedToSet_originBoundary_imp_centered_of_le {d k m : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {u : Site d}
    (hm : m ≤ ((k : ℤ) - (siteRadius u : ℤ)).natAbs) :
    ConnectedToSet d ω u (vertexBoundary d k) →
      ConnectedToSet d ω u (centeredBoundary u m) := by
  rintro ⟨v, hv, huv⟩
  have hrv : siteRadius v = k := siteRadius_eq_of_mem_vertexBoundary hv
  have htri1 := siteRadius_triangle v u
  have htri2 := siteRadius_triangle u v
  rw [centeredRadius_comm v u] at htri2
  have hdist : ((k : ℤ) - (siteRadius u : ℤ)).natAbs ≤ centeredRadius u v := by
    rw [hrv] at htri1 htri2
    by_cases h : siteRadius u ≤ k
    · have habs : ((k : ℤ) - (siteRadius u : ℤ)).natAbs = k - siteRadius u := by omega
      rw [habs]
      omega
    · have habs : ((k : ℤ) - (siteRadius u : ℤ)).natAbs = siteRadius u - k := by omega
      rw [habs]
      omega
  rcases huv with ⟨w⟩
  obtain ⟨z, hz, huz⟩ := openWalk_hits_centeredBoundary w (hm.trans hdist)
  exact ⟨z, hz, huz⟩


theorem connectedToSet_originBoundary_imp_centered {d k : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {u : Site d} :
    ConnectedToSet d ω u (vertexBoundary d k) →
      ConnectedToSet d ω u
        (centeredBoundary u (((k : ℤ) - (siteRadius u : ℤ)).natAbs)) := by
  exact connectedToSet_originBoundary_imp_centered_of_le le_rfl

lemma sum_Icc_one_pred_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f (k - 1) = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega) (fun k => f (k - 1))]
      rw [Finset.sum_range_succ, ih]
      simp

lemma mean_indicator_nonneg {E : Type*} [Fintype E] [DecidableEq E]
    {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω) (P : ConfigSpace E → Prop)
    [DecidablePred P] :
    0 ≤ Lindeberg.mean μ (fun ω => if P ω then (1 : ℝ) else 0) := by
  unfold Lindeberg.mean
  apply Finset.sum_nonneg
  intro ω _
  by_cases h : P ω <;> simp [h, hμ0 ω]



theorem revealment_sum_bound_lattice
    {E : Type*} [Fintype E] [DecidableEq E] {d n : ℕ}
    (μ : ConfigSpace E → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω)
    (edge : E → Sym2 (Site d)) (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (u : Site d) (hu : u ∈ Λ) (hubox : u ∈ box d n)
    [∀ (ω : ConfigSpace E) (x : Site d) (k : ℕ),
      Decidable (ConnectedToSet d (liftCfg edge ω) x (vertexBoundary d k))]
    [∀ (ω : ConfigSpace E) (x : Site d) (k : ℕ),
      Decidable (ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x k))] :
    (∑ k ∈ Finset.Icc 1 n,
        Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) u
          (vertexBoundary d k) then (1 : ℝ) else 0))
      ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
        Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) x
          (centeredBoundary x j) then (1 : ℝ) else 0)) := by
  let conn : Site d → ℕ → ℝ := fun x j =>
    Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) x
      (centeredBoundary x j) then (1 : ℝ) else 0)
  let q : ℕ → ℝ := fun k =>
    Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) u
      (vertexBoundary d k) then (1 : ℝ) else 0)
  have hconn0 : ∀ x j, 0 ≤ conn x j := fun x j => mean_indicator_nonneg hμ0 _
  have hrn : siteRadius u ≤ n := mem_box_iff_siteRadius_le.mp hubox
  change (∑ k ∈ Finset.Icc 1 n, q k) ≤
    2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j)
  by_cases hr0 : siteRadius u = 0
  · have hcomp0 : ∀ k, 1 ≤ k → q k ≤ conn u (k - 1) := by
      intro k hk
      apply ReachBoxCrossing.mean_indicator_mono hμ0
      intro ω hω
      have hm : k - 1 ≤ ((k : ℤ) - (siteRadius u : ℤ)).natAbs := by
        rw [hr0]
        simp
      exact connectedToSet_originBoundary_imp_centered_of_le hm hω
    have hsum : (∑ k ∈ Finset.Icc 1 n, q k) ≤
        ∑ j ∈ Finset.range n, conn u j := by
      calc
        (∑ k ∈ Finset.Icc 1 n, q k)
            ≤ ∑ k ∈ Finset.Icc 1 n, conn u (k - 1) :=
          Finset.sum_le_sum (fun k hk => hcomp0 k (Finset.mem_Icc.mp hk).1)
        _ = ∑ j ∈ Finset.range n, conn u j := sum_Icc_one_pred_eq_sum_range (conn u) n
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, conn u j :=
      Finset.sum_nonneg (fun j _ => hconn0 u j)
    have hsup : 2 * ∑ j ∈ Finset.range n, conn u j ≤
        2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, conn x j) :=
      sum_le_two_mul_sup' Λ hne
        (fun x => ∑ j ∈ Finset.range n, conn x j) u hu
    exact hsum.trans ((show (∑ j ∈ Finset.range n, conn u j) ≤
      2 * ∑ j ∈ Finset.range n, conn u j by linarith).trans hsup)
  · have hr1 : 1 ≤ siteRadius u := Nat.one_le_iff_ne_zero.mpr hr0
    apply revealment_sum_bound_range Λ hne conn hconn0 n (siteRadius u)
      hr1 hrn u hu q
    intro k
    apply ReachBoxCrossing.mean_indicator_mono hμ0
    intro ω hω
    exact connectedToSet_originBoundary_imp_centered hω

end RevealmentTranslation
end OSSS
end StatMech
