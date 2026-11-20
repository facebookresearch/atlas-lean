/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice




instance instDecidableRelNearestNeighbour (d : ℕ) : DecidableRel (NearestNeighbour d) :=
  fun x y => by unfold NearestNeighbour; infer_instance


instance instDecidableRelAdj (d : ℕ) : DecidableRel (hypercubicLattice d).Adj :=
  instDecidableRelNearestNeighbour d



def shift (d : ℕ) (x : Site d) (j : Fin d) (s : ℤ) : Site d :=
  Function.update x j (x j + s)



def candMap (d : ℕ) (x : Site d) : Fin d × Bool → Site d :=
  fun p => shift d x p.1 (if p.2 then 1 else -1)


def candFinset (d : ℕ) (x : Site d) : Finset (Site d) :=
  Finset.univ.image (candMap d x)



theorem nearestNeighbour_iff_shift (d : ℕ) (x y : Site d) :
    NearestNeighbour d x y ↔ ∃ j : Fin d, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ y = shift d x j s := by
  constructor
  · intro h
    unfold NearestNeighbour at h
    
    have hne : ∃ j, (x j - y j).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      simp only [hc] at h
      simp at h
    obtain ⟨j, hj⟩ := hne
    
    have hle : (x j - y j).natAbs ≤ ∑ i, (x i - y i).natAbs :=
      Finset.single_le_sum (f := fun i => (x i - y i).natAbs)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h] at hle
    have h1 : (x j - y j).natAbs = 1 := by omega
    
    have hother : ∀ i, i ≠ j → (x i - y i).natAbs = 0 := by
      intro i hi
      by_contra hc
      have hpair : (x j - y j).natAbs + (x i - y i).natAbs ≤ ∑ k, (x k - y k).natAbs := by
        have := Finset.sum_le_sum_of_subset (s := ({j, i} : Finset (Fin d))) (t := Finset.univ)
          (f := fun k => (x k - y k).natAbs) (Finset.subset_univ _)
        rwa [Finset.sum_pair (Ne.symm hi)] at this
      rw [h] at hpair; omega
    refine ⟨j, y j - x j, ?_, ?_⟩
    · rcases Int.natAbs_eq (x j - y j) with he | he <;> rw [h1] at he <;> omega
    · funext i
      by_cases hi : i = j
      · subst hi; simp [shift, Function.update_self]
      · rw [shift, Function.update_of_ne hi]; have := hother i hi; omega
  · rintro ⟨j, s, hs, rfl⟩
    unfold NearestNeighbour shift
    rw [Finset.sum_eq_single j]
    · rw [Function.update_self]
      rcases hs with rfl | rfl <;> simp
    · intro i _ hi; rw [Function.update_of_ne hi]; simp
    · intro h; simp at h


theorem adj_candMap (d : ℕ) (x : Site d) (p : Fin d × Bool) :
    (hypercubicLattice d).Adj x (candMap d x p) := by
  change NearestNeighbour d x (candMap d x p)
  rw [nearestNeighbour_iff_shift]
  exact ⟨p.1, if p.2 then 1 else -1, by rcases p.2 <;> simp, rfl⟩


theorem mem_candFinset_of_adj (d : ℕ) (x y : Site d)
    (h : (hypercubicLattice d).Adj x y) : y ∈ candFinset d x := by
  change NearestNeighbour d x y at h
  rw [nearestNeighbour_iff_shift] at h
  obtain ⟨j, s, hs, hys⟩ := h
  rw [candFinset, Finset.mem_image]
  refine ⟨(j, s = 1), Finset.mem_univ _, ?_⟩
  rw [candMap]
  rcases hs with rfl | rfl
  · simp [hys]
  · simp [hys, shift]


theorem candMap_injective (d : ℕ) (x : Site d) : Function.Injective (candMap d x) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  simp only [candMap, shift] at h
  by_cases hjj : j = j'
  · subst hjj
    have := congrFun h j
    rw [Function.update_self, Function.update_self] at this
    rcases b <;> rcases b' <;> simp_all
  · have hj := congrFun h j
    rw [Function.update_self, Function.update_of_ne hjj] at hj
    rcases b <;> simp_all



instance instLocallyFinite (d : ℕ) : SimpleGraph.LocallyFinite (hypercubicLattice d) :=
  fun x =>
    Fintype.ofFinset ((candFinset d x).filter (fun y => (hypercubicLattice d).Adj x y)) (by
      intro y
      rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
      exact ⟨fun h => h.2, fun h => ⟨mem_candFinset_of_adj d x y h, h⟩⟩)


theorem neighborFinset_eq_candFinset (d : ℕ) (x : Site d) :
    (hypercubicLattice d).neighborFinset x = candFinset d x := by
  apply Finset.ext
  intro y
  rw [SimpleGraph.mem_neighborFinset]
  refine ⟨fun h => mem_candFinset_of_adj d x y h, ?_⟩
  intro hy
  rw [candFinset, Finset.mem_image] at hy
  obtain ⟨p, _, rfl⟩ := hy
  exact adj_candMap d x p


theorem card_candFinset (d : ℕ) (x : Site d) : (candFinset d x).card = 2 * d := by
  rw [candFinset, Finset.card_image_of_injective _ (candMap_injective d x),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring


theorem degree_eq (d : ℕ) (x : Site d) : (hypercubicLattice d).degree x = 2 * d := by
  rw [SimpleGraph.degree, neighborFinset_eq_candFinset, card_candFinset]


theorem isRegularOfDegree (d : ℕ) :
    (hypercubicLattice d).IsRegularOfDegree (2 * d) := degree_eq d


theorem degree_le (d : ℕ) (x : Site d) : (hypercubicLattice d).degree x ≤ 2 * d :=
  (degree_eq d x).le








section Counting

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [SimpleGraph.LocallyFinite G]





theorem card_finsetWalkLength_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v).card ≤ D ^ n := by
  induction n generalizing u with
  | zero =>
    rw [pow_zero, Finset.card_le_one]
    intro a ha b hb
    rw [SimpleGraph.mem_finsetWalkLength_iff] at ha hb
    have hav := SimpleGraph.Walk.eq_of_length_eq_zero ha
    subst hav
    rw [SimpleGraph.Walk.length_eq_zero_iff] at ha hb
    rw [ha.eq_nil, hb.eq_nil]
  | succ n ih =>
    rw [SimpleGraph.finsetWalkLength]
    calc (Finset.univ.biUnion (fun (w : G.neighborSet u) =>
            (G.finsetWalkLength n w v).map
              ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩)).card
        ≤ ∑ w : G.neighborSet u,
            ((G.finsetWalkLength n (w : V) v).map
              ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩).card :=
          Finset.card_biUnion_le
      _ = ∑ w : G.neighborSet u, (G.finsetWalkLength n (w : V) v).card := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.card_map]
      _ ≤ ∑ _w : G.neighborSet u, D ^ n := Finset.sum_le_sum (fun w _ => ih (w : V))
      _ = (Fintype.card (G.neighborSet u)) * D ^ n := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ = G.degree u * D ^ n := by rw [← SimpleGraph.card_neighborSet_eq_degree]
      _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
      _ = D ^ (n + 1) := by rw [pow_succ]; ring



theorem card_finsetWalkLength_self_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (v : V) :
    (G.finsetWalkLength n v v).card ≤ D ^ n :=
  card_finsetWalkLength_le G hD n v v





theorem card_circuits_based_in_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (B : Finset V) (n : ℕ) :
    (B.sigma (fun v => G.finsetWalkLength n v v)).card ≤ B.card * D ^ n := by
  rw [Finset.card_sigma]
  calc ∑ v ∈ B, (G.finsetWalkLength n v v).card
      ≤ ∑ _v ∈ B, D ^ n :=
        Finset.sum_le_sum (fun v _ => card_finsetWalkLength_le G hD n v v)
    _ = B.card * D ^ n := by rw [Finset.sum_const, smul_eq_mul]

end Counting





theorem card_finsetWalkLength_le_pow (d n : ℕ) (u v : Site d) :
    ((hypercubicLattice d).finsetWalkLength n u v).card ≤ (2 * d) ^ n :=
  card_finsetWalkLength_le (hypercubicLattice d) (degree_le d) n u v




theorem card_circuits_le_pow (d n : ℕ) (v : Site d) :
    ((hypercubicLattice d).finsetWalkLength n v v).card ≤ (2 * d) ^ n :=
  card_finsetWalkLength_le_pow d n v v





theorem card_circuits_based_in_le_pow (d : ℕ) (B : Finset (Site d)) (n : ℕ) :
    (B.sigma (fun v => (hypercubicLattice d).finsetWalkLength n v v)).card
      ≤ B.card * (2 * d) ^ n :=
  card_circuits_based_in_le (hypercubicLattice d) (degree_le d) B n








instance instDecidableRelDualAdj : DecidableRel dualLattice.Adj :=
  instDecidableRelAdj 2


instance instLocallyFiniteDual : SimpleGraph.LocallyFinite dualLattice :=
  instLocallyFinite 2



theorem card_dual_circuits_le_pow (n : ℕ) (v : Site 2) :
    (dualLattice.finsetWalkLength n v v).card ≤ 4 ^ n := by
  have h : (dualLattice.finsetWalkLength n v v).card ≤ (2 * 2) ^ n :=
    card_circuits_le_pow 2 n v
  simpa using h









def l1dist (d : ℕ) (x y : Site d) : ℕ := ∑ i, (x i - y i).natAbs

@[simp] theorem l1dist_self (d : ℕ) (x : Site d) : l1dist d x x = 0 := by
  unfold l1dist; simp

theorem l1dist_comm (d : ℕ) (x y : Site d) : l1dist d x y = l1dist d y x := by
  unfold l1dist
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Int.natAbs_neg, neg_sub]


theorem l1dist_of_adj (d : ℕ) {x y : Site d} (h : (hypercubicLattice d).Adj x y) :
    l1dist d x y = 1 := h


theorem l1dist_triangle (d : ℕ) (x y z : Site d) :
    l1dist d x z ≤ l1dist d x y + l1dist d y z := by
  unfold l1dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hsplit : (x i - z i) = (x i - y i) + (y i - z i) := by ring
  rw [hsplit]
  exact Int.natAbs_add_le _ _


theorem l1dist_le_walk_length (d : ℕ) {x y : Site d}
    (w : (hypercubicLattice d).Walk x y) : l1dist d x y ≤ w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    rename_i u v z
    rw [SimpleGraph.Walk.length_cons]
    calc l1dist d u z ≤ l1dist d u v + l1dist d v z := l1dist_triangle d u v z
      _ = 1 + l1dist d v z := by rw [l1dist_of_adj d h]
      _ ≤ 1 + p.length := Nat.add_le_add_left ih 1
      _ = p.length + 1 := by ring




theorem mem_support_l1dist_le (d : ℕ) {x y : Site d}
    (w : (hypercubicLattice d).Walk x y) {z : Site d} (hz : z ∈ w.support) :
    l1dist d x z ≤ w.length := by
  induction w with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz; simp
  | cons h p ih =>
    rename_i u v t
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rw [SimpleGraph.Walk.length_cons]
    rcases hz with rfl | hz
    · simp
    · calc l1dist d u z ≤ l1dist d u v + l1dist d v z := l1dist_triangle d u v z
        _ = 1 + l1dist d v z := by rw [l1dist_of_adj d h]
        _ ≤ 1 + p.length := Nat.add_le_add_left (ih hz) 1
        _ = p.length + 1 := by ring




theorem circuit_support_subset_ball (d n : ℕ) (v : Site d)
    (w : (hypercubicLattice d).Walk v v) (hw : w.length = n) :
    ∀ z ∈ w.support, l1dist d v z ≤ n := by
  intro z hz
  rw [← hw]
  exact mem_support_l1dist_le d w hz

end Lattice

end StatMech
