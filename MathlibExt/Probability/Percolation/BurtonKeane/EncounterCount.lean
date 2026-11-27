/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SiteRemoval
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Counting encounter points in lattice boxes

A spanning forest connecting boundary sites has degree at least three at each encounter point.
Its leaves bound the number of such points, so translation invariance gives encounter probability
zero by the boundary-to-volume ratio.

The spanning-forest proof is adapted from the `CanonForestCount`, `DecoupledForestCount`, and
`CanonTrifProb` modules in the archived ATLAS statistical mechanics development.
-/

namespace MathlibExt.Probability.Percolation.BurtonKeaneWanted

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

noncomputable section

/-! ## The boundary-to-volume ratio -/

section

open Finset
variable {d : ℕ}

theorem boxFinset_card_pos (d n : ℕ) : 0 < (boxFinset d n).card := by
  unfold boxFinset; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; positivity

theorem boundary_vol_ratio_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (boxSV_boundaryCard d n : ℝ) / ((boxFinset d n).card : ℝ) ≤ (2 * d : ℝ) / n := by
  have hboxcard : ((boxFinset d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
    unfold boxFinset; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  set P : ℝ := (2 * (n : ℝ) + 1) ^ (d - 1) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  have hbound : (boxSV_boundaryCard d n : ℝ) ≤ 2 * (d * P) := by
    have hbR : (boxSV_boundaryCard d n : ℝ)
        = (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d := by
      rw [boxSV_boundary_card d n hn]
      have hle : (2 * n - 1) ^ d ≤ (2 * n + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      rw [Nat.cast_sub hle]
      congr 1
      · push_cast; ring
      · have h1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
          have : (1 : ℕ) ≤ 2 * n := by omega
          rw [Nat.cast_sub this]; push_cast; ring
        rw [← h1]; push_cast; ring_nf
    rw [hbR]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsub := boxSV_pow_sub_pow_le (2 * (n : ℝ) + 1) (2 * (n : ℝ) - 1)
      (by linarith) (by linarith) d
    calc (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d
        ≤ ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1)) * (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := hsub
      _ = 2 * (d * P) := by rw [hP]; ring
  have hpow : (2 * (n : ℝ) + 1) ^ d = (2 * (n : ℝ) + 1) * P := by
    rw [hP, ← pow_succ']; congr 1; omega
  rw [hboxcard, hpow, div_le_div_iff₀ (by positivity) (by exact_mod_cast hn)]
  calc (boxSV_boundaryCard d n : ℝ) * n ≤ 2 * (d * P) * n :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ ≤ 2 * d * ((2 * (n : ℝ) + 1) * P) := by
        have hle : (n : ℝ) ≤ 2 * (n : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ n by positivity]
        nlinarith [hP0, mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 2 * d * P)]

end

/-! ## Boundary sites -/

section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

theorem mem_boundary_of_exit (n : ℕ) (hn : 1 ≤ n) (z z' : Site d) (hz : z ∈ box d n)
    (hz' : z' ∉ box d n) (hadj : (hypercubicLattice d).Adj z z') :
    z ∈ vertexBoundary d n := by
  rw [mem_box] at hz; rw [mem_box] at hz'; push Not at hz'
  obtain ⟨i, hi⟩ := hz'
  rw [hypercubicLattice_adj] at hadj
  have hipos : 1 ≤ (z i - z' i).natAbs := by
    rcases Nat.eq_zero_or_pos (z i - z' i).natAbs with h0 | hpos
    · exfalso; rw [Int.natAbs_eq_zero, sub_eq_zero] at h0
      have := hz i; rw [h0] at this; omega
    · exact hpos
  have hterm : (z i - z' i).natAbs = 1 := by
    by_contra hne
    have hge2 : 2 ≤ (z i - z' i).natAbs := by omega
    have hle : (z i - z' i).natAbs ≤ ∑ j, (z j - z' j).natAbs :=
      Finset.single_le_sum (f := fun j => (z j - z' j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hzin : (z i).natAbs = n := by have h1 := hz i; omega
  refine ⟨fun j => hz j, ?_⟩
  rw [mem_box]; push Not
  exact ⟨i, by rw [hzin]; omega⟩

noncomputable def boundaryFinset (d n : ℕ) : Finset (Site d) :=
  (vertexBoundary_finite d n).toFinset

theorem boundaryFinset_card (d n : ℕ) :
    (boundaryFinset d n).card = boxSV_boundaryCard d n := rfl

theorem mem_boundaryFinset {d n : ℕ} {x : Site d} :
    x ∈ boundaryFinset d n ↔ x ∈ vertexBoundary d n := by
  rw [boundaryFinset, Set.Finite.mem_toFinset]

end

/-! ## Branch vertices and leaves in a finite forest -/

section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

theorem card_le_of_degree_ge_three {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (Tw : Finset W) (hTw : ∀ w ∈ Tw, 3 ≤ G.degree w) :
    Tw.card ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := by
  classical
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hTw w hw

theorem forest_branches_le_leaves {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hEle : G.edgeFinset.card + 1 ≤ Fintype.card V := by
    obtain ⟨T, hGT, hTmax⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (le_top (a := G)) hacyc
    have hmax2 : Maximal IsAcyclic T :=
      ⟨hTmax.1.2, fun H hHac hTH => hTmax.2 ⟨le_top, hHac⟩ hTH⟩
    have hTtree : T.IsTree := isTree_iff_maximal_isAcyclic.mpr ⟨‹Nonempty V›, hmax2⟩
    have hTedge : T.edgeFinset.card + 1 = Fintype.card V := hTtree.card_edgeFinset
    have hsub : G.edgeFinset ⊆ T.edgeFinset := by
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      exact SimpleGraph.edgeSet_subset_edgeSet.mpr hGT he
    have : G.edgeFinset.card ≤ T.edgeFinset.card := Finset.card_le_card hsub
    omega
  set indI : V → ℤ := fun v => if 3 ≤ G.degree v then 1 else 0 with hindI
  set indL : V → ℤ := fun v => if G.degree v = 1 then 1 else 0 with hindL
  have hbound : ∀ v, (2 : ℤ) + indI v - indL v ≤ (G.degree v : ℤ) := by
    intro v
    simp only [hindI, hindL]
    have h1 := hmin v
    have hcast : (1 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h1
    by_cases h3 : 3 ≤ G.degree v
    · have hne1 : ¬ G.degree v = 1 := by omega
      have h3cast : (3 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h3
      simp only [ite_eq_left h3, ite_eq_right hne1]; linarith
    · by_cases h1' : G.degree v = 1
      · have h1cast : (G.degree v : ℤ) = 1 := by exact_mod_cast h1'
        simp only [ite_eq_right h3, ite_eq_left h1']; linarith
      · have h2 : G.degree v = 2 := by omega
        have h2cast : (G.degree v : ℤ) = 2 := by exact_mod_cast h2
        simp only [ite_eq_right h3, ite_eq_right h1']; linarith
  have hsumbound : ∑ v, ((2 : ℤ) + indI v - indL v) ≤ ∑ v, (G.degree v : ℤ) :=
    Finset.sum_le_sum (fun v _ => hbound v)
  have hLHS : ∑ v, ((2 : ℤ) + indI v - indL v)
      = 2 * Fintype.card V + (univ.filter (fun v => 3 ≤ G.degree v)).card
        - (univ.filter (fun v => G.degree v = 1)).card := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hindI, hindL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  have hRHS : ∑ v, (G.degree v : ℤ) ≤ 2 * Fintype.card V - 2 := by
    have h : (∑ v, (G.degree v : ℤ)) = ((∑ v, G.degree v : ℕ) : ℤ) := by rw [Nat.cast_sum]
    rw [h, hhand]
    have : (G.edgeFinset.card : ℤ) + 1 ≤ Fintype.card V := by exact_mod_cast hEle
    push_cast
    omega
  rw [hLHS] at hsumbound
  have hfin : ((univ.filter (fun v => 3 ≤ G.degree v)).card : ℤ)
      ≤ ((univ.filter (fun v => G.degree v = 1)).card : ℤ) := by linarith
  exact_mod_cast hfin

end

/-! ## Degrees at cut vertices -/

section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

theorem cut_neighbor {W : Type*} {G : SimpleGraph W} {x a : W} (hxa : x ≠ a)
    (h : G.Reachable x a) :
    ∃ (c : W) (hc : c ≠ x) (ha : a ≠ x), G.Adj x c ∧
      (G.induce ({x}ᶜ : Set W)).Reachable ⟨c, by simpa using hc⟩ ⟨a, by simpa using ha⟩ := by
  classical
  obtain ⟨p⟩ := h
  set q : G.Walk x a := (p.toPath : G.Walk x a) with hq
  have hqp : q.IsPath := (p.toPath).2
  have hnnil : ¬ q.Nil := Walk.not_nil_of_ne hxa
  set c := q.snd with hc
  have hadj : G.Adj x c := q.adj_snd hnnil
  have hcx : c ≠ x := (G.ne_of_adj hadj).symm
  have hax : a ≠ x := fun h => hxa h.symm
  have hsupp : ∀ y ∈ q.tail.support, y ∈ ({x}ᶜ : Set W) := by
    intro y hy
    have hcons : q.support = x :: q.tail.support := by
      rw [Walk.support_tail_of_not_nil q hnnil, Walk.cons_tail_support]
    have hnd := hqp.support_nodup
    rw [hcons, List.nodup_cons] at hnd
    intro hyx
    simp only [Set.mem_singleton_iff] at hyx
    subst hyx
    exact hnd.1 hy
  have hind := q.tail.induce ({x}ᶜ : Set W) hsupp
  exact ⟨c, hcx, hax, hadj, ⟨hind.copy (by simp [hc]) rfl⟩⟩

theorem deg_ge_three_of_cut {W : Type*} [Fintype W] {G : SimpleGraph W}
    [DecidableRel G.Adj] {x a₁ a₂ a₃ : W}
    (hr₁ : G.Reachable x a₁) (hr₂ : G.Reachable x a₂) (hr₃ : G.Reachable x a₃)
    (hx₁ : x ≠ a₁) (hx₂ : x ≠ a₂) (hx₃ : x ≠ a₃)
    (hcut₁₂ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₂, by simpa using hx₂.symm⟩)
    (hcut₁₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩)
    (hcut₂₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable
      ⟨a₂, by simpa using hx₂.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩) :
    3 ≤ G.degree x := by
  classical
  obtain ⟨c₁, _, _, hadj₁, hreach₁⟩ := cut_neighbor hx₁ hr₁
  obtain ⟨c₂, _, _, hadj₂, hreach₂⟩ := cut_neighbor hx₂ hr₂
  obtain ⟨c₃, _, _, hadj₃, hreach₃⟩ := cut_neighbor hx₃ hr₃
  have h12 : c₁ ≠ c₂ := by rintro rfl; exact hcut₁₂ (hreach₁.symm.trans hreach₂)
  have h13 : c₁ ≠ c₃ := by rintro rfl; exact hcut₁₃ (hreach₁.symm.trans hreach₃)
  have h23 : c₂ ≠ c₃ := by rintro rfl; exact hcut₂₃ (hreach₂.symm.trans hreach₃)
  have hsub : ({c₁, c₂, c₃} : Finset W) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [G.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact hadj₁
    · exact hadj₂
    · exact hadj₃
  have hcard : ({c₁, c₂, c₃} : Finset W).card = 3 :=
    Finset.card_eq_three.mpr ⟨c₁, c₂, c₃, h12, h13, h23, rfl⟩
  calc 3 = ({c₁, c₂, c₃} : Finset W).card := hcard.symm
    _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
    _ = G.degree x := G.card_neighborFinset_eq_degree x

theorem edge_transfer (x u v : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    (hadj : (openSubgraph d ω).Adj u v) (hux : u ≠ x) (hvx : v ≠ x) :
    (openSubgraph d (removeSite x ω)).Adj u v := by
  obtain ⟨hl, ho⟩ := hadj
  refine ⟨hl, ?_⟩
  rw [removeSite_apply_of_notMem]
  · exact ho
  · intro hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hux rfl
    · exact hvx rfl

theorem walk_avoid_transfer {x u v : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d ω).Walk u v) (hw : x ∉ w.support) :
    (openSubgraph d (removeSite x ω)).Reachable u v := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    obtain ⟨hax, hw'⟩ := hw
    have hbx : x ≠ b := fun h => by subst h; exact hw' (w.start_mem_support)
    exact (Adj.reachable
      (edge_transfer x a b ω hab (Ne.symm hax) (Ne.symm hbx))).trans (ih hw')

theorem connected_removeSite_of_G_induce {W : Type*} {ω : ConfigSpace (Sym2 (Site d))}
    {G : SimpleGraph W} (π : W → Site d)
    (hπ : ∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v))
    (hπinj : Function.Injective π)
    {p wi wj : W} (hwi : wi ≠ p) (hwj : wj ≠ p)
    (h : (G.induce ({p}ᶜ : Set W)).Reachable ⟨wi, by simpa using hwi⟩ ⟨wj, by simpa using hwj⟩) :
    Connected d (removeSite (π p) ω) (π wi) (π wj) := by
  obtain ⟨w⟩ := h
  set f : (G.induce ({p}ᶜ : Set W)) →g (openSubgraph d ω) :=
    { toFun := fun u => π u.1
      map_rel' := fun {a b} hab => hπ a.1 b.1 hab } with hf
  set w' := w.map f with hw'
  have hsupp : (π p) ∉ w'.support := by
    intro hx
    rw [hw', Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨c, hc⟩, _, hcx⟩ := hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hc (hπinj (by simpa [hf] using hcx))
  exact walk_avoid_transfer w' hsupp

end

/-! ## Three separated arms force degree at least three -/

section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

theorem degree_ge_three_of_separated_targets {ω : ConfigSpace (Sym2 (Site d))}
    {Vset : Finset (Site d)} {F : SimpleGraph (↑Vset : Type)} [DecidableRel F.Adj]
    {vx : Site d → (↑Vset : Type)} {b : Site d → Fin 3 → (↑Vset : Type)}
    (hπ : ∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
    {x : Site d}
    (hvx : (vx x : Site d) = x)
    (hreach : ∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x)
    (hcut : ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)) :
    3 ≤ F.degree (vx x) := by
  classical
  set p := vx x with hp
  obtain ⟨hr0, hb0⟩ := hreach 0
  obtain ⟨hr1, hb1⟩ := hreach 1
  obtain ⟨hr2, hb2⟩ := hreach 2
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  have hπinj : Function.Injective (fun u : (↑Vset : Type) => (u : Site d)) := Subtype.val_injective
  have hcutG : ∀ (u v : (↑Vset : Type)) (hup : u ≠ p) (hvp : v ≠ p),
      ¬ Connected d (removeSite x ω) (u : Site d) (v : Site d) →
      ¬ (F.induce ({p}ᶜ : Set (↑Vset : Type))).Reachable
        ⟨u, by simpa using hup⟩ ⟨v, by simpa using hvp⟩ := by
    intro u v hup hvp hc hreach2
    apply hc
    have := connected_removeSite_of_G_induce (fun u : (↑Vset : Type) => (u : Site d))
      hπ hπinj hup hvp hreach2
    rw [show (p : Site d) = x from hvx] at this
    exact this
  exact deg_ge_three_of_cut hr0 hr1 hr2 hb0.symm hb1.symm hb2.symm
    (hcutG _ _ hb0 hb1 hcut01)
    (hcutG _ _ hb0 hb2 hcut02)
    (hcutG _ _ hb1 hb2 hcut12)

end

/-! ## Spanning forests -/

section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

noncomputable def spanForest {V : Type*} [Fintype V] (G : SimpleGraph V) : SimpleGraph V :=
  Classical.choose (exists_maximal_isAcyclic_of_le_isAcyclic (bot_le (a := G)) isAcyclic_bot)

theorem spanForest_spec {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (spanForest G) :=
  (Classical.choose_spec
    (exists_maximal_isAcyclic_of_le_isAcyclic (bot_le (a := G)) isAcyclic_bot)).2

theorem spanForest_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (spanForest G).IsAcyclic := (spanForest_spec G).1.2

theorem spanForest_le {V : Type*} [Fintype V] (G : SimpleGraph V) :
    spanForest G ≤ G := (spanForest_spec G).1.1

theorem spanForest_reachable {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : (spanForest G).Reachable u v := by
  classical
  by_contra hnr
  have hmax := spanForest_spec G
  set T := spanForest G with hT
  set T' := T ⊔ SimpleGraph.fromEdgeSet {s(u, v)} with hT'
  have huv_ne : u ≠ v := G.ne_of_adj h
  have hT'ac : T'.IsAcyclic := IsAcyclic.sup_edge_of_not_reachable hnr (spanForest_acyclic G)
  have hT'le : T' ≤ G := by
    refine sup_le (spanForest_le G) ?_
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    obtain ⟨hmem, hne⟩ := hab
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact h.symm
  have hle := hmax.2 ⟨hT'le, hT'ac⟩ le_sup_left
  have hadjT : T.Adj u v := by
    apply hle
    rw [hT']; right; rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, huv_ne⟩
  exact hnr hadjT.reachable

theorem spanForest_reachable_of {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V}
    (h : G.Reachable u v) : (spanForest G).Reachable u v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab w ih => exact (spanForest_reachable G hab).trans ih

end

/-! ## Paths between boundary sites -/

section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

def OnBoundaryPath {V : Type*} (T : SimpleGraph V) (B : Set V) (v : V) : Prop :=
  ∃ b₁ b₂ : V, b₁ ∈ B ∧ b₂ ∈ B ∧ b₁ ≠ b₂ ∧ ∃ p : T.Walk b₁ b₂, p.IsPath ∧ v ∈ p.support

theorem survivor_has_neighbor {V : Type*} (T : SimpleGraph V) (B : Set V)
    (v : V) (h : OnBoundaryPath T B v) : ∃ w, T.Adj v w ∧ OnBoundaryPath T B w := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, hmem⟩ := h
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hvi, hile⟩ := hmem
  have hlen : 0 < p.length := by
    rcases Nat.eq_zero_or_pos p.length with h0 | h0
    · exact absurd (p.eq_of_length_eq_zero h0) hne
    · exact h0
  by_cases hi : i < p.length
  · exact ⟨p.getVert (i + 1), hvi ▸ p.adj_getVert_succ hi,
      ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩⟩
  · have hieq : i = p.length := le_antisymm hile (not_lt.mp hi)
    refine ⟨p.getVert (p.length - 1), ?_,
      ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩⟩
    have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [Nat.sub_add_cancel hlen] at hadj
    rw [← hvi, hieq]; exact hadj.symm

theorem interior_two_neighbors {V : Type*} (T : SimpleGraph V) (B : Set V)
    (v : V) (hv : OnBoundaryPath T B v) (hvB : v ∉ B) :
    ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ T.Adj v w₁ ∧ T.Adj v w₂ ∧
      OnBoundaryPath T B w₁ ∧ OnBoundaryPath T B w₂ := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, hmem⟩ := hv
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hvi, hile⟩ := hmem
  have hvb1 : v ≠ b₁ := fun h => hvB (h ▸ hb₁)
  have hvb2 : v ≠ b₂ := fun h => hvB (h ▸ hb₂)
  have hi0 : i ≠ 0 := by intro h; subst h; rw [p.getVert_zero] at hvi; exact hvb1 hvi.symm
  have hilen : i ≠ p.length := by
    intro h; subst h; rw [p.getVert_length] at hvi; exact hvb2 hvi.symm
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  have hilt : i < p.length := lt_of_le_of_ne hile hilen
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro hcontra
    have := hp.getVert_injOn (x₁ := i - 1) (x₂ := i + 1)
      (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; omega) hcontra
    omega
  · rw [← hvi]
    have hadj := p.adj_getVert_succ (i := i - 1) (by omega)
    rw [Nat.sub_add_cancel hipos] at hadj; exact hadj.symm
  · rw [← hvi]; exact p.adj_getVert_succ hilt
  · exact ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩
  · exact ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩
variable {W : Type*} [Fintype W] (F : SimpleGraph W) [DecidableRel F.Adj]
theorem deg_ge_one (v w : W) (h : F.Adj v w) : 1 ≤ F.degree v := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, F.degree_pos_iff_exists_adj]; exact ⟨w, h⟩

theorem deg_ge_two (v w₁ w₂ : W) (hne : w₁ ≠ w₂) (h1 : F.Adj v w₁) (h2 : F.Adj v w₂) :
    2 ≤ F.degree v := by
  classical
  rw [← F.card_neighborFinset_eq_degree]
  have hsub : ({w₁, w₂} : Finset W) ⊆ F.neighborFinset v := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> rw [mem_neighborFinset] <;> assumption
  calc (2 : ℕ) = ({w₁, w₂} : Finset W).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem map_acyclic {V V' : Type*} {G : SimpleGraph V} (hac : G.IsAcyclic) (f : V ↪ V') :
    (SimpleGraph.map f G).IsAcyclic := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have hbot : SimpleGraph.map f G = ⊥ := by
      ext x y; rw [SimpleGraph.map_adj]; simp only [bot_adj, iff_false]
      rintro ⟨a, _, _, _, _⟩; exact isEmptyElim a
    rw [hbot]; exact isAcyclic_bot
  obtain ⟨g, hg⟩ : ∃ g : V' → V, ∀ a, g (f a) = a :=
    ⟨Function.invFun f, Function.leftInverse_invFun f.injective⟩
  set gHom : (SimpleGraph.map f G) →g G :=
    ⟨g, by intro x y hxy; rw [SimpleGraph.map_adj] at hxy
           obtain ⟨a, b, hab, rfl, rfl⟩ := hxy; rw [hg, hg]; exact hab⟩ with hgHom
  have hgHom_apply : ∀ w, gHom w = g w := fun _ => rfl
  intro u c hc
  have hlen : 0 < c.length := by have := hc.three_le_length; omega
  have hsupp_mem : ∀ w ∈ c.support, ∃ a, f a = w := by
    intro w hw
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
    obtain ⟨i, hi, hil⟩ := hw
    rcases Nat.lt_or_ge i c.length with hlt | hge
    · have hadj := c.adj_getVert_succ hlt
      rw [SimpleGraph.map_adj] at hadj; obtain ⟨a, b, hab, h1, h2⟩ := hadj
      exact ⟨a, h1.trans hi⟩
    · have hieq : i = c.length := le_antisymm hil hge
      have hadj := c.adj_getVert_succ (i := c.length - 1) (by omega)
      rw [SimpleGraph.map_adj] at hadj; obtain ⟨a, b, hab, h1, h2⟩ := hadj
      refine ⟨b, ?_⟩; rw [h2, ← hi, hieq]; congr 1; omega
  have hginj : ∀ x ∈ c.support, ∀ y ∈ c.support, g x = g y → x = y := by
    intro x hx y hy hxy
    obtain ⟨ax, rfl⟩ := hsupp_mem x hx
    obtain ⟨ay, rfl⟩ := hsupp_mem y hy
    rw [hg, hg] at hxy; rw [hxy]
  refine hac (c.map gHom) ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.edges_map]
    refine List.Nodup.map_on ?_ hc.edges_nodup
    intro e1 he1 e2 he2 heq
    induction e1 with
    | _ p q =>
      induction e2 with
      | _ r s =>
        simp only [Sym2.map_mk, Sym2.eq_iff] at heq
        have hp := c.fst_mem_support_of_mem_edges he1
        have hq := c.snd_mem_support_of_mem_edges he1
        have hr := c.fst_mem_support_of_mem_edges he2
        have hs := c.snd_mem_support_of_mem_edges he2
        rw [Sym2.eq_iff]
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨hginj p hp r hr h1, hginj q hq s hs h2⟩
        · exact Or.inr ⟨hginj p hp s hs h1, hginj q hq r hr h2⟩
  · intro hnil
    have hl := SimpleGraph.Walk.length_map gHom c
    rw [hnil] at hl; simp only [SimpleGraph.Walk.length_nil] at hl; omega
  · rw [SimpleGraph.Walk.support_map]
    have htail : (List.map (⇑gHom) c.support).tail = List.map (⇑gHom) c.support.tail := by
      cases c.support <;> simp
    rw [htail]
    refine List.Nodup.map_on ?_ hc.support_nodup
    intro x hx y hy
    simp only [hgHom_apply]
    exact fun h => hginj x (List.mem_of_mem_tail hx) y (List.mem_of_mem_tail hy) h

end

/-! ## Joining disjoint arms -/

section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
variable {d : ℕ}

theorem glue_path {V : Type*} {T : SimpleGraph V} {x c0 c1 z0 z1 : V}
    (hxc0 : T.Adj x c0) (hxc1 : T.Adj x c1)
    (w0 : T.Walk c0 z0) (hw0p : w0.IsPath) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1p : w1.IsPath) (hw1x : x ∉ w1.support)
    (hdisj : ∀ v, v ∈ w0.support → v ∈ w1.support → False) :
    ∃ p : T.Walk z0 z1, p.IsPath ∧ x ∈ p.support ∧ c0 ∈ p.support ∧ c1 ∈ p.support := by
  set tw : T.Walk c0 z1 := Walk.cons hxc0.symm (Walk.cons hxc1 w1) with htw
  set p : T.Walk z0 z1 := w0.reverse.append tw with hp
  have htwsupp : tw.support = c0 :: x :: w1.support := by
    rw [htw, Walk.support_cons, Walk.support_cons]
  have hpsupp : p.support = w0.reverse.support ++ (x :: w1.support) := by
    rw [hp, Walk.support_append, htwsupp]; rfl
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [Walk.isPath_def, hpsupp, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.support_reverse, List.nodup_reverse]; exact hw0p.support_nodup
    · rw [List.nodup_cons]; exact ⟨hw1x, hw1p.support_nodup⟩
    · intro a ha b hb
      rw [Walk.support_reverse, List.mem_reverse] at ha
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact fun h => hw0x (h ▸ ha)
      · exact fun h => hdisj a ha (h ▸ hb)
  · rw [hpsupp, List.mem_append, List.mem_cons]; right; left; rfl
  · rw [hpsupp, List.mem_append]; left; rw [Walk.support_reverse, List.mem_reverse]
    exact w0.start_mem_support
  · rw [hpsupp, List.mem_append, List.mem_cons]; right; right; exact w1.start_mem_support

theorem walk_avoid_connected (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x a b : Site d} (w : T.Walk a b) (hwx : x ∉ w.support) :
    Connected d (removeSite x ω) a b := by
  classical
  set f : T →g (openSubgraph d ω) :=
    { toFun := id, map_rel' := fun {p q} hpq => hπ p q hpq } with hf
  set ww := w.map f with hww
  have hsupp : x ∉ ww.support := by
    intro hx
    rw [hww, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [hf] at hyx; subst hyx
    exact hwx hy
  exact walk_avoid_transfer ww hsupp

theorem armWalks_disjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ v, v ∈ w0.support → v ∈ w1.support → False := by
  classical
  intro v hv0 hv1
  apply hcut
  have h0 : Connected d (removeSite x ω) c0 v :=
    walk_avoid_connected ω T hπ (w0.takeUntil v hv0)
      (fun hx => hw0x (w0.support_takeUntil_subset_support hv0 hx))
  have h1 : Connected d (removeSite x ω) c1 v :=
    walk_avoid_connected ω T hπ (w1.takeUntil v hv1)
      (fun hx => hw1x (w1.support_takeUntil_subset_support hv1 hx))
  exact h0.trans h1.symm

theorem onBoundaryPath_of_arms (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) (B : Set (Site d))
    {x ci cj zi zj : Site d}
    (hxci : T.Adj x ci) (hxcj : T.Adj x cj)
    (wi : T.Walk ci zi) (hwix : x ∉ wi.support) (hzi : zi ∈ B)
    (wj : T.Walk cj zj) (hwjx : x ∉ wj.support) (hzj : zj ∈ B)
    (hcut : ¬ Connected d (removeSite x ω) ci cj) :
    OnBoundaryPath T B x ∧ OnBoundaryPath T B ci ∧ OnBoundaryPath T B cj := by
  classical
  have hzne : zi ≠ zj := by
    intro h; subst h; apply hcut
    exact (walk_avoid_connected ω T hπ wi hwix).trans
      (walk_avoid_connected ω T hπ wj hwjx).symm
  set pi : T.Walk ci zi := (wi.toPath : T.Walk ci zi) with hpi
  set pj : T.Walk cj zj := (wj.toPath : T.Walk cj zj) with hpj
  have hpix : x ∉ pi.support := fun h => hwix (wi.support_toPath_subset_support h)
  have hpjx : x ∉ pj.support := fun h => hwjx (wj.support_toPath_subset_support h)
  have hdisj : ∀ v, v ∈ pi.support → v ∈ pj.support → False := by
    have := armWalks_disjoint ω T hπ pi hpix pj hpjx hcut
    exact this
  obtain ⟨p, hpp, hxp, hcip, hcjp⟩ :=
    glue_path hxci hxcj pi (wi.toPath).2 hpix pj (wj.toPath).2 hpjx hdisj
  refine ⟨⟨zi, zj, hzi, hzj, hzne, p, hpp, hxp⟩,
    ⟨zi, zj, hzi, hzj, hzne, p, hpp, hcip⟩,
    ⟨zi, zj, hzi, hzj, hzne, p, hpp, hcjp⟩⟩

end

/-! ## Deleting a site -/

section

open Set SimpleGraph Finset
variable {d : ℕ}

theorem not_adj_removeSite (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSite x ω)).Adj x y := by
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  rw [removeSite_apply_of_mem (by simp)] at hopen
  exact Bool.false_ne_true hopen

theorem walk_avoids_x {x a b : Site d} {ω : ConfigSpace (Sym2 (Site d))} (hax : a ≠ x)
    (w : (openSubgraph d (removeSite x ω)).Walk a b) : x ∉ w.support := by
  induction w with
  | nil => simpa using (Ne.symm hax)
  | @cons u v c huv w' ih =>
    rw [Walk.support_cons, List.mem_cons, not_or]
    refine ⟨Ne.symm hax, ?_⟩
    have hvx : v ≠ x := fun h => by subst h; exact not_adj_removeSite v ω u huv.symm
    exact ih hvx

theorem neighbour_in_box_succ {x c : Site d} {n : ℕ} (hx : x ∈ box d n)
    (hadj : (hypercubicLattice d).Adj x c) : c ∈ box d (n + 1) := by
  rw [hypercubicLattice_adj] at hadj
  rw [mem_box] at hx ⊢
  intro i
  have hcoord : (x i - c i).natAbs ≤ 1 := by
    have hle : (x i - c i).natAbs ≤ ∑ j, (x j - c j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - c j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have := hx i
  omega

end

/-! ## Encounter points -/

section

open Set SimpleGraph Finset
variable {d : ℕ}

/-- An encounter point has three open neighbors in distinct infinite clusters after all
edges incident to the point are closed. -/
@[expose] public def IsEncounterPoint (d : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
    ((cluster d (removeSite x ω) a₁).Infinite ∧ (cluster d (removeSite x ω) a₂).Infinite ∧
      (cluster d (removeSite x ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
      ¬ Connected d (removeSite x ω) a₁ a₃ ∧
      ¬ Connected d (removeSite x ω) a₂ a₃)

open Classical in
noncomputable def encounterCount (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : ℕ :=
  ((boxFinset d n).filter (fun x => IsEncounterPoint d ω x)).card

end

/-! ## A spanning forest in the enlarged box -/

section

open Set SimpleGraph Finset
variable {d : ℕ}

local instance boxFintype (d n : ℕ) : Fintype (↑(box d n) : Type) :=
  (box_finite d n).fintype

noncomputable def boxEmbedding (d n : ℕ) : (↑(box d (n + 1)) : Type) ↪ Site d :=
  ⟨Subtype.val, Subtype.val_injective⟩

noncomputable def boxGraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (↑(box d (n + 1)) : Type) :=
  (openSubgraph d ω).induce (box d (n + 1))

noncomputable def boxForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (↑(box d (n + 1)) : Type) :=
  spanForest (boxGraph ω n)

noncomputable def latticeForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : SimpleGraph (Site d) :=
  (boxForest ω n).map (boxEmbedding d n)

theorem latticeForest_acyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (latticeForest ω n).IsAcyclic :=
  map_acyclic (spanForest_acyclic (boxGraph ω n)) _

theorem latticeForest_le_openSubgraph (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (u v : Site d)
    (h : (latticeForest ω n).Adj u v) : (openSubgraph d ω).Adj u v := by
  rw [latticeForest, SimpleGraph.map_adj] at h
  obtain ⟨p, q, hpq, rfl, rfl⟩ := h
  exact spanForest_le (boxGraph ω n) hpq

theorem mem_box_of_latticeForest_adj (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (u v : Site d)
    (h : (latticeForest ω n).Adj u v) : u ∈ box d (n + 1) := by
  rw [latticeForest, SimpleGraph.map_adj] at h
  obtain ⟨p, q, hpq, rfl, rfl⟩ := h
  exact p.2

theorem induce_reachable_of_walk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ {a b : Site d} (w : (openSubgraph d ω).Walk a b),
      (∀ v ∈ w.support, v ∈ box d (n + 1)) →
      ∀ (ha : a ∈ box d (n + 1)) (hb : b ∈ box d (n + 1)),
        (boxGraph ω n).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b w
  induction w with
  | nil => intro _ ha hb; exact Reachable.refl _
  | @cons u v c hadj w' ih =>
    intro hsupp hu hc
    have hv : v ∈ box d (n + 1) := hsupp v (by simp [Walk.support_cons])
    have hw'supp : ∀ z ∈ w'.support, z ∈ box d (n + 1) := fun z hz => hsupp z (by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have hadj' : (boxGraph ω n).Adj ⟨u, hu⟩ ⟨v, hv⟩ := hadj
    exact hadj'.reachable.trans (ih hw'supp hv hc)

theorem map_reachable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {a b : (↑(box d (n + 1)) : Type)} (h : (boxForest ω n).Reachable a b) :
    (latticeForest ω n).Reachable (a : Site d) (b : Site d) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | @cons u v c hadj w' ih =>
    have hadj' : (latticeForest ω n).Adj (u : Site d) (v : Site d) := by
      rw [latticeForest, SimpleGraph.map_adj]; exact ⟨u, v, hadj, rfl, rfl⟩
    exact hadj'.reachable.trans ih

theorem removeSite_walk_to_ambient (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {a b : Site d} (w : (openSubgraph d (removeSite x ω)).Walk a b) :
    ∃ w' : (openSubgraph d ω).Walk a b, w'.support = w.support := by
  have hle : ∀ u v, (openSubgraph d (removeSite x ω)).Adj u v → (openSubgraph d ω).Adj u v := by
    intro u v hadj
    obtain ⟨hadj1, hopen⟩ := hadj
    refine ⟨hadj1, ?_⟩
    by_cases hx : x ∈ s(u, v)
    · rw [removeSite_apply_of_mem hx] at hopen; exact absurd hopen (by simp)
    · rwa [removeSite_apply_of_notMem hx] at hopen
  let f : (openSubgraph d (removeSite x ω)) →g (openSubgraph d ω) :=
    { toFun := id, map_rel' := fun {p q} hpq => hle p q hpq }
  refine ⟨w.map f, ?_⟩
  calc (w.map f).support = List.map (⇑f) w.support := SimpleGraph.Walk.support_map f w
    _ = List.map id w.support := by rfl
    _ = w.support := List.map_id _

theorem latticeForest_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a z : Site d} (hxbox : x ∈ box d n)
    (hadjxa : (openSubgraph d ω).Adj x a)
    (w : (openSubgraph d (removeSite x ω)).Walk a z) (hwx : x ∉ w.support)
    (hwbox : ∀ v ∈ w.support, v ∈ box d (n + 1)) :
    (latticeForest ω n).Reachable x z := by
  obtain ⟨w', hw'supp⟩ := removeSite_walk_to_ambient ω x w
  have hxbox1 : x ∈ box d (n + 1) := box_subset_succ d n hxbox
  set hpath : (openSubgraph d ω).Walk x z := Walk.cons hadjxa w' with hpathdef
  have hpath_box : ∀ v ∈ hpath.support, v ∈ box d (n + 1) := by
    intro v hv
    rw [hpathdef, Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hxbox1
    · exact hwbox v (hw'supp ▸ hv)
  have hz_box : z ∈ box d (n + 1) := by
    have : z ∈ w.support := w.end_mem_support
    exact hwbox z this
  have hreach_box : (boxGraph ω n).Reachable ⟨x, hxbox1⟩ ⟨z, hz_box⟩ :=
    induce_reachable_of_walk ω n hpath hpath_box hxbox1 hz_box
  have hreach_F : (boxForest ω n).Reachable ⟨x, hxbox1⟩ ⟨z, hz_box⟩ :=
    spanForest_reachable_of (boxGraph ω n) hreach_box
  exact map_reachable ω n hreach_F

theorem extract_arm {T : SimpleGraph (Site d)} {x z : Site d}
    (h : T.Reachable x z) (hxz : x ≠ z) :
    ∃ (c : Site d) (rest : T.Walk c z), T.Adj x c ∧ x ∉ rest.support := by
  obtain ⟨w⟩ := h
  obtain ⟨p, hpp⟩ := w.toPath
  cases p with
  | nil => exact absurd rfl hxz
  | @cons _ c _ hadj rest =>
    refine ⟨c, rest, hadj, ?_⟩
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, List.nodup_cons] at hpp
    exact hpp.1

theorem exists_first_edge_of_branch (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a z : Site d} (hxbox : x ∈ box d n)
    (hadjxa : (openSubgraph d ω).Adj x a)
    (w : (openSubgraph d (removeSite x ω)).Walk a z) (hwx : x ∉ w.support)
    (hwbox : ∀ v ∈ w.support, v ∈ box d (n + 1)) (hzx : z ≠ x) :
    ∃ c : Site d, (latticeForest ω n).Adj x c ∧
      (∃ wt : (latticeForest ω n).Walk c z, x ∉ wt.support) ∧
      Connected d (removeSite x ω) c z := by
  have hreach : (latticeForest ω n).Reachable x z :=
    latticeForest_reaches_boundary ω n hxbox hadjxa w hwx hwbox
  have hxz : x ≠ z := fun h => hzx h.symm
  obtain ⟨c, rest, hadjxc, hrestx⟩ := extract_arm hreach hxz
  refine ⟨c, hadjxc, ⟨rest, hrestx⟩, ?_⟩
  exact walk_avoid_connected ω (latticeForest ω n) (latticeForest_le_openSubgraph ω n) rest hrestx

theorem walk_crossing_confined {V : Type*} (G : SimpleGraph V) (p : V → Prop)
    {x y : V} (w : G.Walk x y) (hx0 : p x) (hy0 : ¬ p y) :
    ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧
        ∃ wxa : G.Walk x a, ∀ v ∈ wxa.support, p v := by
  classical
  induction w with
  | nil => exact absurd hx0 hy0
  | @cons u v z hadj w' ih =>
    by_cases hv : p v
    · obtain ⟨a, b, hab, ha, hb, wva, hwva⟩ := ih hv hy0
      refine ⟨a, b, hab, ha, hb, Walk.cons hadj wva, ?_⟩
      intro ww hw
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hx0
      · exact hwva ww hw
    · refine ⟨u, v, hadj, hx0, hv, Walk.nil, ?_⟩
      intro ww hw; rw [Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact hx0

theorem arm_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x a : Site d) (hax : a ≠ x) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support ∧
        ∀ v ∈ w.support, v ∈ box d n := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, wab, hwab⟩ :=
    walk_crossing_confined (openSubgraph d (removeSite x ω)) (fun v => v ∈ box d n) w habox
      hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSite x ω)) hbc
  refine ⟨b, mem_boundary_of_exit n hn b c hb hc hblat, wab,
    walk_avoids_x hax wab, hwab⟩

theorem exists_three_forest_arms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    {x : Site d} (hxbox : x ∈ box d n)
    (c0 : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c0 i))
    (hne : ∀ i, c0 i ≠ x)
    (hcbox : ∀ i, c0 i ∈ box d n)
    (hcut : ¬ Connected d (removeSite x ω) (c0 0) (c0 1) ∧
            ¬ Connected d (removeSite x ω) (c0 0) (c0 2) ∧
            ¬ Connected d (removeSite x ω) (c0 1) (c0 2))
    (hinf : ∀ i, (cluster d (removeSite x ω) (c0 i)).Infinite) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (latticeForest ω n).Adj x (c i)) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d n ∧
        ∃ w : (latticeForest ω n).Walk (c i) (zr i), x ∉ w.support) := by
  classical
  have hreach : ∀ i, ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSite x ω)).Walk (c0 i) z, x ∉ w.support ∧
        ∀ v ∈ w.support, v ∈ box d n := fun i =>
    arm_reaches_boundary ω n hn x (c0 i) (hne i) (hcbox i) (hinf i)
  choose z hzb w hwx hwbox using hreach
  have hwbox1 : ∀ i, ∀ v ∈ (w i).support, v ∈ box d (n + 1) := fun i v hv =>
    box_subset_succ d n (hwbox i v hv)
  have hzx : ∀ i, z i ≠ x := by
    intro i hzix
    exact (hwx i) (hzix ▸ (w i).end_mem_support)
  have hper : ∀ i, ∃ c : Site d, (latticeForest ω n).Adj x c ∧
      (∃ wt : (latticeForest ω n).Walk c (z i), x ∉ wt.support) ∧
      Connected d (removeSite x ω) c (z i) := fun i =>
    exists_first_edge_of_branch ω n hxbox (hadj i) (w i) (hwx i) (hwbox1 i) (hzx i)
  choose c hadjxc htail hconn using hper
  have hzc0 : ∀ i, Connected d (removeSite x ω) (c0 i) (z i) := fun i => ⟨w i⟩
  have hcc0 : ∀ i, Connected d (removeSite x ω) (c i) (c0 i) := fun i =>
    (hconn i).trans (hzc0 i).symm
  have hcutc : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
      ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
      ¬ Connected d (removeSite x ω) (c 1) (c 2) := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact hcut.1 ((hcc0 0).symm.trans (h.trans (hcc0 1)))
    · intro h; exact hcut.2.1 ((hcc0 0).symm.trans (h.trans (hcc0 2)))
    · intro h; exact hcut.2.2 ((hcc0 1).symm.trans (h.trans (hcc0 2)))
  exact ⟨c, z, hadjxc, hcutc, fun i => ⟨hzb i, htail i⟩⟩

end

/-! ## Counting encounter points by boundary leaves -/

section

open Set SimpleGraph Finset
variable {d : ℕ}

def HasBoundaryLeafForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vset : Finset (Site d)) (_ : Nonempty (↑Vset : Type)) (F : SimpleGraph (↑Vset : Type))
    (_ : DecidableRel F.Adj) (vx : Site d → (↑Vset : Type)) (b : Site d → Fin 3 → (↑Vset : Type)),
    (∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d)) ∧
    F.IsAcyclic ∧
    (∀ v : (↑Vset : Type), 1 ≤ F.degree v) ∧
    (∀ x, x ∈ box d n → IsEncounterPoint d ω x →
      ((vx x : Site d) = x ∧
       (∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧
       (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧
        ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)))) ∧
    (∀ v : (↑Vset : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d (n + 1))

theorem encounterCount_le_of_boundaryLeafForest
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : HasBoundaryLeafForest ω n) :
    encounterCount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  obtain ⟨Vset, hVne, F, _, vx, b, hπ, hacyc, hmin, htriData, hleaf⟩ := h
  set Cf : Finset (Site d) := (boxFinset d n).filter (fun x => IsEncounterPoint d ω x)
    with hCf
  have hmemCf : ∀ x, x ∈ Cf ↔ x ∈ box d n ∧ IsEncounterPoint d ω x := by
    intro x; rw [hCf, Finset.mem_filter, boxFinset, Set.Finite.mem_toFinset]
  have hCfcard : Cf.card = encounterCount d ω n := rfl
  have hdeg3 : ∀ x, x ∈ box d n → IsEncounterPoint d ω x → 3 ≤ F.degree (vx x) := by
    intro x hxbox htri
    obtain ⟨hvx, hreach, hcut⟩ := htriData x hxbox htri
    exact degree_ge_three_of_separated_targets hπ hvx
      hreach hcut
  have hvxinjOn : Set.InjOn vx Cf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hmemCf] at hx hy
    have hx' : (vx x : Site d) = x := (htriData x hx.1 hx.2).1
    have hy' : (vx y : Site d) = y := (htriData y hy.1 hy.2).1
    rw [← hx', ← hy', hxy]
  set Cw : Finset (↑Vset : Type) := Cf.image vx with hCw
  have hcardCw : Cw.card = Cf.card := by rw [hCw, Finset.card_image_of_injOn hvxinjOn]
  have hCwdeg : ∀ w ∈ Cw, 3 ≤ F.degree w := by
    intro w hw
    rw [hCw, Finset.mem_image] at hw
    obtain ⟨x, hxC, rfl⟩ := hw
    rw [hmemCf] at hxC
    exact hdeg3 x hxC.1 hxC.2
  have h1 : Cf.card ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := by
    rw [← hcardCw]; exact card_le_of_degree_ge_three F Cw hCwdeg
  have h2 : (univ.filter (fun v => 3 ≤ F.degree v)).card
      ≤ (univ.filter (fun v => F.degree v = 1)).card :=
    forest_branches_le_leaves F hacyc hmin
  have h3 : (univ.filter (fun v => F.degree v = 1)).card ≤ boxSV_boundaryCard d (n + 1) := by
    rw [← boundaryFinset_card]
    apply Finset.card_le_card_of_injOn (fun v : (↑Vset : Type) => (v : Site d))
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, mem_boundaryFinset]
      exact hleaf v hv.2
    · intro u _ v _ huv; exact Subtype.val_injective huv
  calc encounterCount d ω n = Cf.card := hCfcard.symm
    _ ≤ (univ.filter (fun v => 3 ≤ F.degree v)).card := h1
    _ ≤ (univ.filter (fun v => F.degree v = 1)).card := h2
    _ ≤ boxSV_boundaryCard d (n + 1) := h3

def HasBoundaryArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, OnBoundaryPath T B v) ∧
    (∀ x, x ∈ box d n → IsEncounterPoint d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : T.Walk (c x i) (zr x i), x ∉ w.support))

def HasPrunedArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (m : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d (n + 1)) ∧
    (∃ v, OnBoundaryPath T B v) ∧
    (∀ x, x ∈ box d n → IsEncounterPoint d ω x →
      OnBoundaryPath T B x ∧
      ((m x 0 ≠ m x 1 ∧ m x 0 ≠ m x 2 ∧ m x 1 ≠ m x 2) ∧
       (∀ i, T.Adj x (m x i) ∧ OnBoundaryPath T B (m x i)) ∧
       (¬ Connected d (removeSite x ω) (m x 0) (m x 1) ∧
        ¬ Connected d (removeSite x ω) (m x 0) (m x 2) ∧
        ¬ Connected d (removeSite x ω) (m x 1) (m x 2))))

theorem prunedArms_of_boundaryArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : HasBoundaryArms ω n) : HasPrunedArms ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  refine ⟨Vall, T, hTdec, B, c, hTac, hTopen, hTsupp, hBbd, hRne, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  have hne01 : c x 0 ≠ c x 1 := fun h => hcut01 (h ▸ connected_refl _ _)
  have hne02 : c x 0 ≠ c x 2 := fun h => hcut02 (h ▸ connected_refl _ _)
  have hne12 : c x 1 ≠ c x 2 := fun h => hcut12 (h ▸ connected_refl _ _)
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  obtain ⟨hz2, w2, hw2x⟩ := hreach 2
  obtain ⟨hxsurv, hc0surv, hc1surv⟩ :=
    onBoundaryPath_of_arms ω T hTopen B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01
  obtain ⟨_, _, hc2surv⟩ :=
    onBoundaryPath_of_arms ω T hTopen B (hadj 0) (hadj 2) w0 hw0x hz0 w2 hw2x hz2 hcut02
  refine ⟨hxsurv, ⟨hne01, hne02, hne12⟩, ?_, hcut01, hcut02, hcut12⟩
  intro i
  refine ⟨hadj i, ?_⟩
  fin_cases i
  · exact hc0surv
  · exact hc1surv
  · exact hc2surv

theorem boundaryLeafForest_of_prunedArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : HasPrunedArms ω n) : HasBoundaryLeafForest ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, m, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  have hRfin : {v | OnBoundaryPath T B v}.Finite := by
    apply Set.Finite.subset (Vall.finite_toSet)
    intro v hv
    obtain ⟨w, hadj, _⟩ := survivor_has_neighbor T B v hv
    exact hTsupp v w hadj
  set Vset : Finset (Site d) := hRfin.toFinset with hVset
  have hmemVset : ∀ v, v ∈ Vset ↔ OnBoundaryPath T B v := by
    intro v; rw [hVset, Set.Finite.mem_toFinset]; rfl
  have hVne : Nonempty (↥Vset) := by
    obtain ⟨v, hv⟩ := hRne; exact ⟨⟨v, (hmemVset v).mpr hv⟩⟩
  set F₀ : SimpleGraph (↥Vset) := T.comap (fun (u : ↥Vset) => (u : Site d)) with hF₀
  let hF₀dec : DecidableRel F₀.Adj := fun a b => by rw [hF₀, comap_adj]; infer_instance
  have hF₀adj : ∀ u v : ↥Vset, F₀.Adj u v ↔ T.Adj (u : Site d) (v : Site d) := by
    intro u v; rw [hF₀, comap_adj]
  have hF₀ac : F₀.IsAcyclic :=
    hTac.comap ⟨(fun (u : ↥Vset) => (u : Site d)), fun {a b} h => h⟩ (fun a b h => Subtype.ext h)
  have hlift : ∀ v, OnBoundaryPath T B v → v ∈ Vset := fun v hv => (hmemVset v).mpr hv
  let dflt : ↥Vset := hVne.some
  set vx : Site d → ↥Vset := fun x =>
    if hx : OnBoundaryPath T B x then ⟨x, hlift x hx⟩ else dflt with hvxdef
  set bb : Site d → Fin 3 → ↥Vset := fun x i =>
    if hx : OnBoundaryPath T B (m x i) then ⟨m x i, hlift _ hx⟩ else dflt with hbbdef
  refine ⟨Vset, hVne, F₀, hF₀dec, vx, bb, ?_, hF₀ac, ?_, ?_, ?_⟩
  · intro u v huv
    rw [hF₀adj] at huv; exact hTopen _ _ huv
  · intro v
    have hvR : OnBoundaryPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    obtain ⟨w, hadjw, hwR⟩ := survivor_has_neighbor T B (v : Site d) hvR
    exact deg_ge_one F₀ v ⟨w, hlift w hwR⟩ (by rw [hF₀adj]; exact hadjw)
  · intro x hxbox htri
    obtain ⟨hxR, hmne, hmadj, hmsep⟩ := hData x hxbox htri
    have hvxval : (vx x : Site d) = x := by simp only [hvxdef, dite_eq_left hxR]
    refine ⟨hvxval, ?_, ?_⟩
    · intro i
      have hmi := hmadj i
      have hbbval : (bb x i : Site d) = m x i := by simp only [hbbdef, dite_eq_left hmi.2]
      refine ⟨?_, ?_⟩
      · refine Adj.reachable ?_
        rw [hF₀adj, hvxval, hbbval]; exact hmi.1
      · intro hh
        have hval : (bb x i : Site d) = (vx x : Site d) :=
          congrArg (fun (u : ↥Vset) => (u : Site d)) hh
        rw [hbbval, hvxval] at hval
        exact (T.ne_of_adj hmi.1) hval.symm
    · have h0 : (bb x 0 : Site d) = m x 0 := by simp only [hbbdef, dite_eq_left (hmadj 0).2]
      have h1 : (bb x 1 : Site d) = m x 1 := by simp only [hbbdef, dite_eq_left (hmadj 1).2]
      have h2 : (bb x 2 : Site d) = m x 2 := by simp only [hbbdef, dite_eq_left (hmadj 2).2]
      rw [h0, h1, h2]; exact hmsep
  · intro v hv
    have hvR : OnBoundaryPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    by_cases hvB : (v : Site d) ∈ B
    · exact hBbd hvB
    · exfalso
      obtain ⟨w₁, w₂, hw12, ha1, ha2, hr1, hr2⟩ :=
        interior_two_neighbors T B (v : Site d) hvR hvB
      have hdeg2 : 2 ≤ F₀.degree v :=
        deg_ge_two F₀ v ⟨w₁, hlift w₁ hr1⟩ ⟨w₂, hlift w₂ hr2⟩
          (fun hh => hw12 (Subtype.ext_iff.mp hh))
          (by rw [hF₀adj]; exact ha1) (by rw [hF₀adj]; exact ha2)
      omega

theorem hasBoundaryArms_of_encounter (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hexists : ∃ x, x ∈ box d n ∧ IsEncounterPoint d ω x) :
    HasBoundaryArms ω n := by
  classical
  have hdata : ∀ x, x ∈ box d n → IsEncounterPoint d ω x →
      ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
        (∀ i, (latticeForest ω (n + 1)).Adj x (c i)) ∧
        (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
         ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
         ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
        (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
          ∃ w : (latticeForest ω (n + 1)).Walk (c i) (zr i), x ∉ w.support) := by
    intro x hxbox htri
    obtain ⟨a₁, a₂, a₃, _hne3, hadj3, hinf3, hsep3⟩ := htri
    refine exists_three_forest_arms ω (n + 1) (by omega) (box_subset_succ d n hxbox)
      ![a₁, a₂, a₃] ?_ ?_ ?_
      ?_ ?_
    · intro i; fin_cases i
      · exact hadj3.1
      · exact hadj3.2.1
      · exact hadj3.2.2
    · intro i; fin_cases i
      · exact ((openSubgraph d ω).ne_of_adj hadj3.1).symm
      · exact ((openSubgraph d ω).ne_of_adj hadj3.2.1).symm
      · exact ((openSubgraph d ω).ne_of_adj hadj3.2.2).symm
    · intro i; fin_cases i
      · exact neighbour_in_box_succ hxbox hadj3.1.1
      · exact neighbour_in_box_succ hxbox hadj3.2.1.1
      · exact neighbour_in_box_succ hxbox hadj3.2.2.1
    · exact ⟨hsep3.1, hsep3.2.1, hsep3.2.2⟩
    · intro i; fin_cases i
      · exact hinf3.1
      · exact hinf3.2.1
      · exact hinf3.2.2
  choose! c zr hcadj hccut hcreach using hdata
  set B : Set (Site d) := vertexBoundary d (n + 1) with hBdef
  obtain ⟨x0, hx0box, hx0tri⟩ := hexists
  have hc0reach := hcreach x0 hx0box hx0tri
  obtain ⟨hz0, w0, hw0x⟩ := hc0reach 0
  obtain ⟨hz1, w1, hw1x⟩ := hc0reach 1
  have hcut01 := (hccut x0 hx0box hx0tri).1
  obtain ⟨hxsurv, _, _⟩ :=
    onBoundaryPath_of_arms ω (latticeForest ω (n + 1)) (latticeForest_le_openSubgraph ω (n + 1)) B
      (hcadj x0 hx0box hx0tri 0) (hcadj x0 hx0box hx0tri 1)
      w0 hw0x hz0 w1 hw1x hz1 hcut01
  refine ⟨boxFinset d (n + 2), latticeForest ω (n + 1), Classical.decRel _, B, c, zr,
    latticeForest_acyclic ω (n + 1), latticeForest_le_openSubgraph ω (n + 1),
    ?_, le_refl _, ⟨x0, hxsurv⟩, ?_⟩
  · intro u v huv
    rw [boxFinset, Set.Finite.mem_toFinset]
    exact mem_box_of_latticeForest_adj ω (n + 1) u v huv
  · intro x hxbox htri
    exact ⟨hcadj x hxbox htri, hccut x hxbox htri, hcreach x hxbox htri⟩

theorem encounterCount_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) :
    encounterCount d ω n ≤ boxSV_boundaryCard d (n + 1) := by
  classical
  by_cases hexists : ∃ x, x ∈ box d n ∧ IsEncounterPoint d ω x
  · exact encounterCount_le_of_boundaryLeafForest ω n
      (boundaryLeafForest_of_prunedArms ω n
        (prunedArms_of_boundaryArms ω n
          (hasBoundaryArms_of_encounter ω n hn hexists)))
  · have h0 : encounterCount d ω n = 0 := by
      unfold encounterCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [boxFinset, Set.Finite.mem_toFinset] at hx
      exact fun htri => hexists ⟨x, hx, htri⟩
    rw [h0]; exact Nat.zero_le _

end

/-! ## Expected number of encounter points -/

section

open scoped ENNReal
variable {d : ℕ}

theorem measurableSet_removeSiteClusterInfinite (x a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [heq]
  exact (measurable_removeSite x) (measurableSet_clusterInfinite a)

/-- The event that a given site is an encounter point is measurable. -/
public theorem measurableSet_isEncounterPoint (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsEncounterPoint d ω x} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | IsEncounterPoint d ω x}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          ((if a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ then Set.univ else ∅)
            ∩ ({ω | (openSubgraph d ω).Adj x a₁} ∩ {ω | (openSubgraph d ω).Adj x a₂}
                ∩ {ω | (openSubgraph d ω).Adj x a₃})
            ∩ ({ω | (cluster d (removeSite x ω) a₁).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₂).Infinite}
                ∩ {ω | (cluster d (removeSite x ω) a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSite x ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSite x ω) a₂ a₃})) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
      refine ⟨a₁, a₂, a₃, ⟨⟨⟨?_, ⟨⟨hadj.1, hadj.2.1⟩, hadj.2.2⟩⟩,
        ⟨⟨hinf.1, hinf.2.1⟩, hinf.2.2⟩⟩, ⟨⟨hsep.1, hsep.2.1⟩, hsep.2.2⟩⟩⟩
      rw [ite_eq_left hne]; exact Set.mem_univ _
    · rintro ⟨a₁, a₂, a₃, ⟨⟨⟨hif, ⟨⟨hc1, hc2⟩, hc3⟩⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩⟩
      by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
      · exact ⟨a₁, a₂, a₃, hh, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
      · rw [ite_eq_right hh] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  refine MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    MeasurableSet.iUnion fun a₃ => ?_
  refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_) ?_
  · by_cases hh : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃
    · rw [ite_eq_left hh]; exact MeasurableSet.univ
    · rw [ite_eq_right hh]; exact MeasurableSet.empty
  · exact ((measurableSet_openAdj x a₁).inter (measurableSet_openAdj x a₂)).inter
      (measurableSet_openAdj x a₃)
  · exact ((measurableSet_removeSiteClusterInfinite x a₁).inter
      (measurableSet_removeSiteClusterInfinite x a₂)).inter
      (measurableSet_removeSiteClusterInfinite x a₃)
  · exact (((measurableSet_connected_removeSite x a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite x a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite x a₂ a₃).compl)

theorem isEncounterPoint_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    IsEncounterPoint d (shift g ω) (g • x) ↔ IsEncounterPoint d ω x := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
    refine ⟨g⁻¹ • a₁, g⁻¹ • a₂, g⁻¹ • a₃, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun h => hne.1 ?_, fun h => hne.2.1 ?_, fun h => hne.2.2 ?_⟩ <;>
        · apply smul_injective g; simpa [smul_inv_smul] using h
    · refine ⟨?_, ?_, ?_⟩
      · exact (openSubgraph_adj_shift g ω x (g⁻¹ • a₁)).mp (by rw [smul_inv_smul]; exact hadj.1)
      · exact (openSubgraph_adj_shift g ω x (g⁻¹ • a₂)).mp (by rw [smul_inv_smul]; exact hadj.2.1)
      · exact (openSubgraph_adj_shift g ω x (g⁻¹ • a₃)).mp (by rw [smul_inv_smul]; exact hadj.2.2)
    · refine ⟨?_, ?_, ?_⟩
      · have hc := cluster_shift g (removeSite x ω) (g⁻¹ • a₁)
        rw [smul_inv_smul, ← removeSite_shift] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.1
      · have hc := cluster_shift g (removeSite x ω) (g⁻¹ • a₂)
        rw [smul_inv_smul, ← removeSite_shift] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.1
      · have hc := cluster_shift g (removeSite x ω) (g⁻¹ • a₃)
        rw [smul_inv_smul, ← removeSite_shift] at hc; rw [hc] at hinf
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf.2.2
    · refine ⟨?_, ?_, ?_⟩
      · intro hcon
        apply hsep.1
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₂)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₂)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
      · intro hcon
        apply hsep.2.1
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₁) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
      · intro hcon
        apply hsep.2.2
        have : Connected d (shift g (removeSite x ω)) (g • (g⁻¹ • a₂)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSite x ω) (g⁻¹ • a₂) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← removeSite_shift] at this
        exact this
  · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
    refine ⟨g • a₁, g • a₂, g • a₃, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => hne.1 (smul_injective g h), fun h => hne.2.1 (smul_injective g h),
        fun h => hne.2.2 (smul_injective g h)⟩
    · exact ⟨(openSubgraph_adj_shift g ω x a₁).mpr hadj.1,
        (openSubgraph_adj_shift g ω x a₂).mpr hadj.2.1,
        (openSubgraph_adj_shift g ω x a₃).mpr hadj.2.2⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [removeSite_shift g x ω, cluster_shift g (removeSite x ω) a₁]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.1
      · rw [removeSite_shift g x ω, cluster_shift g (removeSite x ω) a₂]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.1
      · rw [removeSite_shift g x ω, cluster_shift g (removeSite x ω) a₃]
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.2
    · rw [removeSite_shift]
      exact ⟨fun hcon => hsep.1 ((connected_shift g (removeSite x ω) a₁ a₂).mp hcon),
        fun hcon => hsep.2.1 ((connected_shift g (removeSite x ω) a₁ a₃).mp hcon),
        fun hcon => hsep.2.2 ((connected_shift g (removeSite x ω) a₂ a₃).mp hcon)⟩

/-- For a translation-invariant law, every site has the same encounter probability. -/
public theorem measure_encounter_eq_origin (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (x : Site d) :
    μ {ω | IsEncounterPoint d ω x} = μ {ω | IsEncounterPoint d ω 0} := by
  set g : Multiplicative (Site d) := Multiplicative.ofAdd x with hg
  have hgx : g • (0 : Site d) = x := by
    change Multiplicative.toAdd g + (0 : Site d) = x
    simp [hg]
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹'
      {ω | IsEncounterPoint d ω x} = {ω | IsEncounterPoint d ω 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← hgx, isEncounterPoint_shift g ω 0]
  calc μ {ω | IsEncounterPoint d ω x}
      = μ ((shift g) ⁻¹' {ω | IsEncounterPoint d ω x}) :=
        (hinv.measure_preimage g (measurableSet_isEncounterPoint x)).symm
    _ = μ {ω | IsEncounterPoint d ω 0} := by rw [hpre]

lemma encounterCount_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (encounterCount d ω n : ℝ≥0∞) =
      ∑ x ∈ boxFinset d n,
        ({ω' | IsEncounterPoint d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
  classical
  unfold encounterCount
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : IsEncounterPoint d ω x
  · rw [ite_eq_left h,
      Set.indicator_of_mem (show ω ∈ {ω' | IsEncounterPoint d ω' x} from h)]
  · rw [ite_eq_right h,
      Set.indicator_of_notMem (show ω ∉ {ω' | IsEncounterPoint d ω' x} from h)]

theorem lintegral_encounterCount (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (n : ℕ) :
    ∫⁻ ω, (encounterCount d ω n : ℝ≥0∞) ∂μ
      = (boxFinset d n).card • μ {ω | IsEncounterPoint d ω 0} := by
  classical
  have hmeas : ∀ x : Site d, Measurable
      (fun ω => ({ω' | IsEncounterPoint d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω) :=
    fun x => Measurable.indicator measurable_const (measurableSet_isEncounterPoint x)
  calc ∫⁻ ω, (encounterCount d ω n : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑ x ∈ boxFinset d n,
          ({ω' | IsEncounterPoint d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        apply lintegral_congr; intro ω; exact encounterCount_eq_sum_indicator ω n
    _ = ∑ x ∈ boxFinset d n,
          ∫⁻ ω, ({ω' | IsEncounterPoint d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]
        intro x _; exact hmeas x
    _ = ∑ x ∈ boxFinset d n, μ {ω | IsEncounterPoint d ω x} := by
        apply Finset.sum_congr rfl; intro x _
        rw [MeasureTheory.lintegral_indicator (measurableSet_isEncounterPoint x)]; simp
    _ = ∑ _x ∈ boxFinset d n, μ {ω | IsEncounterPoint d ω 0} := by
        apply Finset.sum_congr rfl; intro x _; exact measure_encounter_eq_origin μ hinv x
    _ = (boxFinset d n).card • μ {ω | IsEncounterPoint d ω 0} := by
        rw [Finset.sum_const]

theorem measure_encounter_eq_zero_of_ratio (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hvol : ∀ n, 0 < (boxFinset d n).card)
    (hdens : Filter.Tendsto
      (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinset d n).card : ℝ))
      Filter.atTop (nhds 0)) :
    μ {ω | IsEncounterPoint d ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | IsEncounterPoint d ω 0} with hp
  have hkey : ∀ n, 1 ≤ n →
      ((boxFinset d n).card : ℝ≥0∞) * p ≤ (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
    intro n hn
    have hexp := lintegral_encounterCount μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (encounterCount d ω n : ℝ≥0∞) ∂μ
        ≤ (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
      calc ∫⁻ ω, (encounterCount d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω
            simp only
            exact_mod_cast encounterCount_le_boundary ω n hn
        _ = (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact measure_ne_top μ _
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ n, 1 ≤ n →
      ((boxFinset d n).card : ℝ) * pr ≤ (boxSV_boundaryCard d (n + 1) : ℝ) := by
    intro n hn
    have h := hkey n hn
    have h' : (((boxFinset d n).card : ℝ≥0∞) * p).toReal
        ≤ (boxSV_boundaryCard d (n + 1) : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinset d n).card : ℝ) := fun n => by exact_mod_cast hvol n
  have hle : ∀ n, 1 ≤ n →
      pr ≤ (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinset d n).card : ℝ) := by
    intro n hn
    rw [le_div_iff₀ (hvolr n)]
    linarith [hkeyr n hn]
  have hpr0 : pr ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hdens
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hle n hn⟩)
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this

end

/-! ## Vanishing encounter probability -/

section

open scoped ENNReal
variable {d : ℕ}

theorem boundary_succ_vol_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinset d n).card : ℝ))
      atTop (𝓝 0) := by
  have hub : Tendsto (fun n : ℕ => (2 * (d : ℝ) * 3 ^ d) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (2 * (d : ℝ) * 3 ^ d))).div_atTop hden
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hub
  filter_upwards with n
  have hVn : ((boxFinset d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
    unfold boxFinset; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  have hVn1 : ((boxFinset d (n + 1)).card : ℝ) = (2 * (n : ℝ) + 3) ^ d := by
    unfold boxFinset; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring
  have hVnpos : (0 : ℝ) < ((boxFinset d n).card : ℝ) := by rw [hVn]; positivity
  have hVn1pos : (0 : ℝ) < ((boxFinset d (n + 1)).card : ℝ) := by rw [hVn1]; positivity
  have hr : (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinset d (n + 1)).card : ℝ)
      ≤ 2 * (d : ℝ) / ((n : ℝ) + 1) := by
    have h := boundary_vol_ratio_le d (n + 1) hd (Nat.le_add_left 1 n)
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hVratio : ((boxFinset d (n + 1)).card : ℝ) ≤ 3 ^ d * ((boxFinset d n).card : ℝ) := by
    rw [hVn1, hVn, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hAle : (boxSV_boundaryCard d (n + 1) : ℝ)
      ≤ (2 * (d : ℝ) * 3 ^ d / ((n : ℝ) + 1)) * ((boxFinset d n).card : ℝ) := by
    have h1 : (boxSV_boundaryCard d (n + 1) : ℝ)
        ≤ (2 * (d : ℝ) / ((n : ℝ) + 1)) * ((boxFinset d (n + 1)).card : ℝ) :=
      (div_le_iff₀ hVn1pos).mp hr
    have h2 : (2 * (d : ℝ) / ((n : ℝ) + 1)) * ((boxFinset d (n + 1)).card : ℝ)
        ≤ (2 * (d : ℝ) / ((n : ℝ) + 1)) * (3 ^ d * ((boxFinset d n).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hVratio (by positivity)
    calc (boxSV_boundaryCard d (n + 1) : ℝ) ≤ _ := h1
      _ ≤ _ := h2
      _ = (2 * (d : ℝ) * 3 ^ d / ((n : ℝ) + 1)) * ((boxFinset d n).card : ℝ) := by ring
  rw [div_le_iff₀ hVnpos]
  exact hAle

/-- The boundary-to-volume ratio on the lattice forces the probability of an encounter
point at the origin to vanish for every translation-invariant law in positive dimension. -/
public theorem measure_encounter_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    μ {ω | IsEncounterPoint d ω 0} = 0 :=
  measure_encounter_eq_zero_of_ratio μ hinv (fun n => boxFinset_card_pos d n)
    (boundary_succ_vol_tendsto d hd)

end

end

end MathlibExt.Probability.Percolation.BurtonKeaneWanted
