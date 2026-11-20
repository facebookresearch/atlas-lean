/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib
import Code.TwoDim.ZhangHarris
import Code.Lattice.JordanExteriorClosure

open MeasureTheory Set SimpleGraph
open scoped ENNReal NNReal

namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation
open StatMech.RSW.Box


def zfe_primalEmb (p : Site 2) : Site 2 := ![2 * p 0, 2 * p 1]


def zfe_primalMid (p q : Site 2) : Site 2 := ![p 0 + q 0, p 1 + q 1]


def zfe_faceEmb (f : Site 2) : Site 2 := ![2 * f 0 + 1, 2 * f 1 + 1]


def zfe_faceMid (f g : Site 2) : Site 2 :=
  ![f 0 + g 0 + 1, f 1 + g 1 + 1]

theorem zfe_primalEmb_mid_adj {p q : Site 2}
    (h : (hypercubicLattice 2).Adj p q) :
    (hypercubicLattice 2).Adj (zfe_primalEmb p) (zfe_primalMid p q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_primalEmb, zfe_primalMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem zfe_primalMid_emb_adj {p q : Site 2}
    (h : (hypercubicLattice 2).Adj p q) :
    (hypercubicLattice 2).Adj (zfe_primalMid p q) (zfe_primalEmb q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_primalEmb, zfe_primalMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem zfe_faceEmb_mid_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    (hypercubicLattice 2).Adj (zfe_faceEmb f) (zfe_faceMid f g) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_faceEmb, zfe_faceMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

theorem zfe_faceMid_emb_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    (hypercubicLattice 2).Adj (zfe_faceMid f g) (zfe_faceEmb g) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h ⊢
  simp only [zfe_faceEmb, zfe_faceMid, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega


def zfe_primalSubdiv {p q : Site 2} :
    (hypercubicLattice 2).Walk p q →
      (hypercubicLattice 2).Walk (zfe_primalEmb p) (zfe_primalEmb q)
  | .nil => .nil
  | .cons h w => .cons (zfe_primalEmb_mid_adj h)
      (.cons (zfe_primalMid_emb_adj h) (zfe_primalSubdiv w))


def zfe_faceSubdiv {f g : Site 2} :
    (hypercubicLattice 2).Walk f g →
      (hypercubicLattice 2).Walk (zfe_faceEmb f) (zfe_faceEmb g)
  | .nil => .nil
  | .cons h w => .cons (zfe_faceEmb_mid_adj h)
      (.cons (zfe_faceMid_emb_adj h) (zfe_faceSubdiv w))

theorem zfe_primalSubdiv_support_cases {p q z : Site 2}
    (w : (hypercubicLattice 2).Walk p q)
    (hz : z ∈ (zfe_primalSubdiv w).support) :
    (∃ u ∈ w.support, z = zfe_primalEmb u) ∨
      ∃ u v, s(u, v) ∈ w.edges ∧ z = zfe_primalMid u v := by
  induction w with
  | nil =>
      simp only [zfe_primalSubdiv, Walk.support_nil, List.mem_singleton] at hz
      exact Or.inl ⟨_, by simp, hz⟩
  | @cons u v t huv w ih =>
      simp only [zfe_primalSubdiv, Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl ⟨u, by simp, rfl⟩
      · rcases hz with rfl | hz
        · exact Or.inr ⟨u, v, by simp, rfl⟩
        · rcases ih hz with h | h
          · obtain ⟨a, ha, rfl⟩ := h
            exact Or.inl ⟨a, by simp [ha], rfl⟩
          · obtain ⟨a, b, hab, rfl⟩ := h
            exact Or.inr ⟨a, b, by simp [hab], rfl⟩

theorem zfe_faceSubdiv_support_cases {f g z : Site 2}
    (w : (hypercubicLattice 2).Walk f g)
    (hz : z ∈ (zfe_faceSubdiv w).support) :
    (∃ u ∈ w.support, z = zfe_faceEmb u) ∨
      ∃ u v, s(u, v) ∈ w.edges ∧ z = zfe_faceMid u v := by
  induction w with
  | nil =>
      simp only [zfe_faceSubdiv, Walk.support_nil, List.mem_singleton] at hz
      exact Or.inl ⟨_, by simp, hz⟩
  | @cons u v t huv w ih =>
      simp only [zfe_faceSubdiv, Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl ⟨u, by simp, rfl⟩
      · rcases hz with rfl | hz
        · exact Or.inr ⟨u, v, by simp, rfl⟩
        · rcases ih hz with h | h
          · obtain ⟨a, ha, rfl⟩ := h
            exact Or.inl ⟨a, by simp [ha], rfl⟩
          · obtain ⟨a, b, hab, rfl⟩ := h
            exact Or.inr ⟨a, b, by simp [hab], rfl⟩

theorem zfe_primalEmb_ne_faceEmb (p f : Site 2) :
    zfe_primalEmb p ≠ zfe_faceEmb f := by
  intro h
  have h0 := congrFun h 0
  simp only [zfe_primalEmb, zfe_faceEmb, Matrix.cons_val_zero] at h0
  omega

theorem zfe_primalEmb_ne_faceMid {p f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    zfe_primalEmb p ≠ zfe_faceMid f g := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rcases face_adj_dir hfg with hg | hg | hg | hg <;> subst g <;>
    simp only [zfe_primalEmb, zfe_faceMid, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h0 h1 <;> omega

theorem zfe_primalMid_ne_faceEmb {p q f : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q) :
    zfe_primalMid p q ≠ zfe_faceEmb f := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rcases face_adj_dir hpq with hq | hq | hq | hq <;> subst q <;>
    simp only [zfe_primalMid, zfe_faceEmb, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h0 h1 <;> omega



theorem zfe_midpoint_sharedPrimalEdge {p q f g : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hmid : zfe_primalMid p q = zfe_faceMid f g) :
    s(p, q) = sharedPrimalEdge f g := by
  have hp : p = ![p 0, p 1] := by funext i; fin_cases i <;> rfl
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  rcases face_adj_dir hpq with hq | hq | hq | hq <;>
  rcases face_adj_dir hfg with hg | hg | hg | hg <;>
    (rw [hp, hq] at hmid ⊢; rw [hf, hg] at hmid ⊢;
     simp only [zfe_primalMid, zfe_faceMid, sharedPrimalEdge_right',
       sharedPrimalEdge_left', sharedPrimalEdge_top', sharedPrimalEdge_bottom',
       Sym2.eq_iff, site2_eq, Matrix.cons_val_zero, Matrix.cons_val_one] at hmid ⊢;
     omega)



theorem zfe_subdiv_meeting_edge {a b c d z : Site 2}
    (H : (hypercubicLattice 2).Walk a b)
    (V : (hypercubicLattice 2).Walk c d)
    (hzH : z ∈ (zfe_primalSubdiv H).support)
    (hzV : z ∈ (zfe_faceSubdiv V).support) :
    ∃ p q f g,
      s(p, q) ∈ H.edges ∧ s(f, g) ∈ V.edges ∧
        s(p, q) = sharedPrimalEdge f g := by
  rcases zfe_primalSubdiv_support_cases H hzH with hPE | hPM
  · obtain ⟨p, _hp, hzp⟩ := hPE
    rcases zfe_faceSubdiv_support_cases V hzV with hFE | hFM
    · obtain ⟨f, _hf, hzf⟩ := hFE
      exact absurd (hzp.symm.trans hzf) (zfe_primalEmb_ne_faceEmb p f)
    · obtain ⟨f, g, hfgE, hzf⟩ := hFM
      have hfg := V.adj_of_mem_edges hfgE
      exact absurd (hzp.symm.trans hzf) (zfe_primalEmb_ne_faceMid hfg)
  · obtain ⟨p, q, hpqE, hzp⟩ := hPM
    rcases zfe_faceSubdiv_support_cases V hzV with hFE | hFM
    · obtain ⟨f, _hf, hzf⟩ := hFE
      have hpq := H.adj_of_mem_edges hpqE
      exact absurd (hzp.symm.trans hzf) (zfe_primalMid_ne_faceEmb hpq)
    · obtain ⟨f, g, hfgE, hzf⟩ := hFM
      refine ⟨p, q, f, g, hpqE, hfgE, ?_⟩
      exact zfe_midpoint_sharedPrimalEdge
        (H.adj_of_mem_edges hpqE) (V.adj_of_mem_edges hfgE)
        (hzp.symm.trans hzf)



theorem zfe_liftWalk_edge_open
    (omega : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2))
    {x y : R} (w : (openSubgraphInduce 2 omega R).Walk x y)
    {e : Sym2 (Site 2)} (he : e ∈ (liftWalk omega R w).edges) :
    omega e = true := by
  have heMap : e ∈ w.edges.map (Sym2.map (projHom omega R)) := by
    change e ∈ (w.map (projHom omega R)).edges at he
    rw [Walk.edges_map (projHom omega R) w] at he
    exact he
  obtain ⟨e', he', hmap⟩ := List.mem_map.mp heMap
  induction e' using Sym2.inductionOn with
  | _ u v =>
      have huv := w.adj_of_mem_edges he'
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      simp only [projHom, Sym2.map_mk] at hmap
      rw [← hmap]
      exact huv.2






theorem zfe_faithfulMatchedExclusive (N : ℕ) :
    zfk_FaithfulMatchedExclusive N := by
  rw [zfk_FaithfulMatchedExclusive, Set.disjoint_left]
  intro omega hH hV
  change StatMech.RSW.Box.HorizontalCrossing omega
    (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) at hH
  change StatMech.RSW.Box.VerticalCrossing (fci_faceDualConfig omega)
    (-(N : ℤ)) (N : ℤ) (-(N : ℤ) - 1) (N : ℤ) at hV
  obtain ⟨xH, yH, hxyH⟩ := hH
  obtain ⟨xV, yV, hxyV⟩ := hV
  obtain ⟨wH⟩ := hxyH
  obtain ⟨wV⟩ := hxyV
  let RH := rect (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)
  let RV := rect (-(N : ℤ)) (N : ℤ) (-(N : ℤ) - 1) (N : ℤ)
  let H := liftWalk omega RH wH
  let V := liftWalk (fci_faceDualConfig omega) RV wV
  let Hd := zfe_primalSubdiv H
  let Vd := zfe_faceSubdiv V
  let alpha : ℤ := -2 * (N : ℤ)
  let beta : ℤ := 2 * (N : ℤ) + 2
  let c : ℤ := -2 * (N : ℤ) - 1
  let d : ℤ := 2 * (N : ℤ) + 1
  have hHsupport : ∀ z ∈ H.support, z ∈ RH := by
    intro z hz
    obtain ⟨z', _hz', rfl⟩ := liftWalk_support_mem omega RH wH hz
    exact z'.2
  have hVsupport : ∀ z ∈ V.support, z ∈ RV := by
    intro z hz
    obtain ⟨z', _hz', rfl⟩ :=
      liftWalk_support_mem (fci_faceDualConfig omega) RV wV hz
    exact z'.2
  have hHdbox : ∀ z ∈ Hd.support, z ∈ rect alpha beta c d := by
    intro z hz
    rcases zfe_primalSubdiv_support_cases H hz with he | hm
    · obtain ⟨p, hp, rfl⟩ := he
      have hpR := hHsupport p hp
      simp only [RH, mem_rect] at hpR
      simp only [alpha, beta, c, d, zfe_primalEmb, mem_rect,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · obtain ⟨p, q, hpq, rfl⟩ := hm
      have hpR := hHsupport p (H.fst_mem_support_of_mem_edges hpq)
      have hqR := hHsupport q (H.snd_mem_support_of_mem_edges hpq)
      simp only [RH, mem_rect] at hpR hqR
      simp only [alpha, beta, c, d, zfe_primalMid, mem_rect,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  have hVdbox : ∀ z ∈ Vd.support, z ∈ rect alpha beta c d := by
    intro z hz
    rcases zfe_faceSubdiv_support_cases V hz with he | hm
    · obtain ⟨f, hf, rfl⟩ := he
      have hfR := hVsupport f hf
      simp only [RV, mem_rect] at hfR
      simp only [alpha, beta, c, d, zfe_faceEmb, mem_rect,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · obtain ⟨f, g, hfg, rfl⟩ := hm
      have hfR := hVsupport f (V.fst_mem_support_of_mem_edges hfg)
      have hgR := hVsupport g (V.snd_mem_support_of_mem_edges hfg)
      simp only [RV, mem_rect] at hfR hgR
      simp only [alpha, beta, c, d, zfe_faceMid, mem_rect,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  let a0 : ℤ := 2 * (xV : Site 2) 0 + 1
  let b0 : ℤ := 2 * (yV : Site 2) 0 + 1
  have hVstart : zfe_faceEmb (xV : Site 2) = ![a0, c] := by
    have hxrow : (xV : Site 2) 1 = -(N : ℤ) - 1 := xV.2.2
    ext i
    fin_cases i
    · simp [zfe_faceEmb, a0]
    · simp [zfe_faceEmb, c, hxrow]
      omega
  have hVend : zfe_faceEmb (yV : Site 2) = ![b0, d] := by
    have hyrow : (yV : Site 2) 1 = (N : ℤ) := yV.2.2
    ext i
    fin_cases i <;> simp [zfe_faceEmb, b0, d, hyrow]
  let Vdc : (hypercubicLattice 2).Walk ![a0, c] ![b0, d] :=
    Vd.copy hVstart hVend
  have hVdcbox : ∀ z ∈ Vdc.support, z ∈ rect alpha beta c d := by
    intro z hz
    apply hVdbox z
    simpa [Vdc] using hz
  have ha0 : alpha ≤ a0 ∧ a0 ≤ beta := by
    have hx := (StatMech.RSW.Box.bottomSide_subset xV.2)
    simp only [mem_rect] at hx
    simp only [alpha, beta, a0]
    omega
  have hb0 : alpha ≤ b0 ∧ b0 ≤ beta := by
    have hy := (StatMech.RSW.Box.topSide_subset yV.2)
    simp only [mem_rect] at hy
    simp only [alpha, beta, b0]
    omega
  have hsep : ArcSeparatingSet {z | z ∈ Vdc.support} alpha beta c d :=
    jec_arcSeparatingSet alpha beta c d a0 b0 (by
      simp only [alpha, beta]; omega) (by simp only [c, d]; omega)
      ha0.1 ha0.2 hb0.1 hb0.2 Vdc hVdcbox _ (by intro p hp; exact hp)
  have hxHbox : zfe_primalEmb (xH : Site 2) ∈ rect alpha beta c d :=
    hHdbox _ Hd.start_mem_support
  have hyHbox : zfe_primalEmb (yH : Site 2) ∈ rect alpha beta c d :=
    hHdbox _ Hd.end_mem_support
  have hxH0 : zfe_primalEmb (xH : Site 2) 0 = alpha := by
    simp only [zfe_primalEmb, Matrix.cons_val_zero, alpha]
    have hx := xH.2.2
    omega
  have hyH0 : zfe_primalEmb (yH : Site 2) 0 = beta := by
    simp only [zfe_primalEmb, Matrix.cons_val_zero, beta]
    have hy := yH.2.2
    omega
  obtain ⟨z, hzH, hzV⟩ :=
    tpc_two_paths_cross_of_sep hsep hxHbox hyHbox hxH0 hyH0 Hd hHdbox
  have hzV' : z ∈ Vd.support := by simpa [Vdc] using hzV
  obtain ⟨p, q, f, g, hpq, hfg, hedge⟩ :=
    zfe_subdiv_meeting_edge H V hzH hzV'
  have hopen : omega s(p, q) = true :=
    zfe_liftWalk_edge_open omega RH wH hpq
  have hdual : fci_faceDualConfig omega s(f, g) = true :=
    zfe_liftWalk_edge_open (fci_faceDualConfig omega) RV wV hfg
  have hclosed : omega (sharedPrimalEdge f g) = false := by
    have hadj := V.adj_of_mem_edges hfg
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hadj] at hdual
    simpa using hdual
  rw [hedge] at hopen
  simp_all

theorem zfe_percolationProbability_zero :
    percolationProbability 2 (2⁻¹ : NNReal)
      StatMech.Universality.half_le_one = 0 :=
  zih_percolationProbability_zero_of_faithful_exclusive
    zfe_faithfulMatchedExclusive

theorem zfe_criticalProbability_eq_half :
    criticalProbability 2 = (1 : ℝ) / 2 := by
  apply zih_criticalProbability_eq_half_of_faithful_exclusive
    zfe_faithfulMatchedExclusive
  · intro a b _ha _hb
    exact rlc_horizontalCrossingEvent_measurableSet 0 a 0 b
  · intro n _hn
    exact rlc_verticalCrossingEvent_measurableSet 0 (n - 1) (-1) n
  · intro n _hn
    exact rlc_horizontalCrossingEvent_measurableSet (-1) n 0 (n - 1)

end StatMech.TwoDim
