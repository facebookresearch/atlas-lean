/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.EffectiveResistance
public import MathlibExt.Combinatorics.SimpleGraph.MatrixTree

import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Kirchhoff's effective resistance formula

The fraction of spanning trees containing an edge is the effective resistance across that edge
in a finite connected simple graph with unit conductances. Grounding the Laplacian at one
endpoint turns edge deletion into a change to a single diagonal entry, so Cramer's rule
and the matrix-tree theorem give the fraction.
-/

namespace MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
open Matrix

private theorem card_trees_delete_edge_add {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (u v : V) [DecidableRel (G.deleteEdges {s(u, v)}).Adj] :
    Nat.card {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v} +
        numSpanningTrees (G.deleteEdges {s(u, v)}) = numSpanningTrees G := by
  classical
  let S := {T : G.Subgraph // IsSpanningTree T}
  let p : S → Prop := fun T => T.1.Adj u v
  let A := {H : SimpleGraph V // H ≤ G ∧ H.IsTree}
  let H := G.deleteEdges {s(u, v)}
  have hle (K : SimpleGraph V) : K ≤ H ↔ K ≤ G ∧ ¬ K.Adj u v := by
    constructor
    · intro h
      exact ⟨h.trans (G.deleteEdges_le _), fun huv => (SimpleGraph.deleteEdges_adj.mp (h huv)).2
        (Set.mem_singleton _)⟩
    · rintro ⟨h, huv⟩ a b hab
      refine SimpleGraph.deleteEdges_adj.mpr ⟨h hab, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact huv hab
      · exact huv hab.symm
  have havoid : {T : S // ¬ p T} ≃ {K : SimpleGraph V // K ≤ H ∧ K.IsTree} := by
    refine ((spanningTreeSubgraphEquiv G).subtypeEquiv
      (q := fun K : A => ¬ K.1.Adj u v) (fun _ => Iff.rfl)).trans ?_
    refine (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun K : SimpleGraph V => K ≤ G ∧ K.IsTree) (fun K => ¬ K.Adj u v)).trans
      (Equiv.subtypeEquivRight ?_)
    intro K
    rw [hle]
    tauto
  have hin := Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (IsSpanningTree (G := G)) (fun T => T.Adj u v))
  rw [numSpanningTrees_eq_card_trees H, ← Nat.card_congr havoid, ← hin, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl p)

private theorem det_grounded_lapMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((G.lapMatrix ℝ).submatrix (Subtype.val : {x : V // x ≠ v} → V) Subtype.val).det =
      (numSpanningTrees G : ℝ) := by
  have hmap : (G.lapMatrix ℤ).map (Int.castRingHom ℝ) = G.lapMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.lapMatrix, Matrix.sub_apply, map_sub,
      SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp
  have hdet := congrArg (Int.castRingHom ℝ) (kirchhoff_matrix_tree_lapMatrix G v)
  rw [RingHom.map_det_submatrix, hmap] at hdet
  simpa using hdet

section WeightedMatrixTree

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem dart_eq_of_fst_snd {W : Type*} (H : SimpleGraph W) {d : H.Dart} {u v : W}
    (h1 : d.fst = u) (h2 : d.snd = v) (h : H.Adj u v) : d = ⟨(u, v), h⟩ := by
  obtain ⟨⟨a, b⟩, hab⟩ := d
  have ha : a = u := h1
  have hb : b = v := h2
  subst ha; subst hb
  rfl

private theorem sum_fst_snd (c : Sym2 V → ℝ) (u v : V) :
    (∑ d : G.Dart, (c d.edge / 2) * (if d.fst = u then (1:ℝ) else 0) *
      (if d.snd = v then 1 else 0)) = if G.Adj u v then c s(u, v) / 2 else 0 := by
  by_cases h : G.Adj u v
  · simp only [h, ↓reduceIte]
    rw [Fintype.sum_eq_single (⟨(u, v), h⟩ : G.Dart)]
    · simp
    · intro d hd
      by_cases h1 : d.fst = u
      · have h2 : d.snd ≠ v := by
          intro h2
          exact hd (dart_eq_of_fst_snd G h1 h2 h)
        simp [h1, h2]
      · simp [h1]
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro d _
    by_cases h1 : d.fst = u
    · have h2 : d.snd ≠ v := fun h2 => h (by rw [← h1, ← h2]; exact d.adj)
      simp [h1, h2]
    · simp [h1]

private theorem sum_fst_fst (c : Sym2 V → ℝ) (u v : V) :
    (∑ d : G.Dart, (c d.edge / 2) * (if d.fst = u then (1:ℝ) else 0) *
      (if d.fst = v then 1 else 0)) =
      if u = v then ∑ y ∈ G.neighborFinset u, c s(u, y) / 2 else 0 := by
  by_cases huv : u = v
  · subst huv
    have hstep : (∑ d : G.Dart, (c d.edge / 2) * (if d.fst = u then (1:ℝ) else 0) *
        (if d.fst = u then 1 else 0)) =
        ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = u), c d.edge / 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h1 : d.fst = u <;> simp [h1]
    rw [ite_eq_left rfl, hstep]
    refine Finset.sum_bij (fun d : G.Dart => fun _ => d.snd) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      exact (SimpleGraph.mem_neighborFinset G u d.snd).mpr (hd ▸ d.adj)
    · intro d₁ hd₁ d₂ hd₂ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd₁ hd₂
      ext <;> simp [hd₁, hd₂, h]
    · intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      exact ⟨⟨(u, y), hy⟩, by simp, rfl⟩
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      have he : d.edge = s(u, d.snd) := by
        change s(d.fst, d.snd) = s(u, d.snd)
        rw [hd]
      rw [he]
  · simp only [huv, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro d _
    by_cases h1 : d.fst = u
    · have h2 : d.fst ≠ v := fun h2 => huv (h1.symm.trans h2)
      rw [ite_eq_left h1, ite_eq_right h2, mul_one, mul_zero]
    · rw [ite_eq_right h1]; simp

private theorem sum_snd_snd (c : Sym2 V → ℝ) (u v : V) :
    (∑ d : G.Dart, (c d.edge / 2) * (if d.snd = u then (1:ℝ) else 0) *
      (if d.snd = v then 1 else 0)) =
      if u = v then ∑ y ∈ G.neighborFinset u, c s(u, y) / 2 else 0 := by
  rw [← sum_fst_fst G c u v]
  exact Fintype.sum_equiv (SimpleGraph.Dart.symm_involutive (G := G)).toPerm _ _
    (fun d => by simp [SimpleGraph.Dart.edge_symm])

private theorem laplacian_dart_apply (c : Sym2 V → ℝ) (u v : V) :
    EndpointMapMultigraph.laplacian (fun d : G.Dart => d.fst) (fun d : G.Dart => d.snd)
        (fun d => c d.edge / 2) u v =
      if u = v then ∑ y ∈ G.neighborFinset u, c s(u, y)
        else if G.Adj u v then -c s(u, v) else 0 := by
  rw [EndpointMapMultigraph.laplacian_apply]
  simp only [EndpointMapMultigraph.orientedIncidence_apply]
  have hexpand : ∀ d : G.Dart, (c d.edge / 2) *
      ((if d.fst = u then (1:ℝ) else 0) - (if d.snd = u then 1 else 0)) *
      ((if d.fst = v then (1:ℝ) else 0) - (if d.snd = v then 1 else 0)) =
      (c d.edge / 2) * (if d.fst = u then (1:ℝ) else 0) * (if d.fst = v then 1 else 0) -
        (c d.edge / 2) * (if d.fst = u then (1:ℝ) else 0) *
          (if d.snd = v then 1 else 0) -
        (c d.edge / 2) * (if d.fst = v then (1:ℝ) else 0) *
          (if d.snd = u then 1 else 0) +
        (c d.edge / 2) * (if d.snd = u then (1:ℝ) else 0) *
          (if d.snd = v then 1 else 0) := fun d => by ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_fst_fst G c u v, sum_fst_snd G c u v, sum_fst_snd G c v u, sum_snd_snd G c u v]
  by_cases huv : u = v
  · subst huv
    have hirr : ¬ G.Adj u u := fun h => G.irrefl h
    simp only [↓reduceIte, hirr, ↓reduceIte, sub_zero]
    have h2 : (∑ y ∈ G.neighborFinset u, c s(u, y) / 2) +
        (∑ y ∈ G.neighborFinset u, c s(u, y) / 2) = ∑ y ∈ G.neighborFinset u, c s(u, y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => by ring
    linarith
  · simp only [huv, ↓reduceIte]
    by_cases hadj : G.Adj u v
    · have hadj' : G.Adj v u := G.adj_comm u v |>.mp hadj
      simp only [hadj, hadj', ↓reduceIte]
      rw [show s(v, u) = s(u, v) from Sym2.eq_swap]
      ring
    · have hadj' : ¬ G.Adj v u := fun h => hadj (G.adj_comm v u |>.mp h)
      simp only [hadj, hadj', ↓reduceIte]
      ring

/-- Determinant after replacing one row by the row plus a multiple of `u`. -/
private theorem det_updateRow_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (i : ι) (u : ι → ℝ) (t : ℝ) :
    (M.updateRow i (M i + t • u)).det = M.det + t * (M.updateRow i u).det := by
  rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]

/-- Determinant after replacing two distinct rows by rows plus multiples of `u` and `-u`:
the quadratic term vanishes because the two new rows are proportional. -/
private theorem det_updateRow_add_smul_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) {i j : ι} (hij : i ≠ j) (u : ι → ℝ) (t : ℝ) :
    (M.updateRow i (M i + t • u) |>.updateRow j (M j + t • (-u))).det =
      M.det + t * ((M.updateRow i u).det - (M.updateRow j u).det) := by
  have hN := det_updateRow_add_smul M i u t
  have hcommA : (M.updateRow i (M i + t • u)).updateRow j (M j) =
      M.updateRow i (M i + t • u) := by
    rw [Matrix.updateRow_comm M hij, Matrix.updateRow_eq_self]
  have hmain : (M.updateRow i (M i + t • u) |>.updateRow j (M j + t • (-u))).det =
      (M.updateRow i (M i + t • u)).det +
        t * ((M.updateRow i (M i + t • u)).updateRow j (-u)).det := by
    rw [Matrix.det_updateRow_add, hcommA, Matrix.det_updateRow_smul]
  rw [hmain, hN]
  have hzero : ((M.updateRow i (M i + t • u)).updateRow j (-u)).det =
      - (M.updateRow j u).det := by
    have hcommB : (M.updateRow i (M i + t • u)).updateRow j (-u) =
        (M.updateRow j (-u)).updateRow i (M i + t • u) :=
      Matrix.updateRow_comm M hij _ _
    have hcommC : (M.updateRow j (-u)).updateRow i (M i) = M.updateRow j (-u) := by
      rw [Matrix.updateRow_comm M hij.symm, Matrix.updateRow_eq_self]
    have hstep : ((M.updateRow i (M i + t • u)).updateRow j (-u)).det =
        (M.updateRow j (-u)).det +
          t * ((M.updateRow j (-u)).updateRow i u).det := by
      rw [hcommB, Matrix.det_updateRow_add, hcommC, Matrix.det_updateRow_smul]
    rw [hstep]
    have hdet0 : ((M.updateRow j (-u)).updateRow i u).det = 0 := by
      have hcommD : (M.updateRow j (-u)).updateRow i u =
          (M.updateRow i u).updateRow j (-u) :=
        Matrix.updateRow_comm M hij.symm _ _
      have hneg : (-u : ι → ℝ) = (-1 : ℝ) • u := by
        funext k; simp [Pi.neg_apply]
      rw [hcommD, hneg, Matrix.det_updateRow_smul]
      have hrow : ((M.updateRow i u).updateRow j u) i = ((M.updateRow i u).updateRow j u) j := by
        simp [hij]
      rw [Matrix.det_zero_of_row_eq hij hrow, mul_zero]
    rw [hdet0, mul_zero, add_zero]
    have hneg : (-u : ι → ℝ) = (-1 : ℝ) • u := by
      funext k; simp [Pi.neg_apply]
    rw [hneg, Matrix.det_updateRow_smul]
    ring
  rw [hzero]
  ring

/-- The network Laplacian entry is affine in each conductance. -/
private theorem weightedLaplacianEntry_update_affine (c : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (u v : V) :
    (if u = v then ∑ y ∈ G.neighborFinset u, (Function.update c e₀ t) s(u, y)
      else if G.Adj u v then -(Function.update c e₀ t) s(u, v) else 0)
    = (if u = v then ∑ y ∈ G.neighborFinset u, (Function.update c e₀ 0) s(u, y)
      else if G.Adj u v then -(Function.update c e₀ 0) s(u, v) else 0)
      + t * ((if u = v then ∑ y ∈ G.neighborFinset u, (Function.update c e₀ 1) s(u, y)
      else if G.Adj u v then -(Function.update c e₀ 1) s(u, v) else 0)
      - (if u = v then ∑ y ∈ G.neighborFinset u, (Function.update c e₀ 0) s(u, y)
      else if G.Adj u v then -(Function.update c e₀ 0) s(u, v) else 0)) := by
  have hpoint : ∀ e : Sym2 V, Function.update c e₀ t e =
      Function.update c e₀ 0 e +
        t * (Function.update c e₀ 1 e - Function.update c e₀ 0 e) := by
    intro e
    by_cases he : e = e₀
    · subst he
      simp only [Function.update_self]
      ring
    · have h1 : Function.update c e₀ t e = c e := Function.update_of_ne he t c
      have h2 : Function.update c e₀ 0 e = c e := Function.update_of_ne he 0 c
      have h3 : Function.update c e₀ 1 e = c e := Function.update_of_ne he 1 c
      rw [h1, h2, h3]
      ring
  by_cases huv : u = v
  · subst huv
    simp only [↓reduceIte]
    have hsum : (∑ y ∈ G.neighborFinset u, (Function.update c e₀ t) s(u, y)) =
        ∑ y ∈ G.neighborFinset u, ((Function.update c e₀ 0) s(u, y) +
          t * ((Function.update c e₀ 1) s(u, y) - (Function.update c e₀ 0) s(u, y))) :=
      Finset.sum_congr rfl fun y _ => hpoint _
    rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  · simp only [huv, ↓reduceIte]
    by_cases hadj : G.Adj u v
    · simp only [hadj, ↓reduceIte]
      rw [hpoint]
      ring
    · simp only [hadj, ↓reduceIte]
      ring

/-- The difference between the Laplacian entries at conductances `1` and `0` on one
unordered pair `s(a, b)` is supported on the rows and columns of `a` and `b`. -/
private theorem diffEntry_eq (c : Sym2 V → ℝ) {a b : V} (hab : a ≠ b) (x : V)
    (i j : {y : V // y ≠ x}) :
    (if i.1 = j.1 then ∑ y ∈ G.neighborFinset i.1, (Function.update c s(a, b) 1) s(i.1, y)
      else if G.Adj i.1 j.1 then -(Function.update c s(a, b) 1) s(i.1, j.1) else 0)
    - (if i.1 = j.1 then ∑ y ∈ G.neighborFinset i.1, (Function.update c s(a, b) 0) s(i.1, y)
      else if G.Adj i.1 j.1 then -(Function.update c s(a, b) 0) s(i.1, j.1) else 0)
    = if i.1 = a then (if j.1 = a then (if G.Adj a b then (1:ℝ) else 0)
        else if j.1 = b then -(if G.Adj a b then (1:ℝ) else 0) else 0)
      else if i.1 = b then (if j.1 = b then (if G.Adj a b then (1:ℝ) else 0)
        else if j.1 = a then -(if G.Adj a b then (1:ℝ) else 0) else 0)
      else 0 := by
  classical
  have hdiff : ∀ e : Sym2 V, Function.update c s(a, b) 1 e - Function.update c s(a, b) 0 e =
      if e = s(a, b) then (1:ℝ) else 0 := by
    intro e
    by_cases he : e = s(a, b)
    · subst he
      simp only [Function.update_self, ↓reduceIte, sub_zero]
    · have h1 : Function.update c s(a, b) 1 e = c e := Function.update_of_ne he 1 c
      have h2 : Function.update c s(a, b) 0 e = c e := Function.update_of_ne he 0 c
      rw [h1, h2, ite_eq_right he, sub_self]
  have heq : ∀ i j : V, (s(i, j) = s(a, b) ↔ (i = a ∧ j = b) ∨ (i = b ∧ j = a)) :=
    fun i j => Sym2.eq_iff
  have hdiag : ∀ i : V,
      (∑ y ∈ G.neighborFinset i, (Function.update c s(a, b) 1) s(i, y)) -
        (∑ y ∈ G.neighborFinset i, (Function.update c s(a, b) 0) s(i, y)) =
        if i = a ∨ i = b then (if G.Adj a b then (1:ℝ) else 0) else 0 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    have hsum : (∑ y ∈ G.neighborFinset i,
        ((Function.update c s(a, b) 1) s(i, y) - (Function.update c s(a, b) 0) s(i, y))) =
        ∑ y ∈ G.neighborFinset i, (if s(i, y) = s(a, b) then (1:ℝ) else 0) :=
      Finset.sum_congr rfl fun y _ => hdiff _
    rw [hsum]
    by_cases hia : i = a
    · simp only [hia, true_or, ↓reduceIte]
      have hcond : ∀ y : V, (s(a, y) = s(a, b) ↔ y = b) := by
        intro y
        rw [heq]
        constructor
        · rintro (⟨-, h⟩ | ⟨h1, -⟩)
          · exact h
          · exact absurd h1 hab
        · intro h
          exact Or.inl ⟨rfl, h⟩
      simp only [hcond]
      rw [Finset.sum_ite_eq']
      simp [SimpleGraph.mem_neighborFinset, hia]
    · by_cases hib : i = b
      · simp only [hib, or_true, ↓reduceIte]
        have hcond : ∀ y : V, (s(b, y) = s(a, b) ↔ y = a) := by
          intro y
          rw [heq]
          constructor
          · rintro (⟨h1, -⟩ | ⟨-, h⟩)
            · exact absurd h1 hab.symm
            · exact h
          · intro h
            exact Or.inr ⟨rfl, h⟩
        simp only [hcond]
        rw [Finset.sum_ite_eq']
        simp [SimpleGraph.mem_neighborFinset, G.adj_comm, hib]
      · rw [ite_eq_right (by simp [hia, hib])]
        apply Finset.sum_eq_zero
        intro y _
        have hne : s(i, y) ≠ s(a, b) := by
          intro h
          rw [heq] at h
          rcases h with (⟨h1, -⟩ | ⟨h1, -⟩) <;> simp_all
        rw [ite_eq_right hne]
  by_cases hij : i.1 = j.1
  · obtain rfl : i = j := Subtype.ext hij
    simp only [↓reduceIte]
    rw [hdiag]
    by_cases hia : i.1 = a
    · simp [hia]
    · by_cases hib : i.1 = b
      · simp [hib, hab.symm]
      · simp [hia, hib]
  · by_cases hadj : G.Adj i.1 j.1
    · simp only [hij, ↓reduceIte, hadj, ↓reduceIte]
      have hsub : -(Function.update c s(a, b) 1) s(i.1, j.1) -
          -(Function.update c s(a, b) 0) s(i.1, j.1) =
          -(if s(i.1, j.1) = s(a, b) then (1:ℝ) else 0) := by
        rw [← hdiff]
        ring
      rw [hsub]
      by_cases hia : i.1 = a
      · by_cases hjb : j.1 = b
        · have hadj' : G.Adj a b := by rw [← hia, ← hjb]; exact hadj
          have he : s(i.1, j.1) = s(a, b) := by rw [hia, hjb]
          simp [hia, hjb, hadj', hab.symm]
        · have hja : j.1 ≠ a := fun h => hij (hia.trans h.symm)
          have hne : s(i.1, j.1) ≠ s(a, b) := by
            intro h
            rw [heq] at h
            rcases h with (⟨-, h⟩ | ⟨h1, -⟩)
            · exact hjb h
            · exact hab (hia.symm.trans h1)
          simp [hia, hjb, hja]
      · by_cases hib : i.1 = b
        · by_cases hja : j.1 = a
          · have hadj' : G.Adj a b := by
              have hba : G.Adj b a := by rw [← hib, ← hja]; exact hadj
              exact G.adj_comm _ _ |>.mp hba
            have he : s(i.1, j.1) = s(a, b) := by
              rw [hib, hja]
              exact Sym2.eq_swap
            simp [hib, hja, hadj', hab, hab.symm]
          · have hjb : j.1 ≠ b := fun h => hij (hib.trans h.symm)
            have hne : s(i.1, j.1) ≠ s(a, b) := by
              intro h
              rw [heq] at h
              rcases h with (⟨h1, -⟩ | ⟨-, h⟩)
              · exact hab.symm (hib.symm.trans h1)
              · exact hja h
            simp [hib, hja, hjb]
        · have hne : s(i.1, j.1) ≠ s(a, b) := by
            intro h
            rw [heq] at h
            rcases h with (⟨h1, -⟩ | ⟨h1, -⟩) <;> simp_all
          simp [hia, hib, hne]
    · simp only [hij, ↓reduceIte, hadj, ↓reduceIte, sub_self]
      by_cases hia : i.1 = a
      · by_cases hjb : j.1 = b
        · have hadj' : ¬ G.Adj a b := by rw [← hia, ← hjb]; exact hadj
          simp [hia, hjb, hadj', hab.symm]
        · have hja : j.1 ≠ a := fun h => hij (hia.trans h.symm)
          simp [hia, hjb, hja]
      · by_cases hib : i.1 = b
        · by_cases hja : j.1 = a
          · have hba : ¬ G.Adj b a := by rw [← hib, ← hja]; exact hadj
            have hadj' : ¬ G.Adj a b := fun h => hba (G.adj_comm _ _ |>.mp h)
            simp [hib, hja, hadj']
          · have hjb : j.1 ≠ b := fun h => hij (hib.trans h.symm)
            simp [hib, hja, hjb]
        · simp [hia, hib]

/-- The reduced weighted Laplacian: the dart-multigraph Laplacian with the row and
column of `x` removed. -/
private noncomputable def reducedWeightedLaplacian (c : Sym2 V → ℝ) (x : V) :
    Matrix {y : V // y ≠ x} {y : V // y ≠ x} ℝ :=
  (EndpointMapMultigraph.laplacian (fun d : G.Dart => d.fst) (fun d : G.Dart => d.snd)
    (fun d => c d.edge / 2)).submatrix (Subtype.val : {y : V // y ≠ x} → V)
    (Subtype.val : {y : V // y ≠ x} → V)

/-- Entries of the reduced weighted Laplacian. -/
private theorem reducedLaplacian_entry (c : Sym2 V → ℝ) (x : V)
    (i j : {y : V // y ≠ x}) :
    reducedWeightedLaplacian G c x i j
    = if i.1 = j.1 then ∑ y ∈ G.neighborFinset i.1, c s(i.1, y)
      else if G.Adj i.1 j.1 then -c s(i.1, j.1) else 0 := by
  change ((EndpointMapMultigraph.laplacian (fun d : G.Dart => d.fst) (fun d : G.Dart => d.snd)
    (fun d => c d.edge / 2)).submatrix (Subtype.val : {y : V // y ≠ x} → V)
    (Subtype.val : {y : V // y ≠ x} → V)) i j = _
  rw [Matrix.submatrix_apply, laplacian_dart_apply]

/-- Laplacian entries in a row whose vertex is not an endpoint of `s(a, b)` do not see
the conductance of `s(a, b)`. -/
private theorem entry_update_eq_of_ne (c : Sym2 V → ℝ) {a b : V}
    {u : V} (hua : u ≠ a) (hub : u ≠ b) (k : ℝ) (v : V) :
    (if u = v then ∑ y ∈ G.neighborFinset u, (Function.update c s(a, b) k) s(u, y)
      else if G.Adj u v then -(Function.update c s(a, b) k) s(u, v) else 0)
    = (if u = v then ∑ y ∈ G.neighborFinset u, c s(u, y)
      else if G.Adj u v then -c s(u, v) else 0) := by
  have hne : ∀ e : Sym2 V, (∃ w : V, e = s(u, w)) → e ≠ s(a, b) := by
    intro e ⟨w, hw⟩ h
    rw [hw, Sym2.eq_iff] at h
    rcases h with (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hua h1
    · exact hub h1
  by_cases huv : u = v
  · subst huv
    simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Function.update_of_ne (hne _ ⟨y, rfl⟩) k c]
  · simp only [huv, ↓reduceIte]
    by_cases hadj : G.Adj u v
    · simp only [hadj, ↓reduceIte]
      rw [Function.update_of_ne (hne _ ⟨v, rfl⟩) k c]
    · simp only [hadj, ↓reduceIte]

/-- The row of the reduced Laplacian at vertex `i` for the difference between
conductance `1` and conductance `0` on the pair `s(a, b)`. -/
private def updateRowDiff (c : Sym2 V → ℝ) {a b : V} (x : V) (i : V) :
    {y : V // y ≠ x} → ℝ := fun j =>
  (if i = j.1 then ∑ y ∈ G.neighborFinset i, (Function.update c s(a, b) 1) s(i, y)
    else if G.Adj i j.1 then -(Function.update c s(a, b) 1) s(i, j.1) else 0)
  - (if i = j.1 then ∑ y ∈ G.neighborFinset i, (Function.update c s(a, b) 0) s(i, y)
    else if G.Adj i j.1 then -(Function.update c s(a, b) 0) s(i, j.1) else 0)

/-- The row differences at the two endpoints of `s(a, b)` are negatives of each other. -/
private theorem updateRowDiff_neg (c : Sym2 V → ℝ) {a b : V} (hab : a ≠ b) (x : V)
    (ha : a ≠ x) (hb : b ≠ x) (j : {y : V // y ≠ x}) :
    updateRowDiff (G := G) c (a := a) (b := b) x b j =
      - updateRowDiff (G := G) c (a := a) (b := b) x a j := by
  change (if b = j.1 then ∑ y ∈ G.neighborFinset b, (Function.update c s(a, b) 1) s(b, y)
      else if G.Adj b j.1 then -(Function.update c s(a, b) 1) s(b, j.1) else 0)
    - (if b = j.1 then ∑ y ∈ G.neighborFinset b, (Function.update c s(a, b) 0) s(b, y)
      else if G.Adj b j.1 then -(Function.update c s(a, b) 0) s(b, j.1) else 0)
    = -((if a = j.1 then ∑ y ∈ G.neighborFinset a, (Function.update c s(a, b) 1) s(a, y)
      else if G.Adj a j.1 then -(Function.update c s(a, b) 1) s(a, j.1) else 0)
    - (if a = j.1 then ∑ y ∈ G.neighborFinset a, (Function.update c s(a, b) 0) s(a, y)
      else if G.Adj a j.1 then -(Function.update c s(a, b) 0) s(a, j.1) else 0))
  have hb := diffEntry_eq (G := G) c hab x (⟨b, hb⟩ : {y : V // y ≠ x}) j
  have ha := diffEntry_eq (G := G) c hab x (⟨a, ha⟩ : {y : V // y ≠ x}) j
  dsimp only at hb ha
  rw [hb, ha]
  by_cases hja : j.1 = a
  · simp [hja, hab, hab.symm]
  · by_cases hjb : j.1 = b
    · simp [hjb, hab.symm]
    · simp [hja, hjb]

/-- The determinant of the reduced weighted Laplacian is affine in each
conductance. -/
private theorem det_reducedWeightedLaplacian_update_affine (c : Sym2 V → ℝ) (e₀ : Sym2 V)
    (x : V) (t : ℝ) :
    (reducedWeightedLaplacian G (Function.update c e₀ t) x).det
      = (reducedWeightedLaplacian G (Function.update c e₀ 0) x).det
        + t * ((reducedWeightedLaplacian G (Function.update c e₀ 1) x).det
          - (reducedWeightedLaplacian G (Function.update c e₀ 0) x).det) := by
  refine Sym2.ind ?_ e₀
  intro a b
  by_cases hab : a = b
  · have hentry : ∀ (k : ℝ) (u v : V),
        (if u = v then ∑ y ∈ G.neighborFinset u, (Function.update c s(a, b) k) s(u, y)
          else if G.Adj u v then -(Function.update c s(a, b) k) s(u, v) else 0)
        = (if u = v then ∑ y ∈ G.neighborFinset u, c s(u, y)
          else if G.Adj u v then -c s(u, v) else 0) := by
      intro k u v
      by_cases huv : u = v
      · subst huv
        simp only [↓reduceIte]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hne : s(u, y) ≠ s(a, b) := by
          intro h
          rw [Sym2.eq_iff] at h
          rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · have hyu : y = u := h2.trans (hab ▸ h1).symm
            have hadj : G.Adj u y := (SimpleGraph.mem_neighborFinset G u y).mp hy
            exact G.irrefl (hyu.symm ▸ hadj)
          · have hyu : y = u := (h2.trans hab).trans h1.symm
            have hadj : G.Adj u y := (SimpleGraph.mem_neighborFinset G u y).mp hy
            exact G.irrefl (hyu.symm ▸ hadj)
        rw [Function.update_of_ne hne k c]
      · simp only [huv, ↓reduceIte]
        by_cases hadj : G.Adj u v
        · simp only [hadj, ↓reduceIte]
          have hne : s(u, v) ≠ s(a, b) := by
            intro h
            rw [Sym2.eq_iff] at h
            rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact huv (h1.trans (h2.trans hab.symm).symm)
            · exact huv (h1.trans (hab.symm.trans h2.symm))
          rw [Function.update_of_ne hne k c]
        · simp only [hadj, ↓reduceIte]
    have hmat : ∀ k : ℝ, reducedWeightedLaplacian G (Function.update c s(a, b) k) x
        = reducedWeightedLaplacian G (Function.update c s(a, b) 0) x := by
      intro k
      apply Matrix.ext
      intro i j
      rw [reducedLaplacian_entry, reducedLaplacian_entry, hentry k, hentry 0]
    rw [hmat t, hmat 1]
    simp
  · by_cases hax : a = x
    · have hbx : b ≠ x := fun h => hab (hax.trans h.symm)
      have hmat : ∀ s : ℝ,
          reducedWeightedLaplacian G (Function.update c s(a, b) s) x
            = (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow
              ⟨b, hbx⟩ ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨b, hbx⟩
                + s • updateRowDiff (G := G) c (a := a) (b := b) x b) := by
        intro s
        apply Matrix.ext
        intro k j
        by_cases hk : k = ⟨b, hbx⟩
        · rw [hk]
          simp only [Matrix.updateRow_apply, ↓reduceIte]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [reducedLaplacian_entry, reducedLaplacian_entry]
          change (if b = j.1 then ∑ y ∈ G.neighborFinset b, (Function.update c s(a, b) s) s(b, y)
              else if G.Adj b j.1 then -(Function.update c s(a, b) s) s(b, j.1) else 0)
            = (if b = j.1 then ∑ y ∈ G.neighborFinset b, (Function.update c s(a, b) 0) s(b, y)
              else if G.Adj b j.1 then -(Function.update c s(a, b) 0) s(b, j.1) else 0)
            + s * (updateRowDiff (G := G) c (a := a) (b := b) x b j)
          unfold updateRowDiff
          exact weightedLaplacianEntry_update_affine G c s(a, b) s b j.1
        · rw [Matrix.updateRow_apply, ite_eq_right hk]
          rw [reducedLaplacian_entry, reducedLaplacian_entry]
          have hka : k.1 ≠ a := fun h => k.2 (h.trans hax)
          have hkb : k.1 ≠ b := fun h => hk (Subtype.ext h)
          rw [entry_update_eq_of_ne G c (u := k.1) hka hkb s j.1,
            entry_update_eq_of_ne G c (u := k.1) hka hkb 0 j.1]
      have hd := det_updateRow_add_smul
        (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨b, hbx⟩
        (updateRowDiff (G := G) c (a := a) (b := b) x b) t
      rw [hmat t, hd]
      have hd1 := det_updateRow_add_smul
        (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨b, hbx⟩
        (updateRowDiff (G := G) c (a := a) (b := b) x b) 1
      rw [← hmat 1] at hd1
      have hdiff : (reducedWeightedLaplacian G (Function.update c s(a, b) 1) x).det -
          (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).det =
          ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow ⟨b, hbx⟩
            (updateRowDiff (G := G) c (a := a) (b := b) x b)).det := by
        rw [hd1]
        ring
      rw [hdiff]
    · by_cases hbx : b = x
      · have hax' : a ≠ x := hax
        have hmat : ∀ s : ℝ,
            reducedWeightedLaplacian G (Function.update c s(a, b) s) x
              = (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow
                ⟨a, hax'⟩ ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨a, hax'⟩
                  + s • updateRowDiff (G := G) c (a := a) (b := b) x a) := by
          intro s
          apply Matrix.ext
          intro k j
          by_cases hk : k = ⟨a, hax'⟩
          · rw [hk]
            simp only [Matrix.updateRow_apply, ↓reduceIte]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [reducedLaplacian_entry, reducedLaplacian_entry]
            change (if a = j.1 then ∑ y ∈ G.neighborFinset a, (Function.update c s(a, b) s) s(a, y)
                else if G.Adj a j.1 then -(Function.update c s(a, b) s) s(a, j.1) else 0)
              = (if a = j.1 then ∑ y ∈ G.neighborFinset a, (Function.update c s(a, b) 0) s(a, y)
                else if G.Adj a j.1 then -(Function.update c s(a, b) 0) s(a, j.1) else 0)
              + s * (updateRowDiff (G := G) c (a := a) (b := b) x a j)
            unfold updateRowDiff
            exact weightedLaplacianEntry_update_affine G c s(a, b) s a j.1
          · rw [Matrix.updateRow_apply, ite_eq_right hk]
            rw [reducedLaplacian_entry, reducedLaplacian_entry]
            have hka : k.1 ≠ a := fun h => hk (Subtype.ext h)
            have hkb : k.1 ≠ b := fun h => k.2 (h.trans hbx)
            rw [entry_update_eq_of_ne G c (u := k.1) hka hkb s j.1,
              entry_update_eq_of_ne G c (u := k.1) hka hkb 0 j.1]
        have hd := det_updateRow_add_smul
          (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨a, hax'⟩
          (updateRowDiff (G := G) c (a := a) (b := b) x a) t
        rw [hmat t, hd]
        have hd1 := det_updateRow_add_smul
          (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨a, hax'⟩
          (updateRowDiff (G := G) c (a := a) (b := b) x a) 1
        rw [← hmat 1] at hd1
        have hdiff : (reducedWeightedLaplacian G (Function.update c s(a, b) 1) x).det -
            (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).det =
            ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow ⟨a, hax'⟩
              (updateRowDiff (G := G) c (a := a) (b := b) x a)).det := by
          rw [hd1]
          ring
        rw [hdiff]
      · have hne_ij : (⟨a, hax⟩ : {y : V // y ≠ x}) ≠ ⟨b, hbx⟩ := by
          intro h
          exact hab (congrArg Subtype.val h)
        have hmat : ∀ s : ℝ,
            reducedWeightedLaplacian G (Function.update c s(a, b) s) x
              = ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow
                ⟨a, hax⟩ ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨a, hax⟩
                  + s • updateRowDiff (G := G) c (a := a) (b := b) x a)).updateRow
                ⟨b, hbx⟩ ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) ⟨b, hbx⟩
                  + s • (-updateRowDiff (G := G) c (a := a) (b := b) x a)) := by
          intro s
          apply Matrix.ext
          intro k j
          by_cases hka : k = ⟨a, hax⟩
          · rw [hka]
            simp only [Matrix.updateRow_apply, hne_ij, ↓reduceIte]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [reducedLaplacian_entry, reducedLaplacian_entry]
            change (if a = j.1 then ∑ y ∈ G.neighborFinset a, (Function.update c s(a, b) s) s(a, y)
                else if G.Adj a j.1 then -(Function.update c s(a, b) s) s(a, j.1) else 0)
              = (if a = j.1 then ∑ y ∈ G.neighborFinset a, (Function.update c s(a, b) 0) s(a, y)
                else if G.Adj a j.1 then -(Function.update c s(a, b) 0) s(a, j.1) else 0)
              + s * (updateRowDiff (G := G) c (a := a) (b := b) x a j)
            unfold updateRowDiff
            exact weightedLaplacianEntry_update_affine G c s(a, b) s a j.1
          · by_cases hkb : k = ⟨b, hbx⟩
            · rw [hkb]
              simp only [Matrix.updateRow_apply, ↓reduceIte]
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
              rw [reducedLaplacian_entry, reducedLaplacian_entry]
              have hneg := updateRowDiff_neg (G := G) c hab x hax hbx j
              have haff := weightedLaplacianEntry_update_affine G c s(a, b) s b j.1
              have hdiffb : (if b = j.1 then
                    ∑ y ∈ G.neighborFinset b, (Function.update c s(a, b) 1) s(b, y)
                    else if G.Adj b j.1 then -(Function.update c s(a, b) 1) s(b, j.1)
                    else 0)
                  - (if b = j.1 then
                    ∑ y ∈ G.neighborFinset b, (Function.update c s(a, b) 0) s(b, y)
                    else if G.Adj b j.1 then -(Function.update c s(a, b) 0) s(b, j.1)
                    else 0)
                  = -updateRowDiff (G := G) c (a := a) (b := b) x a j := by
                rw [← hneg]
                rfl
              rw [haff, hdiffb]
            · simp only [Matrix.updateRow_apply, ite_eq_right hkb, ite_eq_right hka]
              rw [reducedLaplacian_entry, reducedLaplacian_entry]
              have hk1 : k.1 ≠ a := fun h => hka (Subtype.ext h)
              have hk2 : k.1 ≠ b := fun h => hkb (Subtype.ext h)
              rw [entry_update_eq_of_ne G c (u := k.1) hk1 hk2 s j.1,
                entry_update_eq_of_ne G c (u := k.1) hk1 hk2 0 j.1]
        have hd := det_updateRow_add_smul_neg
          (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) hne_ij
          (updateRowDiff (G := G) c (a := a) (b := b) x a) t
        rw [hmat t, hd]
        have hd1 := det_updateRow_add_smul_neg
          (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x) hne_ij
          (updateRowDiff (G := G) c (a := a) (b := b) x a) 1
        rw [← hmat 1] at hd1
        have hdiff : (reducedWeightedLaplacian G (Function.update c s(a, b) 1) x).det -
            (reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).det =
            ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow ⟨a, hax⟩
              (updateRowDiff (G := G) c (a := a) (b := b) x a)).det -
            ((reducedWeightedLaplacian G (Function.update c s(a, b) 0) x).updateRow ⟨b, hbx⟩
              (updateRowDiff (G := G) c (a := a) (b := b) x a)).det := by
          rw [hd1]
          ring
        rw [hdiff]

open Classical in
/-- The weighted spanning-tree sum as a sum over a finset of subgraphs. -/
private theorem weightedTreeSum_eq_filterSum (c : Sym2 V → ℝ) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e)
      = ∑ T ∈ Finset.univ.filter (fun T : G.Subgraph => IsSpanningTree T),
        ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, c e := by
  have : Fintype {T : G.Subgraph // IsSpanningTree T} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_bij (fun T _ => T.1) ?_ ?_ ?_ ?_
  · intro T _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.2⟩
  · intro T₁ _ T₂ _ h
    exact Subtype.ext h
  · intro T hT
    rw [Finset.mem_filter] at hT
    exact ⟨⟨T, hT.2⟩, Finset.mem_univ _, rfl⟩
  · intro T _
    have : Fintype ↥T.1.edgeSet := Fintype.ofFinite _
    rw [finprod_mem_eq_toFinset_prod]
    have hset : T.1.edgeSet.toFinset = (Set.toFinite T.1.edgeSet).toFinset := by
      ext e
      simp [Set.mem_toFinset]
    rw [hset]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The weighted spanning-tree sum is affine in each conductance. -/
private theorem weightedTreeSum_update_affine [Finite V] (c : Sym2 V → ℝ) (e₀ : Sym2 V)
    (t : ℝ) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T},
        ∏ᶠ e ∈ T.1.edgeSet, (Function.update c e₀ t) e)
      = (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T},
          ∏ᶠ e ∈ T.1.edgeSet, (Function.update c e₀ 0) e)
        + t * ((∑ᶠ T : {T : G.Subgraph // IsSpanningTree T},
            ∏ᶠ e ∈ T.1.edgeSet, (Function.update c e₀ 1) e)
          - (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T},
            ∏ᶠ e ∈ T.1.edgeSet, (Function.update c e₀ 0) e)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  rw [weightedTreeSum_eq_filterSum, weightedTreeSum_eq_filterSum,
    weightedTreeSum_eq_filterSum]
  have hprod : ∀ T : G.Subgraph,
      ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ t) e
        = ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ 0) e
          + t * (∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ 1) e
            - ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ 0) e) := by
    intro T
    by_cases hmem : e₀ ∈ (Set.toFinite T.edgeSet).toFinset
    · have hrest : ∀ s : ℝ, ∏ e ∈ (Set.toFinite T.edgeSet).toFinset.erase e₀,
          (Function.update c e₀ s) e
          = ∏ e ∈ (Set.toFinite T.edgeSet).toFinset.erase e₀, c e := by
        intro s
        refine Finset.prod_congr rfl fun e he => ?_
        exact Function.update_of_ne (Finset.ne_of_mem_erase he) s c
      have hexpand : ∀ s : ℝ, ∏ e ∈ (Set.toFinite T.edgeSet).toFinset,
          (Function.update c e₀ s) e
          = (Function.update c e₀ s) e₀ *
            ∏ e ∈ (Set.toFinite T.edgeSet).toFinset.erase e₀, c e := by
        intro s
        rw [← Finset.mul_prod_erase _ _ hmem, hrest]
      rw [hexpand t, hexpand 0, hexpand 1]
      simp only [Function.update_self]
      ring
    · have heq : ∀ s : ℝ, ∏ e ∈ (Set.toFinite T.edgeSet).toFinset,
          (Function.update c e₀ s) e
          = ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, c e := by
        intro s
        refine Finset.prod_congr rfl fun e he => ?_
        have hne : e ≠ e₀ := by
          intro h
          exact hmem (h ▸ he)
        exact Function.update_of_ne hne s c
      rw [heq t, heq 0, heq 1]
      ring
  have hsum : (∑ T ∈ Finset.univ.filter (fun T : G.Subgraph => IsSpanningTree T),
        ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ t) e)
      = ∑ T ∈ Finset.univ.filter (fun T : G.Subgraph => IsSpanningTree T),
        (∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ 0) e
          + t * (∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ 1) e
            - ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, (Function.update c e₀ 0) e)) :=
    Finset.sum_congr rfl fun T _ => hprod T
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- The weighted matrix-tree theorem for `0`/`1` conductances: the spanning-tree sum
counts the spanning trees of the subgraph of edges of conductance `1`, and the
determinant is its number by the unweighted matrix-tree theorem. -/
private theorem weightedTreeSum_eq_det_of_bool (c : Sym2 V → ℝ) (x : V)
    (hc : ∀ e, c e = 0 ∨ c e = 1) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e)
      = (reducedWeightedLaplacian G c x).det := by
  classical
  set S : Set (Sym2 V) := {e | e ∈ G.edgeSet ∧ c e = 0} with hS
  set H : SimpleGraph V := G.deleteEdges S with hH
  have hHle : H ≤ G := G.deleteEdges_le S
  have hHadj : ∀ {u v : V}, H.Adj u v ↔ G.Adj u v ∧ c s(u, v) = 1 := by
    intro u v
    rw [hH, SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨hadj, hnot⟩
      refine ⟨hadj, ?_⟩
      rcases hc s(u, v) with h0 | h1
      · exact absurd ⟨(SimpleGraph.mem_edgeSet G).mpr hadj, h0⟩ hnot
      · exact h1
    · rintro ⟨hadj, h1⟩
      refine ⟨hadj, ?_⟩
      rintro ⟨-, h0⟩
      rw [h1] at h0
      exact one_ne_zero h0
  have hLHS : (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e)
      = ((Finset.univ.filter (fun T : G.Subgraph =>
          IsSpanningTree T ∧ ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1)).card : ℝ) := by
    rw [weightedTreeSum_eq_filterSum]
    have hterm : ∀ T : G.Subgraph, ∏ e ∈ (Set.toFinite T.edgeSet).toFinset, c e
        = if (∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1) then (1:ℝ) else 0 := by
      intro T
      by_cases hP : ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1
      · rw [ite_eq_left hP]
        exact Finset.prod_eq_one hP
      · rw [ite_eq_right hP]
        have hex : ∃ e ∈ (Set.toFinite T.edgeSet).toFinset, c e ≠ 1 := by
          by_contra hcon
          apply hP
          intro e he
          by_contra hne
          exact hcon ⟨e, he, hne⟩
        obtain ⟨e, he, hne⟩ := hex
        have h0 : c e = 0 := (hc e).elim id (fun h1 => absurd h1 hne)
        exact Finset.prod_eq_zero he h0
    rw [Finset.sum_congr rfl fun T _ => hterm T]
    calc (∑ T ∈ Finset.univ.filter (fun T : G.Subgraph => IsSpanningTree T),
            (if (∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1) then (1:ℝ) else 0))
          = (((Finset.univ.filter (fun T : G.Subgraph => IsSpanningTree T)).filter
              (fun T : G.Subgraph =>
                ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1)).card : ℝ) := by
            exact Finset.sum_boole (fun T : G.Subgraph =>
              ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1) _
        _ = ((Finset.univ.filter (fun T : G.Subgraph =>
              IsSpanningTree T ∧ ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1)).card : ℝ) := by
            rw [Finset.filter_filter]
  have hcard : (Finset.univ.filter (fun T : G.Subgraph =>
        IsSpanningTree T ∧ ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1)).card
      = numSpanningTrees H := by
    have hcard2 : numSpanningTrees H
        = (Finset.univ.filter (fun H' : SimpleGraph V => H' ≤ H ∧ H'.IsTree)).card := by
      rw [numSpanningTrees_eq_card_trees, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard2]
    set S₁ : Finset G.Subgraph := Finset.univ.filter (fun T : G.Subgraph =>
      IsSpanningTree T ∧ ∀ e ∈ (Set.toFinite T.edgeSet).toFinset, c e = 1) with hS₁
    refine Finset.card_bij (fun (T : G.Subgraph) (_ : T ∈ S₁) => T.spanningCoe) ?_ ?_ ?_
    · intro T hT
      simp only [hS₁, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rw [Finset.mem_filter]
      obtain ⟨⟨hspan, htree⟩, hP⟩ := hT
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [SimpleGraph.le_iff_adj]
        intro u v hadj
        rw [SimpleGraph.Subgraph.spanningCoe_adj] at hadj
        exact hHadj.mpr ⟨hadj.adj_sub, hP _ (by
          rw [Set.Finite.mem_toFinset]
          exact (SimpleGraph.Subgraph.mem_edgeSet).mpr hadj)⟩
      · exact (SimpleGraph.Iso.isTree_iff (T.spanningCoeEquivCoeOfSpanning hspan)).mpr htree
    · intro T₁ hT₁ T₂ hT₂ h
      apply SimpleGraph.Subgraph.ext
      · simp only [hS₁, Finset.mem_filter, Finset.mem_univ, true_and] at hT₁ hT₂
        have hv1 := SimpleGraph.Subgraph.isSpanning_iff.mp hT₁.1.1
        have hv2 := SimpleGraph.Subgraph.isSpanning_iff.mp hT₂.1.1
        rw [hv1, hv2]
      · funext v w
        rw [← SimpleGraph.Subgraph.spanningCoe_adj, h, SimpleGraph.Subgraph.spanningCoe_adj]
    · intro H' hH'
      rw [Finset.mem_filter] at hH'
      obtain ⟨-, hleH, htree⟩ := hH'
      have hleG : H' ≤ G := hleH.trans hHle
      refine ⟨SimpleGraph.toSubgraph H' hleG, ?_, ?_⟩
      · rw [hS₁, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ⟨SimpleGraph.toSubgraph.isSpanning H' hleG, ?_⟩, ?_⟩
        · have hspan_eq : (SimpleGraph.toSubgraph H' hleG).spanningCoe = H' := by
            apply SimpleGraph.ext
            funext v w
            rw [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.toSubgraph_adj]
          have h1 : (SimpleGraph.toSubgraph H' hleG).spanningCoe.IsTree :=
            hspan_eq.symm ▸ htree
          exact (SimpleGraph.Iso.isTree_iff (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning _
            (SimpleGraph.toSubgraph.isSpanning H' hleG))).mp h1
        · intro e he
          rw [Set.Finite.mem_toFinset] at he
          induction e using Sym2.ind with
          | _ u v =>
          have hadj : (SimpleGraph.toSubgraph H' hleG).Adj u v :=
            (SimpleGraph.Subgraph.mem_edgeSet).mp he
          rw [SimpleGraph.toSubgraph_adj] at hadj
          exact (hHadj.mp (hleH hadj)).2
      · have hspan_eq : (SimpleGraph.toSubgraph H' hleG).spanningCoe = H' := by
          apply SimpleGraph.ext
          funext v w
          rw [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.toSubgraph_adj]
        exact hspan_eq
  have hRHS : (reducedWeightedLaplacian G c x).det = (numSpanningTrees H : ℝ) := by
    have hmat : reducedWeightedLaplacian G c x
        = (H.lapMatrix ℝ).submatrix (Subtype.val : {y : V // y ≠ x} → V)
          (Subtype.val : {y : V // y ≠ x} → V) := by
      apply Matrix.ext
      intro i j
      rw [reducedLaplacian_entry, Matrix.submatrix_apply]
      simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
        Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
      by_cases hij : i.1 = j.1
      · obtain rfl : i = j := Subtype.ext hij
        simp only [↓reduceIte]
        have hsum : (∑ y ∈ G.neighborFinset i.1, c s(i.1, y)) = (H.degree i.1 : ℝ) := by
          have h1 : ∀ y ∈ G.neighborFinset i.1, c s(i.1, y)
              = if c s(i.1, y) = 1 then (1:ℝ) else 0 := by
            intro y _
            rcases hc s(i.1, y) with h0 | h1
            · simp [h0]
            · simp [h1]
          rw [Finset.sum_congr rfl h1, Finset.sum_boole]
          have hfin : (G.neighborFinset i.1).filter (fun y => c s(i.1, y) = 1)
              = H.neighborFinset i.1 := by
            ext y
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
            constructor
            · rintro ⟨hadj, h1⟩
              exact hHadj.mpr ⟨hadj, h1⟩
            · intro hadj
              exact ⟨(hHadj.mp hadj).1, (hHadj.mp hadj).2⟩
          rw [hfin, ← SimpleGraph.card_neighborFinset_eq_degree]
        rw [hsum]
        have hirr : ¬ H.Adj i.1 i.1 := fun h => H.irrefl h
        simp only [↓reduceIte, hirr, sub_zero]
      · by_cases hadj : G.Adj i.1 j.1
        · by_cases hH' : H.Adj i.1 j.1
          · have hc1 : c s(i.1, j.1) = 1 := (hHadj.mp hH').2
            simp [hij, hadj, hH', hc1]
          · have hc0 : c s(i.1, j.1) = 0 := by
              rcases hc s(i.1, j.1) with h0 | h1
              · exact h0
              · exact absurd (hHadj.mpr ⟨hadj, h1⟩) hH'
            simp [hij, hadj, hH', hc0]
        · have hH' : ¬ H.Adj i.1 j.1 := fun h => hadj (hHadj.mp h).1
          simp [hij, hadj, hH']
    rw [hmat]
    exact det_grounded_lapMatrix H x
  rw [hLHS, hcard, hRHS]

/-- Two functions of the conductances, each affine in each coordinate and equal
on `0`/`1` conductances, are equal everywhere. -/
private theorem eq_of_affine_of_bool {E : Type*} [Finite E] [DecidableEq E]
    (F Gc : (E → ℝ) → ℝ)
    (hF : ∀ (c : E → ℝ) (e : E) (t : ℝ), F (Function.update c e t)
      = F (Function.update c e 0) + t * (F (Function.update c e 1) - F (Function.update c e 0)))
    (hG : ∀ (c : E → ℝ) (e : E) (t : ℝ), Gc (Function.update c e t)
      = Gc (Function.update c e 0) + t * (Gc (Function.update c e 1) - Gc (Function.update c e 0)))
    (h01 : ∀ c : E → ℝ, (∀ e, c e = 0 ∨ c e = 1) → F c = Gc c) :
    ∀ c, F c = Gc c := by
  have : Fintype E := Fintype.ofFinite E
  have key : ∀ n : ℕ, ∀ c : E → ℝ,
      (Finset.univ.filter (fun e => c e ≠ 0 ∧ c e ≠ 1)).card ≤ n → F c = Gc c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hle
      by_cases hbad : (Finset.univ.filter (fun e => c e ≠ 0 ∧ c e ≠ 1)).card = 0
      · apply h01
        intro e
        by_contra hcon
        have hbad2 : c e ≠ 0 ∧ c e ≠ 1 :=
          ⟨fun h0 => hcon (Or.inl h0), fun h1 => hcon (Or.inr h1)⟩
        have hmem : e ∈ Finset.univ.filter (fun e => c e ≠ 0 ∧ c e ≠ 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad2⟩
        rw [Finset.card_eq_zero] at hbad
        rw [hbad] at hmem
        exact Finset.notMem_empty e hmem
      · have hpos : 0 < (Finset.univ.filter (fun e => c e ≠ 0 ∧ c e ≠ 1)).card :=
          Nat.pos_of_ne_zero hbad
        obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter] at he
        obtain ⟨-, he0, he1⟩ := he
        have hupd : ∀ (s : ℝ), s = 0 ∨ s = 1 →
            (Finset.univ.filter (fun e' => (Function.update c e s) e' ≠ 0
              ∧ (Function.update c e s) e' ≠ 1)).card
              < (Finset.univ.filter (fun e' => c e' ≠ 0 ∧ c e' ≠ 1)).card := by
          intro s hs
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro e' he'
            rw [Finset.mem_filter] at he' ⊢
            refine ⟨Finset.mem_univ _, ?_⟩
            obtain ⟨-, h0, h1⟩ := he'
            have hne : e' ≠ e := by
              intro h
              subst h
              rw [Function.update_self] at h0 h1
              rcases hs with rfl | rfl
              · exact h0 rfl
              · exact h1 rfl
            rw [Function.update_of_ne hne s c] at h0 h1
            exact ⟨h0, h1⟩
          · intro heq
            have hmem : e ∈ Finset.univ.filter (fun e' => c e' ≠ 0 ∧ c e' ≠ 1) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨he0, he1⟩⟩
            have hnot : e ∉ Finset.univ.filter (fun e' => (Function.update c e s) e' ≠ 0
                ∧ (Function.update c e s) e' ≠ 1) := by
              intro hmem2
              rw [Finset.mem_filter] at hmem2
              obtain ⟨-, h0, h1⟩ := hmem2
              rw [Function.update_self] at h0 h1
              rcases hs with rfl | rfl
              · exact h0 rfl
              · exact h1 rfl
            exact hnot (heq ▸ hmem)
        have hlt0 := hupd 0 (Or.inl rfl)
        have hlt1 := hupd 1 (Or.inr rfl)
        have ih0 := ih _ (Nat.lt_of_lt_of_le hlt0 hle) (Function.update c e 0) le_rfl
        have ih1 := ih _ (Nat.lt_of_lt_of_le hlt1 hle) (Function.update c e 1) le_rfl
        have hself : Function.update c e (c e) = c := by
          funext e'
          by_cases h : e' = e
          · subst h
            rw [Function.update_self]
          · rw [Function.update_of_ne h (c e) c]
        calc F c = F (Function.update c e (c e)) := by rw [hself]
          _ = F (Function.update c e 0)
              + c e * (F (Function.update c e 1) - F (Function.update c e 0)) :=
            hF c e (c e)
          _ = Gc (Function.update c e 0)
              + c e * (Gc (Function.update c e 1) - Gc (Function.update c e 0)) := by
            rw [ih0, ih1]
          _ = Gc (Function.update c e (c e)) := (hG c e (c e)).symm
          _ = Gc c := by rw [hself]
  exact fun c => key _ c le_rfl

end WeightedMatrixTree

private theorem grounded_lapMatrix_delete_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    [DecidableRel (G.deleteEdges {s(u, v)}).Adj] :
    let A : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
      (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val
    let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
    (((G.deleteEdges {s(u, v)}).lapMatrix ℝ).submatrix
      (Subtype.val : {x : V // x ≠ v} → V) Subtype.val) =
        A.updateCol i ((fun x => A x i) - Pi.single i 1) := by
  classical
  dsimp only
  let H := G.deleteEdges {s(u, v)}
  have hadj {x y : V} (hx : x ≠ v) : H.Adj x y ↔ G.Adj x y ∧ ¬ (x = u ∧ y = v) := by
    simp [H, SimpleGraph.deleteEdges_adj, hx]
  have hdeg {x : V} (hx : x ≠ v) :
      (H.degree x : ℝ) = (G.degree x : ℝ) - if x = u then 1 else 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    by_cases hxu : x = u
    · subst x
      have hfin : H.neighborFinset u = (G.neighborFinset u).erase v := by
        ext y
        simp [Finset.mem_erase, SimpleGraph.mem_neighborFinset, hadj huv.ne, and_comm]
      have hmem := (G.mem_neighborFinset u v).2 huv
      rw [hfin, Finset.card_erase_of_mem hmem, Nat.cast_sub (Finset.card_pos.mpr ⟨v, hmem⟩)]
      simp
    · have hfin : H.neighborFinset x = G.neighborFinset x := by
        ext y
        simp [SimpleGraph.mem_neighborFinset, hadj hx, hxu]
      simp [hfin, hxu]
  let A : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
    (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val
  let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
  change (H.lapMatrix ℝ).submatrix Subtype.val Subtype.val =
    A.updateCol i ((fun x => A x i) - Pi.single i 1)
  ext x y
  have hxy : H.Adj x.1 y.1 ↔ G.Adj x.1 y.1 := by simp [hadj x.2, y.2]
  have hdeg' : (H.degree x.1 : ℝ) = (G.degree x.1 : ℝ) - if x = i then 1 else 0 := by
    simpa only [Subtype.ext_iff] using hdeg x.2
  have hentry : (H.lapMatrix ℝ) x.1 y.1 =
      A x y - if x = i ∧ y = i then 1 else 0 := by
    simp only [A, Matrix.submatrix_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, hxy]
    by_cases h : x = y
    · subst y
      simp only [ite_true, and_self, hdeg']
      ring
    · have hval : x.1 ≠ y.1 := fun h' => h (Subtype.ext h')
      have hne : ¬ (x = i ∧ y = i) := fun ⟨hx, hy⟩ => h (hx.trans hy.symm)
      simp [hval, hne]
  rw [Matrix.submatrix_apply, hentry]
  by_cases hy : y = i
  · subst y
    simp [Pi.single_apply]
  · simp [hy]

private theorem exists_grounded_potential {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    ∃ f : V → ℝ, f v = 0 ∧
      G.lapMatrix ℝ *ᵥ f = Pi.single u 1 - Pi.single v 1 := by
  let d : G.Dart := ⟨(u, v), huv⟩
  let a : G.Dart → V := fun d => d.fst
  let b : G.Dart → V := fun d => d.snd
  have hmem : Pi.single u 1 - Pi.single v 1 ∈ LinearMap.range (G.lapMatrix ℝ).mulVecLin := by
    rw [← EndpointMapMultigraph.laplacian_dart_eq_lapMatrix,
      EndpointMapMultigraph.range_laplacian_eq_range_orientedIncidence _ _
        (fun _ => show (0 : ℝ) < 1 / 2 by norm_num) (fun d => d.adj.ne)]
    refine ⟨Pi.single d 1, ?_⟩
    change EndpointMapMultigraph.orientedIncidence a b *ᵥ Pi.single d 1 = _
    rw [Matrix.mulVec_single_one]
    ext x
    simp [a, b, d, EndpointMapMultigraph.orientedIncidence_apply, Pi.single_apply, eq_comm]
  obtain ⟨f, hf⟩ := hmem
  refine ⟨f - f v • 1, by simp, ?_⟩
  change G.lapMatrix ℝ *ᵥ f = _ at hf
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero,
    sub_zero, hf]

public section

/-- **Kirchhoff's effective resistance formula.** In a finite connected simple graph `G`, for
every edge `uv` the fraction of spanning trees of `G` that contain `uv` equals the effective
resistance between `u` and `v` with unit conductances, that is
`P[uv ∈ T] = R_eff(u, v)` for a uniform spanning tree `T` (R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Cambridge University Press 2016, corrected online version of
19 August 2026, Section 4.2, Kirchhoff's Effective Resistance Formula, with `c ≡ 1`). The
effective resistance is that of the multigraph of darts of `G` with conductance `1/2` on each
dart, whose Laplacian is `SimpleGraph.lapMatrix ℝ G`
(`EndpointMapMultigraph.laplacian_dart_eq_lapMatrix`), so that each edge of `G` is one unit
resistor. -/
theorem card_spanningTree_adj_div_numSpanningTrees {V : Type*} [Fintype V]
    [DecidableEq V] (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) {u v : V}
    (huv : G.Adj u v) :
    (Nat.card {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v} : ℝ) / numSpanningTrees G =
      EndpointMapMultigraph.effectiveResistance (fun d : G.Dart => d.fst)
        (fun d : G.Dart => d.snd) (fun _ => (1 / 2 : ℝ)) u v := by
  classical
  let H := G.deleteEdges {s(u, v)}
  let : DecidableRel H.Adj := Classical.decRel _
  let A : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℝ :=
    (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val
  let i : {x : V // x ≠ v} := ⟨u, huv.ne⟩
  let b : {x : V // x ≠ v} → ℝ := Pi.single i 1
  obtain ⟨f, hfv, hf⟩ := exists_grounded_potential huv
  have hr := (EndpointMapMultigraph.effectiveResistance_eq_sub_of_laplacian_mulVec
    (fun d : G.Dart => d.fst) (fun d => d.snd)
    (show 0 ≤ (fun _ : G.Dart => (1 / 2 : ℝ)) from fun _ => by norm_num) huv.ne
    (by rwa [EndpointMapMultigraph.laplacian_dart_eq_lapMatrix])).1
  rw [hfv, sub_zero] at hr
  let g : {x : V // x ≠ v} → ℝ := fun x => f x
  have hground : A *ᵥ g = b := by
    ext x
    have hx := congrFun hf x.1
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ v, hfv, mul_zero,
      zero_add] at hx
    simpa [A, g, b, i, Matrix.mulVec, dotProduct, Pi.single_apply, x.2, Subtype.ext_iff]
      using hx
  have hcramer : A.cramer b i = A.det * f u := by
    rw [← hground, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hdelete : (numSpanningTrees H : ℝ) = A.det - A.cramer b i := by
    rw [← det_grounded_lapMatrix H v]
    change _ = A.det - (A.updateCol i b).det
    rw [grounded_lapMatrix_delete_edge huv]
    have hcol : (fun x => A x i) - b = (fun x => A x i) + (-1 : ℝ) • b := by
      simp [sub_eq_add_neg]
    rw [hcol, Matrix.det_updateCol_add, Matrix.updateCol_eq_self, Matrix.det_updateCol_smul]
    ring
  have hcount := card_trees_delete_edge_add (G := G) u v
  have hcountR := congrArg (Nat.cast : ℕ → ℝ) hcount
  push_cast at hcountR
  have hdet : A.det = (numSpanningTrees G : ℝ) := det_grounded_lapMatrix G v
  have hpos : 0 < numSpanningTrees G := by
    rw [numSpanningTrees_eq_card_trees]
    obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
    let : Nonempty {T : SimpleGraph V // T ≤ G ∧ T.IsTree} := ⟨⟨T, hle, hT⟩⟩
    exact Nat.card_pos
  rw [hr, div_eq_iff (by exact_mod_cast hpos.ne')]
  rw [hcramer, hdet] at hdelete
  linarith

/-- **Weighted matrix-tree theorem.** In a finite simple graph `G` with conductances `c` on its
edges, the weighted spanning-tree sum `Ξ(G) = ∑_T ∏_{e ∈ T} c(e)` equals `det Δ_G^{(x)}` for every
vertex `x`, where `Δ_G` is the network Laplacian (`c(x, y)` summed into the diagonal, `-c(x, y)`
off it) and `Δ_G^{(x)}` strikes the row and column of `x` (R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Cambridge University Press 2016, corrected online version of
19 August 2026, Section 4.4, the paragraph before Exercise 4.16, stated there for simple networks;
the network Laplacian is that of Exercise 2.62). The network Laplacian is the Laplacian of the
dart multigraph with conductance `c(d.edge) / 2` on the dart `d`. -/
theorem weighted_matrix_tree {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → ℝ) (x : V) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e) =
      ((EndpointMapMultigraph.laplacian (fun d : G.Dart => d.fst) (fun d : G.Dart => d.snd)
        (fun d => c d.edge / 2)).submatrix (Subtype.val : {y : V // y ≠ x} → V)
          (Subtype.val : {y : V // y ≠ x} → V)).det := by
  change (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e) =
      (reducedWeightedLaplacian G c x).det
  exact eq_of_affine_of_bool
    (F := fun cc => ∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, cc e)
    (Gc := fun cc => (reducedWeightedLaplacian G cc x).det)
    (fun cc e t => weightedTreeSum_update_affine (G := G) cc e t)
    (fun cc e t => det_reducedWeightedLaplacian_update_affine (G := G) cc e x t)
    (fun cc hc => weightedTreeSum_eq_det_of_bool (G := G) cc x hc) c

end
end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted
