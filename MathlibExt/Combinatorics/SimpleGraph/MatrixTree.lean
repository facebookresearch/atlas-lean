/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-!
# Matrix-tree and Cayley landmarks

Records Kirchhoff's matrix-tree theorem and Cayley's formula.
-/

/-- **Integer Laplacian of a graph.** For a simple graph $G$ on a finite vertex set $V$, the integer
Laplacian of $G$ is the $V \times V$ integer matrix $L$ with $L_{uu} = \deg u$ for every vertex
$u$, $L_{uv} = -1$ when $u \ne v$ are adjacent, and $L_{uv} = 0$ when $u \ne v$ are not adjacent.
-/
def laplacianInt {V : Type*} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] : Matrix V V ℤ :=
  Matrix.of fun u v => if u = v then (G.degree u : ℤ) else if G.Adj u v then -1 else 0

/-- **Reduced Laplacian.** For a simple graph $G$ on a finite vertex set $V$ and a vertex
$r \in V$, the reduced Laplacian of $G$ at $r$ is the integer Laplacian of $G$ with the row and
the column of $r$ deleted, a matrix indexed by the vertices of $G$ other than $r$. -/
def reducedLaplacian {V : Type*} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] (root : V) :
    Matrix { v : V // v ≠ root } { v : V // v ≠ root } ℤ :=
  Matrix.of fun ⟨u, _⟩ ⟨v, _⟩ => laplacianInt G u v

/-- **Spanning tree.** A subgraph $T$ of a simple graph $G$ is a spanning tree of $G$ if it contains
every vertex of $G$ and, regarded as a graph on its own vertex set, it is a tree (connected and
acyclic). -/
def IsSpanningTree {V : Type*} {G : _root_.SimpleGraph V} (T : G.Subgraph) : Prop :=
  T.IsSpanning ∧ T.coe.IsTree

/-- **Number of spanning trees.** For a simple graph $G$ on a finite vertex set, the number of
spanning trees of $G$ is the number of subgraphs of $G$ that are spanning trees, that is,
subgraphs that contain every vertex of $G$ and are trees. -/
noncomputable def numSpanningTrees {V : Type*} (G : _root_.SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : ℕ :=
  Nat.card { T : G.Subgraph // IsSpanningTree T }

/-- **The integer Laplacian is degree minus adjacency.** For a simple graph $G$ on a finite vertex
set, the integer Laplacian of $G$ equals $D - A$, where $D$ is the diagonal matrix of vertex
degrees and $A$ is the adjacency matrix of $G$, both with integer entries. -/
theorem laplacianInt_eq_lapMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    laplacianInt G = G.lapMatrix ℤ := by
  apply Matrix.ext
  intro u v
  simp only [laplacianInt, Matrix.of_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
  by_cases huv : u = v
  · subst huv
    simp
  · simp only [huv, ite_false]
    by_cases hadj : G.Adj u v <;> simp [hadj]

/-- **The reduced Laplacian is a principal submatrix.** Let $G$ be a simple graph on a finite vertex
set $V$ and let $L = D - A$ be its Laplacian matrix over $\mathbb{Z}$, where $D$ is the diagonal
matrix of vertex degrees and $A$ is the adjacency matrix of $G$. For every vertex $r \in V$, the
reduced Laplacian of $G$ at $r$ equals the submatrix of $L$ obtained by deleting the row and the
column of $r$. -/
theorem reducedLaplacian_eq_lapMatrix_submatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    reducedLaplacian G root =
      (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val := by
  apply Matrix.ext
  intro v w
  rw [Matrix.submatrix_apply, ← laplacianInt_eq_lapMatrix]
  obtain ⟨u, _⟩ := v
  obtain ⟨w, _⟩ := w
  rfl

/-! ## Helpers for the matrix-tree proof (blueprint nodes N0–N13). -/

/-- N0: extend a parent map on non-root vertices to all vertices. -/
private def parentExt {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) : V → V :=
  fun x => if h : x = root then root else f ⟨x, h⟩

/-- N0: rooted map: fixes the root and admits a rank function. -/
private def IsRootedMap {V : Type*} (root : V) (g : V → V) : Prop :=
  g root = root ∧ ∃ h : V → ℕ, ∀ x, x ≠ root → h (g x) < h x

/-- N0: parent matrix with `1` on the diagonal minus the parent indicator. -/
private def parentMatrix {V : Type*} [Fintype V] [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) :
    Matrix { v : V // v ≠ root } { v : V // v ≠ root } ℤ :=
  Matrix.of fun v w => (if w = v then (1 : ℤ) else 0) - (if (w : V) = f v then 1 else 0)

@[simp] private theorem parentExt_root {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) : parentExt root f root = root := by
  simp [parentExt]

@[simp] private theorem parentExt_apply {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) (v : { v : V // v ≠ root }) :
    parentExt root f (v : V) = f v := by
  simp [parentExt, v.2]

/-- N1 entry lemma: the reduced Laplacian unfolds to the full Laplacian. -/
private theorem reducedLaplacian_entry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (v w : { v : V // v ≠ root }) :
    reducedLaplacian G root v w = laplacianInt G (v : V) (w : V) := by
  obtain ⟨v, hv⟩ := v
  obtain ⟨w, hw⟩ := w
  rfl

/-- N1: each row of the reduced Laplacian is a sum over neighbours. -/
private theorem reducedLaplacian_eq_of_sum_rows {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    reducedLaplacian G root =
      Matrix.of (fun (v : { v : V // v ≠ root }) =>
        ∑ u ∈ G.neighborFinset (v : V),
          (fun (w : { v : V // v ≠ root }) =>
            ((if w = v then (1 : ℤ) else 0) - (if (w : V) = u then 1 else 0)))) := by
  apply Matrix.ext
  intro vv ww
  rw [reducedLaplacian_entry]
  obtain ⟨v, hv⟩ := vv
  obtain ⟨w, hw⟩ := ww
  change laplacianInt G v w = _
  simp only [Matrix.of_apply, Finset.sum_apply]
  rw [Finset.sum_sub_distrib]
  by_cases hwv : w = v
  · have h1 : (∑ u ∈ G.neighborFinset v,
        (if (⟨w, hw⟩ : { v : V // v ≠ root }) = (⟨v, hv⟩ : { v : V // v ≠ root })
          then (1 : ℤ) else 0)) = (G.degree v : ℤ) := by
      have heq : (⟨w, hw⟩ : { v : V // v ≠ root }) =
          (⟨v, hv⟩ : { v : V // v ≠ root }) := by
        simp [hwv]
      simp [heq, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree G v,
        mul_one]
    have h2 : (∑ u ∈ G.neighborFinset v, (if w = u then (1 : ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hmem : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp hu
      have hne : w ≠ u := by
        rw [hwv]
        intro heq
        subst heq
        exact (SimpleGraph.irrefl G) hmem
      simp [hne]
    have h2' : (∑ u ∈ G.neighborFinset v,
        (if ((⟨w, hw⟩ : { v : V // v ≠ root }) : V) = u then (1 : ℤ) else 0)) = 0 := by
      have hcongr : ∀ u ∈ G.neighborFinset v,
          (if ((⟨w, hw⟩ : { v : V // v ≠ root }) : V) = u then (1 : ℤ) else 0) =
          (if w = u then (1 : ℤ) else 0) := by
        intro u _
        rfl
      rw [Finset.sum_congr rfl hcongr]
      exact h2
    rw [h1, h2']
    simp [laplacianInt, Matrix.of_apply, hwv]
  · have hvv : (⟨w, hw⟩ : { v : V // v ≠ root }) ≠
        (⟨v, hv⟩ : { v : V // v ≠ root }) := by
      simp [Subtype.ext_iff, hwv]
    have h1 : (∑ u ∈ G.neighborFinset v,
        (if (⟨w, hw⟩ : { v : V // v ≠ root }) = (⟨v, hv⟩ : { v : V // v ≠ root })
          then (1 : ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      simp [hvv]
    rw [h1, zero_sub]
    have h2 : (∑ u ∈ G.neighborFinset v,
        (if ((⟨w, hw⟩ : { v : V // v ≠ root }) : V) = u then (1 : ℤ) else 0))
        = (∑ u ∈ G.neighborFinset v, (if w = u then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro u _
      rfl
    rw [h2, Finset.sum_ite_eq _ _ (fun _ => (1 : ℤ))]
    simp only [SimpleGraph.mem_neighborFinset]
    have hne : v ≠ w := by
      intro heq
      apply hwv
      rw [heq]
    simp [laplacianInt, Matrix.of_apply, hne]
    by_cases hadj : G.Adj v w <;> simp [hadj]

/-- N2: det of the reduced Laplacian expands as a sum over parent maps. -/
private theorem det_reducedLaplacian_eq_sum_parentMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    (reducedLaplacian G root).det =
      ∑ f ∈ Fintype.piFinset (fun v : { v : V // v ≠ root } => G.neighborFinset (v : V)),
        (parentMatrix root f).det := by
  rw [reducedLaplacian_eq_of_sum_rows]
  -- rows of `Matrix.of` of row-sums are the row-sums
  have hexpand := MultilinearMap.map_sum_finset
    (↑(Matrix.detRowAlternating (n := { v : V // v ≠ root }) (R := ℤ)) :
      MultilinearMap ℤ (fun _ : { v : V // v ≠ root } => { v : V // v ≠ root } → ℤ) ℤ)
    (fun (v : { v : V // v ≠ root }) (u : V) =>
      (fun (w : { v : V // v ≠ root }) =>
        ((if w = v then (1 : ℤ) else 0) - (if (w : V) = u then 1 else 0))))
    (fun (v : { v : V // v ≠ root }) => G.neighborFinset (v : V))
  -- det = detRowAlternating applied to rows, by rfl
  have hdet : ∀ (M : Matrix { v : V // v ≠ root } { v : V // v ≠ root } ℤ),
      M.det = Matrix.detRowAlternating M.row := fun M => rfl
  have hrow : ∀ (f : { v : V // v ≠ root } → V),
      (parentMatrix root f).row =
        (fun (v : { v : V // v ≠ root }) =>
          (fun (w : { v : V // v ≠ root }) =>
            ((if w = v then (1 : ℤ) else 0) - (if (w : V) = f v then 1 else 0)))) := by
    intro f
    rfl
  simp only [hdet, hrow]
  exact hexpand

/-- N5: rooted parent maps give determinant one. -/
private theorem det_parentMatrix_of_isRootedMap {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (f : { v : V // v ≠ root } → V)
    (hroot : IsRootedMap root (parentExt root f)) :
    (parentMatrix root f).det = 1 := by
  classical
  obtain ⟨hgroot, hrank, hrank_lt⟩ := hroot
  have hdrop : ∀ v : { v : V // v ≠ root }, hrank (f v) < hrank (v : V) := by
    intro v
    have hlt := hrank_lt (v : V) v.2
    have hgv : parentExt root f (v : V) = f v := parentExt_apply root f v
    rw [hgv] at hlt
    exact hlt
  set b : { v : V // v ≠ root } → ℕᵒᵈ :=
    fun v => OrderDual.toDual (hrank (v : V)) with hb
  have htri : (parentMatrix root f).BlockTriangular b := by
    intro i j hij
    have hlt : hrank (i : V) < hrank (j : V) := by
      simp only [hb] at hij
      exact (OrderDual.toDual_lt_toDual).mp hij
    have hne_ij : j ≠ i := by
      intro heq
      subst heq
      exact lt_irrefl _ hlt
    have hne_val : (j : V) ≠ f i := by
      intro heq
      have h1 := hdrop i
      rw [← heq] at h1
      omega
    change (parentMatrix root f) i j = 0
    have hentry : (parentMatrix root f) i j =
        ((if j = i then (1 : ℤ) else 0) - (if (j : V) = f i then 1 else 0)) := rfl
    rw [hentry]
    simp [hne_ij, hne_val]
  have hblock : ∀ a : ℕᵒᵈ, (parentMatrix root f).toSquareBlock b a = 1 := by
    intro a
    apply Matrix.ext
    intro i j
    have hentry : (parentMatrix root f).toSquareBlock b a i j =
        ((if (j.1 : { v : V // v ≠ root }) = (i.1 : { v : V // v ≠ root })
          then (1 : ℤ) else 0) -
         (if ((j.1 : { v : V // v ≠ root }) : V) = f (i.1 : { v : V // v ≠ root })
          then 1 else 0)) := by
      rw [Matrix.toSquareBlock_def]
      simp only [Matrix.of_apply, parentMatrix, Matrix.of_apply]
    have hrank_eq : hrank ((i.1 : { v : V // v ≠ root }) : V) =
        hrank ((j.1 : { v : V // v ≠ root }) : V) := by
      have h2 := i.2.trans j.2.symm
      simp only [hb] at h2
      exact congrArg OrderDual.ofDual h2
    rw [hentry, Matrix.one_apply]
    by_cases hij : (j.1 : { v : V // v ≠ root }) = (i.1 : { v : V // v ≠ root })
    · have hfib : j = i := Subtype.ext hij
      have hne2 : ((i.1 : { v : V // v ≠ root }) : V) ≠
          f (i.1 : { v : V // v ≠ root }) := by
        intro heq
        have h1 := hdrop (i.1 : { v : V // v ≠ root })
        rw [heq] at h1
        exact lt_irrefl _ h1
      rw [hfib]
      simp [hne2]
    · have hfib_ne : i ≠ j := fun h => hij ((congrArg Subtype.val h).symm)
      have hne2 : ((j.1 : { v : V // v ≠ root }) : V) ≠
          f (i.1 : { v : V // v ≠ root }) := by
        intro heq
        have h1 := hdrop (i.1 : { v : V // v ≠ root })
        rw [← heq] at h1
        omega
      simp [hij, hfib_ne, hne2]
  rw [Matrix.BlockTriangular.det htri]
  apply Finset.prod_eq_one
  intro a _
  rw [hblock a, Matrix.det_one]

/-- N3: reachability to the root yields a rank function. -/
private theorem isRootedMap_of_forall_iterate {V : Type*} [Finite V]
    (root : V) (g : V → V) (hroot : g root = root)
    (hreach : ∀ x : V, ∃ k : ℕ, (g^[k]) x = root) : IsRootedMap root g := by
  have := Fintype.ofFinite V
  classical
  refine ⟨hroot, ?_⟩
  classical
  refine ⟨fun x => Nat.find (hreach x), fun x hx => ?_⟩
  have h0 : Nat.find (hreach x) ≠ 0 := by
    intro hz
    have hspec := Nat.find_spec (hreach x)
    rw [hz] at hspec
    simp only [Function.iterate_zero, id_eq]at hspec
    exact hx hspec
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hspec : (g^[Nat.find (hreach x)]) x = root := Nat.find_spec (hreach x)
  rw [hm] at hspec
  rw [Function.iterate_succ_apply] at hspec
  have hle : Nat.find (hreach (g x)) ≤ m := Nat.find_min' (hreach (g x)) hspec
  change Nat.find (hreach (g x)) < Nat.find (hreach x)
  omega

/-- N4: a rank function yields reachability to the root. -/
private theorem forall_iterate_of_isRootedMap {V : Type*} [Finite V]
    (rt : V) (g : V → V) (h : IsRootedMap rt g) :
    ∀ x : V, ∃ k : ℕ, (g^[k]) x = rt := by
  have := Fintype.ofFinite V
  classical
  obtain ⟨hroot, hrank, hrank_lt⟩ := h
  suffices hsuff : ∀ (n : ℕ) (y : V), hrank y = n → ∃ k : ℕ, (g^[k]) y = rt from
    fun y => hsuff (hrank y) y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy
    by_cases hyr : y = rt
    · subst hyr
      exact ⟨0, by simp⟩
    · have hlt : hrank (g y) < hrank y := hrank_lt y hyr
      rw [hy] at hlt
      obtain ⟨k, hk⟩ := ih (hrank (g y)) hlt (g y) rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- N6: non-rooted parent maps give determinant zero. -/
private theorem det_parentMatrix_eq_zero_of_not_reach {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (f : { v : V // v ≠ root } → V)
    (hnot : ¬ ∀ x : V, ∃ k : ℕ, ((parentExt root f)^[k]) x = root) :
    (parentMatrix root f).det = 0 := by
  classical
  have hR_root : (∃ k : ℕ, ((parentExt root f)^[k]) root = root) := ⟨0, by simp⟩
  -- reachability transfers between v and f v
  have htrans : ∀ v : { v : V // v ≠ root },
      (∃ k : ℕ, ((parentExt root f)^[k]) (v : V) = root) ↔
      (∃ k : ℕ, ((parentExt root f)^[k]) (f v) = root) := by
    intro v
    constructor
    · intro ⟨k, hk⟩
      cases k with
      | zero =>
        simp only [ne_eq, Function.iterate_zero, id_eq] at hk
        exact absurd hk v.2
      | succ k' =>
        rw [Function.iterate_succ_apply] at hk
        have hgv : parentExt root f (v : V) = f v := parentExt_apply root f v
        rw [hgv] at hk
        exact ⟨k', hk⟩
    · intro ⟨k', hk'⟩
      refine ⟨k' + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have hgv : parentExt root f (v : V) = f v := parentExt_apply root f v
      rw [hgv]
      exact hk'
  -- indicator vector of non-reachability
  set x0 : { v : V // v ≠ root } → ℤ :=
    fun w => if (∃ k : ℕ, ((parentExt root f)^[k]) (w : V) = root) then 0 else 1 with hx0
  -- its values agree with the indicator at f v
  have hval : ∀ v : { v : V // v ≠ root },
      x0 v = (if (∃ k : ℕ, ((parentExt root f)^[k]) (f v) = root) then (0 : ℤ) else 1) := by
    intro v
    simp only [hx0]
    rw [htrans v]
  have hx0_root : ∀ v : { v : V // v ≠ root }, f v = root → x0 v = 0 := by
    intro v hfv
    have h2 : (∃ k : ℕ, ((parentExt root f)^[k]) (f v) = root) := by
      rw [hfv]
      exact hR_root
    rw [hval v]
    simp [h2]
  -- x0 is a kernel vector
  have hmul : (parentMatrix root f).mulVec x0 = 0 := by
    funext v
    have hexpand : ∀ (w : { v : V // v ≠ root }),
        (parentMatrix root f) v w * x0 w =
          (if w = v then x0 w else 0) - (if (w : V) = f v then x0 w else 0) := by
      intro w
      change ((if w = v then (1 : ℤ) else 0) - (if (w : V) = f v then 1 else 0)) * x0 w = _
      simp only [sub_mul, ite_mul, one_mul, zero_mul]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_congr rfl (fun w _ => hexpand w),
      Finset.sum_sub_distrib, Pi.zero_apply]
    have hfirst : (∑ w : { v : V // v ≠ root }, (if w = v then x0 w else 0)) = x0 v := by
      rw [Finset.sum_ite_eq' Finset.univ v _]
      simp
    rw [hfirst]
    by_cases hfv : f v = root
    · have hsecond : (∑ w : { v : V // v ≠ root }, (if (w : V) = f v then x0 w else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        have hne : ¬ ((w : V) = f v) := by
          rw [hfv]
          exact w.2
        simp [hne]
      rw [hsecond, hx0_root v hfv, sub_zero]
    · have hsecond : (∑ w : { v : V // v ≠ root }, (if (w : V) = f v then x0 w else 0))
          = x0 v := by
        have hif : ((⟨f v, hfv⟩ : { v : V // v ≠ root }) : V) = f v := rfl
        have hpack : x0 (⟨f v, hfv⟩ : { v : V // v ≠ root }) =
            (if (∃ k : ℕ, ((parentExt root f)^[k]) (f v) = root) then (0:ℤ) else 1) := by
          simp only [hx0]
        have hsingle := Finset.sum_eq_single (⟨f v, hfv⟩ : { v : V // v ≠ root })
          (s := Finset.univ)
          (f := fun (w : { v : V // v ≠ root }) => if (w : V) = f v then x0 w else 0)
          (fun w _ hne => by
            have hne' : ¬ ((w : V) = f v) := by
              intro heq
              apply hne
              exact Subtype.ext_iff.mpr heq
            simp [hne'])
          (fun hcon => absurd (Finset.mem_univ _) hcon)
        rw [hsingle]
        simp only [ite_true]
        rw [hpack, hval v]
      rw [hsecond, sub_self]
  -- x0 is nonzero
  have hne : x0 ≠ 0 := by
    simp only [not_forall, not_exists] at hnot
    obtain ⟨x, hx⟩ := hnot
    have hxne : x ≠ root := by
      intro heq
      subst heq
      have h0 := hx 0
      simp [Function.iterate_zero] at h0
    have hxval : x0 ⟨x, hxne⟩ = 1 := by
      have hneg : ¬ (∃ k : ℕ, ((parentExt root f)^[k]) (x : V) = root) :=
        fun ⟨k, hk⟩ => hx k hk
      have hif : x0 ⟨x, hxne⟩ =
          (if (∃ k : ℕ, ((parentExt root f)^[k]) (x : V) = root) then (0:ℤ) else 1) := by
        simp only [hx0]
      rw [hif]
      simp [hneg]
    intro h0
    have hcon := congrFun h0 (⟨x, hxne⟩ : { v : V // v ≠ root })
    simp [hxval] at hcon
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x0, hne, hmul⟩

open Classical in
private theorem det_reducedLaplacian_eq_card_rooted {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    (reducedLaplacian G root).det =
      (((Fintype.piFinset (fun v : { v : V // v ≠ root } => G.neighborFinset (v : V))).filter
        (fun f => IsRootedMap root (parentExt root f))).card : ℤ) := by
  classical
  rw [det_reducedLaplacian_eq_sum_parentMatrix]
  have hterm : ∀ f ∈ Fintype.piFinset
      (fun v : { v : V // v ≠ root } => G.neighborFinset (v : V)),
      (parentMatrix root f).det =
        (if IsRootedMap root (parentExt root f) then (1 : ℤ) else 0) := by
    intro f _
    by_cases h : IsRootedMap root (parentExt root f)
    · rw [det_parentMatrix_of_isRootedMap root f h]
      simp [h]
    · have hnot : ¬ ∀ x : V, ∃ k : ℕ, ((parentExt root f)^[k]) x = root := by
        intro hall
        apply h
        exact isRootedMap_of_forall_iterate root _ (parentExt_root root f) hall
      rw [det_parentMatrix_eq_zero_of_not_reach root f hnot]
      simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]

open Classical in
private theorem isTree_fromRel_of_isRootedMap {V : Type*} [Finite V]
    (root : V) (g : V → V) (h : IsRootedMap root g) :
    (SimpleGraph.fromRel (fun u w => g u = w)).IsTree := by
  have := Fintype.ofFinite V
  classical
  obtain ⟨hgroot, hrank, hrank_lt⟩ := h
  have hne_self : ∀ x : V, x ≠ root → g x ≠ x := by
    intro x hx hcon
    have hlt := hrank_lt x hx
    rw [hcon] at hlt
    exact lt_irrefl _ hlt
  have hReach : ∀ (n : ℕ) (y : V), hrank y = n →
      (SimpleGraph.fromRel (fun u w => g u = w)).Reachable y root := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hy
      by_cases hyr : y = root
      · subst hyr
        exact SimpleGraph.Reachable.rfl
      · have hlt : hrank (g y) < hrank y := hrank_lt y hyr
        rw [hy] at hlt
        have hadj : (SimpleGraph.fromRel (fun u w => g u = w)).Adj y (g y) := by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨Ne.symm (hne_self y hyr), Or.inl rfl⟩
        exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hadj)
          (ih (hrank (g y)) hlt (g y) rfl)
  have hconn : (SimpleGraph.fromRel (fun u w => g u = w)).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨root, fun w => SimpleGraph.Reachable.symm (hReach (hrank w) w rfl)⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hbij : (Finset.univ.erase root).card =
      (SimpleGraph.fromRel (fun u w => g u = w)).edgeFinset.card := by
    apply Finset.card_bij (fun x _ => s(x, g x))
    · intro x hx
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
      have hxne : x ≠ root := Finset.ne_of_mem_erase hx
      exact ⟨Ne.symm (hne_self x hxne), Or.inl rfl⟩
    · intro x hx y hy hxy
      rw [Sym2.eq_iff] at hxy
      cases hxy with
      | inl h => exact h.1
      | inr h =>
        obtain ⟨h1, h2⟩ := h
        have hxne : x ≠ root := Finset.ne_of_mem_erase hx
        have hyne : y ≠ root := Finset.ne_of_mem_erase hy
        have hgy := hrank_lt y hyne
        have hgx := hrank_lt x hxne
        rw [← h1] at hgy
        rw [h2] at hgx
        omega
    · intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.fromRel_adj] at he
        obtain ⟨hne, hor⟩ := he
        cases hor with
        | inl h =>
          have hune : u ≠ root := by
            intro hcon
            subst hcon
            rw [hgroot] at h
            exact hne h
          refine ⟨u, Finset.mem_erase.mpr ⟨hune, Finset.mem_univ _⟩, ?_⟩
          show s(u, g u) = s(u, v)
          rw [h]
        | inr h =>
          have hvne : v ≠ root := by
            intro hcon
            subst hcon
            rw [hgroot] at h
            exact hne h.symm
          refine ⟨v, Finset.mem_erase.mpr ⟨hvne, Finset.mem_univ _⟩, ?_⟩
          show s(v, g v) = s(u, v)
          rw [h]
          exact Sym2.eq_swap
  have hcardV : 1 ≤ Fintype.card V := by
    have hne : Nonempty V := ⟨root⟩
    have hpos := (Fintype.card_pos_iff).mpr hne
    omega
  have huniv : (Finset.univ.erase root).card = Fintype.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ root), Finset.card_univ]
  rw [huniv] at hbij
  have hedge : (SimpleGraph.fromRel (fun u w => g u = w)).edgeFinset.card =
      Fintype.card ((SimpleGraph.fromRel (fun u w => g u = w)).edgeSet) := by
    rw [SimpleGraph.edgeFinset_card]
  rw [hedge] at hbij
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

private theorem fromRel_injective_on_rooted {V : Type*} [Finite V]
    (root : V) (g₁ g₂ : V → V) (h₁ : g₁ root = root) (h₂ : IsRootedMap root g₂)
    (heq : SimpleGraph.fromRel (fun u w => g₁ u = w) =
      SimpleGraph.fromRel (fun u w => g₂ u = w)) : g₁ = g₂ := by
  have := Fintype.ofFinite V
  classical
  obtain ⟨hg₂root, hrank, hrank_lt⟩ := h₂
  funext x
  suffices hsuff : ∀ (n : ℕ) (y : V), hrank y = n → g₁ y = g₂ y from
    hsuff (hrank x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy
    by_cases hyr : y = root
    · subst hyr
      rw [h₁, hg₂root]
    · have hne : g₂ y ≠ y := by
        intro hcon
        have hlt := hrank_lt y hyr
        rw [hcon] at hlt
        exact lt_irrefl _ hlt
      have hadj2 : (SimpleGraph.fromRel (fun u w => g₂ u = w)).Adj y (g₂ y) := by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨Ne.symm hne, Or.inl rfl⟩
      have hadj1 : (SimpleGraph.fromRel (fun u w => g₁ u = w)).Adj y (g₂ y) := by
        rw [heq]
        exact hadj2
      rw [SimpleGraph.fromRel_adj] at hadj1
      obtain ⟨_, hor⟩ := hadj1
      cases hor with
      | inl h => exact h
      | inr h =>
        set z := g₂ y with hz
        have hzroot : z ≠ root := by
          intro hcon
          apply hyr
          rw [← h, hcon, h₁]
        have hlt : hrank z < hrank y := hrank_lt y hyr
        rw [hy] at hlt
        have hih := ih (hrank z) hlt z rfl
        have hgz : g₂ z = y := by
          rw [← hih]
          exact h
        have hlt2 : hrank (g₂ z) < hrank z := hrank_lt z hzroot
        rw [hgz] at hlt2
        omega

private theorem exists_rootedMap_of_isTree {V : Type*} [Finite V]
    (root : V) (H : SimpleGraph V) (hH : H.IsTree) :
    ∃ g : V → V, IsRootedMap root g ∧ (∀ x : V, x ≠ root → H.Adj x (g x)) ∧
      SimpleGraph.fromRel (fun u w => g u = w) ≤ H := by
  have := Fintype.ofFinite V
  classical
  have hconn := SimpleGraph.IsTree.connected hH
  have hex : ∀ x : V, x ≠ root → ∃ y : V, H.Adj x y ∧ H.dist y root < H.dist x root := by
    intro x hx
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x root
    have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hx
    refine ⟨p.snd, SimpleGraph.Walk.adj_snd hnil, ?_⟩
    have htail := SimpleGraph.dist_le p.tail
    have hlen := SimpleGraph.Walk.length_tail_add_one hnil
    rw [hp] at hlen
    have hpos := hconn.pos_dist_of_ne hx
    omega
  have hex2 : ∀ x : V, ∃ y : V, (x = root → y = root) ∧
      (x ≠ root → H.Adj x y ∧ H.dist y root < H.dist x root) := by
    intro x
    by_cases hx : x = root
    · exact ⟨root, fun _ => rfl, fun hcon => absurd hx hcon⟩
    · obtain ⟨y, hadj, hlt⟩ := hex x hx
      exact ⟨y, fun hcon => absurd hcon hx, fun _ => ⟨hadj, hlt⟩⟩
  choose g hg using hex2
  have hgroot : g root = root := (hg root).1 rfl
  have hadj : ∀ x : V, x ≠ root → H.Adj x (g x) := fun x hx => ((hg x).2 hx).1
  have hdist : ∀ x : V, x ≠ root → H.dist (g x) root < H.dist x root :=
    fun x hx => ((hg x).2 hx).2
  refine ⟨g, ⟨hgroot, fun x => H.dist x root, fun x hx => hdist x hx⟩, hadj, ?_⟩
  rw [SimpleGraph.le_iff_adj]
  intro v w hadjvw
  rw [SimpleGraph.fromRel_adj] at hadjvw
  obtain ⟨hne, hor⟩ := hadjvw
  cases hor with
  | inl h =>
    have hvne : v ≠ root := by
      intro hcon
      subst hcon
      rw [hgroot] at h
      exact hne h
    rw [← h]
    exact hadj v hvne
  | inr h =>
    have hwne : w ≠ root := by
      intro hcon
      subst hcon
      rw [hgroot] at h
      exact hne h.symm
    have h2 : H.Adj w (g w) := hadj w hwne
    rw [h] at h2
    exact SimpleGraph.Adj.symm h2

/-- N11: two nested trees on the same vertices are equal. -/
private theorem eq_of_le_of_isTree {V : Type*} [Finite V]
    {H1 H2 : SimpleGraph V} (hle : H1 ≤ H2) (h1 : H1.IsTree) (h2 : H2.IsTree) :
    H1 = H2 := by
  have := Fintype.ofFinite V
  classical
  have hsub : H1.edgeFinset ⊆ H2.edgeFinset := by
    rw [SimpleGraph.edgeFinset_subset_edgeFinset]
    exact hle
  have hc1 : H1.edgeFinset.card + 1 = Fintype.card V :=
    SimpleGraph.IsTree.card_edgeFinset h1
  have hc2 : H2.edgeFinset.card + 1 = Fintype.card V :=
    SimpleGraph.IsTree.card_edgeFinset h2
  have hfin : H1.edgeFinset = H2.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact (SimpleGraph.edgeFinset_inj.mp hfin)

open Classical in
private theorem card_rooted_eq_card_trees_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) :
    ((Fintype.piFinset (fun v : { v : V // v ≠ root } => G.neighborFinset (v : V))).filter
      (fun f => IsRootedMap root (parentExt root f))).card =
    ((Finset.univ.filter (fun H : SimpleGraph V => H ≤ G ∧ H.IsTree))).card := by
  classical
  apply Finset.card_bij
    (fun f _ => SimpleGraph.fromRel (fun u w => parentExt root f u = w))
  · intro f hf
    have hfrooted : IsRootedMap root (parentExt root f) := (Finset.mem_filter.mp hf).2
    have hfmem0 : f ∈ Fintype.piFinset
        (fun v : { v : V // v ≠ root } => G.neighborFinset (v : V)) :=
      (Finset.mem_filter.mp hf).1
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- the fromRel graph lies below G
      show SimpleGraph.fromRel (fun u w => parentExt root f u = w) ≤ G
      rw [SimpleGraph.le_iff_adj]
      intro v w hadjvw
      rw [SimpleGraph.fromRel_adj] at hadjvw
      obtain ⟨hne, hor⟩ := hadjvw
      have hfmem : ∀ (a : { v : V // v ≠ root }), f a ∈ G.neighborFinset (a : V) :=
        Fintype.mem_piFinset.mp hfmem0
      cases hor with
      | inl h =>
        have hvne : v ≠ root := by
          intro hcon
          subst hcon
          rw [parentExt_root] at h
          exact hne h
        have hpa := parentExt_apply root f (⟨v, hvne⟩ : { v : V // v ≠ root })
        have hfv : f ⟨v, hvne⟩ = w := by
          rw [← hpa]
          exact h
        have hadjmem := (SimpleGraph.mem_neighborFinset G _ _).mp (hfmem ⟨v, hvne⟩)
        rw [hfv] at hadjmem
        exact hadjmem
      | inr h =>
        have hwne : w ≠ root := by
          intro hcon
          subst hcon
          rw [parentExt_root] at h
          exact hne h.symm
        have hpa := parentExt_apply root f (⟨w, hwne⟩ : { v : V // v ≠ root })
        have hfw : f ⟨w, hwne⟩ = v := by
          rw [← hpa]
          exact h
        have hadjmem := (SimpleGraph.mem_neighborFinset G _ _).mp (hfmem ⟨w, hwne⟩)
        rw [hfw] at hadjmem
        exact SimpleGraph.Adj.symm hadjmem
    · show (SimpleGraph.fromRel (fun u w => parentExt root f u = w)).IsTree
      exact isTree_fromRel_of_isRootedMap root _ hfrooted
  · intro f₁ hf₁ f₂ hf₂ heq
    have hflt2 : IsRootedMap root (parentExt root f₂) :=
      (Finset.mem_filter.mp hf₂).2
    have hpar := fromRel_injective_on_rooted root _ _ (parentExt_root root f₁) hflt2 heq
    funext v
    have e1 := parentExt_apply root f₁ v
    have e2 := parentExt_apply root f₂ v
    rw [← e1, ← e2, hpar]
  · intro H hH
    rw [Finset.mem_filter] at hH
    obtain ⟨_, hleG, hHt⟩ := hH
    obtain ⟨g, hg_rooted, hadj_spec, hleH⟩ := exists_rootedMap_of_isTree root H hHt
    have htree : (SimpleGraph.fromRel (fun u w => g u = w)).IsTree :=
      isTree_fromRel_of_isRootedMap root g hg_rooted
    have hHeq : SimpleGraph.fromRel (fun u w => g u = w) = H :=
      eq_of_le_of_isTree hleH htree hHt
    have hpar : parentExt root (fun v : { v : V // v ≠ root } => g (v : V)) = g := by
      funext x
      by_cases hx : x = root
      · rw [hx, parentExt_root]
        exact hg_rooted.1.symm
      · exact parentExt_apply root _ ⟨x, hx⟩
    refine ⟨fun v : { v : V // v ≠ root } => g (v : V), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro v
        show g (v : V) ∈ G.neighborFinset (v : V)
        rw [SimpleGraph.mem_neighborFinset]
        exact (SimpleGraph.le_iff_adj.mp hleG) _ _ (hadj_spec (v : V) v.2)
      · exact hpar.symm ▸ hg_rooted
    · show SimpleGraph.fromRel
          (fun u w => parentExt root (fun v : { v : V // v ≠ root } => g (v : V)) u = w) = H
      rw [hpar]
      exact hHeq

/-- **Spanning trees as trees contained in the graph.** For a simple graph $G$ on a vertex set $V$,
there is an equivalence between the spanning trees of $G$ (subgraphs of $G$ that contain every
vertex and are trees) and the simple graphs $H$ on $V$ that are trees with $H \le G$, that is,
every edge of $H$ is an edge of $G$. It sends a spanning tree to the graph on $V$ with the same
edges. -/
def spanningTreeSubgraphEquiv {V : Type*} (G : SimpleGraph V) :
    {T : G.Subgraph // IsSpanningTree T} ≃ {H : SimpleGraph V // H ≤ G ∧ H.IsTree} := by
  classical
  refine
    { toFun := fun T => ⟨T.1.spanningCoe, T.1.spanningCoe_le, ?_⟩
      invFun := fun H => ⟨SimpleGraph.toSubgraph H.1 H.2.1,
        SimpleGraph.toSubgraph.isSpanning H.1 H.2.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (SimpleGraph.Iso.isTree_iff (T.1.spanningCoeEquivCoeOfSpanning T.2.1)).mpr T.2.2
  · obtain ⟨H, hle, htreeH⟩ := H
    have hspan_eq : (SimpleGraph.toSubgraph H hle).spanningCoe = H := by
      apply SimpleGraph.ext
      funext v w
      rw [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.toSubgraph_adj]
    have h1 : (SimpleGraph.toSubgraph H hle).spanningCoe.IsTree := hspan_eq.symm ▸ htreeH
    exact (SimpleGraph.Iso.isTree_iff
      (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning _
        (SimpleGraph.toSubgraph.isSpanning H hle))).mp h1
  · intro T
    obtain ⟨T, hTspan, hTtree⟩ := T
    apply Subtype.ext
    change SimpleGraph.toSubgraph T.spanningCoe T.spanningCoe_le = T
    apply SimpleGraph.Subgraph.ext
    · have hv1 : (SimpleGraph.toSubgraph T.spanningCoe T.spanningCoe_le).verts = Set.univ :=
        SimpleGraph.Subgraph.isSpanning_iff.mp (SimpleGraph.toSubgraph.isSpanning _ _)
      have hv2 : T.verts = Set.univ := SimpleGraph.Subgraph.isSpanning_iff.mp hTspan
      rw [hv1, hv2]
    · funext v w
      rw [SimpleGraph.toSubgraph_adj, SimpleGraph.Subgraph.spanningCoe_adj]
  · intro H
    obtain ⟨H, hle, htreeH⟩ := H
    apply Subtype.ext
    change (SimpleGraph.toSubgraph H hle).spanningCoe = H
    apply SimpleGraph.ext
    funext v w
    rw [SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.toSubgraph_adj]

open Classical in
private theorem numSpanningTrees_eq_card_trees_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    numSpanningTrees G =
    ((Finset.univ.filter (fun H : SimpleGraph V => H ≤ G ∧ H.IsTree))).card := by
  classical
  have hcard : Nat.card {T : G.Subgraph // IsSpanningTree T} =
      Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} :=
    Nat.card_congr (spanningTreeSubgraphEquiv G)
  rw [show numSpanningTrees G = Nat.card {T : G.Subgraph // IsSpanningTree T} from rfl,
    hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Spanning trees as trees on the whole vertex set.** For a simple graph $G$ on a finite vertex
set $V$, the number of spanning trees of $G$ equals the number of simple graphs $H$ on $V$ such
that every edge of $H$ is an edge of $G$ and $H$ is a tree. -/
theorem numSpanningTrees_eq_card_trees {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    numSpanningTrees G = Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} := by
  change Nat.card {T : G.Subgraph // IsSpanningTree T} = _
  exact Nat.card_congr (spanningTreeSubgraphEquiv G)

/--
**Matrix-tree theorem for a chosen root.** Let $G$ be a simple graph on a finite vertex set $V$
and let $r \in V$. Then the determinant of the reduced Laplacian of $G$ at $r$, that is, the
integer Laplacian of $G$ with the row and the column of $r$ deleted, equals the number of spanning
trees of $G$.

No separate nonemptiness hypothesis on $V$ is needed, since $r$ is a vertex.
-/
theorem kirchhoff_matrix_tree_of_root :
    ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
      (root : V),
      (reducedLaplacian G root).det = (numSpanningTrees G : ℤ) := by
  intro V G _ _ _ root
  rw [det_reducedLaplacian_eq_card_rooted, card_rooted_eq_card_trees_le,
    numSpanningTrees_eq_card_trees_le]

/-- **Matrix-tree theorem for principal minors of the Laplacian.** Let $G$ be a simple graph on a
finite vertex set $V$, let $L = D - A$ be its Laplacian matrix over $\mathbb{Z}$, where $D$ is the
diagonal matrix of vertex degrees and $A$ is the adjacency matrix of $G$, and let $r \in V$. Then
the determinant of the submatrix of $L$ obtained by deleting the row and the column of $r$ equals
the number of spanning trees of $G$. -/
theorem kirchhoff_matrix_tree_lapMatrix :
    ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
      (root : V),
      ((G.lapMatrix ℤ).submatrix (Subtype.val : { v : V // v ≠ root } → V)
        (Subtype.val : { v : V // v ≠ root } → V)).det
        = (numSpanningTrees G : ℤ) := by
  intro V G _ _ _ root
  rw [← reducedLaplacian_eq_lapMatrix_submatrix]
  exact kirchhoff_matrix_tree_of_root G root

/--
**Kirchhoff's matrix-tree theorem.** Let $G$ be a simple graph on a finite nonempty vertex set $V$
and let $r \in V$. Then the determinant of the reduced Laplacian of $G$ at $r$, that is, the
integer Laplacian of $G$ with the row and the column of $r$ deleted, equals the number of spanning
trees of $G$.

In particular, this determinant is $0$ when $G$ is disconnected.

Proves `Wanted` entry `kirchhoff_matrix_tree`.

Source: G. Kirchhoff, "Über die Auflösung der Gleichungen, auf welche man bei der Untersuchung der
linearen Verteilung galvanischer Ströme geführt wird", Annalen der Physik und Chemie 72 (1847),
497–508, DOI 10.1002/andp.18471481202
-/
theorem kirchhoff_matrix_tree :
    ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
      [Nonempty V] (root : V),
      (reducedLaplacian G root).det = (numSpanningTrees G : ℤ) := by
  intro V G _ _ _ _ root
  exact kirchhoff_matrix_tree_of_root G root

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
end
