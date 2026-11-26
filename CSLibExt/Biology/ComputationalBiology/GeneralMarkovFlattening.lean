/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Flattenings of the general Markov model

In the `κ`-state general Markov model on a tree `T` rooted at a vertex `r`, a root distribution
`π` and a Markov matrix on every edge directed away from `r` give the joint distribution of the
states at all vertices, `π(σ(r)) ∏_{a → b} M_{ab}(σ(a), σ(b))`, and hence the joint distribution
`P` of the leaf states, the sum over the states at the other vertices (`leafDist`).

An edge `e` of `T` induces a split `A | B` of the taxa; the flattening `Flat_e(P)` is the
`κ^|A| × κ^|B|` matrix with entries `P(u, v)` (`flatten`). Since
`Flat_e(P) = M₁ᵀ diag(π_r) M₂` for `κ`-row Markov matrices `M₁, M₂`, it has rank at most `κ`
(`rank_flatten_leafDist_le`).

For an unrooted binary phylogenetic tree `T` on four taxa displaying the quartet `01|23`, each of
the two splits `{0, 2} | {1, 3}` and `{0, 3} | {1, 2}` that are not edges of `T` admits complex
stochastic parameters whose leaf-distribution flattening along that split has rank larger than
`κ` (Allman and Rhodes 2006, Theorem 2 with `λ = κ`; `exists_card_lt_rank_flatten_nonEdge`).
Since the rank-at-most-`κ` locus is algebraic in the parameters, it is then a proper algebraic
subset of the parameter space, and the tree is identified from generic parameters by the
vanishing of the `(κ + 1)`-minors of its own flattening.

Trees are the repository's unrooted binary phylogenetic trees (`UnrootedBinaryTree`) with their
edge splits (`CSLibExt.Bioinformatics.Phylogenetics.Splits`); the root may be any vertex.

Sources: E. S. Allman and J. A. Rhodes, "Phylogenetic ideals and varieties for the general Markov
model", Advances in Applied Mathematics 40 (2008) 127–148, doi:10.1016/j.aam.2006.10.002,
Section 2; E. S. Allman and J. A. Rhodes, "The identifiability of tree topology for
phylogenetic models, including covarion and mixture models", Journal of Computational Biology 13
(2006) 1101–1113, doi:10.1089/cmb.2006.13.1101, Theorem 2.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.SimpleGraph.ConnectedParent
import MathlibExt.Combinatorics.SimpleGraph.WalkPath

set_option autoImplicit false
@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

/-- The edge `a – b` is directed away from the root `r`: `b` is one step farther from `r`. -/
def IsAwayFrom {V : Type} (G : SimpleGraph V) (r a b : V) : Prop :=
  G.Adj a b ∧ G.dist r b = G.dist r a + 1

open Classical in
/-- The joint distribution of the states `σ` at all vertices for the root distribution `π` and
the edge matrices `M a b` on the edges `a → b` directed away from the root `r`:
`π(σ r) ∏_{a → b} M a b (σ a) (σ b)`. -/
noncomputable def treeJoint {V K R : Type} [Fintype V] [CommSemiring R]
    (G : SimpleGraph V) (r : V) (π : K → R) (M : V → V → Matrix K K R)
    (σ : V → K) : R :=
  π (σ r) * ∏ ab ∈ Finset.univ.filter (fun ab : V × V => IsAwayFrom G r ab.1 ab.2),
    M ab.1 ab.2 (σ ab.1) (σ ab.2)

open Classical in
/-- The joint distribution of the leaf states, `φ_r(π, M)`: the probability that the leaf of each
taxon `x` has state `u x`, summing the joint distribution over the states at the other
vertices. -/
noncomputable def leafDist {V K X R : Type} [Fintype V] [Fintype K] [CommSemiring R]
    (G : SimpleGraph V) (ℓ : X → V) (r : V) (π : K → R) (M : V → V → Matrix K K R)
    (u : X → K) : R :=
  ∑ σ ∈ Finset.univ.filter (fun σ : V → K => ∀ x, σ (ℓ x) = u x), treeJoint G r π M σ

/-- Stochastic parameters for the root `r`: a probability vector `π` and, on every edge directed
away from `r`, a Markov matrix (nonnegative entries, rows summing to one). -/
def IsStochastic {V K : Type} [Fintype K] (G : SimpleGraph V) (r : V) (π : K → ℝ)
    (M : V → V → Matrix K K ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ ∀ a b, IsAwayFrom G r a b →
    (∀ i j, 0 ≤ M a b i j) ∧ ∀ i, ∑ j, M a b i j = 1

/-- Complex parameters for the root `r` satisfying the stochastic linear constraints: the root
vector sums to one and every edge matrix directed away from `r` has rows summing to one. -/
def IsComplexStochastic {V K : Type} [Fintype K] (G : SimpleGraph V)
    (r : V) (π : K → ℂ) (M : V → V → Matrix K K ℂ) : Prop :=
  ∑ i, π i = 1 ∧ ∀ a b, IsAwayFrom G r a b → ∀ i, ∑ j, M a b i j = 1

/-- The **flattening** of a function `P` of leaf states along the split `A | Aᶜ`: the matrix with
rows the states on `A`, columns the states off `A`, and entries `P(u, v)`. -/
def flatten {X K R : Type} [DecidableEq X] (A : Finset X) (P : (X → K) → R) :
    Matrix ({x // x ∈ A} → K) ({x // x ∉ A} → K) R :=
  fun u v => P fun x => if h : x ∈ A then u ⟨x, h⟩ else v ⟨x, h⟩

/-- The leaf of each taxon, as a vertex. -/
def leafOf {X : Type} (T : UnrootedBinaryTree X) (x : X) : T.V :=
  T.label x

/-! ### Sides of an edge in a tree -/

/-- The `p`-side of the edge `p – v`: the vertices strictly closer to `p` than to `v`. -/
private noncomputable def sideNear {V : Type} [Fintype V] (G : SimpleGraph V) (p v : V) :
    Finset V :=
  Finset.univ.filter fun w => G.dist w p < G.dist w v

private theorem mem_sideNear {V : Type} [Fintype V] (G : SimpleGraph V) (p v w : V) :
    w ∈ sideNear G p v ↔ G.dist w p < G.dist w v := by
  simp [sideNear]

private theorem disjoint_sideNear {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p v : V) :
    Disjoint (sideNear G p v) (sideNear G v p) := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [mem_sideNear] at hw1 hw2
  omega

private theorem cover_sideNear {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) {p v : V} (hpv : G.Adj p v) :
    sideNear G p v ∪ sideNear G v p = Finset.univ := by
  ext w
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rw [mem_sideNear, mem_sideNear]
  rcases hG.dist_eq_dist_add_one_of_adj w hpv with h | h <;> omega

private theorem self_mem_sideNear {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {p v : V} (hpv : G.Adj p v) : p ∈ sideNear G p v := by
  rw [mem_sideNear, SimpleGraph.dist_self]
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hpv]
  exact Nat.zero_lt_one

/-- In a tree, the only edge crossing the cut of the edge `p – v` is `p – v` itself: if the
edge `a – b` has `a` strictly closer to `p` than to `v` and `b` strictly closer to `v` than
to `p`, then `a = p` and `b = v`. Otherwise a shortest path from `a` to `p`, the edge `p – v`
and a shortest path from `v` to `b` concatenate to a second simple path from `a` to `b`. -/
private theorem eq_crossing_of_mem_sides {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    {p v a b : V} (hpv : G.Adj p v) (hab : G.Adj a b)
    (ha : G.dist a p < G.dist a v) (hb : G.dist b v < G.dist b p) :
    a = p ∧ b = v := by
  have hconn := hG.connected
  have hdpv : G.dist p v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpv
  have hdab : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
  have hdba : G.dist b a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab.symm
  have hav : G.dist a v = G.dist a p + 1 := by
    have h := hconn.dist_triangle (u := a) (v := p) (w := v)
    rw [hdpv] at h
    omega
  have hbp : G.dist b p = G.dist b v + 1 := by
    have h := hconn.dist_triangle (u := b) (v := v) (w := p)
    have hvp : G.dist v p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpv.symm
    rw [hvp] at h
    omega
  have hda : G.dist a p = G.dist b v := by
    have t1 := hconn.dist_triangle (u := a) (v := b) (w := v)
    have t2 := hconn.dist_triangle (u := b) (v := a) (w := p)
    rw [hdab] at t1
    rw [hdba] at t2
    omega
  by_cases hd : G.dist a p = 0
  · refine ⟨(hconn a p).dist_eq_zero_iff.mp hd, ?_⟩
    have hbv0 : G.dist b v = 0 := by omega
    exact (hconn b v).dist_eq_zero_iff.mp hbv0
  · have hd1 : 1 ≤ G.dist a p := Nat.one_le_iff_ne_zero.mpr hd
    obtain ⟨Pa, hPa_path, hPa_len⟩ := hconn.exists_path_of_dist a p
    obtain ⟨Pvb, hPvb_path, hPvb_len⟩ := hconn.exists_path_of_dist v b
    have hvb : G.dist v b = G.dist a p := by rw [SimpleGraph.dist_comm]; exact hda.symm
    have hPa_side : ∀ w ∈ Pa.support, G.dist w p < G.dist w v := by
      intro w hw
      by_contra hcon
      have hle : G.dist w v ≤ G.dist w p := le_of_not_gt hcon
      have hlen := congrArg SimpleGraph.Walk.length (Pa.take_spec hw)
      rw [SimpleGraph.Walk.length_append] at hlen
      have t1 := SimpleGraph.dist_le (Pa.takeUntil w hw)
      have t2 := SimpleGraph.dist_le (Pa.dropUntil w hw)
      have t3 := hconn.dist_triangle (u := a) (v := w) (w := v)
      omega
    have hPvb_side : ∀ w ∈ Pvb.support, G.dist w v < G.dist w p := by
      intro w hw
      by_contra hcon
      have hle : G.dist w p ≤ G.dist w v := le_of_not_gt hcon
      have hlen := congrArg SimpleGraph.Walk.length (Pvb.take_spec hw)
      rw [SimpleGraph.Walk.length_append] at hlen
      have t1 := SimpleGraph.dist_le (Pvb.takeUntil w hw)
      have t2 := SimpleGraph.dist_le (Pvb.dropUntil w hw)
      have t3 := hconn.dist_triangle (u := b) (v := w) (w := p)
      have hcomm : G.dist b w = G.dist w b := SimpleGraph.dist_comm
      have hcomm2 : G.dist v w = G.dist w v := SimpleGraph.dist_comm
      omega
    have hpnv : p ≠ v := hpv.ne
    set E : G.Walk p v := SimpleGraph.Walk.cons hpv SimpleGraph.Walk.nil with hEdef
    have hE : E.IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simpa [hEdef] using hpnv)
    have hdisj : ∀ w ∈ Pa.support, w ∈ Pvb.support → False := by
      intro w hw1 hw2
      have g1 := hPa_side w hw1
      have g2 := hPvb_side w hw2
      omega
    have hpPvb : p ∉ Pvb.support := by
      intro hm
      have g := hPvb_side p hm
      rw [SimpleGraph.dist_self] at g
      omega
    have hvPa : v ∉ Pa.support := by
      intro hm
      have g := hPa_side v hm
      have hvp : G.dist v p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hpv.symm
      rw [SimpleGraph.dist_self] at g
      omega
    have hinner : (E.append Pvb).IsPath := by
      apply SimpleGraph.Walk.isPath_append_of_isPath hE hPvb_path
      intro x hx1 hx2
      rw [hEdef, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hx1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
      rcases hx1 with rfl | rfl
      · exact (hpPvb hx2).elim
      · rfl
    have hW : (Pa.append (E.append Pvb)).IsPath := by
      apply SimpleGraph.Walk.isPath_append_of_isPath hPa_path hinner
      intro x hx1 hx2
      rw [SimpleGraph.Walk.support_append, List.mem_append] at hx2
      rcases hx2 with hxE | hxT
      · rw [hEdef, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hxE
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxE
        rcases hxE with rfl | rfl
        · rfl
        · exact (hvPa hx1).elim
      · exact (hdisj x hx1 (List.mem_of_mem_tail hxT)).elim
    have hlenW : (Pa.append (E.append Pvb)).length = 2 * G.dist a p + 1 := by
      simp only [SimpleGraph.Walk.length_append, hEdef, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_nil, hPa_len, hPvb_len, hvb]
      omega
    have hsub := (hG.isAcyclic.subsingleton_path a b).elim
      (⟨Pa.append (E.append Pvb), hW⟩ : G.Path a b)
      (SimpleGraph.Path.singleton hab)
    have hlen := congrArg (fun r : G.Path a b => r.1.length) hsub
    dsimp only at hlen
    rw [hlenW] at hlen
    have hlen1 : (SimpleGraph.Path.singleton hab).1.length = 1 := rfl
    rw [hlen1] at hlen
    have hcontra : False := by omega
    exact hcontra.elim

/-- Every edge directed away from the root, except the crossing edge itself, lies within one
side of the cut. -/
private theorem side_of_directed_of_ne {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (r q₁ q₂ : V) (hpv : G.Adj q₁ q₂) (hdir : IsAwayFrom G r q₁ q₂)
    {a b : V} (hab : IsAwayFrom G r a b) (hne : (a, b) ≠ (q₁, q₂)) :
    (a ∈ sideNear G q₁ q₂ ∧ b ∈ sideNear G q₁ q₂) ∨
      (a ∈ sideNear G q₂ q₁ ∧ b ∈ sideNear G q₂ q₁) := by
  have hcover := cover_sideNear G hG hpv
  have ha12 : a ∈ sideNear G q₁ q₂ ∨ a ∈ sideNear G q₂ q₁ := by
    have hm : a ∈ sideNear G q₁ q₂ ∪ sideNear G q₂ q₁ := by
      rw [hcover]; exact Finset.mem_univ a
    rwa [Finset.mem_union] at hm
  have hb12 : b ∈ sideNear G q₁ q₂ ∨ b ∈ sideNear G q₂ q₁ := by
    have hm : b ∈ sideNear G q₁ q₂ ∪ sideNear G q₂ q₁ := by
      rw [hcover]; exact Finset.mem_univ b
    rwa [Finset.mem_union] at hm
  have hadj : G.Adj a b ∧ G.dist r b = G.dist r a + 1 := hab
  have hdir' : G.Adj q₁ q₂ ∧ G.dist r q₂ = G.dist r q₁ + 1 := hdir
  rcases ha12 with ha1 | ha2 <;> rcases hb12 with hb1 | hb2
  · exact Or.inl ⟨ha1, hb1⟩
  · rw [mem_sideNear] at ha1 hb2
    obtain ⟨rfl, rfl⟩ := eq_crossing_of_mem_sides G hG hpv hadj.1 ha1 hb2
    exact absurd rfl hne
  · rw [mem_sideNear] at ha2 hb1
    obtain ⟨rfl, rfl⟩ := eq_crossing_of_mem_sides G hG hpv.symm hadj.1 ha2 hb1
    have hcontra : False := by omega
    exact hcontra.elim
  · exact Or.inr ⟨ha2, hb2⟩

/-! ### Factorization of the leaf distribution over a cut -/

/-- The flattening along a partitioned cut factors through the states at the cut, with rows on
either side: summing the joint distribution over each side separately, joined over the states at
the crossing edge, exhibits the flattening as a matrix product with middle dimension `K`. -/
private theorem flatten_eq_mul_of_partition
    {V K R X : Type} [Fintype V] [Fintype K] [DecidableEq K]
    [CommSemiring R] [DecidableEq X]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : X → V)
    (r : V) (π : K → R) (M : V → V → Matrix K K R)
    (S₁ S₂ : Finset V) (hdisj : Disjoint S₁ S₂) (hcover : ∀ v : V, v ∈ S₁ ∨ v ∈ S₂)
    (hr : r ∈ S₁) (q₁ q₂ : V) (hq₁ : q₁ ∈ S₁) (hq₂ : q₂ ∈ S₂)
    (hdir : IsAwayFrom G r q₁ q₂)
    (hside : ∀ a b, IsAwayFrom G r a b → (a, b) ≠ (q₁, q₂) →
      (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂))
    (X₁f X₂f : Finset X) (hX₁ : ∀ x : X, x ∈ X₁f ↔ ℓ x ∈ S₁)
    (hX₂ : ∀ x : X, x ∈ X₂f ↔ ℓ x ∈ S₂) :
    (∃ L₂ : Matrix (({x // x ∈ X₂f} → K)) K R,
      ∃ R₁ : Matrix K (({x // x ∉ X₂f} → K)) R,
        flatten X₂f (leafDist G ℓ r π M) = L₂ * R₁) ∧
    (∃ L₁ : Matrix (({x // x ∈ X₁f} → K)) K R,
      ∃ R₂ : Matrix K (({x // x ∉ X₁f} → K)) R,
        flatten X₁f (leafDist G ℓ r π M) = L₁ * R₂) := by
  classical
  letI : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  set Df := Finset.univ.filter (fun ab : V × V => IsAwayFrom G r ab.1 ab.2) with hDf
  set E₁ := (Df.erase (q₁, q₂)).filter (fun ab : V × V => ab.1 ∈ S₁) with hE₁
  set E₂ := (Df.erase (q₁, q₂)).filter (fun ab : V × V => ab.1 ∈ S₂) with hE₂
  have memS₂_of : ∀ {v : V}, v ∉ S₁ → v ∈ S₂ := fun hv => (hcover _).resolve_left hv
  have memS₁_of : ∀ {v : V}, v ∉ S₂ → v ∈ S₁ := fun hv => (hcover _).resolve_right hv
  have hpart₁ : ∀ x : X, x ∈ X₁f ↔ x ∉ X₂f := by
    intro x
    rw [hX₁, hX₂]
    constructor
    · intro h1 h2
      exact Finset.disjoint_left.mp hdisj h1 h2
    · intro hn
      exact memS₁_of hn
  have hpart₂ : ∀ x : X, x ∈ X₂f ↔ x ∉ X₁f := by
    intro x
    rw [hX₁, hX₂]
    constructor
    · intro h2 h1
      exact Finset.disjoint_left.mp hdisj h1 h2
    · intro hn
      exact memS₂_of hn
  have hmem1 : ∀ {x : X}, x ∉ X₂f → ℓ x ∈ S₁ :=
    fun hx => memS₁_of (fun h => hx ((hX₂ _).mpr h))
  have hmem2 : ∀ {x : X}, x ∉ X₁f → ℓ x ∈ S₂ :=
    fun hx => memS₂_of (fun h => hx ((hX₁ _).mpr h))
  have hmem_q : (q₁, q₂) ∈ Df := by
    rw [hDf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdir⟩
  have hE₁side : ∀ ab ∈ E₁, ab.1 ∈ S₁ ∧ ab.2 ∈ S₁ := by
    intro ab hab
    rw [hE₁, Finset.mem_filter] at hab
    obtain ⟨hab_erase, hm1⟩ := hab
    rw [Finset.mem_erase, hDf, Finset.mem_filter] at hab_erase
    obtain ⟨hne, -, hdir_ab⟩ := hab_erase
    have hdir_ab' : IsAwayFrom G r ab.1 ab.2 := hdir_ab
    have hne' : (ab.1, ab.2) ≠ (q₁, q₂) := by simpa using hne
    rcases hside ab.1 ab.2 hdir_ab' hne' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact (Finset.disjoint_left.mp hdisj hm1 h1).elim
  have hE₂side : ∀ ab ∈ E₂, ab.1 ∈ S₂ ∧ ab.2 ∈ S₂ := by
    intro ab hab
    rw [hE₂, Finset.mem_filter] at hab
    obtain ⟨hab_erase, hm2⟩ := hab
    rw [Finset.mem_erase, hDf, Finset.mem_filter] at hab_erase
    obtain ⟨hne, -, hdir_ab⟩ := hab_erase
    have hdir_ab' : IsAwayFrom G r ab.1 ab.2 := hdir_ab
    have hne' : (ab.1, ab.2) ≠ (q₁, q₂) := by simpa using hne
    rcases hside ab.1 ab.2 hdir_ab' hne' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Finset.disjoint_left.mp hdisj h1 hm2).elim
    · exact ⟨h1, h2⟩
  have hprod : ∀ σ : V → K, ∏ ab ∈ Df, M ab.1 ab.2 (σ ab.1) (σ ab.2) =
      (∏ ab ∈ E₁, M ab.1 ab.2 (σ ab.1) (σ ab.2)) *
      M q₁ q₂ (σ q₁) (σ q₂) *
      (∏ ab ∈ E₂, M ab.1 ab.2 (σ ab.1) (σ ab.2)) := by
    intro σ
    have h1 : M q₁ q₂ (σ q₁) (σ q₂) *
        ∏ ab ∈ Df.erase (q₁, q₂), M ab.1 ab.2 (σ ab.1) (σ ab.2) =
        ∏ ab ∈ Df, M ab.1 ab.2 (σ ab.1) (σ ab.2) :=
      Finset.mul_prod_erase Df (fun ab => M ab.1 ab.2 (σ ab.1) (σ ab.2)) hmem_q
    have h2 : (∏ ab ∈ (Df.erase (q₁, q₂)).filter (fun ab : V × V => ab.1 ∈ S₁),
          M ab.1 ab.2 (σ ab.1) (σ ab.2)) *
        (∏ ab ∈ (Df.erase (q₁, q₂)).filter (fun ab : V × V => ¬ ab.1 ∈ S₁),
          M ab.1 ab.2 (σ ab.1) (σ ab.2)) =
        ∏ ab ∈ Df.erase (q₁, q₂), M ab.1 ab.2 (σ ab.1) (σ ab.2) :=
      Finset.prod_filter_mul_prod_filter_not _ _ _
    have h2c : ((Df.erase (q₁, q₂)).filter fun ab : V × V => ¬ ab.1 ∈ S₁) = E₂ := by
      rw [hE₂]
      apply Finset.filter_congr
      intro ab _
      constructor
      · intro hn
        exact memS₂_of hn
      · intro h2s h1s
        exact Finset.disjoint_left.mp hdisj h1s h2s
    rw [h2c] at h2
    rw [← h1, ← h2, ← hE₁]
    ring
  set combine : (S₁ → K) → (S₂ → K) → (V → K) :=
    fun σ₁ σ₂ v => if h : v ∈ S₁ then σ₁ ⟨v, h⟩ else σ₂ ⟨v, memS₂_of h⟩ with hcomb
  have hcomb₁ : ∀ (σ₁ : S₁ → K) (σ₂ : S₂ → K) (v : V) (h : v ∈ S₁),
      combine σ₁ σ₂ v = σ₁ ⟨v, h⟩ := by
    intro σ₁ σ₂ v h
    simp only [hcomb, dite_eq_left h]
  have hcomb₂ : ∀ (σ₁ : S₁ → K) (σ₂ : S₂ → K) (v : V) (h : v ∈ S₂),
      combine σ₁ σ₂ v = σ₂ ⟨v, h⟩ := by
    intro σ₁ σ₂ v h
    have hn : v ∉ S₁ := fun hm => Finset.disjoint_left.mp hdisj hm h
    simp only [hcomb, dite_eq_right hn]
  set F₁w : (X → K) → Finset (S₁ → K) := fun w => Finset.univ.filter
    (fun σ₁ : S₁ → K => ∀ x (hx : x ∈ X₁f), σ₁ ⟨ℓ x, (hX₁ x).mp hx⟩ = w x) with hF₁w
  set F₂w : (X → K) → Finset (S₂ → K) := fun w => Finset.univ.filter
    (fun σ₂ : S₂ → K => ∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ = w x) with hF₂w
  set D₁ : (S₁ → K) → (V × V) → R := fun σ₁ ab =>
    if h : ab ∈ E₁ then M ab.1 ab.2 (σ₁ ⟨ab.1, (hE₁side ab h).1⟩)
      (σ₁ ⟨ab.2, (hE₁side ab h).2⟩) else 1 with hD₁
  set D₂ : (S₂ → K) → (V × V) → R := fun σ₂ ab =>
    if h : ab ∈ E₂ then M ab.1 ab.2 (σ₂ ⟨ab.1, (hE₂side ab h).1⟩)
      (σ₂ ⟨ab.2, (hE₂side ab h).2⟩) else 1 with hD₂
  set G₂ : (S₂ → K) → R := fun σ₂ => ∏ ab ∈ E₂, D₂ σ₂ ab with hG₂
  set F₁ : (S₁ → K) → K → R := fun σ₁ s =>
    π (σ₁ ⟨r, hr⟩) * (∏ ab ∈ E₁, D₁ σ₁ ab) * M q₁ q₂ (σ₁ ⟨q₁, hq₁⟩) s with hF₁
  have hrest₁ : ∀ (σ₁ : S₁ → K) (σ₂ : S₂ → K) (ab : V × V) (hab : ab ∈ E₁),
      M ab.1 ab.2 ((combine σ₁ σ₂) ab.1) ((combine σ₁ σ₂) ab.2) = D₁ σ₁ ab := by
    intro σ₁ σ₂ ab hab
    simp only [hD₁, dite_eq_left hab]
    rw [hcomb₁ σ₁ σ₂ ab.1 (hE₁side ab hab).1, hcomb₁ σ₁ σ₂ ab.2 (hE₁side ab hab).2]
  have hrest₂ : ∀ (σ₁ : S₁ → K) (σ₂ : S₂ → K) (ab : V × V) (hab : ab ∈ E₂),
      M ab.1 ab.2 ((combine σ₁ σ₂) ab.1) ((combine σ₁ σ₂) ab.2) = D₂ σ₂ ab := by
    intro σ₁ σ₂ ab hab
    simp only [hD₂, dite_eq_left hab]
    rw [hcomb₂ σ₁ σ₂ ab.1 (hE₂side ab hab).1, hcomb₂ σ₁ σ₂ ab.2 (hE₂side ab hab).2]
  have hcore : ∀ w : X → K, leafDist G ℓ r π M w =
      ∑ s, (∑ σ₂ ∈ Finset.univ.filter (fun σ₂ : S₂ → K =>
        (∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ = w x) ∧ σ₂ ⟨q₂, hq₂⟩ = s),
        G₂ σ₂) * (∑ σ₁ ∈ F₁w w, F₁ σ₁ s) := by
    intro w
    let hEq : ↥(F₁w w) × ↥(F₂w w) ≃
        ↥(Finset.univ.filter (fun σ : V → K => ∀ x, σ (ℓ x) = w x)) :=
      { toFun := fun t => ⟨combine t.1.1 t.2.1, by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
          by_cases hx : ℓ x ∈ S₁
          · rw [hcomb₁ _ _ _ hx]
            have hx1 : x ∈ X₁f := (hX₁ x).mpr hx
            have hc := t.1.2
            simp only [hF₁w, Finset.mem_filter] at hc
            exact hc.2 x hx1
          · have hx2s : ℓ x ∈ S₂ := memS₂_of hx
            rw [hcomb₂ _ _ _ hx2s]
            have hx2 : x ∈ X₂f := (hX₂ x).mpr hx2s
            have hc := t.2.2
            simp only [hF₂w, Finset.mem_filter] at hc
            exact hc.2 x hx2⟩,
        invFun := fun s =>
          (⟨fun q => s.1 q.1, by
            have hs : ∀ x, s.1 (ℓ x) = w x := (Finset.mem_filter.mp s.2).2
            simp only [hF₁w, Finset.mem_filter, Finset.mem_univ, true_and]
            intro x hx
            exact hs x⟩,
          ⟨fun q => s.1 q.1, by
            have hs : ∀ x, s.1 (ℓ x) = w x := (Finset.mem_filter.mp s.2).2
            simp only [hF₂w, Finset.mem_filter, Finset.mem_univ, true_and]
            intro x hx
            exact hs x⟩),
        left_inv := fun t => by
          obtain ⟨t₁, t₂⟩ := t
          show (⟨fun q => (combine t₁.1 t₂.1) q.1, _⟩,
            ⟨fun q => (combine t₁.1 t₂.1) q.1, _⟩) = (t₁, t₂)
          rw [Prod.ext_iff]
          constructor
          · apply Subtype.ext
            funext q
            obtain ⟨v, hv⟩ := q
            show (combine t₁.1 t₂.1) v = t₁.1 ⟨v, hv⟩
            rw [hcomb₁ _ _ _ hv]
          · apply Subtype.ext
            funext q
            obtain ⟨v, hv⟩ := q
            show (combine t₁.1 t₂.1) v = t₂.1 ⟨v, hv⟩
            rw [hcomb₂ _ _ _ hv],
        right_inv := fun s => by
          apply Subtype.ext
          funext v
          show (combine (fun q => s.1 q.1) (fun q => s.1 q.1)) v = s.1 v
          by_cases hv : v ∈ S₁
          · simp only [hcomb, dite_eq_left hv]
          · simp only [hcomb, dite_eq_right hv] }
    have hEq_apply : ∀ t : ↥(F₁w w) × ↥(F₂w w),
        (hEq t).1 = combine t.1.1 t.2.1 := fun t => rfl
    have hsum : leafDist G ℓ r π M w =
        ∑ t₁ : ↥(F₁w w), ∑ t₂ : ↥(F₂w w),
          treeJoint G r π M (combine t₁.1 t₂.1) := by
      have h1 : leafDist G ℓ r π M w =
          ∑ s : ↥(Finset.univ.filter (fun σ : V → K => ∀ x, σ (ℓ x) = w x)),
            treeJoint G r π M s.1 := by
        have hrfl : leafDist G ℓ r π M w =
            ∑ σ ∈ Finset.univ.filter (fun σ : V → K => ∀ x, σ (ℓ x) = w x),
              treeJoint G r π M σ := rfl
        rw [hrfl]
        exact (Finset.sum_coe_sort _ (fun σ => treeJoint G r π M σ)).symm
      calc leafDist G ℓ r π M w
          = ∑ s : ↥(Finset.univ.filter (fun σ : V → K => ∀ x, σ (ℓ x) = w x)),
              treeJoint G r π M s.1 := h1
        _ = ∑ t : ↥(F₁w w) × ↥(F₂w w), treeJoint G r π M (hEq t).1 :=
              (hEq.sum_comp (fun s => treeJoint G r π M s.1)).symm
        _ = ∑ t₁ : ↥(F₁w w), ∑ t₂ : ↥(F₂w w),
              treeJoint G r π M (combine t₁.1 t₂.1) := by
              rw [Fintype.sum_prod_type]
              refine Finset.sum_congr rfl
                (fun t₁ _ => Finset.sum_congr rfl (fun t₂ _ => ?_))
              show treeJoint G r π M (hEq (t₁, t₂)).1 = _
              rw [hEq_apply]
    have hfactor : ∀ (t₁ : ↥(F₁w w)) (t₂ : ↥(F₂w w)),
        treeJoint G r π M (combine t₁.1 t₂.1) =
          F₁ t₁.1 (t₂.1 ⟨q₂, hq₂⟩) * G₂ t₂.1 := by
      intro t₁ t₂
      have hJ : treeJoint G r π M (combine t₁.1 t₂.1) =
          π ((combine t₁.1 t₂.1) r) * ∏ ab ∈ Df, M ab.1 ab.2
            ((combine t₁.1 t₂.1) ab.1) ((combine t₁.1 t₂.1) ab.2) := rfl
      rw [hJ, hprod]
      have he1 : (∏ ab ∈ E₁, M ab.1 ab.2 ((combine t₁.1 t₂.1) ab.1)
          ((combine t₁.1 t₂.1) ab.2)) = ∏ ab ∈ E₁, D₁ t₁.1 ab :=
        Finset.prod_congr rfl (fun ab hab => hrest₁ t₁.1 t₂.1 ab hab)
      have he2 : (∏ ab ∈ E₂, M ab.1 ab.2 ((combine t₁.1 t₂.1) ab.1)
          ((combine t₁.1 t₂.1) ab.2)) = ∏ ab ∈ E₂, D₂ t₂.1 ab :=
        Finset.prod_congr rfl (fun ab hab => hrest₂ t₁.1 t₂.1 ab hab)
      rw [he1, he2, hcomb₁ t₁.1 t₂.1 r hr, hcomb₁ t₁.1 t₂.1 q₁ hq₁,
        hcomb₂ t₁.1 t₂.1 q₂ hq₂, hF₁, hG₂]
      ring
    have hfibfilt : ∀ s : K, (F₂w w).filter (fun σ₂ : S₂ → K => σ₂ ⟨q₂, hq₂⟩ = s) =
        Finset.univ.filter (fun σ₂ : S₂ → K =>
          (∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ = w x) ∧ σ₂ ⟨q₂, hq₂⟩ = s) := by
      intro s
      simp only [hF₂w, Finset.filter_filter]
    calc leafDist G ℓ r π M w
        = ∑ t₁ : ↥(F₁w w), ∑ t₂ : ↥(F₂w w),
            treeJoint G r π M (combine t₁.1 t₂.1) := hsum
      _ = ∑ t₁ : ↥(F₁w w), ∑ t₂ : ↥(F₂w w),
            F₁ t₁.1 (t₂.1 ⟨q₂, hq₂⟩) * G₂ t₂.1 := by
            apply Finset.sum_congr rfl; intro t₁ _
            apply Finset.sum_congr rfl; intro t₂ _
            exact hfactor t₁ t₂
      _ = ∑ t₂ : ↥(F₂w w), ∑ t₁ : ↥(F₁w w),
            F₁ t₁.1 (t₂.1 ⟨q₂, hq₂⟩) * G₂ t₂.1 := Finset.sum_comm
      _ = ∑ t₂ : ↥(F₂w w),
            (∑ t₁ : ↥(F₁w w), F₁ t₁.1 (t₂.1 ⟨q₂, hq₂⟩)) * G₂ t₂.1 := by
            apply Finset.sum_congr rfl; intro t₂ _
            exact (Finset.sum_mul _ _ _).symm
      _ = ∑ σ₂ ∈ F₂w w,
            (∑ t₁ : ↥(F₁w w), F₁ t₁.1 (σ₂ ⟨q₂, hq₂⟩)) * G₂ σ₂ :=
            Finset.sum_coe_sort _
              (fun σ₂ => (∑ t₁ : ↥(F₁w w), F₁ t₁.1 (σ₂ ⟨q₂, hq₂⟩)) * G₂ σ₂)
      _ = ∑ s : K, ∑ σ₂ ∈ (F₂w w).filter (fun σ₂ : S₂ → K => σ₂ ⟨q₂, hq₂⟩ = s),
            (∑ t₁ : ↥(F₁w w), F₁ t₁.1 (σ₂ ⟨q₂, hq₂⟩)) * G₂ σ₂ :=
            (Finset.sum_fiberwise_of_maps_to (s := F₂w w) (t := Finset.univ)
              (g := fun σ₂ : S₂ → K => σ₂ ⟨q₂, hq₂⟩)
              (fun _ _ => Finset.mem_univ _) _).symm
      _ = ∑ s, (∑ σ₂ ∈ Finset.univ.filter (fun σ₂ : S₂ → K =>
              (∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ = w x) ∧
                σ₂ ⟨q₂, hq₂⟩ = s), G₂ σ₂) *
            (∑ σ₁ ∈ F₁w w, F₁ σ₁ s) := by
            apply Finset.sum_congr rfl; intro s _
            have hfib : ∀ σ₂ ∈ (F₂w w).filter (fun σ₂ : S₂ → K => σ₂ ⟨q₂, hq₂⟩ = s),
                (∑ t₁ : ↥(F₁w w), F₁ t₁.1 (σ₂ ⟨q₂, hq₂⟩)) * G₂ σ₂ =
                  (∑ t₁ : ↥(F₁w w), F₁ t₁.1 s) * G₂ σ₂ := by
              intro σ₂ hσ₂
              rw [Finset.mem_filter] at hσ₂
              rw [hσ₂.2]
            have hS : (∑ t₁ : ↥(F₁w w), F₁ t₁.1 s) = ∑ σ₁ ∈ F₁w w, F₁ σ₁ s :=
              Finset.sum_coe_sort _ (fun σ₁ => F₁ σ₁ s)
            rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum, hS, hfibfilt]
            exact mul_comm _ _
  constructor
  · -- rows on the far side
    set F₂u : (({x // x ∈ X₂f} → K)) → K → Finset (S₂ → K) := fun u s =>
      Finset.univ.filter (fun σ₂ : S₂ → K =>
        (∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ = u ⟨x, hx⟩) ∧
          σ₂ ⟨q₂, hq₂⟩ = s) with hF₂u
    set F₁u : (({x // x ∉ X₂f} → K)) → Finset (S₁ → K) := fun v =>
      Finset.univ.filter (fun σ₁ : S₁ → K =>
        ∀ x (hx : x ∉ X₂f), σ₁ ⟨ℓ x, hmem1 hx⟩ = v ⟨x, hx⟩) with hF₁u
    refine ⟨fun u s => ∑ σ₂ ∈ F₂u u s, G₂ σ₂,
      fun s v => ∑ σ₁ ∈ F₁u v, F₁ σ₁ s, ?_⟩
    apply Matrix.ext
    intro u v
    show leafDist G ℓ r π M
      (fun x => if h : x ∈ X₂f then u ⟨x, h⟩ else v ⟨x, h⟩) =
      ∑ s, (∑ σ₂ ∈ F₂u u s, G₂ σ₂) * (∑ σ₁ ∈ F₁u v, F₁ σ₁ s)
    rw [hcore]
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    · have hfu : Finset.univ.filter (fun σ₂ : S₂ → K =>
          (∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ =
            (fun x => if h : x ∈ X₂f then u ⟨x, h⟩ else v ⟨x, h⟩) x) ∧
            σ₂ ⟨q₂, hq₂⟩ = s) = F₂u u s := by
        rw [hF₂u]
        apply Finset.filter_congr
        intro σ₂ _
        constructor
        · intro hcon
          refine ⟨fun x hx => ?_, hcon.2⟩
          have hc := hcon.1 x hx
          simp only [dite_eq_left hx] at hc
          exact hc
        · intro hcon
          refine ⟨fun x hx => ?_, hcon.2⟩
          have hc := hcon.1 x hx
          simp only [dite_eq_left hx]
          exact hc
      rw [hfu]
    · have hfu : F₁w (fun x => if h : x ∈ X₂f then u ⟨x, h⟩ else v ⟨x, h⟩) =
          F₁u v := by
        rw [hF₁u, hF₁w]
        apply Finset.filter_congr
        intro σ₁ _
        constructor
        · intro hcon x hx
          have hx1 : x ∈ X₁f := (hpart₁ x).mpr hx
          have hc := hcon x hx1
          simp only [dite_eq_right hx] at hc
          exact hc
        · intro hcon x hx1
          have hx : x ∉ X₂f := (hpart₁ x).mp hx1
          have hc := hcon x hx
          simp only [dite_eq_right hx]
          exact hc
      rw [hfu]
  · -- rows on the near side
    set F₁n : (({x // x ∈ X₁f} → K)) → Finset (S₁ → K) := fun u =>
      Finset.univ.filter (fun σ₁ : S₁ → K =>
        ∀ x (hx : x ∈ X₁f), σ₁ ⟨ℓ x, (hX₁ x).mp hx⟩ = u ⟨x, hx⟩) with hF₁n
    set F₂n : (({x // x ∉ X₁f} → K)) → K → Finset (S₂ → K) := fun v s =>
      Finset.univ.filter (fun σ₂ : S₂ → K =>
        (∀ x (hx : x ∉ X₁f), σ₂ ⟨ℓ x, hmem2 hx⟩ = v ⟨x, hx⟩) ∧
          σ₂ ⟨q₂, hq₂⟩ = s) with hF₂n
    refine ⟨fun u s => ∑ σ₁ ∈ F₁n u, F₁ σ₁ s,
      fun s v => ∑ σ₂ ∈ F₂n v s, G₂ σ₂, ?_⟩
    apply Matrix.ext
    intro u v
    show leafDist G ℓ r π M
      (fun x => if h : x ∈ X₁f then u ⟨x, h⟩ else v ⟨x, h⟩) =
      ∑ s, (∑ σ₁ ∈ F₁n u, F₁ σ₁ s) * (∑ σ₂ ∈ F₂n v s, G₂ σ₂)
    rw [hcore]
    apply Finset.sum_congr rfl
    intro s _
    have hfu₁ : F₁w (fun x => if h : x ∈ X₁f then u ⟨x, h⟩ else v ⟨x, h⟩) =
        F₁n u := by
      rw [hF₁n, hF₁w]
      apply Finset.filter_congr
      intro σ₁ _
      constructor
      · intro hcon x hx
        have hc := hcon x hx
        simp only [dite_eq_left hx] at hc
        exact hc
      · intro hcon x hx
        have hc := hcon x hx
        simp only [dite_eq_left hx]
        exact hc
    have hfu₂ : Finset.univ.filter (fun σ₂ : S₂ → K =>
        (∀ x (hx : x ∈ X₂f), σ₂ ⟨ℓ x, (hX₂ x).mp hx⟩ =
          (fun x => if h : x ∈ X₁f then u ⟨x, h⟩ else v ⟨x, h⟩) x) ∧
          σ₂ ⟨q₂, hq₂⟩ = s) = F₂n v s := by
      rw [hF₂n]
      apply Finset.filter_congr
      intro σ₂ _
      constructor
      · intro hcon
        refine ⟨fun x hx => ?_, hcon.2⟩
        have hx2 : x ∈ X₂f := (hpart₂ x).mpr hx
        have hc := hcon.1 x hx2
        simp only [dite_eq_right hx] at hc
        exact hc
      · intro hcon
        refine ⟨fun x hx2 => ?_, hcon.2⟩
        have hx : x ∉ X₁f := (hpart₂ x).mp hx2
        have hc := hcon.1 x hx
        simp only [dite_eq_right hx]
        exact hc
    rw [hfu₁, hfu₂, mul_comm]

/-! ### The rank bound -/

/-- **Edge flattenings have rank at most `κ`** (Allman and Rhodes 2008, Section 2): for the
general Markov model with `κ` states on an unrooted binary phylogenetic tree `T`, rooted at any
vertex, with stochastic parameters, the flattening of the leaf distribution along every edge
split of `T` has rank at most `κ`.

Source: Allman and Rhodes (2008), Section 2. -/
public theorem rank_flatten_leafDist_le {X K : Type} [Fintype X] [DecidableEq X] [Fintype K]
    [DecidableEq K] (T : UnrootedBinaryTree X) (r : T.V)
    (π : K → ℝ) (M : T.V → T.V → Matrix K K ℝ) (hp : IsStochastic T.G r π M)
    {A : Finset X} (hA : A ∈ edgeSplits T) :
    (flatten A (leafDist T.G (leafOf T) r π M)).rank ≤ Fintype.card K := by
  classical
  letI : DecidableEq T.V := fun a b => Classical.propDecidable (a = b)
  have hcover_of : ∀ {p v : T.V}, T.G.Adj p v →
      ∀ w, w ∈ sideNear T.G p v ∨ w ∈ sideNear T.G v p := by
    intro p v hpv w
    have h := cover_sideNear T.G T.isTree hpv
    have hm : w ∈ sideNear T.G p v ∪ sideNear T.G v p := by
      rw [h]; exact Finset.mem_univ w
    rwa [Finset.mem_union] at hm
  obtain ⟨⟨c₁, c₂⟩, hmem, heq⟩ := Finset.mem_image.mp hA
  have hadj : T.G.Adj c₁ c₂ := (Finset.mem_filter.mp hmem).2
  have hAeq : A = edgeSide T c₁ c₂ := heq.symm
  subst hAeq
  have hXmem : ∀ (p v : T.V),
      (∀ x : X, x ∈ edgeSide T p v ↔ leafOf T x ∈ sideNear T.G v p) := by
    intro p v x
    have he : edgeSide T p v =
        Finset.univ.filter
          (fun x => T.G.dist (T.label x) v < T.G.dist (T.label x) p) := rfl
    have hl : leafOf T x = (T.label x : T.V) := rfl
    rw [mem_sideNear, he, hl, Finset.mem_filter]
    simp
  rcases T.isTree.dist_eq_dist_add_one_of_adj r hadj with h | h
  · -- The edge points towards the root side; rows are on the near side.
    have hdir : IsAwayFrom T.G r c₂ c₁ := ⟨hadj.symm, h⟩
    have hr : r ∈ sideNear T.G c₂ c₁ :=
      (mem_sideNear T.G c₂ c₁ r).mpr (by omega)
    have hq₁ : c₂ ∈ sideNear T.G c₂ c₁ := self_mem_sideNear T.G hadj.symm
    have hq₂ : c₁ ∈ sideNear T.G c₁ c₂ := self_mem_sideNear T.G hadj
    have hside : ∀ a b, IsAwayFrom T.G r a b → (a, b) ≠ (c₂, c₁) →
        (a ∈ sideNear T.G c₂ c₁ ∧ b ∈ sideNear T.G c₂ c₁) ∨
          (a ∈ sideNear T.G c₁ c₂ ∧ b ∈ sideNear T.G c₁ c₂) :=
      fun a b hab hne => side_of_directed_of_ne T.G T.isTree r c₂ c₁ hadj.symm hdir
        hab hne
    obtain ⟨L₁, R₂, hLR⟩ := (flatten_eq_mul_of_partition T.G (leafOf T) r π M
      (sideNear T.G c₂ c₁) (sideNear T.G c₁ c₂)
      (disjoint_sideNear T.G c₂ c₁) (hcover_of hadj.symm)
      hr c₂ c₁ hq₁ hq₂ hdir hside (edgeSide T c₁ c₂) (edgeSide T c₂ c₁)
      (hXmem c₁ c₂) (hXmem c₂ c₁)).2
    rw [hLR]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_card_width _)
  · -- The edge points away from the root side; rows are on the far side.
    have hdir : IsAwayFrom T.G r c₁ c₂ := ⟨hadj, h⟩
    have hr : r ∈ sideNear T.G c₁ c₂ :=
      (mem_sideNear T.G c₁ c₂ r).mpr (by omega)
    have hq₁ : c₁ ∈ sideNear T.G c₁ c₂ := self_mem_sideNear T.G hadj
    have hq₂ : c₂ ∈ sideNear T.G c₂ c₁ := self_mem_sideNear T.G hadj.symm
    have hside : ∀ a b, IsAwayFrom T.G r a b → (a, b) ≠ (c₁, c₂) →
        (a ∈ sideNear T.G c₁ c₂ ∧ b ∈ sideNear T.G c₁ c₂) ∨
          (a ∈ sideNear T.G c₂ c₁ ∧ b ∈ sideNear T.G c₂ c₁) :=
      fun a b hab hne => side_of_directed_of_ne T.G T.isTree r c₁ c₂ hadj hdir
        hab hne
    obtain ⟨L₂, R₁, hLR⟩ := (flatten_eq_mul_of_partition T.G (leafOf T) r π M
      (sideNear T.G c₁ c₂) (sideNear T.G c₂ c₁)
      (disjoint_sideNear T.G c₁ c₂) (hcover_of hadj)
      hr c₁ c₂ hq₁ hq₂ hdir hside (edgeSide T c₂ c₁) (edgeSide T c₁ c₂)
      (hXmem c₂ c₁) (hXmem c₁ c₂)).1
    rw [hLR]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_card_width _)

section Helpers

private theorem treeJoint_eq_zero_of_neE (V K : Type) [Fintype V] [DecidableEq K]
    (G : SimpleGraph V) (hG : G.IsTree) (e f : V) (hef : G.Adj e f)
    (c : ℂ) (M : V → V → Matrix K K ℂ)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (σ : V → K) (n : ℕ) : ∀ (w : V), G.dist w e = n → G.dist w e < G.dist w f →
      σ w ≠ σ e → treeJoint G e (fun _ => c) M σ = 0 := by
  classical
  induction n with
  | zero =>
    intro w hdist hw hne
    have hwe : w = e := hG.connected.dist_eq_zero_iff.mp hdist
    rw [hwe] at hne
    exact absurd rfl hne
  | succ n ih =>
    intro w hdist hw hne
    have hwe : w ≠ e := fun heq => hne (by rw [heq])
    obtain ⟨p, hp_adj, hp_dist⟩ := SimpleGraph.exists_parent hG.connected hwe
    have hc1 : G.dist e w = G.dist w e := SimpleGraph.dist_comm
    have hc2 : G.dist e p = G.dist p e := SimpleGraph.dist_comm
    have hdist_p : G.dist p e = n := by omega
    have hwp : G.dist w p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp_adj
    have htri_wf : G.dist w f ≤ G.dist w p + G.dist p f := hG.connected.dist_triangle
    have hside_p : G.dist p e < G.dist p f := by omega
    by_cases hσp : σ p = σ e
    · have hσne : σ p ≠ σ w := fun h => hne (h.symm.trans hσp)
      have hnef : ¬(p = e ∧ w = f) := by
        intro h
        rw [h.2] at hw
        have h1 : G.dist f e = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef.symm
        have h0 : G.dist f f = 0 := SimpleGraph.dist_self
        omega
      have hmem : (p, w) ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_adj.symm, hp_dist.symm⟩
      have hfactor : M p w (σ p) (σ w) = 0 := by
        rw [hI p w hnef]
        simp [hσne]
      have hprod : ∏ ab ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2),
          M ab.1 ab.2 (σ ab.1) (σ ab.2) = 0 :=
        Finset.prod_eq_zero hmem hfactor
      simp only [treeJoint, hprod, mul_zero]
    · exact ih p hdist_p hside_p hσp

private theorem treeJoint_eq_zero_of_neF (V K : Type) [Fintype V] [DecidableEq K]
    (G : SimpleGraph V) (hG : G.IsTree) (e f : V) (hef : G.Adj e f)
    (c : ℂ) (M : V → V → Matrix K K ℂ)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (σ : V → K) (n : ℕ) : ∀ (w : V), G.dist w f = n → G.dist w f < G.dist w e →
      σ w ≠ σ f → treeJoint G e (fun _ => c) M σ = 0 := by
  classical
  induction n with
  | zero =>
    intro w hdist hw hne
    have hwf : w = f := hG.connected.dist_eq_zero_iff.mp hdist
    rw [hwf] at hne
    exact absurd rfl hne
  | succ n ih =>
    intro w hdist hw hne
    have hwf : w ≠ f := fun heq => hne (by rw [heq])
    obtain ⟨p, hp_adj, hp_dist⟩ := SimpleGraph.exists_parent hG.connected hwf
    have hc1 : G.dist f w = G.dist w f := SimpleGraph.dist_comm
    have hc2 : G.dist f p = G.dist p f := SimpleGraph.dist_comm
    have hdist_p : G.dist p f = n := by omega
    have hwp : G.dist w p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp_adj
    have htri_we : G.dist w e ≤ G.dist w p + G.dist p e := hG.connected.dist_triangle
    have hside_p : G.dist p f < G.dist p e := by omega
    have hside_w : G.dist e w = G.dist f w + 1 := by
      have hcomm : G.dist e w = G.dist w e := SimpleGraph.dist_comm
      have hcomm2 : G.dist f w = G.dist w f := SimpleGraph.dist_comm
      rcases hG.dist_eq_dist_add_one_of_adj w hef with h | h
      · omega
      · omega
    have hside_p' : G.dist e p = G.dist f p + 1 := by
      have hcomm : G.dist e p = G.dist p e := SimpleGraph.dist_comm
      have hcomm2 : G.dist f p = G.dist p f := SimpleGraph.dist_comm
      rcases hG.dist_eq_dist_add_one_of_adj p hef with h | h
      · omega
      · omega
    have hdir : G.dist e w = G.dist e p + 1 := by omega
    by_cases hσp : σ p = σ f
    · have hσne : σ p ≠ σ w := fun h => hne (h.symm.trans hσp)
      have hpe : p ≠ e := by
        intro h
        rw [h] at hside_p
        have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
        have h0 : G.dist e e = 0 := SimpleGraph.dist_self
        omega
      have hnef : ¬(p = e ∧ w = f) := fun h => hpe h.1
      have hmem : (p, w) ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_adj.symm, hdir⟩
      have hfactor : M p w (σ p) (σ w) = 0 := by
        rw [hI p w hnef]
        simp [hσne]
      have hprod : ∏ ab ∈ Finset.univ.filter
          (fun ab : V × V => IsAwayFrom G e ab.1 ab.2),
          M ab.1 ab.2 (σ ab.1) (σ ab.2) = 0 :=
        Finset.prod_eq_zero hmem hfactor
      simp only [treeJoint, hprod, mul_zero]
    · exact ih p hdist_p hside_p hσp

private theorem treeJoint_pattern (V K : Type) [Fintype V] [DecidableEq K]
    (G : SimpleGraph V) (hG : G.IsTree) (e f : V) (hef : G.Adj e f)
    (c : ℂ) (M : V → V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (a b : K) (σ : V → K)
    (hσ : ∀ w, (G.dist w e < G.dist w f → σ w = a) ∧
      (G.dist w f < G.dist w e → σ w = b)) :
    treeJoint G e (fun _ => c) M σ = c * c := by
  classical
  have hmem_ef : (e, f) ∈ Finset.univ.filter
      (fun ab : V × V => IsAwayFrom G e ab.1 ab.2) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hef, ?_⟩
    have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
    have h0 : G.dist e e = 0 := SimpleGraph.dist_self
    omega
  have hprod : ∏ ab ∈ Finset.univ.filter
      (fun ab : V × V => IsAwayFrom G e ab.1 ab.2),
      M ab.1 ab.2 (σ ab.1) (σ ab.2) = M e f (σ e) (σ f) := by
    apply Finset.prod_eq_single (e, f)
    · intro xy hxy hne
      obtain ⟨x, y⟩ := xy
      show M x y (σ x) (σ y) = 1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      have hxy' : G.Adj x y ∧ G.dist e y = G.dist e x + 1 := hxy
      obtain ⟨hadj, hdir⟩ := hxy'
      have hnef : ¬(x = e ∧ y = f) := by
        intro h
        apply hne
        rw [h.1, h.2]
      have hxside : G.dist x e < G.dist x f ∨ G.dist x f < G.dist x e := by
        have hne' : G.dist x e ≠ G.dist x f := hG.dist_ne_of_adj x hef
        exact lt_or_gt_of_ne hne'
      have hyside : G.dist y e < G.dist y f ∨ G.dist y f < G.dist y e := by
        have hne' : G.dist y e ≠ G.dist y f := hG.dist_ne_of_adj y hef
        exact lt_or_gt_of_ne hne'
      have hsame : σ x = σ y := by
        rcases hxside with hxE | hxF <;> rcases hyside with hyE | hyF
        · rw [(hσ x).1 hxE, (hσ y).1 hyE]
        · obtain ⟨hxe, hyf⟩ := eq_crossing_of_mem_sides G hG hef hadj hxE hyF
          rw [hxe, hyf] at hne
          exact absurd rfl hne
        · obtain ⟨hye, hxf⟩ := eq_crossing_of_mem_sides G hG hef hadj.symm hyE hxF
          rw [hxf, hye] at hdir
          have h1 : G.dist e f = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hef
          have h0 : G.dist e e = 0 := SimpleGraph.dist_self
          exfalso
          omega
        · rw [(hσ x).2 hxF, (hσ y).2 hyF]
      rw [hI x y hnef, Matrix.one_apply]
      exact ite_eq_left hsame
    · intro hcon
      exact absurd hmem_ef hcon
  have hJval : M e f (σ e) (σ f) = c := by rw [hJ]
  simp only [treeJoint, hprod, hJval]

private theorem fin4_cases (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have hmem : x ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by
    rw [← huniv]
    exact Finset.mem_univ x
  simpa using hmem

private theorem rank_of_perm (Row Col : Type) [Fintype Row] [Fintype Col]
    [DecidableEq Row] [DecidableEq Col]
    (M' : Matrix Row Col ℂ) (φ : Row ≃ Col) (d : ℂ) (hd : d ≠ 0)
    (hM : ∀ p q, M' p q = if φ p = q then d else 0) :
    M'.rank = Fintype.card Row := by
  classical
  have hsub : M'.submatrix (Equiv.refl Row) φ = d • (1 : Matrix Row Row ℂ) := by
    funext p r
    show M' p (φ r) = (d • (1 : Matrix Row Row ℂ)) p r
    rw [hM]
    simp only [Matrix.smul_apply, smul_eq_mul]
    by_cases hpr : p = r
    · subst hpr
      rw [ite_eq_left rfl, Matrix.one_apply, ite_eq_left rfl, mul_one]
    · have hne : φ p ≠ φ r := fun h => hpr (φ.injective h)
      rw [ite_eq_right hne, Matrix.one_apply, ite_eq_right hpr, mul_zero]
  have h1 : M'.rank = (M'.submatrix (Equiv.refl Row) φ).rank := by
    rw [Matrix.rank_submatrix]
  rw [h1, hsub]
  have hd' : d ∈ nonZeroDivisors ℂ := mem_nonZeroDivisors_of_ne_zero hd
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ hd', Matrix.rank_one]

private theorem exists_edge_of_quartet (T : UnrootedBinaryTree (Fin 4))
    (hT : DisplaysQuartet T 0 1 2 3) :
    ∃ e f : T.V, T.G.Adj e f ∧
      T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f ∧
      T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f ∧
      T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e ∧
      T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e := by
  obtain ⟨A0, hA0mem, h0mem, h1mem, h2nmem, h3nmem⟩ := hT
  simp only [edgeSplits] at hA0mem
  obtain ⟨⟨p, v⟩, hmem, heq⟩ := Finset.mem_image.mp hA0mem
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hmem
  have h0 : T.G.dist (leafOf T 0) v < T.G.dist (leafOf T 0) p := by
    have : (0 : Fin 4) ∈ edgeSide T p v := heq ▸ h0mem
    simpa [edgeSide, leafOf] using this
  have h1 : T.G.dist (leafOf T 1) v < T.G.dist (leafOf T 1) p := by
    have : (1 : Fin 4) ∈ edgeSide T p v := heq ▸ h1mem
    simpa [edgeSide, leafOf] using this
  have hn2 : ¬ T.G.dist (leafOf T 2) v < T.G.dist (leafOf T 2) p := by
    intro hlt
    have : (2 : Fin 4) ∈ edgeSide T p v := by simpa [edgeSide, leafOf] using hlt
    rw [heq] at this
    exact h2nmem this
  have hn3 : ¬ T.G.dist (leafOf T 3) v < T.G.dist (leafOf T 3) p := by
    intro hlt
    have : (3 : Fin 4) ∈ edgeSide T p v := by simpa [edgeSide, leafOf] using hlt
    rw [heq] at this
    exact h3nmem this
  refine ⟨v, p, hmem.symm, h0, h1, ?_, ?_⟩
  · have hside := T.isTree.dist_eq_dist_add_one_of_adj (leafOf T 2) hmem.symm
    omega
  · have hside := T.isTree.dist_eq_dist_add_one_of_adj (leafOf T 3) hmem.symm
    omega

private theorem leafDist_eq_zero_of_not_both_eq {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : Fin 4 → K) (h : ¬(u 0 = u 1 ∧ u 2 = u 3)) :
    leafDist T.G (leafOf T) e (fun _ => c) M u = 0 := by
  simp only [leafDist]
  apply Finset.sum_eq_zero
  intro σ hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  by_cases h01 : u 0 = u 1
  · by_cases h23 : u 2 = u 3
    · exfalso
      exact h ⟨h01, h23⟩
    · have hσ2 : σ (leafOf T 2) = u 2 := hmem 2
      have hσ3 : σ (leafOf T 3) = u 3 := hmem 3
      have hne23 : σ (leafOf T 2) ≠ σ (leafOf T 3) := by
        rw [hσ2, hσ3]
        exact h23
      by_cases hf2 : σ (leafOf T 2) = σ f
      · by_cases hf3 : σ (leafOf T 3) = σ f
        · exfalso
          exact hne23 (hf2.trans hf3.symm)
        · exact treeJoint_eq_zero_of_neF T.V K T.G T.isTree e f hef c M hI σ
            (T.G.dist (leafOf T 3) f) (leafOf T 3) rfl h3F hf3
      · exact treeJoint_eq_zero_of_neF T.V K T.G T.isTree e f hef c M hI σ
          (T.G.dist (leafOf T 2) f) (leafOf T 2) rfl h2F hf2
  · have hσ0 : σ (leafOf T 0) = u 0 := hmem 0
    have hσ1 : σ (leafOf T 1) = u 1 := hmem 1
    have hne01 : σ (leafOf T 0) ≠ σ (leafOf T 1) := by
      rw [hσ0, hσ1]
      exact h01
    by_cases he0 : σ (leafOf T 0) = σ e
    · by_cases he1 : σ (leafOf T 1) = σ e
      · exfalso
        exact hne01 (he0.trans he1.symm)
      · exact treeJoint_eq_zero_of_neE T.V K T.G T.isTree e f hef c M hI σ
          (T.G.dist (leafOf T 1) e) (leafOf T 1) rfl h1E he1
    · exact treeJoint_eq_zero_of_neE T.V K T.G T.isTree e f hef c M hI σ
        (T.G.dist (leafOf T 0) e) (leafOf T 0) rfl h0E he0

private theorem leafDist_eq_mul_of_both_eq {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : Fin 4 → K) (h01 : u 0 = u 1) (h23 : u 2 = u 3) :
    leafDist T.G (leafOf T) e (fun _ => c) M u = c * c := by
  classical
  set a : K := u 0 with ha
  set b : K := u 2 with hb
  have ha1 : a = u 1 := h01
  have hb3 : b = u 3 := h23
  -- canonical state: a on E side, b on F side
  set σ₀ : T.V → K := fun w => if T.G.dist w e < T.G.dist w f then a else b with hσ₀
  have hσ₀_eq_a : ∀ w, T.G.dist w e < T.G.dist w f → σ₀ w = a := by
    intro w hw
    simp [hσ₀, hw]
  have hσ₀_eq_b : ∀ w, T.G.dist w f < T.G.dist w e → σ₀ w = b := by
    intro w hw
    have hn : ¬ T.G.dist w e < T.G.dist w f := by omega
    simp [hσ₀, hn]
  have hP : ∀ x, σ₀ (leafOf T x) = u x := by
    intro x
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · exact hσ₀_eq_a _ h0E
    · rw [hσ₀_eq_a _ h1E]
      exact ha1
    · exact hσ₀_eq_b _ h2F
    · rw [hσ₀_eq_b _ h3F]
      exact hb3
  have hσ₀_val : treeJoint T.G e (fun _ => c) M σ₀ = c * c := by
    apply treeJoint_pattern T.V K T.G T.isTree e f hef c M hJ hI a b σ₀
    intro w
    exact ⟨fun hw => hσ₀_eq_a w hw, fun hw => hσ₀_eq_b w hw⟩
  simp only [leafDist]
  rw [← hσ₀_val]
  apply Finset.sum_eq_single σ₀
  · intro σ hmem hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    by_cases hE : ∀ w, T.G.dist w e < T.G.dist w f → σ w = σ e
    · by_cases hF : ∀ w, T.G.dist w f < T.G.dist w e → σ w = σ f
      · exfalso
        apply hne
        funext w
        have hσe : σ e = a := by
          have h1 := hE (leafOf T 0) h0E
          have h2 := hmem 0
          rw [h2] at h1
          exact h1.symm
        have hσf : σ f = b := by
          have h1 := hF (leafOf T 2) h2F
          have h2 := hmem 2
          rw [h2] at h1
          exact h1.symm
        have hside : T.G.dist w e < T.G.dist w f ∨ T.G.dist w f < T.G.dist w e := by
          have hne' : T.G.dist w e ≠ T.G.dist w f := T.isTree.dist_ne_of_adj w hef
          exact lt_or_gt_of_ne hne'
        rcases hside with hwE | hwF
        · rw [hE w hwE, hσe]
          exact (hσ₀_eq_a w hwE).symm
        · rw [hF w hwF, hσf]
          exact (hσ₀_eq_b w hwF).symm
      · push Not at hF
        obtain ⟨w, hwF, hwne⟩ := hF
        exact treeJoint_eq_zero_of_neF T.V K T.G T.isTree e f hef c M hI σ
          (T.G.dist w f) w rfl hwF hwne
    · push Not at hE
      obtain ⟨w, hwE, hwne⟩ := hE
      exact treeJoint_eq_zero_of_neE T.V K T.G T.isTree e f hef c M hI σ
        (T.G.dist w e) w rfl hwE hwne
  · intro hcon
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcon
    exact False.elim (hcon hP)

private theorem leafDist_pattern {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : Fin 4 → K) :
    leafDist T.G (leafOf T) e (fun _ => c) M u =
      if u 0 = u 1 ∧ u 2 = u 3 then c * c else 0 := by
  by_cases h : u 0 = u 1 ∧ u 2 = u 3
  · rw [ite_eq_left h]
    exact leafDist_eq_mul_of_both_eq T e f hef h0E h1E h2F h3F c M hJ hI u h.1 h.2
  · rw [ite_eq_right h]
    exact leafDist_eq_zero_of_not_both_eq T e f hef h0E h1E h2F h3F c M hI u h

private noncomputable def equivRowCol02 {K : Type} :
    (({x // x ∈ ({0, 2} : Finset (Fin 4))} → K) ≃
      (({x // x ∉ ({0, 2} : Finset (Fin 4))} → K))) where
  toFun := fun u ⟨x, hx⟩ =>
    if h1 : x = 1 then u ⟨0, by decide⟩
    else if h3 : x = 3 then u ⟨2, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact hx (by decide)
      · exact h1 rfl
      · exact hx (by decide)
      · exact h3 rfl)
  invFun := fun v ⟨x, hx⟩ =>
    if h0 : x = 0 then v ⟨1, by decide⟩
    else if h2 : x = 2 then v ⟨3, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact h0 rfl
      · exact (by decide : (1 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx
      · exact h2 rfl
      · exact (by decide : (3 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx)
  left_inv := fun u => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · show (if h0 : (0 : Fin 4) = 0 then _ else _) = u ⟨0, hx⟩
      simp
    · exact False.elim ((by decide : (1 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx)
    · show (if h0 : (2 : Fin 4) = 0 then _ else _) = u ⟨2, hx⟩
      have hne : (2 : Fin 4) ≠ 0 := by decide
      simp [hne]
    · exact False.elim ((by decide : (3 : Fin 4) ∉ ({0, 2} : Finset (Fin 4))) hx)
  right_inv := fun v => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · exact False.elim (hx (by decide))
    · show (if h1 : (1 : Fin 4) = 1 then _ else _) = v ⟨1, hx⟩
      simp
    · exact False.elim (hx (by decide))
    · show (if h1 : (3 : Fin 4) = 1 then _ else _) = v ⟨3, hx⟩
      have hne : (3 : Fin 4) ≠ 1 := by decide
      simp [hne]

private noncomputable def equivRowCol03 {K : Type} :
    (({x // x ∈ ({0, 3} : Finset (Fin 4))} → K) ≃
      (({x // x ∉ ({0, 3} : Finset (Fin 4))} → K))) where
  toFun := fun u ⟨x, hx⟩ =>
    if h1 : x = 1 then u ⟨0, by decide⟩
    else if h2 : x = 2 then u ⟨3, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact hx (by decide)
      · exact h1 rfl
      · exact h2 rfl
      · exact hx (by decide))
  invFun := fun v ⟨x, hx⟩ =>
    if h0 : x = 0 then v ⟨1, by decide⟩
    else if h3 : x = 3 then v ⟨2, by decide⟩
    else False.elim (by
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact h0 rfl
      · exact (by decide : (1 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx
      · exact (by decide : (2 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx
      · exact h3 rfl)
  left_inv := fun u => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · show (if h0 : (0 : Fin 4) = 0 then _ else _) = u ⟨0, hx⟩
      simp
    · exact False.elim ((by decide : (1 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx)
    · exact False.elim ((by decide : (2 : Fin 4) ∉ ({0, 3} : Finset (Fin 4))) hx)
    · show (if h0 : (3 : Fin 4) = 0 then _ else _) = u ⟨3, hx⟩
      have hne : (3 : Fin 4) ≠ 0 := by decide
      simp [hne]
  right_inv := fun v => by
    funext ⟨x, hx⟩
    rcases fin4_cases x with rfl | rfl | rfl | rfl
    · exact False.elim (hx (by decide))
    · show (if h1 : (1 : Fin 4) = 1 then _ else _) = v ⟨1, hx⟩
      simp
    · show (if h1 : (2 : Fin 4) = 1 then _ else _) = v ⟨2, hx⟩
      have hne : (2 : Fin 4) ≠ 1 := by decide
      simp [hne]
    · exact False.elim (hx (by decide))

private theorem flatten_eq_of_phi02 {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : ({x // x ∈ ({0, 2} : Finset (Fin 4))} → K))
    (v : ({x // x ∉ ({0, 2} : Finset (Fin 4))} → K)) :
    (flatten ({0, 2} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      if equivRowCol02 (K := K) u = v then c * c else 0 := by
  classical
  set w : Fin 4 → K :=
    fun x => if h : x ∈ ({0, 2} : Finset (Fin 4)) then u ⟨x, h⟩ else v ⟨x, h⟩ with hw
  have hflat : (flatten ({0, 2} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      leafDist T.G (leafOf T) e (fun _ => c) M w := rfl
  rw [hflat]
  rw [leafDist_pattern T e f hef h0E h1E h2F h3F c M hJ hI w]
  have h0mem : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have h2mem : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by decide
  have h1nmem : (1 : Fin 4) ∉ ({0, 2} : Finset (Fin 4)) := by decide
  have h3nmem : (3 : Fin 4) ∉ ({0, 2} : Finset (Fin 4)) := by decide
  have hw0 : w 0 = u ⟨0, h0mem⟩ := rfl
  have hw1 : w 1 = v ⟨1, h1nmem⟩ := rfl
  have hw2 : w 2 = u ⟨2, h2mem⟩ := rfl
  have hw3 : w 3 = v ⟨3, h3nmem⟩ := rfl
  have e1 : (equivRowCol02 (K := K) u) ⟨1, h1nmem⟩ = u ⟨0, h0mem⟩ := rfl
  have e3 : (equivRowCol02 (K := K) u) ⟨3, h3nmem⟩ = u ⟨2, h2mem⟩ := rfl
  have hiff : (w 0 = w 1 ∧ w 2 = w 3) ↔ equivRowCol02 (K := K) u = v := by
    constructor
    · intro ⟨h01, h23⟩
      rw [hw0, hw1] at h01
      rw [hw2, hw3] at h23
      have f1 : (equivRowCol02 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ := e1.trans h01
      have f3 : (equivRowCol02 (K := K) u) ⟨3, h3nmem⟩ = v ⟨3, h3nmem⟩ := e3.trans h23
      funext ⟨x, hx⟩
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact False.elim (hx (by decide))
      · exact f1
      · exact False.elim (hx (by decide))
      · exact f3
    · intro hφ
      have h1 : (equivRowCol02 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ :=
        congrFun hφ ⟨1, h1nmem⟩
      have h3 : (equivRowCol02 (K := K) u) ⟨3, h3nmem⟩ = v ⟨3, h3nmem⟩ :=
        congrFun hφ ⟨3, h3nmem⟩
      rw [e1] at h1
      rw [e3] at h3
      rw [hw0, hw1, hw2, hw3]
      exact ⟨h1, h3⟩
  by_cases hφ : equivRowCol02 (K := K) u = v
  · have hP : w 0 = w 1 ∧ w 2 = w 3 := hiff.mpr hφ
    rw [ite_eq_left hP, ite_eq_left hφ]
  · have hP : ¬(w 0 = w 1 ∧ w 2 = w 3) := fun h => hφ (hiff.mp h)
    rw [ite_eq_right hP, ite_eq_right hφ]

private theorem flatten_eq_of_phi03 {K : Type} [Fintype K] [DecidableEq K]
    (T : UnrootedBinaryTree (Fin 4)) (e f : T.V) (hef : T.G.Adj e f)
    (h0E : T.G.dist (leafOf T 0) e < T.G.dist (leafOf T 0) f)
    (h1E : T.G.dist (leafOf T 1) e < T.G.dist (leafOf T 1) f)
    (h2F : T.G.dist (leafOf T 2) f < T.G.dist (leafOf T 2) e)
    (h3F : T.G.dist (leafOf T 3) f < T.G.dist (leafOf T 3) e)
    (c : ℂ) (M : T.V → T.V → Matrix K K ℂ)
    (hJ : M e f = fun _ _ => c)
    (hI : ∀ a b, ¬(a = e ∧ b = f) → M a b = 1)
    (u : ({x // x ∈ ({0, 3} : Finset (Fin 4))} → K))
    (v : ({x // x ∉ ({0, 3} : Finset (Fin 4))} → K)) :
    (flatten ({0, 3} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      if equivRowCol03 (K := K) u = v then c * c else 0 := by
  classical
  set w : Fin 4 → K :=
    fun x => if h : x ∈ ({0, 3} : Finset (Fin 4)) then u ⟨x, h⟩ else v ⟨x, h⟩ with hw
  have hflat : (flatten ({0, 3} : Finset (Fin 4)) (leafDist T.G (leafOf T) e (fun _ => c) M)) u v =
      leafDist T.G (leafOf T) e (fun _ => c) M w := rfl
  rw [hflat]
  rw [leafDist_pattern T e f hef h0E h1E h2F h3F c M hJ hI w]
  have h0mem : (0 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by decide
  have h3mem : (3 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by decide
  have h1nmem : (1 : Fin 4) ∉ ({0, 3} : Finset (Fin 4)) := by decide
  have h2nmem : (2 : Fin 4) ∉ ({0, 3} : Finset (Fin 4)) := by decide
  have hw0 : w 0 = u ⟨0, h0mem⟩ := rfl
  have hw1 : w 1 = v ⟨1, h1nmem⟩ := rfl
  have hw2 : w 2 = v ⟨2, h2nmem⟩ := rfl
  have hw3 : w 3 = u ⟨3, h3mem⟩ := rfl
  have e1 : (equivRowCol03 (K := K) u) ⟨1, h1nmem⟩ = u ⟨0, h0mem⟩ := rfl
  have e2 : (equivRowCol03 (K := K) u) ⟨2, h2nmem⟩ = u ⟨3, h3mem⟩ := rfl
  have hiff : (w 0 = w 1 ∧ w 2 = w 3) ↔ equivRowCol03 (K := K) u = v := by
    constructor
    · intro ⟨h01, h23⟩
      rw [hw0, hw1] at h01
      rw [hw2, hw3] at h23
      have f1 : (equivRowCol03 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ := e1.trans h01
      have f2 : (equivRowCol03 (K := K) u) ⟨2, h2nmem⟩ = v ⟨2, h2nmem⟩ := by
        rw [e2]
        exact h23.symm.trans rfl
      funext ⟨x, hx⟩
      rcases fin4_cases x with rfl | rfl | rfl | rfl
      · exact False.elim (hx (by decide))
      · exact f1
      · exact f2
      · exact False.elim (hx (by decide))
    · intro hφ
      have h1 : (equivRowCol03 (K := K) u) ⟨1, h1nmem⟩ = v ⟨1, h1nmem⟩ :=
        congrFun hφ ⟨1, h1nmem⟩
      have h2 : (equivRowCol03 (K := K) u) ⟨2, h2nmem⟩ = v ⟨2, h2nmem⟩ :=
        congrFun hφ ⟨2, h2nmem⟩
      rw [e1] at h1
      rw [e2] at h2
      rw [hw0, hw1, hw2, hw3]
      exact ⟨h1, h2.symm⟩
  by_cases hφ : equivRowCol03 (K := K) u = v
  · have hP : w 0 = w 1 ∧ w 2 = w 3 := hiff.mpr hφ
    rw [ite_eq_left hP, ite_eq_left hφ]
  · have hP : ¬(w 0 = w 1 ∧ w 2 = w 3) := fun h => hφ (hiff.mp h)
    rw [ite_eq_right hP, ite_eq_right hφ]

private theorem card_lt_card_row {K : Type} [Fintype K] [DecidableEq K]
    (hK : 2 ≤ Fintype.card K) (A : Finset (Fin 4)) (hAcard : A.card = 2) :
    Fintype.card K < Fintype.card ({x // x ∈ A} → K) := by
  have hsub : Fintype.card {x // x ∈ A} = 2 := by
    rw [Fintype.card_coe]
    exact hAcard
  have hrow : Fintype.card ({x // x ∈ A} → K) = (Fintype.card K) ^ 2 := by
    rw [Fintype.card_fun, hsub]
  rw [hrow]
  have hpos : 0 < Fintype.card K := by omega
  have h1 : 1 < Fintype.card K := by omega
  calc Fintype.card K = Fintype.card K * 1 := (mul_one _).symm
    _ < Fintype.card K * Fintype.card K :=
        (Nat.mul_lt_mul_left hpos).mpr h1
    _ = (Fintype.card K) ^ 2 := (pow_two _).symm

end Helpers

/-- **Non-edge flattenings of four-taxon trees have rank larger than `κ` for generic parameters**
(Allman and Rhodes 2006, Theorem 2 with `λ = κ`): for an unrooted binary phylogenetic tree `T` on
four taxa displaying the quartet `01|23`, and each of the two splits `{0, 2} | {1, 3}` and
`{0, 3} | {1, 2}` that are not edges of `T`, some complex stochastic parameters give a leaf
distribution whose flattening along that split has rank larger than `κ`, the number of states
(`2 ≤ κ`). Since the rank-at-most-`κ` locus is algebraic in the parameters, it is then a proper
algebraic subset of the parameter space, and the tree is identified from generic parameters by
the vanishing of the `(κ + 1)`-minors of its own flattening.

Source: Allman and Rhodes (2006), Theorem 2. -/
public theorem exists_card_lt_rank_flatten_nonEdge {K : Type} [Fintype K] [DecidableEq K]
    (hK : 2 ≤ Fintype.card K)
    (T : UnrootedBinaryTree (Fin 4)) (hT : DisplaysQuartet T 0 1 2 3)
    (A : Finset (Fin 4)) (hA : A = {0, 2} ∨ A = {0, 3}) :
    ∃ (r : T.V) (π : K → ℂ) (M : T.V → T.V → Matrix K K ℂ), IsComplexStochastic T.G r π M ∧
      Fintype.card K < (flatten A (leafDist T.G (leafOf T) r π M)).rank := by
  classical
  have hpos : 0 < Fintype.card K := by omega
  obtain ⟨e, f, hef, h0E, h1E, h2F, h3F⟩ := exists_edge_of_quartet T hT
  set c : ℂ := (Fintype.card K : ℂ)⁻¹ with hc
  have hcard_ne : (Fintype.card K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hpos)
  have hc_ne : c ≠ 0 := inv_ne_zero hcard_ne
  have hd_ne : c * c ≠ 0 := mul_ne_zero hc_ne hc_ne
  have hsum_c : ∑ _ : K, c = 1 := by
    have h1 : ∑ _ : K, c = (Fintype.card K : ℂ) * c := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, hc]
    exact mul_inv_cancel₀ hcard_ne
  set M : T.V → T.V → Matrix K K ℂ :=
    fun a b => if _ : a = e ∧ b = f then (fun _ _ => c) else 1 with hM
  have hJ : M e f = (fun _ _ => c) := by
    simp [hM]
    rfl
  have hI : ∀ a b : T.V, ¬(a = e ∧ b = f) → M a b = 1 := by
    intro a b h
    simp [hM, h]
  refine ⟨e, fun _ => c, M, ?_, ?_⟩
  · constructor
    · simpa using hsum_c
    · intro a b _ i
      by_cases h : a = e ∧ b = f
      · simp [hM, h]
        simpa using hsum_c
      · simp [hM, h]
        simp [Matrix.one_apply]
  · rcases hA with rfl | rfl
    · have hM : ∀ p q,
          (flatten ({0, 2} : Finset (Fin 4))
            (leafDist T.G (leafOf T) e (fun _ => c) M)) p q =
            if equivRowCol02 (K := K) p = q then c * c else 0 := by
        intro p q
        exact flatten_eq_of_phi02 T e f hef h0E h1E h2F h3F c M hJ hI p q
      have hrank : (flatten ({0, 2} : Finset (Fin 4))
          (leafDist T.G (leafOf T) e (fun _ => c) M)).rank =
          Fintype.card ({x // x ∈ ({0, 2} : Finset (Fin 4))} → K) :=
        rank_of_perm _ _ _ _ _ hd_ne hM
      rw [hrank]
      have hcard : (({0, 2} : Finset (Fin 4))).card = 2 := by decide
      exact card_lt_card_row hK _ hcard
    · have hM : ∀ p q,
          (flatten ({0, 3} : Finset (Fin 4))
            (leafDist T.G (leafOf T) e (fun _ => c) M)) p q =
            if equivRowCol03 (K := K) p = q then c * c else 0 := by
        intro p q
        exact flatten_eq_of_phi03 T e f hef h0E h1E h2F h3F c M hJ hI p q
      have hrank : (flatten ({0, 3} : Finset (Fin 4))
          (leafDist T.G (leafOf T) e (fun _ => c) M)).rank =
          Fintype.card ({x // x ∈ ({0, 3} : Finset (Fin 4))} → K) :=
        rank_of_perm _ _ _ _ _ hd_ne hM
      rw [hrank]
      have hcard : (({0, 3} : Finset (Fin 4))).card = 2 := by decide
      exact card_lt_card_row hK _ hcard

end WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted
