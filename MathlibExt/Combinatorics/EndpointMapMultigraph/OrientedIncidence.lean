/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import MathlibExt.Combinatorics.EndpointMapMultigraph

@[expose] public section

/-!
# Oriented incidence matrices of finite multigraphs

For a finite multigraph given by endpoint maps `end₁ end₂ : E → V` (see
`MathlibExt.Combinatorics.EndpointMapMultigraph`), `orientedIncidence end₁ end₂ : Matrix V E ℝ`
has column `e` equal to `+1` at `end₁ e` and `-1` at `end₂ e`. Parallel edges are distinct
values of `E` and so give distinct, equal columns. Connectivity is that of
`underlyingGraph end₁ end₂`, the simple graph joining distinct endpoints of some edge; its
reachability is reachability through edges of the multigraph
(`underlyingGraph_reachable_iff`).

For a loopless finite multigraph over `ℝ`:

* `vecMul_orientedIncidence_eq_zero_iff`: the left kernel consists of the vectors constant on each
  connected component;
* `mem_range_orientedIncidence_iff`: the range consists of the vectors whose sum over each
  connected component vanishes;
* `rank_orientedIncidence_add_card_connectedComponent`: rank plus the number of connected
  components equals the number of vertices (with `rank_orientedIncidence` as a subtraction form);
* `surjective_mulVec_fromCols_boundaryColumns_iff`: adjoining free boundary columns `±e_{b j}`
  gives a surjective map iff every connected component contains some anchor `b j`.

These are standard facts of algebraic graph theory. The loopless hypothesis fixes the scope: the
statements do not cover loops, edge weights or other column constraints. This file does not
state any Laplacian identity `B Bᵀ = L`; with parallel edges or boundary columns such an identity
needs multiplicities and a boundary diagonal.
-/

namespace EndpointMapMultigraph

open Matrix

section Graph

variable {V E : Type*} (end₁ end₂ : E → V)

/-- **Underlying simple graph of a multigraph.** For endpoint maps `end₁ end₂ : E → V`, the
simple graph on `V` in which distinct vertices are adjacent when some edge joins them. It forgets
multiplicities and loops and is used only for connectivity. -/
def underlyingGraph : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, end₁ e = u ∧ end₂ e = v

/-- **Adjacency in the underlying graph.** Vertices `u` and `v` are adjacent in
`underlyingGraph end₁ end₂` if and only if they are distinct and some edge joins them, in either
orientation. -/
theorem underlyingGraph_adj {u v : V} :
    (underlyingGraph end₁ end₂).Adj u v ↔
      u ≠ v ∧ ∃ e, (end₁ e = u ∧ end₂ e = v) ∨ (end₁ e = v ∧ end₂ e = u) := by
  simp only [underlyingGraph, SimpleGraph.fromRel_adj, exists_or]

/-- **An edge joins its endpoints in the underlying graph.** An edge whose endpoints are distinct
makes them adjacent in `underlyingGraph end₁ end₂`. -/
theorem underlyingGraph_adj_of_ne {e : E} (h : end₁ e ≠ end₂ e) :
    (underlyingGraph end₁ end₂).Adj (end₁ e) (end₂ e) :=
  (underlyingGraph_adj end₁ end₂).2 ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩

/-- **Reachability in the underlying graph.** Reachability in `underlyingGraph end₁ end₂` is
reachability through edges of the multigraph, `Relation.ReflTransGen` of `AdjacentUsing` on all
edges. -/
theorem underlyingGraph_reachable_iff [Fintype E] {u v : V} :
    (underlyingGraph end₁ end₂).Reachable u v ↔
      Relation.ReflTransGen (AdjacentUsing end₁ end₂ Finset.univ) u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih =>
      obtain ⟨-, e, he⟩ := (underlyingGraph_adj end₁ end₂).1 hbc
      exact ih.tail (by simpa [AdjacentUsing] using ⟨e, he⟩)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih =>
      rename_i b c _
      by_cases hb : b = c
      · exact hb ▸ ih
      · refine ih.tail ((underlyingGraph_adj end₁ end₂).2 ⟨hb, ?_⟩)
        simpa [AdjacentUsing] using hbc

end Graph

section Incidence

variable {V E : Type*} [DecidableEq V] (end₁ end₂ : E → V)

/-- **Oriented incidence matrix of a multigraph.** The real `V × E` matrix of the multigraph
with endpoint maps `end₁ end₂`: column `e` is `+1` at `end₁ e` and `-1` at `end₂ e`. Distinct
edges, including parallel ones, give distinct columns. -/
def orientedIncidence : Matrix V E ℝ :=
  Matrix.of fun v e => (if end₁ e = v then 1 else 0) - if end₂ e = v then 1 else 0

/-- **Entries of the oriented incidence matrix.** Entry `(v, e)` is `[end₁ e = v] - [end₂ e = v]`.
-/
theorem orientedIncidence_apply (v : V) (e : E) :
    orientedIncidence end₁ end₂ v e =
      (if end₁ e = v then 1 else 0) - if end₂ e = v then 1 else 0 := rfl

/-- **First-endpoint entry.** If the endpoints of `e` are distinct, the entry of
`orientedIncidence end₁ end₂` at `(end₁ e, e)` is `1`. -/
theorem orientedIncidence_apply_end₁ {e : E} (h : end₁ e ≠ end₂ e) :
    orientedIncidence end₁ end₂ (end₁ e) e = 1 := by
  simp [orientedIncidence_apply, Ne.symm h]

/-- **Second-endpoint entry.** If the endpoints of `e` are distinct, the entry of
`orientedIncidence end₁ end₂` at `(end₂ e, e)` is `-1`. -/
theorem orientedIncidence_apply_end₂ {e : E} (h : end₁ e ≠ end₂ e) :
    orientedIncidence end₁ end₂ (end₂ e) e = -1 := by
  simp [orientedIncidence_apply, h]

/-- **Entries away from the endpoints.** The column of `e` vanishes at every vertex other than
`end₁ e` and `end₂ e`. -/
theorem orientedIncidence_apply_of_ne {v : V} {e : E} (h₁ : end₁ e ≠ v) (h₂ : end₂ e ≠ v) :
    orientedIncidence end₁ end₂ v e = 0 := by
  simp [orientedIncidence_apply, h₁, h₂]

/-- **Row vector times the oriented incidence matrix.** Entry `e` of
`x ᵥ* orientedIncidence end₁ end₂` is the difference `x (end₁ e) - x (end₂ e)` across `e`. -/
theorem vecMul_orientedIncidence_apply [Fintype V] (x : V → ℝ) (e : E) :
    (x ᵥ* orientedIncidence end₁ end₂) e = x (end₁ e) - x (end₂ e) := by
  simp [Matrix.vecMul, dotProduct, orientedIncidence_apply, mul_sub, Finset.sum_sub_distrib]

/-- **Left kernel of the oriented incidence matrix.** For a loopless multigraph with finitely
many vertices, a real vector `x` satisfies `x ᵥ* orientedIncidence end₁ end₂ = 0` if and only if
`x` is constant on each connected component of `underlyingGraph end₁ end₂`. -/
theorem vecMul_orientedIncidence_eq_zero_iff [Fintype V] (hloop : ∀ e, end₁ e ≠ end₂ e)
    (x : V → ℝ) :
    x ᵥ* orientedIncidence end₁ end₂ = 0 ↔
      ∀ u v, (underlyingGraph end₁ end₂).Reachable u v → x u = x v := by
  constructor
  · intro hx u v huv
    rw [SimpleGraph.reachable_iff_reflTransGen] at huv
    induction huv with
    | refl => rfl
    | tail _ hbc ih =>
      rename_i b c _
      obtain ⟨-, e, he⟩ := (underlyingGraph_adj end₁ end₂).1 hbc
      have hxe := congrFun hx e
      rw [vecMul_orientedIncidence_apply, Pi.zero_apply, sub_eq_zero] at hxe
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans hxe
      · exact ih.trans hxe.symm
  · intro hx
    funext e
    rw [vecMul_orientedIncidence_apply, Pi.zero_apply, sub_eq_zero]
    exact hx _ _ (underlyingGraph_adj_of_ne end₁ end₂ (hloop e)).reachable

/-- For a finite real matrix, `mulVec` is surjective iff the left kernel is trivial. -/
private theorem mulVec_surjective_iff_vecMul_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    Function.Surjective A.mulVec ↔ ∀ x : m → ℝ, x ᵥ* A = 0 → x = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  change Aᵀ.rank + _ = _ at hrn
  rw [rank_transpose] at hrn
  rw [mulVec_surjective_iff_rank_eq_card]
  have hker : (∀ x : m → ℝ, x ᵥ* A = 0 → x = 0) ↔
      LinearMap.ker Aᵀ.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    simp
  rw [hker, ← Submodule.finrank_eq_zero]
  omega

/-- **Incidence rank plus number of components.** For a loopless finite multigraph, the rank of
its real oriented incidence matrix plus the number of connected components of
`underlyingGraph end₁ end₂` equals the number of vertices. -/
theorem rank_orientedIncidence_add_card_connectedComponent [Fintype V] [Fintype E]
    (hloop : ∀ e, end₁ e ≠ end₂ e) :
    (orientedIncidence end₁ end₂).rank +
        Nat.card (underlyingGraph end₁ end₂).ConnectedComponent = Fintype.card V := by
  classical
  set G := underlyingGraph end₁ end₂
  let B := orientedIncidence end₁ end₂
  have hrn := LinearMap.finrank_range_add_finrank_ker Bᵀ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  change Bᵀ.rank + _ = _ at hrn
  rw [rank_transpose] at hrn
  have hker : LinearMap.ker Bᵀ.mulVecLin =
      LinearMap.range (LinearMap.funLeft ℝ ℝ G.connectedComponentMk) := by
    ext x
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_transpose,
      vecMul_orientedIncidence_eq_zero_iff end₁ end₂ hloop, LinearMap.mem_range]
    constructor
    · intro hx
      refine ⟨fun c => x c.out, funext fun v => ?_⟩
      simp only [LinearMap.funLeft_apply]
      exact (hx _ _ (SimpleGraph.ConnectedComponent.exact (Quot.out_eq _).symm)).symm
    · rintro ⟨f, rfl⟩ u v huv
      exact congrArg f (SimpleGraph.ConnectedComponent.sound huv)
  have hinj := LinearMap.funLeft_injective_of_surjective ℝ ℝ G.connectedComponentMk
    fun c => c.ind fun v => ⟨v, rfl⟩
  have := Fintype.ofFinite G.ConnectedComponent
  rw [hker, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at hrn
  rw [Nat.card_eq_fintype_card]
  exact hrn

/-- **Rank of the oriented incidence matrix.** For a loopless finite multigraph, the rank of its
real oriented incidence matrix is the number of vertices minus the number of connected components
of `underlyingGraph end₁ end₂`. -/
theorem rank_orientedIncidence [Fintype V] [Fintype E] (hloop : ∀ e, end₁ e ≠ end₂ e) :
    (orientedIncidence end₁ end₂).rank =
      Fintype.card V - Nat.card (underlyingGraph end₁ end₂).ConnectedComponent := by
  have := rank_orientedIncidence_add_card_connectedComponent end₁ end₂ hloop
  omega

open Classical in
/-- **Range of the oriented incidence matrix.** For a loopless finite multigraph, a real vector
`r` lies in the range of `orientedIncidence end₁ end₂` if and only if its sum over the vertices of
every connected component of `underlyingGraph end₁ end₂` vanishes. -/
theorem mem_range_orientedIncidence_iff [Fintype V] [Fintype E]
    (hloop : ∀ e, end₁ e ≠ end₂ e) (r : V → ℝ) :
    r ∈ LinearMap.range (orientedIncidence end₁ end₂).mulVecLin ↔
      ∀ c : (underlyingGraph end₁ end₂).ConnectedComponent,
        ∑ v with (underlyingGraph end₁ end₂).connectedComponentMk v = c, r v = 0 := by
  set G := underlyingGraph end₁ end₂
  let B := orientedIncidence end₁ end₂
  let S : (V → ℝ) →ₗ[ℝ] (G.ConnectedComponent → ℝ) :=
    { toFun := fun r c => ∑ v with G.connectedComponentMk v = c, r v
      map_add' := fun r s => funext fun c => by simp [Finset.sum_add_distrib]
      map_smul' := fun a r => funext fun c => by simp [Finset.mul_sum] }
  have hS : ∀ r c, S r c = ∑ v with G.connectedComponentMk v = c, r v := fun _ _ => rfl
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker S := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    funext c
    have hcol : ∀ e, ∑ v with G.connectedComponentMk v = c, B v e = 0 := by
      intro e
      have hmk : G.connectedComponentMk (end₁ e) = G.connectedComponentMk (end₂ e) :=
        SimpleGraph.ConnectedComponent.sound
          (underlyingGraph_adj_of_ne end₁ end₂ (hloop e)).reachable
      simp [B, orientedIncidence_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, hmk]
    simp only [hS, mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [← Finset.sum_mul, hcol e, zero_mul]
  have hsurj : Function.Surjective S := by
    intro f
    refine ⟨fun v => if v = (G.connectedComponentMk v).out then f (G.connectedComponentMk v)
      else 0, funext fun c => ?_⟩
    rw [hS]
    rw [Finset.sum_congr rfl fun v hv => by rw [(Finset.mem_filter.1 hv).2]]
    rw [Finset.sum_ite_eq']
    have hc : G.connectedComponentMk c.out = c := Quot.out_eq c
    simp [hc]
  have := Fintype.ofFinite G.ConnectedComponent
  have hS_rn := LinearMap.finrank_range_add_finrank_ker S
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at hS_rn
  have hB := rank_orientedIncidence_add_card_connectedComponent end₁ end₂ hloop
  change Nat.card (underlyingGraph end₁ end₂).ConnectedComponent + _ = _ at hS_rn
  have heq : LinearMap.range B.mulVecLin = LinearMap.ker S := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    change (orientedIncidence end₁ end₂).rank = _
    omega
  change r ∈ LinearMap.range B.mulVecLin ↔ _
  rw [heq, LinearMap.mem_ker, funext_iff]
  rfl

/-- **Boundary columns.** The real `V × F` matrix whose column `j` is `σ j` times the standard
basis vector at the anchor `b j`. -/
def boundaryColumns {F : Type*} (b : F → V) (σ : F → ℝ) : Matrix V F ℝ :=
  Matrix.of fun v j => if b j = v then σ j else 0

/-- **Entries of the boundary-column matrix.** Entry `(v, j)` is `σ j` if `b j = v` and `0`
otherwise. -/
theorem boundaryColumns_apply {F : Type*} (b : F → V) (σ : F → ℝ) (v : V) (j : F) :
    boundaryColumns b σ v j = if b j = v then σ j else 0 := rfl

/-- **Row vector times the boundary columns.** Entry `j` of `x ᵥ* boundaryColumns b σ` is
`x (b j) * σ j`. -/
theorem vecMul_boundaryColumns_apply [Fintype V] {F : Type*} (b : F → V) (σ : F → ℝ)
    (x : V → ℝ) (j : F) : (x ᵥ* boundaryColumns b σ) j = x (b j) * σ j := by
  simp [Matrix.vecMul, dotProduct, boundaryColumns_apply]

/-- **Surjectivity with free boundary columns.** For a loopless finite multigraph and finitely
many boundary columns `σ j • e_{b j}` with every `σ j = ±1`, the real matrix obtained by adjoining
them to the oriented incidence matrix is surjective if and only if every connected component of
`underlyingGraph end₁ end₂` contains the anchor `b j` of some boundary column. The components are
those of the interior edges alone. -/
theorem surjective_mulVec_fromCols_boundaryColumns_iff [Finite V] [Fintype E] {F : Type*}
    [Fintype F] (hloop : ∀ e, end₁ e ≠ end₂ e) (b : F → V) (σ : F → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    Function.Surjective
        ((orientedIncidence end₁ end₂).fromCols (boundaryColumns b σ)).mulVec ↔
      ∀ c : (underlyingGraph end₁ end₂).ConnectedComponent,
        ∃ j, (underlyingGraph end₁ end₂).connectedComponentMk (b j) = c := by
  classical
  cases nonempty_fintype V
  set G := underlyingGraph end₁ end₂
  have hσ0 : ∀ j, σ j ≠ 0 := fun j => by rcases hσ j with h | h <;> simp [h]
  have hzero : ∀ x : V → ℝ,
      x ᵥ* (orientedIncidence end₁ end₂).fromCols (boundaryColumns b σ) = 0 ↔
        (∀ u v, G.Reachable u v → x u = x v) ∧ ∀ j, x (b j) = 0 := by
    intro x
    rw [vecMul_fromCols, ← vecMul_orientedIncidence_eq_zero_iff end₁ end₂ hloop]
    constructor
    · intro h
      refine ⟨funext fun e => congrFun h (Sum.inl e), fun j => ?_⟩
      have := congrFun h (Sum.inr j)
      simp only [Sum.elim_inr, vecMul_boundaryColumns_apply, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_right (hσ0 j)
    · rintro ⟨h₁, h₂⟩
      funext i
      cases i with
      | inl e => simpa using congrFun h₁ e
      | inr j => simp [vecMul_boundaryColumns_apply, h₂ j]
  rw [mulVec_surjective_iff_vecMul_eq_zero]
  constructor
  · intro h c
    by_contra hc
    push Not at hc
    have hx := h (fun v => if G.connectedComponentMk v = c then 1 else 0)
      ((hzero _).2 ⟨fun u v huv => by simp [SimpleGraph.ConnectedComponent.sound huv],
        fun j => by simp [hc j]⟩)
    have hout : G.connectedComponentMk c.out = c := Quot.out_eq c
    simpa [hout] using congrFun hx c.out
  · intro h x hx
    obtain ⟨hconst, hb⟩ := (hzero x).1 hx
    funext v
    obtain ⟨j, hj⟩ := h (G.connectedComponentMk v)
    rw [Pi.zero_apply, hconst v (b j) (SimpleGraph.ConnectedComponent.exact hj.symm), hb j]

end Incidence

end EndpointMapMultigraph
