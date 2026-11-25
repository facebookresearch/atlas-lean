/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Relation

/-!
# Cut-rank and local complementation

The cut-rank `ρ_G(X)` of a vertex set `X` of a finite simple graph `G` is the rank, over the
two-element field, of the `X × (V ∖ X)` submatrix of the adjacency matrix. It is the
connectivity function behind rank-width (Oum and Seymour 2006).

Local complementation at a vertex `v` replaces the subgraph induced on the neighbourhood of
`v` by its complement. The fundamental observation of Oum (2005, Proposition 2.6) is that local
complementation does not change the cut-rank of any vertex set; hence locally equivalent graphs
have the same cut-rank function and the same rank-width.

## Main declarations

* `SimpleGraph.localComplement`: the graph `G * v`.
* `SimpleGraph.localComplement_localComplement`: `G * v * v = G`.
* `SimpleGraph.cutRank`: the cut-rank function over `ZMod 2`.
* `SimpleGraph.cutRank_compl`: `ρ_G(V ∖ X) = ρ_G(X)`.
* `SimpleGraph.cutRank_inter_add_cutRank_union_le`: cut-rank is submodular.
* `SimpleGraph.cutRank_localComplement`: `ρ_{G * v}(X) = ρ_G(X)`.
* `SimpleGraph.cutRank_top_le_one`: complete graphs have cut-rank at most one.
* `SimpleGraph.LocallyEquivalent`, `SimpleGraph.IsVertexMinor`.

## References

* S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100
  (author's revised preprint of 18 April 2005).
* S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory
  Ser. B 96 (2006) 514–528 (author's preprint of 20 October 2004).
* S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017)
  15–24, arXiv:1601.03800v2.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-! ## Local complementation -/

/-- **Local complementation.** For a simple graph `G` and a vertex `v`, the graph `G * v` has the
same vertices, and two distinct vertices `x, y` are adjacent in `G * v` exactly when either they
are adjacent in `G` or both are neighbours of `v` in `G`, but not both. Equivalently, the subgraph
induced on the neighbourhood of `v` is replaced by its complement (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Section 2:
`G * v = (V, E Δ {xy : xv, yv ∈ E, x ≠ y})`). -/
def localComplement (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.Adj x y ↔ ¬(G.Adj v x ∧ G.Adj v y))
  symm := ⟨fun x y h => ⟨h.1.symm, by
    rw [G.adj_comm y x, and_comm (a := G.Adj v y)]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable (G : SimpleGraph V)

/-- **Adjacency after local complementation.** Distinct vertices `x, y` are adjacent in `G * v`
exactly when `G.Adj x y` holds if and only if `x` and `y` are not both neighbours of `v`, that
is, when `G.Adj x y` differs from "`x` and `y` are both neighbours of `v`". -/
theorem localComplement_adj {v x y : V} :
    (G.localComplement v).Adj x y ↔ x ≠ y ∧ (G.Adj x y ↔ ¬(G.Adj v x ∧ G.Adj v y)) :=
  Iff.rfl

/-- **Local complementation keeps the neighbourhood of its vertex.** The neighbours of `v` in
`G * v` are exactly its neighbours in `G`. -/
theorem localComplement_adj_left {v x : V} :
    (G.localComplement v).Adj v x ↔ G.Adj v x := by
  have hvv : ¬G.Adj v v := G.loopless.irrefl v
  rw [localComplement_adj]
  constructor
  · rintro ⟨_, h⟩
    exact h.2 fun h' => hvv h'.1
  · intro h
    exact ⟨G.ne_of_adj h, iff_of_true h fun h' => hvv h'.1⟩

/-- **Local complementation is an involution.** `G * v * v = G` (Oum, *Rank-width and
vertex-minors*, 2005, Section 2; Oum, *Rank-width: algorithmic and structural results*,
arXiv:1601.03800v2, Section 4.1). -/
theorem localComplement_localComplement (v : V) :
    (G.localComplement v).localComplement v = G := by
  ext x y
  rw [localComplement_adj, localComplement_adj_left, localComplement_adj_left,
    localComplement_adj]
  constructor
  · rintro ⟨hne, h⟩
    tauto
  · intro h
    have hne := G.ne_of_adj h
    refine ⟨hne, ?_⟩
    tauto

/-! ## Cut-rank -/

section CutRank

variable [Fintype V]

open Classical in
/-- **Cut-rank function.** For a finite simple graph `G` and a vertex set `X`, `ρ_G(X)` is the rank
over the two-element field `ZMod 2` of the `X × (V ∖ X)` submatrix of the adjacency matrix of
`G`; its `(x, y)` entry is `1` exactly when `x` and `y` are adjacent. In particular
`ρ_G(∅) = ρ_G(V) = 0` (Oum and Seymour, *Approximating clique-width and branch-width*, J. Combin.
Theory Ser. B 96 (2006), Definition 6.1; Oum, arXiv:1601.03800v2, Section 2.1). -/
noncomputable def cutRank (X : Set V) : ℕ :=
  ((G.adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V)) (fun y : ↥Xᶜ => (y : V))).rank

/-- **Cut-rank is symmetric.** `ρ_G(V ∖ X) = ρ_G(X)` for every vertex set `X`, since the two
submatrices are transposes of each other (Oum, arXiv:1601.03800v2, inequality (1)). -/
theorem cutRank_compl (X : Set V) : G.cutRank Xᶜ = G.cutRank X := by
  classical
  unfold cutRank
  set A := (G.adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V)) (fun y : ↥Xᶜ => (y : V))
  let e : ↥(Xᶜᶜ) ≃ ↥X := Equiv.subtypeEquivRight (fun x => by simp)
  have key : (G.adjMatrix (ZMod 2)).submatrix (fun x : ↥Xᶜ => (x : V))
      (fun y : ↥(Xᶜᶜ) => (y : V)) = (Matrix.transpose A).submatrix (Equiv.refl _) e := by
    ext i j
    simp only [A, e, Matrix.submatrix_apply, Matrix.transpose_apply, adjMatrix_apply,
      Equiv.refl_apply, Equiv.subtypeEquivRight_apply_coe, G.adj_comm]
  rw [key]
  convert (Matrix.rank_submatrix (Matrix.transpose A) (Equiv.refl _) e).trans
    (Matrix.rank_transpose A) using 2

/-- Row vectors for which both the vector and its product with `A` vanish outside `X`. -/
private def cutKernel (A : Matrix V V (ZMod 2)) (X : Set V) :
    Submodule (ZMod 2) (V → ZMod 2) :=
  let S := Submodule.pi Xᶜ (fun _ => (⊥ : Submodule (ZMod 2) (ZMod 2)))
  S ⊓ S.comap A.vecMulLinear

private theorem mem_cutKernel {A : Matrix V V (ZMod 2)} {X : Set V} {v : V → ZMod 2} :
    v ∈ cutKernel A X ↔ (∀ i ∉ X, v i = 0) ∧ (∀ i ∉ X, A.vecMulLinear v i = 0) := by
  simp only [cutKernel, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_pi,
    Submodule.mem_bot, Set.mem_compl_iff]

open Classical in
/-- Restriction to `X` identifies the supported vectors with the left kernel of the cut matrix. -/
private theorem rank_cut_add_finrank_cutKernel (A : Matrix V V (ZMod 2)) (X : Set V) :
    (A.submatrix (fun i : X => (i : V)) (fun j : ↥Xᶜ => (j : V))).rank +
      Module.finrank (ZMod 2) (cutKernel A X) = X.ncard := by
  classical
  let B := A.submatrix (fun i : X => (i : V)) (fun j : ↥Xᶜ => (j : V))
  let restrict := LinearMap.funLeft (ZMod 2) (ZMod 2) (Subtype.val : X → V)
  have hvecMul (v : V → ZMod 2) (hv : ∀ j ∉ X, v j = 0) (i : ↥Xᶜ) :
      B.vecMulLinear (restrict v) i = A.vecMulLinear v i := by
    change ∑ j : X, v j * A j i = ∑ j : V, v j * A j i
    calc
      ∑ j : X, v j * A j i = ∑ j ∈ X.toFinset, v j * A j i :=
        (Finset.sum_subtype X.toFinset (fun _ => Set.mem_toFinset) (fun j => v j * A j i)).symm
      _ = ∑ j : V, v j * A j i :=
        Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
          rw [hv j (fun h => hj (Set.mem_toFinset.mpr h)), zero_mul]
  let f : cutKernel A X →ₗ[ZMod 2] B.vecMulLinear.ker :=
    (restrict.domRestrict _).codRestrict _ fun v => by
      rw [LinearMap.mem_ker]
      funext i
      exact (hvecMul v (mem_cutKernel.mp v.property).1 i).trans
        ((mem_cutKernel.mp v.property).2 i i.property)
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ X
      · exact congrArg (fun x : B.vecMulLinear.ker => x.val ⟨j, hj⟩) h
      · rw [(mem_cutKernel.mp v.property).1 j hj, (mem_cutKernel.mp w.property).1 j hj]
    · intro w
      let v (j : V) : ZMod 2 := if h : j ∈ X then w.val ⟨j, h⟩ else 0
      have hv (j : V) (hj : j ∉ X) : v j = 0 := dite_eq_right hj
      have hrestrict : restrict v = w.val := by
        funext j
        exact dite_eq_left j.property
      refine ⟨⟨v, mem_cutKernel.mpr ⟨hv, fun i hi => ?_⟩⟩, Subtype.ext hrestrict⟩
      rw [← hvecMul v hv ⟨i, hi⟩, hrestrict]
      exact congrFun (LinearMap.mem_ker.mp w.property) ⟨i, hi⟩
  have hnull := B.vecMulLinear.finrank_range_add_finrank_ker
  rw [range_vecMulLinear, ← Matrix.rank_eq_finrank_span_row,
    Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hnull
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  exact hnull

/-- **Cut-rank is submodular.** For every finite graph `G` and vertex sets `X, Y`,
`ρ_G(X ∩ Y) + ρ_G(X ∪ Y) ≤ ρ_G(X) + ρ_G(Y)` (Oum and Seymour, *Approximating clique-width and
branch-width*, J. Combin. Theory Ser. B 96 (2006), Corollary 6.2, second statement, from the
submodularity of ranks of submatrices, Proposition 6.1). -/
theorem cutRank_inter_add_cutRank_union_le (G : SimpleGraph V) (X Y : Set V) :
    G.cutRank (X ∩ Y) + G.cutRank (X ∪ Y) ≤ G.cutRank X + G.cutRank Y := by
  classical
  let A := G.adjMatrix (ZMod 2)
  have vanish_inter (v : V → ZMod 2) : (∀ i ∉ X ∩ Y, v i = 0) ↔
      (∀ i ∉ X, v i = 0) ∧ (∀ i ∉ Y, v i = 0) := by
    simp only [Set.mem_inter_iff, not_and_or, or_imp, forall_and]
  have hInter : cutKernel A (X ∩ Y) = cutKernel A X ⊓ cutKernel A Y := by
    ext v
    simp only [Submodule.mem_inf, mem_cutKernel, vanish_inter]
    tauto
  have mono {S T : Set V} (h : S ⊆ T) : cutKernel A S ≤ cutKernel A T := by
    intro v hv
    obtain ⟨hv, hAv⟩ := mem_cutKernel.mp hv
    exact mem_cutKernel.mpr ⟨fun i hi => hv i (fun h' => hi (h h')),
      fun i hi => hAv i (fun h' => hi (h h'))⟩
  have hUnion : cutKernel A X ⊔ cutKernel A Y ≤ cutKernel A (X ∪ Y) :=
    sup_le (mono Set.subset_union_left) (mono Set.subset_union_right)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (cutKernel A X) (cutKernel A Y)
  have hle := Submodule.finrank_mono hUnion
  rw [← hInter] at hdim
  -- The nullities are supermodular, while cardinality is modular.
  have hcard := Set.ncard_inter_add_ncard_union X Y
  have hnull (S : Set V) : G.cutRank S + Module.finrank (ZMod 2) (cutKernel A S) = S.ncard :=
    rank_cut_add_finrank_cutKernel A S
  have hX := hnull X
  have hY := hnull Y
  have hI := hnull (X ∩ Y)
  have hU := hnull (X ∪ Y)
  omega

omit [Fintype V] in
/-- The `x, y` entry of the adjacency matrix over `ZMod 2`. -/
private theorem adjMatrix_apply_eq (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) :
    H.adjMatrix (ZMod 2) x y = if H.Adj x y then 1 else 0 := rfl

/-- Row operation behind Proposition 2.6 of Oum (2005): when `v ∈ X`, the cut matrix of `G * v`
is obtained from that of `G` by adding row `v` to the rows of the neighbours of `v` in `X`. -/
private theorem cutRank_localComplement_of_mem {v : V} {X : Set V} (hv : v ∈ X) :
    (G.localComplement v).cutRank X = G.cutRank X := by
  classical
  unfold cutRank
  set N := (G.adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V)) (fun y : ↥Xᶜ => (y : V))
  set N' := ((G.localComplement v).adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V))
    (fun y : ↥Xᶜ => (y : V))
  let E : Matrix X X (ZMod 2) := fun x x' => if G.Adj v x ∧ (x' : V) = v then 1 else 0
  have hE : E * E = 0 := by
    ext x x''
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x' _ => ?_
    simp only [E]
    split_ifs with h1 h2 <;> simp_all
  have hsq : (1 + E) * (1 + E) = 1 := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hE, add_zero, add_assoc,
      ← two_mul]
    have : (2 : Matrix X X (ZMod 2)) = 0 := by
      rw [show (2 : Matrix X X (ZMod 2)) = Matrix.scalar X (2 : ZMod 2) from rfl]
      simp [show (2 : ZMod 2) = 0 from rfl]
    rw [this, zero_mul, add_zero]
  have hdet : IsUnit (1 + E).det := Matrix.isUnit_det_of_right_inverse hsq
  have hN : N' = (1 + E) * N := by
    ext x y
    have hxy : (x : V) ≠ y := fun h => y.2 (h ▸ x.2)
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
      Finset.sum_eq_single ⟨v, hv⟩]
    · simp only [N, N', E, Matrix.submatrix_apply, adjMatrix_apply_eq, localComplement_adj]
      by_cases ha : G.Adj x y <;> by_cases hb : G.Adj v x <;> by_cases hc : G.Adj v y <;>
        simp [ha, hb, hc, hxy, h11]
    · intro x' _ hx'
      have : (x' : V) ≠ v := fun h => hx' (Subtype.ext h)
      simp [E, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hN, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]

/-- **Local complementation preserves the cut-rank function.** For every finite simple graph
`G`, every vertex `v` and every vertex set `X`, `ρ_{G * v}(X) = ρ_G(X)` (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Proposition 2.6). The proof follows the
source: by symmetry of cut-rank assume `v ∈ X`; then the cut matrix of `G * v` arises from that
of `G` by adding row `v` to the rows of the neighbours of `v` in `X`, an invertible row
operation. -/
theorem cutRank_localComplement (v : V) (X : Set V) :
    (G.localComplement v).cutRank X = G.cutRank X := by
  by_cases hv : v ∈ X
  · exact G.cutRank_localComplement_of_mem hv
  · rw [← cutRank_compl, ← G.cutRank_compl X]
    exact G.cutRank_localComplement_of_mem (Set.mem_compl hv)

/-- **Complete graphs have cut-rank at most one.** In the complete graph every cut matrix is the
all-ones matrix, so `ρ_{K_V}(X) ≤ 1` for every vertex set `X`; this is why complete graphs have
rank-width at most one although `K_n` has tree-width `n - 1` (Oum, arXiv:1601.03800v2,
remark after Theorem 4.1). -/
theorem cutRank_top_le_one (X : Set V) : (⊤ : SimpleGraph V).cutRank X ≤ 1 := by
  classical
  unfold cutRank
  convert Matrix.rank_vecMulVec_le (R := ZMod 2) (fun _ : X => (1 : ZMod 2))
    (fun _ : ↥Xᶜ => (1 : ZMod 2)) using 2
  ext x y
  have hxy : (x : V) ≠ y := fun h => y.2 (h ▸ x.2)
  simp [Matrix.vecMulVec_apply, hxy]

end CutRank

/-! ## Local equivalence and vertex-minors -/

/-- **Locally equivalent graphs.** Two simple graphs on the same vertex set are locally
equivalent if one is obtained from the other by a finite sequence of local complementations
(Oum, *Rank-width and vertex-minors*, 2005, Section 2; Oum, arXiv:1601.03800v2, Section 4.1). -/
def LocallyEquivalent (G H : SimpleGraph V) : Prop :=
  Relation.ReflTransGen (fun G₁ G₂ : SimpleGraph V => ∃ v, G₂ = G₁.localComplement v) G H

/-- **Local equivalence is symmetric.** This holds because each local complementation is an
involution. -/
theorem LocallyEquivalent.symm {G H : SimpleGraph V} (h : G.LocallyEquivalent H) :
    H.LocallyEquivalent G := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    obtain ⟨v, rfl⟩ := hstep
    refine Relation.ReflTransGen.head ⟨v, ?_⟩ ih
    exact (localComplement_localComplement _ v).symm

/-- **Locally equivalent graphs have the same cut-rank function.** If `H` is obtained from `G` by
local complementations, then `ρ_H(X) = ρ_G(X)` for every vertex set `X` (iterating Oum, *Rank-width
and vertex-minors*, 2005, Proposition 2.6). -/
theorem LocallyEquivalent.cutRank_eq [Fintype V] {G H : SimpleGraph V}
    (h : G.LocallyEquivalent H) (X : Set V) : H.cutRank X = G.cutRank X := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨v, rfl⟩ := hstep
    rw [cutRank_localComplement, ih]

/-- **Vertex-minor.** A graph `H` on `W` is a vertex-minor of a graph `G` on `V` if `H` is
isomorphic to an induced subgraph of a graph locally equivalent to `G`; here the induced copy is
given by an injective map `f : W ↪ V` with `H = G'.comap f` (Oum, arXiv:1601.03800v2,
Section 4.1; equivalently, `H` is obtained from `G` by local complementations and vertex
deletions, as in Oum, *Rank-width and vertex-minors*, 2005, Section 2). -/
def IsVertexMinor {W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ G' : SimpleGraph V, G.LocallyEquivalent G' ∧ ∃ f : W ↪ V, H = G'.comap f

/-- **Every graph is a vertex-minor of itself.** -/
theorem IsVertexMinor.refl (G : SimpleGraph V) : G.IsVertexMinor G :=
  ⟨G, Relation.ReflTransGen.refl, Function.Embedding.refl V, by ext; rfl⟩

/-- **Local complementation gives a vertex-minor.** `G * v` is a vertex-minor of `G`. -/
theorem isVertexMinor_localComplement (G : SimpleGraph V) (v : V) :
    (G.localComplement v).IsVertexMinor G :=
  ⟨G.localComplement v, Relation.ReflTransGen.single ⟨v, rfl⟩, Function.Embedding.refl V,
    by ext; rfl⟩

end SimpleGraph
