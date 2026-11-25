/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Sparse connected graphs with triangle Ramsey number 2n - 1 (Erdős Problem 1182)

Erdős Problem 1182: let `f(n)` be maximal such that there is a connected graph `G` with `n`
vertices and `f(n)` edges such that `R(K₃, G) = 2n - 1`. Let `F(n)` be maximal such that every
connected graph `G` with `n` vertices and `≤ F(n)` edges has `R(K₃, G) = 2n - 1`. Estimate `f(n)`
and `F(n)`. In particular, is it true that `F(n) / n → ∞`?

The main result, `triangleGoodnessSuperlinearThreshold_refuted`, answers the final question in the
negative. Its proof shows that for every `k ≥ 1` some connected graph `G` on `n = 10k + 3`
vertices with at most `241n` edges has `R(K₃, G) ≠ 2n - 1`, so the statement fails for `C = 241`.

Source: T. F. Bloom, Erdős Problems, Problem #1182, https://www.erdosproblems.com/1182 (status
OPEN). UnsolvedMath record UM-30007223 (`EP-1182`), dataset ulamai/UnsolvedMath v1.8.0.

`R(K₃, G)` is the MathlibExt pair Ramsey number `SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin
3)) G` (least `N` such that every graph on `N` vertices contains a triangle or its complement
contains a copy of `G`). The property 'every connected `G` with `n` vertices and at most `m` edges
has `R(K₃, G) = 2n - 1`' is downward closed in `m`, so `F(n) / n → ∞` says that for every `C`, for
all large `n`, every connected graph on `n` vertices with at most `C n` edges has `R(K₃, G) = 2n -
1`; the target is stated in that form, which avoids a junk value of `F`. Only the final question
is stated: the requests to estimate `f(n)` and `F(n)` are open-ended (the page records bounds and
Brandt's expectation `2n < F(n) < 6n` for large `n`, none of them a resolved statement).
formal-conjectures has no statement of this problem.

## Proof outline

The proof is self-contained and gives the constant `241`, weaker than Brandt's `84`. Counting the
families of `240` self-maps of `Fin n` that miss a given pair of `k`-sets shows that some family
sends a point of every `k`-set into every `k`-set. Joining each vertex to its images and to the
vertex `0` gives a connected graph `G` with at most `241n` edges in which any two disjoint sets of
at least `k` vertices are joined by an edge. The blow-up of the five-cycle with five classes of
`4k + 1` vertices is a triangle-free graph on `2n - 1` vertices. A copy of `G` in its complement
has no edge between neighbouring classes, so each class, or the union of its two neighbours, holds
fewer than `k` vertices of `G`; as each class holds at most `4k + 1` vertices, the copy holds at
most `10k < n` vertices, a contradiction. So `2n - 1` is not in the set whose infimum is
`R(K₃, G)`, and `R(K₃, G) ≠ 2n - 1`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleGoodSparseConnectedGraphsErdosProblem1182Wanted

open Filter

/-- **Superlinear threshold for triangle-good graphs (Erdős Problem 1182).** The statement that for
every real number $C$, for all sufficiently large natural numbers $n$, every connected graph $G$ on
the vertex set $\{0, \dots, n - 1\}$ with at most $Cn$ edges has $R(K_3, G) = 2n - 1$. Here
$R(K_3, G)$ is the Ramsey number of the pair: the least $N$ such that every graph on $N$ vertices
contains a triangle or has a complement containing a copy of $G$.

This is the last question of Erdős Problem 1182, whether $F(n) / n \to \infty$, where $F(n)$ is the
largest $m$ such that every connected graph $G$ on $n$ vertices with at most $m$ edges has
$R(K_3, G) = 2n - 1$; since this property is downward closed in $m$, the two forms agree. -/
def triangleGoodnessSuperlinearThreshold : Prop :=
  ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.Connected →
    (G.edgeSet.ncard : ℝ) ≤ C * n →
    SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin 3)) G = 2 * n - 1

/-! ### Sparse graphs joining all large disjoint sets -/

/-- If `4 ^ n (n - k) ^ (k d) < n ^ (k d)`, some family of `d` self-maps of `Fin n` sends a point
of every `k`-set into every `k`-set: the families missing a given pair of `k`-sets are too few to
cover all `(n ^ n) ^ d` families. -/
private theorem exists_maps_hit (n k d : ℕ) (hkn : k ≤ n)
    (h : 4 ^ n * (n - k) ^ (k * d) < n ^ (k * d)) :
    ∃ f : Fin d → Fin n → Fin n, ∀ X Y : Finset (Fin n), X.card = k → Y.card = k →
      ∃ i, ∃ v ∈ X, f i v ∈ Y := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain rfl : k = 0 := by omega
      simp at h
    · exact hn
  -- the pairs of `k`-sets, and for each pair the families of maps that miss it
  let P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    Finset.univ.filter fun p => p.1.card = k ∧ p.2.card = k
  let miss : Finset (Fin n) × Finset (Fin n) → Finset (Fin d → Fin n → Fin n) := fun p =>
    Fintype.piFinset fun _ => Fintype.piFinset fun v => if v ∈ p.1 then p.2ᶜ else Finset.univ
  have hmiss : ∀ p ∈ P, (miss p).card = ((n - k) ^ k * n ^ (n - k)) ^ d := by
    intro p hp
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp only [miss, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    simp only [apply_ite Finset.card, Finset.card_compl, Finset.card_univ, Fintype.card_fin, h2]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_univ_mem, h1,
      Finset.filter_notMem_eq_sdiff, Finset.card_univ_sdiff, Fintype.card_fin, h1]
  have hP : P.card ≤ 4 ^ n := by
    calc P.card ≤ (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).card :=
          Finset.card_le_univ _
      _ = 4 ^ n := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin,
            ← mul_pow]
          norm_num
  have hlt : (P.biUnion miss).card < (Finset.univ : Finset (Fin d → Fin n → Fin n)).card := by
    calc (P.biUnion miss).card ≤ ∑ p ∈ P, (miss p).card := Finset.card_biUnion_le
      _ = P.card * ((n - k) ^ k * n ^ (n - k)) ^ d := by
          rw [Finset.sum_congr rfl hmiss, Finset.sum_const, smul_eq_mul]
      _ ≤ 4 ^ n * ((n - k) ^ k * n ^ (n - k)) ^ d := Nat.mul_le_mul_right _ hP
      _ = 4 ^ n * (n - k) ^ (k * d) * n ^ ((n - k) * d) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc]
      _ < n ^ (k * d) * n ^ ((n - k) * d) := Nat.mul_lt_mul_of_pos_right h (pow_pos hn _)
      _ = (Finset.univ : Finset (Fin d → Fin n → Fin n)).card := by
          rw [← pow_add, ← add_mul, Nat.add_sub_cancel' hkn, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, fun X Y hX hY => ?_⟩
  by_contra hcon
  push Not at hcon
  refine hf (Finset.mem_biUnion.2 ⟨(X, Y), Finset.mem_filter.2 ⟨Finset.mem_univ _, hX, hY⟩, ?_⟩)
  simp only [miss, Fintype.mem_piFinset]
  intro i v
  split_ifs with hv
  · exact Finset.mem_compl.2 (hcon i v hv)
  · exact Finset.mem_univ _

/-- The counting bound behind `exists_maps_hit` for `n = 10 k + 3` and `240` maps. -/
private theorem count_bound (k : ℕ) (hk : 1 ≤ k) :
    4 ^ (10 * k + 3) * (10 * k + 3 - k) ^ (k * 240) < (10 * k + 3) ^ (k * 240) := by
  have h1 : 13 * (10 * k + 3 - k) ≤ 12 * (10 * k + 3) := by omega
  have h2 : 4 ^ (10 * k + 3) ≤ (4 ^ 13) ^ k := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 4 ^ 13 * 12 ^ 240 < 13 ^ 240 := by norm_num
  have hpos : 0 < (10 * k + 3) ^ (k * 240) := pow_pos (by omega) _
  refine Nat.lt_of_mul_lt_mul_left (a := 13 ^ (k * 240)) ?_
  calc 13 ^ (k * 240) * (4 ^ (10 * k + 3) * (10 * k + 3 - k) ^ (k * 240))
      = 4 ^ (10 * k + 3) * (13 * (10 * k + 3 - k)) ^ (k * 240) := by
        rw [mul_pow, mul_left_comm]
    _ ≤ (4 ^ 13) ^ k * (12 * (10 * k + 3)) ^ (k * 240) :=
        Nat.mul_le_mul h2 (Nat.pow_le_pow_left h1 _)
    _ = (4 ^ 13 * 12 ^ 240) ^ k * (10 * k + 3) ^ (k * 240) := by
        rw [mul_pow 12, pow_mul' 12, ← mul_assoc, ← mul_pow]
    _ < (13 ^ 240) ^ k * (10 * k + 3) ^ (k * 240) :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left h3 (by omega)) hpos
    _ = 13 ^ (k * 240) * (10 * k + 3) ^ (k * 240) := by rw [← pow_mul']

/-- For `k ≥ 1` there is a connected graph on `10 k + 3` vertices with at most `241 (10 k + 3)`
edges in which any two disjoint sets of at least `k` vertices are joined by an edge. -/
private theorem exists_sparse_joined_graph (k : ℕ) (hk : 1 ≤ k) :
    ∃ G : SimpleGraph (Fin (10 * k + 3)), G.Connected ∧ G.edgeSet.ncard ≤ 241 * (10 * k + 3) ∧
      ∀ X Y : Finset (Fin (10 * k + 3)), k ≤ X.card → k ≤ Y.card → Disjoint X Y →
        ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
  obtain ⟨f, hf⟩ := exists_maps_hit (10 * k + 3) k 240 (by omega) (count_bound k hk)
  -- `g none` sends every vertex to `0`, and `g (some i)` is `f i`
  let g : Option (Fin 240) → Fin (10 * k + 3) → Fin (10 * k + 3) := fun o v => o.elim 0 (f · v)
  let G := SimpleGraph.fromRel fun v w => ∃ o, g o v = w
  refine ⟨G, ?_, ?_, ?_⟩
  · have h0 : ∀ v, G.Reachable v 0 := by
      intro v
      by_cases hv : v = 0
      · rw [hv]
      · exact SimpleGraph.Adj.reachable
          ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hv, Or.inl ⟨none, rfl⟩⟩)
    exact ⟨fun u v => (h0 u).trans (h0 v).symm⟩
  · have hsub : G.edgeSet ⊆
        Set.range fun p : Option (Fin 240) × Fin (10 * k + 3) => s(p.2, g p.1 p.2) := by
      intro e he
      induction e using Sym2.ind with
      | h v w =>
        obtain ⟨-, ⟨o, rfl⟩ | ⟨o, rfl⟩⟩ :=
          (SimpleGraph.fromRel_adj _ _ _).1 ((SimpleGraph.mem_edgeSet _).1 he)
        · exact ⟨(o, v), rfl⟩
        · exact ⟨(o, w), Sym2.eq_swap⟩
    calc G.edgeSet.ncard ≤ (Set.range fun p : Option (Fin 240) × Fin (10 * k + 3) =>
          s(p.2, g p.1 p.2)).ncard := Set.ncard_le_ncard hsub (Set.finite_range _)
      _ ≤ (Set.univ : Set (Option (Fin 240) × Fin (10 * k + 3))).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = 241 * (10 * k + 3) := by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_option,
            Fintype.card_fin, Fintype.card_fin]
  · intro X Y hX hY hXY
    obtain ⟨X', hX'X, hX'⟩ := Finset.exists_subset_card_eq hX
    obtain ⟨Y', hY'Y, hY'⟩ := Finset.exists_subset_card_eq hY
    obtain ⟨i, v, hv, hfv⟩ := hf X' Y' hX' hY'
    refine ⟨v, hX'X hv, f i v, hY'Y hfv,
      (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun hvf => ?_, Or.inl ⟨some i, rfl⟩⟩⟩
    exact Finset.disjoint_left.1 hXY (hX'X hv) (hvf ▸ hY'Y hfv)

/-! ### The blown-up five-cycle -/

/-- The blow-up of the five-cycle along a map `c` has no triangle. -/
private theorem not_top_isContained_comap_cycleGraph {V : Type*} (c : V → Fin 5) :
    ¬ (⊤ : SimpleGraph (Fin 3)).IsContained ((SimpleGraph.cycleGraph 5).comap c) := by
  rintro ⟨φ⟩
  have key : ∀ a b c : Fin 5, (SimpleGraph.cycleGraph 5).Adj a b →
      (SimpleGraph.cycleGraph 5).Adj b c → (SimpleGraph.cycleGraph 5).Adj a c → False := by
    decide
  exact key _ _ _ (φ.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1))
    (φ.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2))
    (φ.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 2))

/-- Let `G` be a graph on `10 k + 3` vertices in which any two disjoint sets of at least `k`
vertices are joined by an edge. The complement of the blow-up of the five-cycle along a map `c`
whose fibres have at most `4 k + 1` points contains no copy of `G`. -/
private theorem not_isContained_compl_comap_cycleGraph {V : Type*} (k : ℕ) (c : V → Fin 5)
    (hc : ∀ (i : Fin 5) (S : Finset V), (∀ x ∈ S, c x = i) → S.card ≤ 4 * k + 1)
    (G : SimpleGraph (Fin (10 * k + 3)))
    (hG : ∀ X Y : Finset (Fin (10 * k + 3)), k ≤ X.card → k ≤ Y.card → Disjoint X Y →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y) :
    ¬ G.IsContained ((SimpleGraph.cycleGraph 5).comap c)ᶜ := by
  classical
  rintro ⟨φ⟩
  -- the vertices of `G` sent to the class `i`
  let F : Fin 5 → Finset (Fin (10 * k + 3)) := fun i => Finset.univ.filter fun x => c (φ x) = i
  have hF : ∀ i, (F i).card ≤ 4 * k + 1 := by
    intro i
    have hinj : Function.Injective φ := φ.injective
    have := hc i ((F i).image φ) (by simp [F])
    rwa [Finset.card_image_of_injective _ hinj] at this
  have hsum : (F 0).card + (F 1).card + (F 2).card + (F 3).card + (F 4).card = 10 * k + 3 := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun x => c (φ x)) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_five] at this
    exact this.symm
  have hfin : ∀ i : Fin 5, i + 1 ≠ i - 1 ∧ i ≠ i + 1 ∧ i ≠ i - 1 ∧
      (SimpleGraph.cycleGraph 5).Adj i (i + 1) ∧ (SimpleGraph.cycleGraph 5).Adj i (i - 1) := by
    decide
  have hnb : ∀ i, (F i).card < k ∨ (F (i + 1)).card + (F (i - 1)).card < k := by
    intro i
    by_contra! hcon
    obtain ⟨hne, hne1, hne2, hadj1, hadj2⟩ := hfin i
    have hdisj : Disjoint (F (i + 1)) (F (i - 1)) := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      exact hne (h1.symm.trans h2)
    have hXY : Disjoint (F i) (F (i + 1) ∪ F (i - 1)) := by
      rw [Finset.disjoint_union_right, Finset.disjoint_filter, Finset.disjoint_filter]
      exact ⟨fun x _ h1 h2 => hne1 (h1.symm.trans h2), fun x _ h1 h2 => hne2 (h1.symm.trans h2)⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hG (F i) (F (i + 1) ∪ F (i - 1)) hcon.1
      (by rw [Finset.card_union_of_disjoint hdisj]; exact hcon.2) hXY
    have hc' := φ.toHom.map_adj hxy
    rw [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at hc'
    simp only [F, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply hc'.2
    rcases hy with hy | hy
    · rw [SimpleGraph.Copy.toHom_apply, SimpleGraph.Copy.toHom_apply, hx, hy]
      exact hadj1
    · rw [SimpleGraph.Copy.toHom_apply, SimpleGraph.Copy.toHom_apply, hx, hy]
      exact hadj2
  have h0 : (F 0).card < k ∨ (F 1).card + (F 4).card < k := hnb 0
  have h1 : (F 1).card < k ∨ (F 2).card + (F 0).card < k := hnb 1
  have h2 : (F 2).card < k ∨ (F 3).card + (F 1).card < k := hnb 2
  have h3 : (F 3).card < k ∨ (F 4).card + (F 2).card < k := hnb 3
  have h4 : (F 4).card < k ∨ (F 0).card + (F 3).card < k := hnb 4
  have := hF 0
  have := hF 1
  have := hF 2
  have := hF 3
  have := hF 4
  omega

/-- For `k ≥ 1` some connected graph on `n = 10 k + 3` vertices with at most `241 n` edges has
`R(K₃, G) ≠ 2 n - 1`. -/
private theorem exists_counterexample (k : ℕ) (hk : 1 ≤ k) :
    ∃ G : SimpleGraph (Fin (10 * k + 3)), G.Connected ∧ G.edgeSet.ncard ≤ 241 * (10 * k + 3) ∧
      SimpleGraph.graphPairRamsey (⊤ : SimpleGraph (Fin 3)) G ≠ 2 * (10 * k + 3) - 1 := by
  obtain ⟨G, hconn, hedge, hG⟩ := exists_sparse_joined_graph k hk
  refine ⟨G, hconn, hedge, fun hR => ?_⟩
  -- the vertices `0, …, 2 n - 2` as five classes of `4 k + 1` vertices
  let e : Fin (2 * (10 * k + 3) - 1) ≃ Fin 5 × Fin (4 * k + 1) :=
    (finCongr (by omega)).trans finProdFinEquiv.symm
  let S : Set ℕ := {N | ∀ C : SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ}
  have hR' : sInf S = 2 * (10 * k + 3) - 1 := by
    rw [SimpleGraph.graphPairRamsey_eq_sInf] at hR
    exact hR
  have hmem : 2 * (10 * k + 3) - 1 ∈ S := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · rw [hS, Nat.sInf_empty] at hR'
      omega
    · rw [← hR']
      exact Nat.sInf_mem hS
  rcases hmem ((SimpleGraph.cycleGraph 5).comap fun x => (e x).1) with h | h
  · exact not_top_isContained_comap_cycleGraph _ h
  · refine not_isContained_compl_comap_cycleGraph k (fun x => (e x).1) ?_ G hG h
    intro i T hT
    calc T.card ≤ (Finset.univ : Finset (Fin (4 * k + 1))).card :=
          Finset.card_le_card_of_injOn (fun x => (e x).2)
            (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
            (fun x hx y hy hxy => e.injective (Prod.ext ((hT x hx).trans (hT y hy).symm) hxy))
      _ = 4 * k + 1 := by simp

/-- **No superlinear threshold for triangle-good graphs (Erdős Problem 1182).** It is not true
that for every real number $C$, for all sufficiently large natural numbers $n$, every connected
graph $G$ on the vertex set $\{0, \dots, n - 1\}$ with at most $Cn$ edges has
$R(K_3, G) = 2n - 1$. Equivalently, there is a real number $C$ such that for infinitely many $n$
some connected graph $G$ on $\{0, \dots, n - 1\}$ with at most $Cn$ edges has
$R(K_3, G) \ne 2n - 1$. Here $R(K_3, G)$ is the Ramsey number of the pair: the least $N$ such
that every graph on $N$ vertices contains a triangle or has a complement containing a copy of
$G$, and $0$ if there is no such $N$.

Brandt proved $F(n) \le 84n$, where $F(n)$ is the largest $m$ such that every connected graph on
$n$ vertices with at most $m$ edges has $R(K_3, G) = 2n - 1$. So for all large $n$ some connected
graph on $n$ vertices with at most $84n + 1$ edges has $R(K_3, G) \ne 2n - 1$, and the statement
fails for $C = 85$. Brandt's 1996 preprint is unrefereed; erdosproblems.com/1182 accepts it.

Source: T. F. Bloom, Erdős Problems, Problem #1182,
https://www.erdosproblems.com/1182 (status OPEN); resolution: S. Brandt, Expanding graphs and
Ramsey numbers, preprint, Serie A Mathematik, Freie Universität Berlin, 1996 (unrefereed; accepted
on erdosproblems.com/1182), F(n) ≤ 84n, as recorded on erdosproblems.com/1182: 'The upper bound
was improved to F(n) ≤ 84n by Brandt ... (This resolves the final question in the negative.)',
https://ftp.math.fu-berlin.de/pub/math/publ/pre/1996/pr-a-96-24.ps.
-/
public theorem triangleGoodnessSuperlinearThreshold_refuted :
    ¬ triangleGoodnessSuperlinearThreshold := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h 241)
  obtain ⟨G, hconn, hedge, hR⟩ := exists_counterexample (N + 1) (by omega)
  exact hR (hN (10 * (N + 1) + 3) (by omega) G hconn (by exact_mod_cast hedge))

end MathlibExt.Combinatorics.TriangleGoodSparseConnectedGraphsErdosProblem1182Wanted
