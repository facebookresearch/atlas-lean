/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Field
public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spectral expanders and the expander mixing lemma

A `d`-regular graph on `N` vertices is a *spectral expander with parameter `λ`* (an
`(N, d, λ)`-graph) when its random-walk matrix `M = A / d` shrinks every vector orthogonal to the
constant vector by a factor at least `λ`: `‖M x‖ ≤ λ ‖x‖` whenever `∑ᵢ xᵢ = 0`. This is the
definition of spectral expansion in S. Vadhan, *Pseudorandomness*, Foundations and Trends in
Theoretical Computer Science 7 (2012), Section 4.1.2 (`λ(G) = max_{x ⊥ u} ‖x M‖ / ‖x‖`,
Definition 4.5), and of an `(N, D, λ)`-graph in O. Reingold, S. Vadhan and A. Wigderson,
*Entropy waves, the zig-zag graph product, and new constant-degree expanders*, Ann. of Math. 155
(2002), Definitions 1.1 and 2.2: for a `d`-regular undirected graph with `d ≥ 1`, the smallest
such `λ` is the largest absolute value of an eigenvalue of `M` on the orthogonal complement of the
constants (counted with multiplicity, the constant eigenvector removed), which is `1` when the
graph is disconnected.

The norm form is stated with squared Euclidean norms, as dot products, so that it needs no
spectral theorem. The main results:

* `abs_indicator_dotProduct_mulVec_sub_le`: the expander mixing lemma for any symmetric matrix
  with constant row sums;
* `expander_mixing_lemma`: the expander mixing lemma for spectral expanders (Vadhan, Lemma 4.15),
  with the edge count given by Mathlib's `SimpleGraph.interedges`;
* `abs_card_interedges_sub_le`: its unnormalised form
  `|e(S, T) - d |S| |T| / N| ≤ d λ √(|S| |T|)`;
* `mul_sub_le_sq_mul_of_isSpectralExpander`: the elementary lower bound
  `d (N - d) ≤ (d λ)² (N - 1)`, so `λ ≥ √((N - d) / (d (N - 1)))`, about `1 / √d` for large `N`;
* `isSpectralExpander_top`: the complete graph on `N ≥ 2` vertices is a spectral expander with
  `d = N - 1` and `λ = 1 / (N - 1)`, for which the lower bound is an equality;
* `walkProb G d hreg hd t P`: the probability that a random walk from a uniform start vertex
  satisfies `P`, for a `d`-regular graph with `d ≥ 1` on a nonempty vertex set, and
  `walkProb_true`: it has total mass one.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Combinatorics.SpectralExpander

open EndpointMapMultigraph (indicator)

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Spectral bound on the vectors orthogonal to the constants.** The real square matrix `A`
satisfies `‖A x‖ ≤ c ‖x‖` (Euclidean norms, written as `(A x) · (A x) ≤ c² (x · x)`) for every
vector `x` whose entries sum to zero. For the adjacency matrix of a `d`-regular graph and
`c = d λ` this is spectral expansion `λ(G) ≤ λ` in the sense of S. Vadhan, *Pseudorandomness*
(2012), Section 4.1.2 and Definition 4.5. -/
def IsSpectralBound (A : Matrix V V ℝ) (c : ℝ) : Prop :=
  ∀ x : V → ℝ, ∑ i, x i = 0 → (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ c ^ 2 * (x ⬝ᵥ x)

omit [DecidableEq V] in
/-- **Spectral expander.** A finite simple graph `G` is a spectral expander of degree `d` with
parameter `λ ≥ 0` (an `(N, d, λ)`-graph, `N` the number of vertices) when it is `d`-regular and
its random-walk matrix `A / d` satisfies `‖(A / d) x‖ ≤ λ ‖x‖` for every `x` orthogonal to the
constant vector, stated without division as `‖A x‖ ≤ d λ ‖x‖` (S. Vadhan, *Pseudorandomness*
(2012), Definition 4.5 with `λ = 1 - γ`; O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math.
155 (2002), Definition 1.1). -/
def IsSpectralExpander (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (lam : ℝ) : Prop :=
  G.IsRegularOfDegree d ∧ 0 ≤ lam ∧ IsSpectralBound (G.adjMatrix ℝ) (d * lam)

omit [Fintype V] in
private lemma indicator_mul_self (S : Finset V) (v : V) :
    indicator S v * indicator S v = indicator S v := by
  by_cases h : v ∈ S <;> simp [indicator, h]

private lemma sum_indicator (S : Finset V) : ∑ v, indicator S v = S.card := by
  classical
  simp [indicator]

/-- The centred indicator `1_S - (|S| / N) 1` used in the proof of the mixing lemma. -/
private noncomputable def centred (S : Finset V) : V → ℝ :=
  fun v => indicator S v - S.card / Fintype.card V

private lemma sum_centred (S : Finset V) (hN : (Fintype.card V : ℝ) ≠ 0) :
    ∑ v, centred S v = 0 := by
  simp only [centred, Finset.sum_sub_distrib, sum_indicator, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp
  ring

private lemma centred_dotProduct_self (S : Finset V) (hN : (Fintype.card V : ℝ) ≠ 0) :
    centred S ⬝ᵥ centred S = S.card * (1 - S.card / Fintype.card V) := by
  set a : ℝ := S.card / Fintype.card V
  have h : ∀ v, centred S v * centred S v = indicator S v * (1 - 2 * a) + a ^ 2 := by
    intro v
    have := indicator_mul_self S v
    simp only [centred]
    change (indicator S v - a) * (indicator S v - a) = _
    nlinarith [this]
  rw [dotProduct, Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_indicator, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [a]
  field_simp
  ring

/-- **Expander mixing lemma for matrices.** Let `A` be a symmetric real matrix indexed by a finite
set of size `N`, with every row summing to `d`, such that `‖A x‖ ≤ c ‖x‖` for every `x`
orthogonal to the constant vector. Then for all vertex sets `S` and `T`,
`|1_Sᵀ A 1_T - d |S| |T| / N| ≤ c √(|S| (1 - |S| / N)) √(|T| (1 - |T| / N))`. This is the proof of
the expander mixing lemma in S. Vadhan, *Pseudorandomness* (2012), Lemma 4.15, which uses only
these three properties of the adjacency matrix. -/
theorem abs_indicator_dotProduct_mulVec_sub_le {A : Matrix V V ℝ} (hA : Aᵀ = A) {d c : ℝ}
    (hc : 0 ≤ c) (hrow : A *ᵥ (1 : V → ℝ) = d • (1 : V → ℝ)) (hb : IsSpectralBound A c)
    (S T : Finset V) :
    |indicator S ⬝ᵥ (A *ᵥ indicator T) - d * S.card * T.card / Fintype.card V| ≤
      c * √(S.card * (1 - S.card / Fintype.card V)) *
        √(T.card * (1 - T.card / Fintype.card V)) := by
  by_cases hN : (Fintype.card V : ℝ) = 0
  · have hV : IsEmpty V := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hN)
    simp [Finset.eq_empty_of_isEmpty S, Finset.eq_empty_of_isEmpty T, dotProduct]
  set a : ℝ := S.card / Fintype.card V
  set b : ℝ := T.card / Fintype.card V
  have hS : indicator S = centred S + a • (1 : V → ℝ) := by
    funext v; simp [centred, a]
  have hT : indicator T = centred T + b • (1 : V → ℝ) := by
    funext v; simp [centred, b]
  have hone : ∀ x : V → ℝ, (1 : V → ℝ) ⬝ᵥ (A *ᵥ x) = d * ∑ i, x i := by
    intro x
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, hrow, smul_dotProduct, one_dotProduct,
      smul_eq_mul]
  have key : indicator S ⬝ᵥ (A *ᵥ indicator T) =
      centred S ⬝ᵥ (A *ᵥ centred T) + d * S.card * T.card / Fintype.card V := by
    rw [hS, hT, mulVec_add, mulVec_smul, hrow]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_one, hone, sum_centred T hN, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib,
      sum_centred S hN, Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [a, b]
    field_simp
    ring
  rw [key, add_sub_cancel_right]
  have hxS := centred_dotProduct_self S hN
  have hxT := centred_dotProduct_self T hN
  have hnS : 0 ≤ centred S ⬝ᵥ centred S := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hnT : 0 ≤ centred T ⬝ᵥ centred T := by
    rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hcs : (centred S ⬝ᵥ (A *ᵥ centred T)) ^ 2 ≤
      (centred S ⬝ᵥ centred S) * ((A *ᵥ centred T) ⬝ᵥ (A *ᵥ centred T)) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (centred S) (A *ᵥ centred T)
    simpa [dotProduct, sq] using this
  have hsp := hb (centred T) (sum_centred T hN)
  have hle : (centred S ⬝ᵥ (A *ᵥ centred T)) ^ 2 ≤
      (c * √(centred S ⬝ᵥ centred S) * √(centred T ⬝ᵥ centred T)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnS, Real.sq_sqrt hnT]
    calc _ ≤ (centred S ⬝ᵥ centred S) * ((A *ᵥ centred T) ⬝ᵥ (A *ᵥ centred T)) := hcs
      _ ≤ (centred S ⬝ᵥ centred S) * (c ^ 2 * (centred T ⬝ᵥ centred T)) :=
          mul_le_mul_of_nonneg_left hsp hnS
      _ = _ := by ring
  rw [← hxS, ← hxT]
  exact abs_le_of_sq_le_sq' hle (by positivity) |>.2 |> fun h2 =>
    abs_le.mpr ⟨(abs_le_of_sq_le_sq' hle (by positivity)).1, h2⟩

/-- **Edge count as a bilinear form.** For a finite simple graph and vertex sets `S` and `T`, the
number of ordered pairs `(s, t) ∈ S × T` with `s ~ t` (Mathlib's `SimpleGraph.interedges`) equals
`1_Sᵀ A 1_T`, where `A` is the adjacency matrix. -/
theorem card_interedges_eq_indicator_dotProduct (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    ((G.interedges S T).card : ℝ) = indicator S ⬝ᵥ (G.adjMatrix ℝ *ᵥ indicator T) := by
  classical
  rw [SimpleGraph.dotProduct_mulVec_adjMatrix, SimpleGraph.interedges_def, Finset.card_filter,
    Finset.sum_product]
  push_cast
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_subset (Finset.subset_univ T)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      by_cases h : G.Adj i j <;> simp [indicator, h, hi, hj]
    · intro j _ hj
      by_cases h : G.Adj i j <;> simp [indicator, h, hj]
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : G.Adj i j <;> simp [indicator, h, hi]

omit [DecidableEq V] in
/-- **Expander mixing lemma.** Let `G` be a `d`-regular graph on `N` vertices, `d ≥ 1`, that is a
spectral expander with parameter `λ`. Then for all vertex sets `S` and `T` of densities
`α = |S| / N` and `β = |T| / N`,
`|e(S, T) / (N d) - α β| ≤ λ √(α (1 - α) β (1 - β))`, where `e(S, T)` counts the ordered pairs
`(s, t) ∈ S × T` joined by an edge (S. Vadhan, *Pseudorandomness*, Foundations and Trends in
Theoretical Computer Science 7 (2012), Lemma 4.15, first inequality). -/
theorem expander_mixing_lemma {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} {lam : ℝ}
    (h : IsSpectralExpander G d lam) (hd : 0 < d) (S T : Finset V) :
    |(G.interedges S T).card / (Fintype.card V * d : ℝ) -
        S.card / Fintype.card V * (T.card / Fintype.card V)| ≤
      lam * √(S.card / Fintype.card V * (1 - S.card / Fintype.card V) *
        (T.card / Fintype.card V * (1 - T.card / Fintype.card V))) := by
  classical
  obtain ⟨hreg, hlam, hb⟩ := h
  by_cases hN : (Fintype.card V : ℝ) = 0
  · simp [hN]
  have hrow : G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
    funext v
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simpa using this
  have hmain := abs_indicator_dotProduct_mulVec_sub_le (G.transpose_adjMatrix (α := ℝ))
    (by positivity : (0 : ℝ) ≤ d * lam) hrow hb S T
  rw [← card_interedges_eq_indicator_dotProduct] at hmain
  set N : ℝ := (Fintype.card V : ℝ)
  have hNpos : 0 < N := lt_of_le_of_ne (by positivity) (Ne.symm hN)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := S.card / N
  set b : ℝ := T.card / N
  have ha1 : a ≤ 1 := by
    simp only [a]; rw [div_le_one hNpos]
    exact (by exact_mod_cast Finset.card_le_univ S : (S.card : ℝ) ≤ Fintype.card V)
  have hb1 : b ≤ 1 := by
    simp only [b]; rw [div_le_one hNpos]
    exact (by exact_mod_cast Finset.card_le_univ T : (T.card : ℝ) ≤ Fintype.card V)
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  -- Rewrite the square roots of the matrix lemma in terms of the densities.
  have hsq : √(S.card * (1 - a)) * √(T.card * (1 - b)) = N * √(a * (1 - a) * (b * (1 - b))) := by
    have hP : 0 ≤ (S.card : ℝ) * (1 - a) := mul_nonneg (by positivity) (by linarith)
    rw [← Real.sqrt_mul hP]
    have : (S.card : ℝ) * (1 - a) * (T.card * (1 - b)) = N ^ 2 * (a * (1 - a) * (b * (1 - b))) := by
      simp only [a, b]; field_simp
    rw [this, Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hNpos.le]
  have hlhs : (G.interedges S T).card / (N * d) - a * b =
      ((G.interedges S T).card - d * S.card * T.card / N) / (N * d) := by
    simp only [a, b]; field_simp
  rw [hlhs, abs_div, abs_of_pos (by positivity : 0 < N * d), div_le_iff₀ (by positivity)]
  calc _ ≤ d * lam * √(S.card * (1 - a)) * √(T.card * (1 - b)) := hmain
    _ = _ := by rw [mul_assoc, hsq]; ring

omit [DecidableEq V] in
/-- **Expander mixing lemma, unnormalised form.** For a `d`-regular spectral expander with
parameter `λ` on `N` vertices and all vertex sets `S` and `T`,
`|e(S, T) - d |S| |T| / N| ≤ d λ √(|S| |T|)`. This is the weaker second inequality of S. Vadhan,
*Pseudorandomness* (2012), Lemma 4.15 (`… ≤ λ √(α β)`), multiplied by `N d`. -/
theorem abs_card_interedges_sub_le {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} {lam : ℝ}
    (h : IsSpectralExpander G d lam) (S T : Finset V) :
    |((G.interedges S T).card : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      d * lam * √(S.card * T.card) := by
  classical
  obtain ⟨hreg, hlam, hb⟩ := h
  have hrow : G.adjMatrix ℝ *ᵥ (1 : V → ℝ) = (d : ℝ) • (1 : V → ℝ) := by
    funext v
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simpa using this
  have hmain := abs_indicator_dotProduct_mulVec_sub_le (G.transpose_adjMatrix (α := ℝ))
    (by positivity : (0 : ℝ) ≤ d * lam) hrow hb S T
  rw [← card_interedges_eq_indicator_dotProduct] at hmain
  have hS : S.card * (1 - S.card / (Fintype.card V : ℝ)) ≤ S.card := by
    have : (0 : ℝ) ≤ S.card / Fintype.card V := by positivity
    nlinarith [(by positivity : (0 : ℝ) ≤ S.card)]
  have hT : T.card * (1 - T.card / (Fintype.card V : ℝ)) ≤ T.card := by
    have : (0 : ℝ) ≤ T.card / Fintype.card V := by positivity
    nlinarith [(by positivity : (0 : ℝ) ≤ T.card)]
  have hPQ : √(S.card * (1 - S.card / (Fintype.card V : ℝ))) *
      √(T.card * (1 - T.card / (Fintype.card V : ℝ))) ≤ √(S.card * T.card) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg S.card) (T.card : ℝ)]
    exact mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hT) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  calc _ ≤ _ := hmain
    _ = d * lam * (√(S.card * (1 - S.card / (Fintype.card V : ℝ))) *
          √(T.card * (1 - T.card / (Fintype.card V : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hPQ (by positivity)

omit [DecidableEq V] in
/-- **Elementary lower bound on the spectral parameter.** If a `d`-regular graph on `N ≥ 2`
vertices is a spectral expander with parameter `λ`, then `d (N - d) ≤ (d λ)² (N - 1)`; for
`d ≥ 1` this says `λ ≥ √((N - d) / (d (N - 1)))`, which tends to `1 / √d` as `N → ∞` with `d`
fixed. The test vector is `e_v - (1 / N) 1` for any vertex `v`. This is the trivial bound
`1 / √D - o(1)` mentioned in S. Vadhan, *Pseudorandomness* (2012), Section 4.1.3, before
Theorem 4.11 (the Alon-Boppana bound `2 √(D - 1) / D - o(1)` improves it). -/
theorem mul_sub_le_sq_mul_of_isSpectralExpander {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} {lam : ℝ} (h : IsSpectralExpander G d lam) (hN : 2 ≤ Fintype.card V) :
    (d : ℝ) * (Fintype.card V - d) ≤ (d * lam) ^ 2 * (Fintype.card V - 1) := by
  classical
  obtain ⟨hreg, -, hb⟩ := h
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hV
  set N : ℝ := (Fintype.card V : ℝ)
  have hNpos : (0 : ℝ) < N := by simp only [N]; exact_mod_cast (by omega : 0 < Fintype.card V)
  set A := G.adjMatrix ℝ
  set x : V → ℝ := fun w => (if w = v then 1 else 0) - 1 / N
  have hsum : ∑ i, x i = 0 := by
    simp only [x, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  -- Column sums: `∑_w A w v = d`, and `A w v ^ 2 = A w v`.
  have hcol : ∑ w, A w v = d := by
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simp only [mulVec, dotProduct, Function.const_apply, mul_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [A, SimpleGraph.adjMatrix_apply]
    by_cases hw : G.Adj w v
    · simp [hw, hw.symm]
    · have : ¬ G.Adj v w := fun h => hw h.symm
      simp [hw, this]
  have hAx : ∀ w, (A *ᵥ x) w = A w v - d / N := by
    intro w
    have hdeg := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := w)
    simp only [mulVec, dotProduct, Function.const_apply, mul_one] at hdeg
    simp only [mulVec, dotProduct, x, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul]
    rw [hdeg]
    ring
  have hsq01 : ∀ w, A w v * A w v = A w v := by
    intro w; by_cases hw : G.Adj w v <;> simp [A, SimpleGraph.adjMatrix_apply, hw]
  have hAA : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = d - d ^ 2 / N := by
    have : ∀ w, (A *ᵥ x) w * (A *ᵥ x) w = A w v * (1 - 2 * (d / N)) + (d / N) ^ 2 := by
      intro w; rw [hAx]; nlinarith [hsq01 w]
    rw [dotProduct, Finset.sum_congr rfl fun w _ => this w, Finset.sum_add_distrib,
      ← Finset.sum_mul, hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hxx : x ⬝ᵥ x = 1 - 1 / N := by
    have : ∀ w, x w * x w = (if w = v then 1 else 0) * (1 - 2 / N) + (1 / N) ^ 2 := by
      intro w; by_cases hw : w = v <;> simp [x, hw] <;> ring
    rw [dotProduct, Finset.sum_congr rfl fun w _ => this w, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have key := hb x hsum
  rw [hAA, hxx] at key
  have : (d : ℝ) * (N - d) = N * (d - d ^ 2 / N) := by field_simp
  rw [this]
  have h2 : (d * lam : ℝ) ^ 2 * (N - 1) = N * ((d * lam) ^ 2 * (1 - 1 / N)) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left key hNpos.le

/-- **The complete graph is a spectral expander.** For `N ≥ 2` vertices, the complete graph is a
spectral expander of degree `N - 1` with parameter `λ = 1 / (N - 1)`: its adjacency matrix acts
as `-1` on the vectors orthogonal to the constants, since `(A x)_i = ∑_{j ≠ i} x_j = -x_i` when
`∑_j x_j = 0`. For it the lower bound `mul_sub_le_sq_mul_of_isSpectralExpander` is an equality. -/
theorem isSpectralExpander_top (hN : 2 ≤ Fintype.card V) :
    IsSpectralExpander (⊤ : SimpleGraph V) (Fintype.card V - 1)
      (1 / ((Fintype.card V : ℝ) - 1)) := by
  have hN1 : (1 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 1 < Fintype.card V)
  refine ⟨SimpleGraph.IsRegularOfDegree.top, by
    have : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by linarith
    positivity, ?_⟩
  intro x hx
  have hAx : (⊤ : SimpleGraph V).adjMatrix ℝ *ᵥ x = -x := by
    funext i
    have : ∑ j, (if i = j then 0 else x j) = ∑ j, x j - x i := by
      have h1 : ∀ j, (if i = j then 0 else x j) = x j - if i = j then x j else 0 := by
        intro j; split_ifs <;> simp
      simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply, SimpleGraph.top_adj, ite_not,
      ite_mul, zero_mul, one_mul, Pi.neg_apply]
    rw [this, hx, zero_sub]
  rw [hAx, neg_dotProduct, dotProduct_neg, neg_neg]
  have : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this, mul_one_div_cancel (by linarith), one_pow, one_mul]

/-! ### Random walks from a uniform start -/

omit [DecidableEq V] in
private lemma sum_prod_walk (M : Matrix V V ℝ) (c : ℝ) (hcol : ∀ v, ∑ u, M u v = c) (t : ℕ) :
    ∑ w : Fin (t + 1) → V, ∏ i : Fin t, M (w i.castSucc) (w i.succ) =
      Fintype.card V * c ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero,
      Fin.cons_succ, ← Fin.succ_castSucc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum, ih]
    ring

omit [DecidableEq V] in
/-- **Probability of an event for a random walk on a regular graph.** For a `d`-regular graph `G`
with `d ≥ 1` on a nonempty vertex set, a length `t` and a property `P` of vertex sequences
`(V₀, …, V_t)`, `walkProb G d hreg hd t P` is the probability that the random walk
`V₀, V₁, …, V_t` satisfies `P`, where `V₀` is uniform and each `V_{i+1}` is a uniformly random
neighbour of `V_i`: the sum over all sequences `w` satisfying `P` of
`(1 / N) ∏_{i < t} A(w_i, w_{i+1}) / d` (S. Vadhan, *Pseudorandomness* (2012), Section 4.2,
random walks `V₁, …, V_t` from a uniform start vertex, indexed here from `0`). The hypotheses
make the weights a probability distribution (`walkProb_true`): for a graph that is not
`d`-regular the rows of `A / d` need not sum to `1` (the complete graph on two vertices with
`d = 2` would give the certain event probability `1/2` after one step), and for `d = 0` with a
positive walk length `t`, or for an empty vertex set, every event would have probability `0`. -/
noncomputable def walkProb (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (_hreg : G.IsRegularOfDegree d) (_hd : 0 < d) [Nonempty V] (t : ℕ)
    (P : (Fin (t + 1) → V) → Prop) [DecidablePred P] : ℝ :=
  ∑ w, if P w then (1 / Fintype.card V : ℝ) * ∏ i : Fin t,
    G.adjMatrix ℝ (w i.castSucc) (w i.succ) / d else 0

omit [DecidableEq V] in
/-- **Random-walk probabilities have total mass one.** For a `d`-regular graph with `d ≥ 1` on a
nonempty vertex set, the walk distribution of `walkProb` is a probability distribution: the
certain event has probability `1`. -/
theorem walkProb_true {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hreg : G.IsRegularOfDegree d) (hd : 0 < d) [Nonempty V] (t : ℕ) :
    walkProb G d hreg hd t (fun _ => True) = 1 := by
  have hcol : ∀ v, ∑ u, G.adjMatrix ℝ u v / d = 1 := by
    intro v
    have := G.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg (v := v)
    simp only [mulVec, dotProduct, Function.const_apply, mul_one] at this
    rw [← Finset.sum_div]
    have hsym : ∑ u, G.adjMatrix ℝ u v = ∑ u, G.adjMatrix ℝ v u :=
      Finset.sum_congr rfl fun u _ => by
        simp only [SimpleGraph.adjMatrix_apply, G.adj_comm]
    rw [hsym, this, div_self (by exact_mod_cast hd.ne')]
  simp only [walkProb, ite_true, ← Finset.mul_sum]
  rw [sum_prod_walk (fun u v => G.adjMatrix ℝ u v / d) 1 hcol t, one_pow, mul_one,
    one_div_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)]

end MathlibExt.Combinatorics.SpectralExpander
