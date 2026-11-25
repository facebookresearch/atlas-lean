/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical paths and the spectral gap of a reversible Markov chain

Let `P : Matrix S S ℝ` be a transition matrix on a finite state space `S` and `π : S → ℝ` a
weight (the stationary distribution). Sinclair views a reversible chain as a network whose
oriented edge `e = (u, v)` has capacity `Q(e) = π(u) P(u, v)`, and routes `π(x) π(y)` units
from `x` to `y` along a *canonical path* `γ_xy`, one for each ordered pair of distinct states.
Here a path from `x` is the list `[v₁, …, v_k]` of the states it visits after `x`; its oriented
edges are `(x, v₁), (v₁, v₂), …` (`pathEdges`) and it ends at `pathEnd x [v₁, …, v_k] = v_k`.

## Main definitions

* `pathLoad π γ u v = ∑_{x ≠ y} π(x) π(y) · #{times γ_xy uses (u, v)}`: the flow through the
  oriented edge `(u, v)` (numerator of Sinclair's congestion `ρ(Γ)`, eq. (3)).
* `elongatedPathLoad π γ u v = ∑_{x ≠ y} π(x) π(y) |γ_xy| · #{times γ_xy uses (u, v)}`: the same
  weighted by path lengths (numerator of `ρ̄(Γ)`, eq. (4)).

For the simple paths of the paper an edge is used at most once, so the multiplicity is `0` or `1`
and these are exactly Sinclair's sums; counting multiplicity extends them to arbitrary paths.
Instead of the maxima `ρ(Γ) = max_e pathLoad(e)/Q(e)` and `ρ̄(Γ) = max_e elongatedPathLoad(e)/Q(e)`
the theorems take any bound `B` with `load(e) ≤ B · Q(e)` for every oriented edge `e`; when the
paths only use transitions of positive probability, `ρ(Γ)` (resp. `ρ̄(Γ)`) is such a bound.

## Main results

* `sum_sq_sub_mul_le_of_elongatedPathLoad_le`: **the canonical-path Poincaré inequality**
  (the displayed computation in the proof of Sinclair 1992, Theorem 5):
  `∑_{x,y} (ψ x - ψ y)² π(x) π(y) ≤ B ∑_{x,y} (ψ x - ψ y)² π(x) P(x, y)` for every `ψ : S → ℝ`.
  No reversibility is needed for this inequality.
* `one_le_mul_one_sub_of_poincare`: a Poincaré inequality with constant `B` gives
  `1 ≤ B (1 - μ)` for every real eigenvalue `μ ≠ 1` of a reversible `P` (the variational step of
  Theorems 5 and 5′); `sum_mul_eq_zero_of_eigenvector` supplies the orthogonality to constants.
* `one_le_mul_one_sub_of_eigenvector`: **Sinclair's Theorem 5**. If `P` has unit row sums and is
  reversible with respect to a positive probability vector `π`, every real eigenvalue `μ ≠ 1`
  of `P` satisfies `1 ≤ B (1 - μ)`, i.e. `μ ≤ 1 - 1/B`; so the second eigenvalue satisfies
  `λ₁ ≤ 1 - 1/ρ̄(Γ)`. `le_one_sub_inv_of_eigenvector` states it in that form, and
  `one_le_mul_one_sub_of_eigenvector_of_mean_zero` applies to every eigenvector `π`-orthogonal to
  the constants, `μ = 1` included, so such paths force the eigenvalue `1` to be simple.
* `elongatedPathLoad_le_mul_pathLoad` and `le_one_sub_inv_mul_of_eigenvector`:
  **Corollary 6**, `λ₁ ≤ 1 - 1/(ρ ℓ)` when every path has length at most `ℓ`.
* `mul_sum_compl_le_of_pathLoad_le` and `sum_le_two_mul_of_pathLoad_le`: **the cut bound**
  `π(A) π(Aᶜ) ≤ ρ Q(A, Aᶜ)` (Sinclair 1992, inequality (13)), hence
  `π(A) ≤ 2 ρ Q(A, Aᶜ)` when `π(A) ≤ 1/2`, which is **Theorem 3**: `Φ ≥ 1/(2ρ)`.

Detailed balance is the repository's `ProbabilityTheory.IsDetailedBalance π P`
(`π x * P x y = π y * P y x` for all `x, y`).

## References

* A. Sinclair, "Improved bounds for mixing rates of Markov chains and multicommodity flow",
  *Combinatorics, Probability and Computing* **1** (1992), 351–370: eqs. (3)–(5), Theorem 3,
  Corollary 4, Theorem 5, Corollary 6 and inequality (13).
* P. Diaconis and D. Stroock, "Geometric bounds for eigenvalues of Markov chains",
  *Annals of Applied Probability* **1** (1991), 36–61 (the method Theorem 5 modifies).
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExt.Probability.CanonicalPaths

variable {S : Type*}

/-- **Oriented edges of a path.** The path that starts at `x` and then visits `v₁, …, v_k`
uses the oriented edges `(x, v₁), (v₁, v₂), …, (v_{k-1}, v_k)`. -/
def pathEdges : S → List S → List (S × S)
  | _, [] => []
  | x, v :: l => (x, v) :: pathEdges v l

/-- **Endpoint of a path.** The path that starts at `x` and then visits `v₁, …, v_k` ends at
`v_k` (at `x` itself when it is empty). -/
def pathEnd : S → List S → S
  | x, [] => x
  | _, v :: l => pathEnd v l

/-- **Number of edges of a path.** A path through `k` further states has `k` edges. -/
@[simp] theorem length_pathEdges (x : S) (l : List S) : (pathEdges x l).length = l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons v l ih => simp [pathEdges, ih]

/-- **Telescoping along a path.** The increments `ψ(e⁺) - ψ(e⁻)` of a function along the edges
of a path from `x` sum to `ψ(end) - ψ(x)`. -/
theorem sum_pathEdges_sub (ψ : S → ℝ) (x : S) (l : List S) :
    ((pathEdges x l).map fun e => ψ e.2 - ψ e.1).sum = ψ (pathEnd x l) - ψ x := by
  induction l generalizing x with
  | nil => simp [pathEdges, pathEnd]
  | cons v l ih => simp only [pathEdges, pathEnd, List.map_cons, List.sum_cons, ih]; ring

/-- **A path leaving a set crosses its boundary.** A path that starts in `A` and ends outside
`A` has an edge `(u, v)` with `u ∈ A` and `v ∉ A`. -/
theorem exists_mem_pathEdges_of_mem_of_not_mem (A : Finset S) {x : S} (l : List S)
    (hx : x ∈ A) (hend : pathEnd x l ∉ A) : ∃ e ∈ pathEdges x l, e.1 ∈ A ∧ e.2 ∉ A := by
  induction l generalizing x with
  | nil => exact absurd hx hend
  | cons v l ih =>
    by_cases hv : v ∈ A
    · obtain ⟨e, he, h⟩ := ih hv hend
      exact ⟨e, by simp [pathEdges, he], h⟩
    · exact ⟨(x, v), by simp [pathEdges], hx, hv⟩

/-- **Reindexing a fourfold sum.** In `∑_x ∑_y ∑_u ∑_v F x y u v` the outer and inner pairs of
indices may be exchanged. -/
theorem sum_sum_sum_sum_comm {β : Type*} (s t s' t' : Finset β) (F : β → β → β → β → ℝ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ u ∈ s', ∑ v ∈ t', F x y u v =
      ∑ u ∈ s', ∑ v ∈ t', ∑ x ∈ s, ∑ y ∈ t, F x y u v := by
  calc ∑ x ∈ s, ∑ y ∈ t, ∑ u ∈ s', ∑ v ∈ t', F x y u v
      = ∑ x ∈ s, ∑ u ∈ s', ∑ y ∈ t, ∑ v ∈ t', F x y u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ s', ∑ x ∈ s, ∑ y ∈ t, ∑ v ∈ t', F x y u v := Finset.sum_comm
    _ = ∑ u ∈ s', ∑ x ∈ s, ∑ v ∈ t', ∑ y ∈ t, F x y u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ s', ∑ v ∈ t', ∑ x ∈ s, ∑ y ∈ t, F x y u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable [Fintype S] [DecidableEq S]

/-- **Flow of a path system through an oriented edge.** For canonical paths `γ x y` (a path from
`x` for each ordered pair) and weights `π`, `pathLoad π γ u v = ∑_{x ≠ y} π(x) π(y) m_xy(u, v)`
where `m_xy(u, v)` is the number of times `γ x y` uses the oriented edge `(u, v)`. For simple
paths this is the numerator `∑_{γ_xy ∋ e} π(x) π(y)` of the congestion `ρ(Γ)` (A. Sinclair,
*Combin. Probab. Comput.* 1 (1992), eq. (3)). -/
noncomputable def pathLoad (π : S → ℝ) (γ : S → S → List S) (u v : S) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else π x * π y * ((pathEdges x (γ x y)).count (u, v) : ℝ)

/-- **Length-weighted flow of a path system through an oriented edge.**
`elongatedPathLoad π γ u v = ∑_{x ≠ y} π(x) π(y) |γ_xy| m_xy(u, v)`, with `m_xy(u, v)` the number
of times `γ x y` uses `(u, v)` and `|γ_xy|` its length. For simple paths this is the numerator
`∑_{γ_xy ∋ e} π(x) π(y) |γ_xy|` of `ρ̄(Γ)` (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
eq. (4)). -/
noncomputable def elongatedPathLoad (π : S → ℝ) (γ : S → S → List S) (u v : S) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else
    π x * π y * ((γ x y).length : ℝ) * ((pathEdges x (γ x y)).count (u, v) : ℝ)

/-- **Regrouping a sum over a list of edges.** A sum over a list of oriented edges equals the sum
over all oriented edges `(u, v)` of the multiplicity of `(u, v)` in the list times the summand. -/
theorem sum_map_eq_sum_count (l : List (S × S)) (g : S × S → ℝ) :
    (l.map g).sum = ∑ u, ∑ v, (l.count (u, v) : ℝ) * g (u, v) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [List.map_cons, List.sum_cons, List.count_cons, Nat.cast_add, add_mul,
      Finset.sum_add_distrib, ih, beq_iff_eq, Prod.mk.injEq]
    rw [add_comm]
    congr 1
    simp [Nat.cast_ite, ite_and]

/-- **Cauchy–Schwarz for a list.** For a list `l` and `f` real-valued,
`(∑_{a ∈ l} f a)² ≤ |l| · ∑_{a ∈ l} (f a)²`. -/
theorem sq_sum_map_le {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum ^ 2 ≤ l.length * (l.map fun a => f a ^ 2).sum := by
  rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem]
  simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin l.length)))
    (f := fun i => f l[i.1])

/-- **The canonical-path Poincaré inequality** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
the computation in the proof of Theorem 5, following Diaconis and Stroock). Let `π ≥ 0`, let
`γ x y` be a path from `x` to `y` for each pair `x ≠ y`, and let `B` bound the length-weighted
load of every oriented edge by `B` times its capacity `π(u) P(u, v)` (`B = ρ̄(Γ)` in the paper).
Then for every `ψ : S → ℝ`,
`∑_{x,y} (ψ x - ψ y)² π(x) π(y) ≤ B ∑_{x,y} (ψ x - ψ y)² π(x) P(x, y)`. -/
theorem sum_sq_sub_mul_le_of_elongatedPathLoad_le {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (P : Matrix S S ℝ) (γ : S → S → List S) (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y)
    {B : ℝ} (hB : ∀ u v, elongatedPathLoad π γ u v ≤ B * (π u * P u v)) (ψ : S → ℝ) :
    ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y) := by
  -- Step 1: Cauchy–Schwarz along each path.
  have step1 : ∀ x y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      if x = y then 0 else π x * π y * ((γ x y).length : ℝ) *
        ∑ u, ∑ v, ((pathEdges x (γ x y)).count (u, v) : ℝ) * (ψ v - ψ u) ^ 2 := by
    intro x y
    split_ifs with hxy
    · simp [hxy]
    · have htel := sum_pathEdges_sub ψ x (γ x y)
      rw [hγ x y hxy] at htel
      have hcs := sq_sum_map_le (pathEdges x (γ x y)) (fun e => ψ e.2 - ψ e.1)
      rw [htel, length_pathEdges, sum_map_eq_sum_count] at hcs
      have hsq : (ψ x - ψ y) ^ 2 = (ψ y - ψ x) ^ 2 := by ring
      rw [hsq]
      have hpos : 0 ≤ π x * π y := mul_nonneg (hπ x) (hπ y)
      calc (ψ y - ψ x) ^ 2 * (π x * π y)
          ≤ (((γ x y).length : ℝ) * ∑ u, ∑ v,
              ((pathEdges x (γ x y)).count (u, v) : ℝ) * (ψ v - ψ u) ^ 2) * (π x * π y) :=
            mul_le_mul_of_nonneg_right hcs hpos
        _ = _ := by ring
  -- Step 2: exchange the order of summation.
  have step2 : ∑ x, ∑ y, (if x = y then (0 : ℝ) else π x * π y * ((γ x y).length : ℝ) *
        ∑ u, ∑ v, ((pathEdges x (γ x y)).count (u, v) : ℝ) * (ψ v - ψ u) ^ 2) =
      ∑ u, ∑ v, (ψ v - ψ u) ^ 2 * elongatedPathLoad π γ u v := by
    calc _ = ∑ x, ∑ y, ∑ u, ∑ v, (ψ v - ψ u) ^ 2 * (if x = y then (0 : ℝ) else
            π x * π y * ((γ x y).length : ℝ) * ((pathEdges x (γ x y)).count (u, v) : ℝ)) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          split_ifs
          · simp
          · simp only [Finset.mul_sum]
            exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      _ = ∑ u, ∑ v, ∑ x, ∑ y, (ψ v - ψ u) ^ 2 * (if x = y then (0 : ℝ) else
            π x * π y * ((γ x y).length : ℝ) * ((pathEdges x (γ x y)).count (u, v) : ℝ)) :=
          sum_sum_sum_sum_comm _ _ _ _ _
      _ = _ := by simp only [elongatedPathLoad, Finset.mul_sum]
  -- Step 3: compare each edge load with its capacity.
  have step3 : ∑ u, ∑ v, (ψ v - ψ u) ^ 2 * elongatedPathLoad π γ u v ≤
      ∑ u, ∑ v, (ψ v - ψ u) ^ 2 * (B * (π u * P u v)) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (hB u v) (sq_nonneg _)
  calc ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y)
      ≤ ∑ x, ∑ y, (if x = y then (0 : ℝ) else π x * π y * ((γ x y).length : ℝ) *
          ∑ u, ∑ v, ((pathEdges x (γ x y)).count (u, v) : ℝ) * (ψ v - ψ u) ^ 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => step1 x y
    _ = ∑ u, ∑ v, (ψ v - ψ u) ^ 2 * elongatedPathLoad π γ u v := step2
    _ ≤ ∑ u, ∑ v, (ψ v - ψ u) ^ 2 * (B * (π u * P u v)) := step3
    _ = B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring

omit [DecidableEq S] in
/-- **A Poincaré inequality bounds the spectral gap, for an eigenvector orthogonal to constants.**
Let `P` have unit row sums and satisfy detailed balance with respect to a positive probability
vector `π`, and suppose the Poincaré inequality
`∑_{x,y} (ψ x - ψ y)² π(x) π(y) ≤ B ∑_{x,y} (ψ x - ψ y)² π(x) P(x, y)` holds for every `ψ`.
Then a nonzero real eigenvector `f` of `P` with eigenvalue `μ` and `π`-mean zero
(`∑ π(x) f(x) = 0`) satisfies `1 ≤ B (1 - μ)`. This is the step of A. Sinclair, *Combin. Probab.
Comput.* 1 (1992), proof of Theorem 5, that inserts an eigenvector into the variational
characterisation (5): the two sides are `2 ∑ π f²` and `2 (1 - μ) ∑ π f²`. -/
theorem one_le_mul_one_sub_of_poincare_of_mean_zero {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) {B : ℝ}
    (hpoin : ∀ ψ : S → ℝ, ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hmean : ∑ x, π x * f x = 0) :
    1 ≤ B * (1 - μ) := by
  have hPf : ∀ x, ∑ y, P x y * f y = μ * f x := by
    intro x
    have := congrFun heig x
    simpa [mulVec, dotProduct] using this
  set V := ∑ x, π x * f x ^ 2 with hV
  -- Variance: `∑_{x,y} (f x - f y)² π x π y = 2 V`.
  have hvar : ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * π y) = 2 * V := by
    have e : ∀ x y, (f x - f y) ^ 2 * (π x * π y) =
        π y * (π x * f x ^ 2) + π x * (π y * f y ^ 2) - 2 * ((π x * f x) * (π y * f y)) := by
      intro x y; ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hπ1, hmean]
    rw [hV]; ring
  -- Dirichlet form: `∑_{x,y} (f x - f y)² π x P x y = 2 (1 - μ) V`.
  have hdir : ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y) = 2 * (1 - μ) * V := by
    have e : ∀ x y, (f x - f y) ^ 2 * (π x * P x y) =
        π x * f x ^ 2 * P x y + f y ^ 2 * (π y * P y x) - 2 * (π x * f x) * (P x y * f y) := by
      intro x y; rw [← hrev x y]; ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hrow,
      hPf]
    have h2 : ∑ x, ∑ y, f y ^ 2 * (π y * P y x) = V := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, hrow]; ring
    rw [h2, hV]
    simp only [mul_one]
    have h3 : ∑ x, 2 * (π x * f x) * (μ * f x) = 2 * μ * ∑ x, π x * f x ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
    rw [h3]; ring
  have hpoin := hpoin f
  rw [hvar, hdir] at hpoin
  have hVpos : 0 < V := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
    exact Finset.sum_pos' (fun y _ => mul_nonneg (hπ y).le (sq_nonneg _))
      ⟨x, Finset.mem_univ _, mul_pos (hπ x) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hx).symm)⟩
  nlinarith

omit [DecidableEq S] in
/-- **Eigenvectors for eigenvalues other than `1` have mean zero.** If `P` has unit row sums and
satisfies detailed balance with respect to `π` (so `π` is stationary), then every eigenvector `f`
of `P` whose eigenvalue `μ` is not `1` satisfies `∑ π(x) f(x) = 0`: it is orthogonal to the
constants in the `π`-weighted inner product, as used in A. Sinclair, *Combin. Probab. Comput.* 1
(1992), proof of Theorem 5. -/
theorem sum_mul_eq_zero_of_eigenvector {π : S → ℝ} {P : Matrix S S ℝ}
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : IsDetailedBalance π P) {μ : ℝ}
    {f : S → ℝ} (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) : ∑ x, π x * f x = 0 := by
  -- `π` is stationary, so `∑ π (P f) = ∑ π f`, while `P f = μ f`.
  have hstat : ∑ x, π x * (P *ᵥ f) x = ∑ y, π y * f y := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∑ x, π x * (P x y * f y) = f y * ∑ x, π y * P y x := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hrev x y]; ring
    rw [this, ← Finset.mul_sum, hrow]; ring
  rw [heig] at hstat
  simp only [Pi.smul_apply, smul_eq_mul] at hstat
  have : (μ - 1) * ∑ x, π x * f x = 0 := by
    have e : (μ - 1) * ∑ x, π x * f x = ∑ x, π x * (μ * f x) - ∑ x, π x * f x := by
      rw [sub_mul, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e, hstat, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμ)

omit [DecidableEq S] in
/-- **A Poincaré inequality bounds the spectral gap.** Let `P` have unit row sums and satisfy
detailed balance with respect to a positive probability vector `π`, and suppose
`∑_{x,y} (ψ x - ψ y)² π(x) π(y) ≤ B ∑_{x,y} (ψ x - ψ y)² π(x) P(x, y)` for every `ψ`. Then every
real eigenvalue `μ ≠ 1` of `P` satisfies `1 ≤ B (1 - μ)`. This is how A. Sinclair, *Combin.
Probab. Comput.* 1 (1992), proves Theorems 5 and 5′ from the variational characterisation (5). -/
theorem one_le_mul_one_sub_of_poincare {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) {B : ℝ}
    (hpoin : ∀ ψ : S → ℝ, ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) :
    1 ≤ B * (1 - μ) :=
  one_le_mul_one_sub_of_poincare_of_mean_zero hπ hπ1 hrow hrev hpoin hf heig
    (sum_mul_eq_zero_of_eigenvector hrow hrev heig hμ)

/-- **Canonical paths bound the spectral gap, for an eigenvector orthogonal to constants.**
Under the hypotheses of `one_le_mul_one_sub_of_eigenvector`, a nonzero real eigenvector `f`
of `P` with eigenvalue `μ` and `π`-mean zero (`∑ π(x) f(x) = 0`) satisfies `1 ≤ B (1 - μ)`
(A. Sinclair, *Combin. Probab. Comput.* 1 (1992), proof of Theorem 5). Applied with `μ = 1`, it
shows that such a path system forces the eigenvalue `1` to be simple. -/
theorem one_le_mul_one_sub_of_eigenvector_of_mean_zero {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) (γ : S → S → List S)
    (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y) {B : ℝ}
    (hB : ∀ u v, elongatedPathLoad π γ u v ≤ B * (π u * P u v)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hmean : ∑ x, π x * f x = 0) :
    1 ≤ B * (1 - μ) :=
  one_le_mul_one_sub_of_poincare_of_mean_zero hπ hπ1 hrow hrev
    (sum_sq_sub_mul_le_of_elongatedPathLoad_le (fun x => (hπ x).le) P γ hγ hB) hf heig hmean

/-- **Sinclair's canonical-path bound on the spectral gap** (A. Sinclair, *Combin. Probab.
Comput.* 1 (1992), Theorem 5). Let `P` have unit row sums and satisfy detailed balance
`π(x) P(x, y) = π(y) P(y, x)` with respect to a positive probability vector `π`. Let `γ x y` be
a path from `x` to `y` for each pair `x ≠ y`, and let `B` bound every length-weighted edge load
by `B · π(u) P(u, v)` (`B = ρ̄(Γ)`). Then every real eigenvalue `μ ≠ 1` of `P` satisfies
`1 ≤ B (1 - μ)`: the spectral gap is at least `1/ρ̄(Γ)`. -/
theorem one_le_mul_one_sub_of_eigenvector {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) (γ : S → S → List S)
    (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y) {B : ℝ}
    (hB : ∀ u v, elongatedPathLoad π γ u v ≤ B * (π u * P u v)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) :
    1 ≤ B * (1 - μ) :=
  one_le_mul_one_sub_of_poincare hπ hπ1 hrow hrev
    (sum_sq_sub_mul_le_of_elongatedPathLoad_le (fun x => (hπ x).le) P γ hγ hB) hf heig hμ

/-- **Theorem 5 in the form `μ ≤ 1 - 1/ρ̄`** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
Theorem 5): with the hypotheses of `one_le_mul_one_sub_of_eigenvector` and `0 < B`, every real
eigenvalue `μ ≠ 1` of `P` satisfies `μ ≤ 1 - 1/B`. -/
theorem le_one_sub_inv_of_eigenvector {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) (γ : S → S → List S)
    (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ u v, elongatedPathLoad π γ u v ≤ B * (π u * P u v)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) :
    μ ≤ 1 - 1 / B := by
  have h := one_le_mul_one_sub_of_eigenvector hπ hπ1 hrow hrev γ hγ hB hf heig hμ
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hB0]
  linarith

/-- **Length-weighted load versus load** (the observation behind A. Sinclair, *Combin. Probab.
Comput.* 1 (1992), Corollary 6). If every path `γ x y` (`x ≠ y`) has at most `ℓ` edges and
`π ≥ 0`, the length-weighted load of each edge is at most `ℓ` times its load. -/
theorem elongatedPathLoad_le_mul_pathLoad {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (γ : S → S → List S) {ℓ : ℕ} (hℓ : ∀ x y, x ≠ y → (γ x y).length ≤ ℓ) (u v : S) :
    elongatedPathLoad π γ u v ≤ ℓ * pathLoad π γ u v := by
  simp only [elongatedPathLoad, pathLoad, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  split_ifs with hxy
  · simp
  · have hl : ((γ x y).length : ℝ) ≤ ℓ := by exact_mod_cast hℓ x y hxy
    have h0 : 0 ≤ π x * π y * ((pathEdges x (γ x y)).count (u, v) : ℝ) :=
      mul_nonneg (mul_nonneg (hπ x) (hπ y)) (Nat.cast_nonneg _)
    nlinarith

/-- **Sinclair's Corollary 6: `λ₁ ≤ 1 - 1/(ρ ℓ)`** (A. Sinclair, *Combin. Probab. Comput.* 1
(1992), Corollary 6). Under the hypotheses of `one_le_mul_one_sub_of_eigenvector`, if every
path has at most `ℓ` edges and every edge load is at most `ρ · π(u) P(u, v)` with `0 < ρ ℓ`,
then every real eigenvalue `μ ≠ 1` of `P` satisfies `μ ≤ 1 - 1/(ρ ℓ)`. -/
theorem le_one_sub_inv_mul_of_eigenvector {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) (γ : S → S → List S)
    (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y) {ℓ : ℕ}
    (hℓ : ∀ x y, x ≠ y → (γ x y).length ≤ ℓ) {ρ : ℝ} (hρℓ : 0 < ρ * ℓ)
    (hρ : ∀ u v, pathLoad π γ u v ≤ ρ * (π u * P u v)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) :
    μ ≤ 1 - 1 / (ρ * ℓ) := by
  refine le_one_sub_inv_of_eigenvector hπ hπ1 hrow hrev γ hγ hρℓ (fun u v => ?_) hf heig hμ
  calc elongatedPathLoad π γ u v ≤ ℓ * pathLoad π γ u v :=
        elongatedPathLoad_le_mul_pathLoad (fun x => (hπ x).le) γ hℓ u v
    _ ≤ ℓ * (ρ * (π u * P u v)) :=
        mul_le_mul_of_nonneg_left (hρ u v) (Nat.cast_nonneg _)
    _ = ρ * ℓ * (π u * P u v) := by ring

/-- **Paths crossing a cut** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992), proof of
Theorem 3). If `γ x y` runs from `x` to `y` for `x ≠ y` and `π ≥ 0`, then
`π(A) π(Aᶜ) ≤ ∑_{u ∈ A, v ∉ A} pathLoad π γ u v`: all flow from `A` to its complement crosses
the cut. -/
theorem mul_sum_compl_le_sum_pathLoad {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (γ : S → S → List S)
    (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y) (A : Finset S) :
    (∑ x ∈ A, π x) * (∑ y ∈ Aᶜ, π y) ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, pathLoad π γ u v := by
  set c : S → S → ℝ := fun x y =>
    ∑ u ∈ A, ∑ v ∈ Aᶜ, ((pathEdges x (γ x y)).count (u, v) : ℝ) with hc
  have hc0 : ∀ x y, 0 ≤ c x y := fun x y =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hc1 : ∀ x ∈ A, ∀ y ∈ Aᶜ, 1 ≤ c x y := by
    intro x hx y hy
    have hxy : x ≠ y := by rintro rfl; simp_all
    have hend : pathEnd x (γ x y) ∉ A := by rw [hγ x y hxy]; simpa using hy
    obtain ⟨⟨u, v⟩, he, hu, hv⟩ := exists_mem_pathEdges_of_mem_of_not_mem A (γ x y) hx hend
    have hcount : (1 : ℝ) ≤ ((pathEdges x (γ x y)).count (u, v) : ℝ) := by
      exact_mod_cast List.count_pos_iff.mpr he
    calc (1 : ℝ) ≤ ((pathEdges x (γ x y)).count (u, v) : ℝ) := hcount
      _ ≤ ∑ v' ∈ Aᶜ, ((pathEdges x (γ x y)).count (u, v') : ℝ) :=
          Finset.single_le_sum (f := fun v' => ((pathEdges x (γ x y)).count (u, v') : ℝ))
            (fun _ _ => Nat.cast_nonneg _) (by simpa using hv)
      _ ≤ c x y :=
          Finset.single_le_sum (f := fun u' => ∑ v' ∈ Aᶜ,
            ((pathEdges x (γ x y)).count (u', v') : ℝ))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hu
  have key : ∑ u ∈ A, ∑ v ∈ Aᶜ, pathLoad π γ u v =
      ∑ x, ∑ y, if x = y then 0 else π x * π y * c x y := by
    simp only [pathLoad]
    rw [sum_sum_sum_sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · simp
    · simp only [hc, Finset.mul_sum]
  rw [key, Finset.sum_mul_sum]
  calc ∑ x ∈ A, ∑ y ∈ Aᶜ, π x * π y
      ≤ ∑ x ∈ A, ∑ y ∈ Aᶜ, (if x = y then 0 else π x * π y * c x y) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        have hxy : x ≠ y := by rintro rfl; simp_all
        simp only [hxy, ↓reduceIte]
        have := hc1 x hx y hy
        have h0 := mul_nonneg (hπ x) (hπ y)
        nlinarith
    _ ≤ ∑ x, ∑ y, (if x = y then 0 else π x * π y * c x y) := by
        have hnn : ∀ x y, 0 ≤ (if x = y then (0 : ℝ) else π x * π y * c x y) := by
          intro x y; split_ifs
          · exact le_rfl
          · exact mul_nonneg (mul_nonneg (hπ x) (hπ y)) (hc0 x y)
        calc ∑ x ∈ A, ∑ y ∈ Aᶜ, (if x = y then 0 else π x * π y * c x y)
            ≤ ∑ x ∈ A, ∑ y, (if x = y then 0 else π x * π y * c x y) :=
              Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_univ _) fun y _ _ => hnn x y
          _ ≤ ∑ x, ∑ y, (if x = y then 0 else π x * π y * c x y) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                fun x _ _ => Finset.sum_nonneg fun y _ => hnn x y

/-- **The cut bound `π(A) π(Aᶜ) ≤ ρ Q(A, Aᶜ)`** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
inequality (13): `Φ' ≥ 1/ρ`, the trivial direction of max-flow min-cut). If `γ x y` runs from `x`
to `y` for `x ≠ y`, `π ≥ 0`, and every edge load is at most `ρ · π(u) P(u, v)`, then for every
set `A`, `π(A) π(Aᶜ) ≤ ρ ∑_{u ∈ A, v ∉ A} π(u) P(u, v)`. -/
theorem mul_sum_compl_le_of_pathLoad_le {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (P : Matrix S S ℝ)
    (γ : S → S → List S) (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y) {ρ : ℝ}
    (hρ : ∀ u v, pathLoad π γ u v ≤ ρ * (π u * P u v)) (A : Finset S) :
    (∑ x ∈ A, π x) * (∑ y ∈ Aᶜ, π y) ≤ ρ * ∑ u ∈ A, ∑ v ∈ Aᶜ, π u * P u v := by
  refine (mul_sum_compl_le_sum_pathLoad hπ γ hγ A).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun v _ => hρ u v

/-- **Sinclair's Theorem 3: `Φ ≥ 1/(2ρ)`** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
Theorem 3), set by set. With the hypotheses of `mul_sum_compl_le_of_pathLoad_le`, if `π` is a
probability vector and `π(A) ≤ 1/2`, then `π(A) ≤ 2 ρ Q(A, Aᶜ)` where
`Q(A, Aᶜ) = ∑_{u ∈ A, v ∉ A} π(u) P(u, v)`; that is, `Q(A, Aᶜ)/π(A) ≥ 1/(2ρ)` whenever
`0 < π(A) ≤ 1/2`. -/
theorem sum_le_two_mul_of_pathLoad_le {π : S → ℝ} (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (P : Matrix S S ℝ) (γ : S → S → List S) (hγ : ∀ x y, x ≠ y → pathEnd x (γ x y) = y)
    {ρ : ℝ} (hρ : ∀ u v, pathLoad π γ u v ≤ ρ * (π u * P u v)) (A : Finset S)
    (hA : ∑ x ∈ A, π x ≤ 1 / 2) :
    ∑ x ∈ A, π x ≤ 2 * (ρ * ∑ u ∈ A, ∑ v ∈ Aᶜ, π u * P u v) := by
  have h := mul_sum_compl_le_of_pathLoad_le hπ P γ hγ hρ A
  have hsplit : ∑ y ∈ Aᶜ, π y = 1 - ∑ x ∈ A, π x := by
    rw [← hπ1, ← Finset.sum_add_sum_compl A π]; ring
  rw [hsplit] at h
  have h0 : 0 ≤ ∑ x ∈ A, π x := Finset.sum_nonneg fun x _ => hπ x
  nlinarith

end MathlibExt.Probability.CanonicalPaths
