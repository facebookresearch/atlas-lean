/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
public import CSLibExt.Bioinformatics.Phylogenetics.Parsimony
public import CSLibExt.MachineLearning.Sampling.MonteCarlo
public import MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-!
# The pulley principle, LogDet distances, the Felsenstein zone, and consistency of NJ

Four classical facts about tree reconstruction from sequences.

**The pulley principle** (Felsenstein 1981). For a substitution model whose transition matrices
`P t` satisfy the Chapman–Kolmogorov equation `P s * P t = P (s + t)` and detailed balance
`π a P t a b = π b P t b a` with the root distribution `π`, the Felsenstein likelihood does not
change when the root slides along the edge it sits on (`likelihood_slide`) or moves across a
vertex onto an adjacent edge (`likelihood_reroot`); together with swapping the two subtrees of
the root (`likelihood_node_comm`) these moves reach every placement of the root on the same
unrooted tree with the same edge lengths (swapping subtrees below the root is
`prune_node_comm`), so the likelihood depends only on the unrooted tree.
Unrooted trees themselves are not formalized here. Every reversible continuous-time model
(`IsDetailedBalance π Q`, e.g. GTR) gives such a family (`isReversibleSemigroup_ctmcTransition`).

**LogDet / paralinear distances** (Steel 1994; Lockhart, Steel, Hendy & Penny 1994; Lake 1994).
For a joint distribution matrix `F i j = ℙ(X = i, Y = j)` of the states at two vertices, with
diagonal marginal matrices `Π_X`, `Π_Y`, set
`paralinear F = -log |det F| + (log det Π_X + log det Π_Y) / 2`. Under the general Markov model
with nonsingular transition matrices, the distance is additive along paths
(`paralinear_threePoint`, `paralinear_chain_step`, `paralinear_pathProd`). Lake's paralinear
distance is this quantity divided by the number of states.

**The Felsenstein zone** (Felsenstein 1978). On the quartet `((A, B), (C, D))` under the
symmetric two-state model, with change probability `P` on the two non-sister branches to `A` and
`C` and `Q` on the other three, the expected frequency of the patterns supporting the wrong
split `AC | BD` minus that of the true split `AB | CD` is exactly
`(1 - 2 Q) (P ^ 2 - Q (1 - Q))` (`splitFreq_wrong_sub_true`; Felsenstein's equations (16)–(17),
whose consistency condition for `Q < 1/2` is `P ^ 2 < Q (1 - Q)`, his (18)). Hence in the region
`P ^ 2 > Q (1 - Q)` with `0 ≤ Q < 1/2` the wrong quartet has the strictly smallest expected
Fitch parsimony score (`expectedScore_wrong_lt`), and with independent sites parsimony chooses
the wrong tree for all long enough alignments, almost surely (`ae_eventually_parsimony_wrong`):
it is statistically inconsistent.

**Consistency of neighbor joining under Jukes–Cantor** (Jukes & Cantor 1969; Saitou & Nei 1987;
Atteson 1999). Along a path with branch lengths `t₁, …, t_k` the JC transition matrices multiply
to the matrix of length `t₁ + ⋯ + t_k` (`jcPath_eq`), so the JC-corrected difference
probability of two leaves is `μ` times their path length (`jcDistance_jcPath`). With independent
sites, the empirical p-distances converge almost surely (strong law), hence so do the corrected
distances; if neighbor joining recovers the tree from every dissimilarity within a radius
`r > 0` of the scaled tree metric (for `μ > 0`, Atteson's theorem gives `r = μ m / 2` for the
shortest internal edge length `m`; it is not proved in this library), then almost surely every
complete run of neighbor joining on the corrected empirical distances returns the true splits
for all long enough alignments (`ae_eventually_njRun_splits_jcHat`).

## Main results

* `likelihood_slide`, `likelihood_reroot`, `likelihood_node_comm`: the pulley principle.
* `paralinear_threePoint`, `paralinear_pathProd`: additivity of the LogDet distance.
* `splitFreq_wrong_sub_true`, `expectedScore_wrong_lt`, `ae_eventually_parsimony_wrong`: the
  Felsenstein zone and the inconsistency of parsimony.
* `jcDistance_jcPath`, `ae_eventually_njRun_splits_jcHat`: JC-corrected distances are path
  lengths, and neighbor joining on them is statistically consistent given a robustness radius.

## References

* J. Felsenstein, *Cases in which parsimony or compatibility methods will be positively
  misleading*, Syst. Zool. 27 (1978), 401–410.
* J. Felsenstein, *Evolutionary trees from DNA sequences: a maximum likelihood approach*,
  J. Mol. Evol. 17 (1981), 368–376.
* M. A. Steel, *Recovering a tree from the leaf colourations it generates under a Markov model*,
  Appl. Math. Lett. 7 (1994), 19–23.
* P. J. Lockhart, M. A. Steel, M. D. Hendy and D. Penny, *Recovering evolutionary trees under a
  more realistic model of sequence evolution*, Mol. Biol. Evol. 11 (1994), 605–612.
* J. A. Lake, *Reconstructing evolutionary trees from DNA and protein sequences: paralinear
  distances*, Proc. Natl. Acad. Sci. USA 91 (1994), 1455–1459.
* T. H. Jukes and C. R. Cantor, *Evolution of protein molecules*, in Mammalian Protein
  Metabolism, Academic Press, 1969, 21–132.
* N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing
  phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
* K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*,
  Algorithmica 25 (1999), 251–278.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Phylogenetics.FelsensteinZone

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
open FelsensteinPruning Tree

/-! ## The pulley principle -/

section Pulley

variable {L : Type*} {S : Type*} [Fintype S]

/-- A family of transition matrices `P t`, indexed by branch length, is a **reversible
semigroup** for the distribution `π`: it satisfies the Chapman–Kolmogorov equation and detailed
balance `π a P t a b = π b P t b a`. With rows summing to `1`, detailed balance makes `π`
stationary; the pulley principle uses only the two equations below. -/
structure IsReversibleSemigroup (π : S → ℝ) (P : ℝ → S → S → ℝ) : Prop where
  /-- The Chapman–Kolmogorov equation `P s * P t = P (s + t)`. -/
  chapman_kolmogorov : ∀ s t a c, ∑ b, P s a b * P t b c = P (s + t) a c
  /-- Detailed balance with `π`. -/
  detailed_balance : ∀ t a b, π a * P t a b = π b * P t b a

/-- Swapping the two subtrees of a node does not change its partial likelihoods; with
`likelihood_node_comm` this lets the rerooting move `likelihood_reroot` reach either child. -/
theorem prune_node_comm (obs : L → S → ℝ) (P Q : S → S → ℝ) (l r : Tree L S ℝ) :
    prune obs (node P l Q r) = prune obs (node Q r P l) := by
  funext s
  simp only [prune, mul_comm]

/-- Swapping the two subtrees of the root does not change the likelihood. -/
theorem likelihood_node_comm (obs : L → S → ℝ) (P Q : S → S → ℝ) (l r : Tree L S ℝ)
    (π : S → ℝ) : likelihood obs (node P l Q r) π = likelihood obs (node Q r P l) π := by
  simp only [likelihood_eq_sum_prune, prune, mul_comm (∑ a, P _ a * prune obs l a)]

private lemma sum_detailed_balance {π : S → ℝ} {P : ℝ → S → S → ℝ}
    (hP : IsReversibleSemigroup π P) (u W : S → ℝ) (a : ℝ) :
    ∑ x, π x * (∑ y, P a x y * u y) * W x = ∑ y, π y * u y * ∑ x, P a y x * W x := by
  have lhs : ∀ x, π x * (∑ y, P a x y * u y) * W x = ∑ y, π y * u y * (P a y x * W x) :=
    fun x => by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      linear_combination (u y * W x) * hP.detailed_balance a x y
  calc ∑ x, π x * (∑ y, P a x y * u y) * W x = ∑ x, ∑ y, π y * u y * (P a y x * W x) :=
        Finset.sum_congr rfl fun x _ => lhs x
    _ = ∑ y, ∑ x, π y * u y * (P a y x * W x) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm

private lemma sum_root_edge {π : S → ℝ} {P : ℝ → S → S → ℝ} (hP : IsReversibleSemigroup π P)
    (u v : S → ℝ) (s t : ℝ) :
    ∑ a, π a * ((∑ b, P s a b * u b) * ∑ c, P t a c * v c) =
      ∑ b, π b * u b * ∑ c, P (s + t) b c * v c := by
  have h : ∀ b, ∑ c, P (s + t) b c * v c = ∑ a, P s b a * ∑ c, P t a c * v c := fun b => by
    simp only [← hP.chapman_kolmogorov, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  simp only [h, ← sum_detailed_balance hP u (fun a => ∑ c, P t a c * v c) s]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The root can be pushed to the end of its edge**: with the root on the edge between the
subtrees `l` and `r`, at distances `s` and `t`, the likelihood is that of the root placed at the
root of `l`, with `r` at distance `s + t`. -/
theorem likelihood_node_eq {π : S → ℝ} {P : ℝ → S → S → ℝ} (hP : IsReversibleSemigroup π P)
    (obs : L → S → ℝ) (l r : Tree L S ℝ) (s t : ℝ) :
    likelihood obs (node (P s) l (P t) r) π =
      ∑ b, π b * prune obs l b * ∑ c, P (s + t) b c * prune obs r c := by
  rw [likelihood_eq_sum_prune]
  exact sum_root_edge hP _ _ s t

/-- **Pulley principle, sliding**: moving the root along its edge does not change the
likelihood (Felsenstein 1981). -/
theorem likelihood_slide {π : S → ℝ} {P : ℝ → S → S → ℝ} (hP : IsReversibleSemigroup π P)
    (obs : L → S → ℝ) (l r : Tree L S ℝ) {s t s' t' : ℝ} (h : s + t = s' + t') :
    likelihood obs (node (P s) l (P t) r) π = likelihood obs (node (P s') l (P t') r) π := by
  rw [likelihood_node_eq hP, likelihood_node_eq hP, h]

/-- **Pulley principle, rerooting**: let the root sit on the edge between an internal vertex `x`
(at distance `s₁`) and the subtree `C` (at distance `s₂`), where `x` has the subtrees `A` and
`B` at distances `a` and `b`. Moving the root to the edge between `x` and `A`, at distance `u₁`
from `A` and `u₂` from `x` with `u₁ + u₂ = a`, gives the same likelihood: the unrooted tree and
its edge lengths are unchanged (Felsenstein 1981). -/
theorem likelihood_reroot {π : S → ℝ} {P : ℝ → S → S → ℝ} (hP : IsReversibleSemigroup π P)
    (obs : L → S → ℝ) (A B C : Tree L S ℝ) {s₁ s₂ a b u₁ u₂ : ℝ} (hu : u₁ + u₂ = a) :
    likelihood obs (node (P s₁) (node (P a) A (P b) B) (P s₂) C) π =
      likelihood obs (node (P u₁) A (P u₂) (node (P b) B (P (s₁ + s₂)) C)) π := by
  rw [likelihood_node_eq hP, likelihood_node_eq hP, hu]
  simp only [prune]
  rw [← sum_detailed_balance hP (prune obs A)
    (fun x => (∑ z, P b x z * prune obs B z) * ∑ c, P (s₁ + s₂) x c * prune obs C c) a]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- A reversible continuous-time model gives a reversible semigroup: if `π` is in detailed
balance with the generator `Q`, the transition functions `exp (t • Q)` form a reversible
semigroup for `π`. -/
theorem isReversibleSemigroup_ctmcTransition [DecidableEq S] {π : S → ℝ} {Q : Matrix S S ℝ}
    (h : IsDetailedBalance π Q) :
    IsReversibleSemigroup π (fun t => ctmcTransition Q t) where
  chapman_kolmogorov s t a c := by
    rw [ctmcTransition_add, Matrix.mul_apply]
  detailed_balance t := h.ctmcTransition t

end Pulley

/-! ## LogDet / paralinear distances -/

section LogDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **LogDet (paralinear) distance** of a joint distribution matrix `F`
(`F i j = ℙ(X = i, Y = j)`): `-log |det F| + (log det Π_X + log det Π_Y) / 2`, where the
diagonal marginal matrices have determinants `∏ i, ∑ j, F i j` and `∏ j, ∑ i, F i j`. It is a
distance only when `det F ≠ 0` and the marginals are positive; otherwise the value is Lean's
totalized logarithm (`log 0 = 0`). -/
noncomputable def paralinear (F : Matrix ι ι ℝ) : ℝ :=
  -Real.log |F.det| + (Real.log (∏ i, ∑ j, F i j) + Real.log (∏ j, ∑ i, F i j)) / 2

/-- The distance of a vertex to itself is `0`: the joint distribution of `X` with itself is the
diagonal matrix of its (positive) marginal. -/
theorem paralinear_diagonal {p : ι → ℝ} (hp : ∀ i, 0 < p i) : paralinear (diagonal p) = 0 := by
  have hpr : 0 < ∏ i, p i := Finset.prod_pos fun i _ => hp i
  have hr : ∀ i, ∑ j, diagonal p i j = p i := fun i => by simp [diagonal_apply]
  have hc : ∀ j, ∑ i, diagonal p i j = p j := fun j => by simp [diagonal_apply]
  simp only [paralinear, det_diagonal, hr, hc, abs_of_pos hpr]
  ring

private lemma rowSum_diagonal_mul (p : ι → ℝ) (A : Matrix ι ι ℝ) (i : ι) :
    ∑ j, (diagonal p * A) i j = p i * ∑ j, A i j := by
  simp [diagonal_mul, Finset.mul_sum]

private lemma colSum_diagonal_mul (p : ι → ℝ) (A : Matrix ι ι ℝ) (j : ι) :
    ∑ i, (diagonal p * A) i j = (p ᵥ* A) j := by
  simp [diagonal_mul, vecMul, dotProduct]

omit [DecidableEq ι] in
private lemma rowSum_mul {A B : Matrix ι ι ℝ} (hA : ∀ i, ∑ j, A i j = 1)
    (hB : ∀ i, ∑ j, B i j = 1) (i : ι) : ∑ j, (A * B) i j = 1 := by
  simp only [mul_apply]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hB, hA]

private lemma log_abs_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log |a * b| = Real.log |a| + Real.log |b| := by
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb)]

/-- Under a nonnegative, nonsingular transition matrix, a positive distribution stays positive:
every column of `M` has a positive entry. This puts the LogDet logarithms in their domain. -/
theorem vecMul_pos {p : ι → ℝ} (hp : ∀ i, 0 < p i) {M : Matrix ι ι ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hdet : M.det ≠ 0) (j : ι) : 0 < (p ᵥ* M) j := by
  have hnn : ∀ k ∈ univ, 0 ≤ p k * M k j := fun k _ => mul_nonneg (hp k).le (hM k j)
  have he : (p ᵥ* M) j = ∑ k, p k * M k j := by simp [vecMul, dotProduct]
  rw [he]
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun hsum => hdet ?_
  refine det_eq_zero_of_column_eq_zero j fun i => ?_
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum.symm i (mem_univ i)
  exact (mul_eq_zero.mp this).resolve_left (hp i).ne'

/-- **Additivity of the LogDet distance at a separating vertex** (Steel 1994; Lockhart et al.
1994; Lake 1994). Let `Y` have distribution `p` (positive) and let `X` and `Z` be conditionally
independent given `Y`, with transition matrices `M` (from `Y` to `X`) and `N` (from `Y` to `Z`)
whose rows sum to `1` and whose determinants are nonzero. The joint distribution matrices are
`F_XY = Mᵀ Π_Y`, `F_YZ = Π_Y N` and `F_XZ = Mᵀ Π_Y N`, and `d(X, Z) = d(X, Y) + d(Y, Z)`. The
identity uses no sign condition on `M` and `N`; with nonnegative entries all logarithms are of
positive numbers (`vecMul_pos`). -/
theorem paralinear_threePoint {p : ι → ℝ} (hp : ∀ i, 0 < p i) {M N : Matrix ι ι ℝ}
    (hMrow : ∀ i, ∑ j, M i j = 1) (hNrow : ∀ i, ∑ j, N i j = 1) (hM : M.det ≠ 0)
    (hN : N.det ≠ 0) :
    paralinear (Mᵀ * diagonal p * N) =
      paralinear (Mᵀ * diagonal p) + paralinear (diagonal p * N) := by
  have hpr : 0 < ∏ i, p i := Finset.prod_pos fun i _ => hp i
  have hT : Mᵀ * diagonal p = (diagonal p * M)ᵀ := by
    rw [transpose_mul, diagonal_transpose]
  have r1 : ∀ x, ∑ z, (Mᵀ * diagonal p * N) x z = (p ᵥ* M) x := fun x => by
    rw [hT]
    simp only [mul_apply, transpose_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hNrow, mul_one]
    exact colSum_diagonal_mul p M x
  have c1 : ∀ z, ∑ x, (Mᵀ * diagonal p * N) x z = (p ᵥ* N) z := fun z => by
    rw [hT]
    simp only [mul_apply, transpose_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    simp only [vecMul, dotProduct]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp [diagonal_apply, ← Finset.mul_sum, hMrow]
  have r2 : ∀ x, ∑ y, (Mᵀ * diagonal p) x y = (p ᵥ* M) x := fun x => by
    rw [hT]
    exact colSum_diagonal_mul p M x
  have c2 : ∀ y, ∑ x, (Mᵀ * diagonal p) x y = p y := fun y => by
    rw [hT]
    simp only [transpose_apply, rowSum_diagonal_mul, hMrow, mul_one]
  simp only [paralinear, r1, c1, r2, c2, rowSum_diagonal_mul, colSum_diagonal_mul, hNrow,
    mul_one, det_mul, det_transpose, det_diagonal]
  rw [log_abs_mul (mul_ne_zero hM hpr.ne') hN, log_abs_mul hM hpr.ne',
    log_abs_mul hpr.ne' hN, abs_of_pos hpr]
  ring

/-- **Additivity of the LogDet distance along a chain, one step**: for a Markov chain
`X → Y → Z` with `X` distributed as `p` (positive), transition matrices `A` (nonnegative) and
`B` with unit row sums and nonzero determinants, `d(X, Z) = d(X, Y) + d(Y, Z)`, where
`F_XZ = Π_X A B`, `F_XY = Π_X A` and `F_YZ = Π_Y B` with `Y` distributed as `p A`. -/
theorem paralinear_chain_step {p : ι → ℝ} (hp : ∀ i, 0 < p i) {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hArow : ∀ i, ∑ j, A i j = 1) (hBrow : ∀ i, ∑ j, B i j = 1)
    (hAdet : A.det ≠ 0) (hBdet : B.det ≠ 0) :
    paralinear (diagonal p * (A * B)) =
      paralinear (diagonal p * A) + paralinear (diagonal (p ᵥ* A) * B) := by
  have hpr : 0 < ∏ i, p i := Finset.prod_pos fun i _ => hp i
  have hqr : 0 < ∏ i, (p ᵥ* A) i := Finset.prod_pos fun i _ => vecMul_pos hp hA hAdet i
  simp only [paralinear, rowSum_diagonal_mul, colSum_diagonal_mul, rowSum_mul hArow hBrow,
    hArow, hBrow, mul_one, det_mul, det_diagonal, vecMul_vecMul]
  rw [log_abs_mul hpr.ne' (mul_ne_zero hAdet hBdet), log_abs_mul hAdet hBdet,
    log_abs_mul hpr.ne' hAdet, log_abs_mul hqr.ne' hBdet, abs_of_pos hqr]
  ring

/-- The product `M 0 * M 1 * ⋯ * M (n - 1)` of the transition matrices along the first `n`
edges of a path. -/
def pathProd (M : ℕ → Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | n + 1 => pathProd M n * M n

/-- **Additivity of the LogDet distance along a path** (Steel 1994; Lockhart et al. 1994):
for a Markov chain `v₀ → v₁ → ⋯ → v_n` along a path, with positive initial distribution `p`
and nonnegative nonsingular transition matrices `M i` with unit row sums, the LogDet distance
between the ends is the sum of the distances of consecutive vertices. The joint distribution of
`v₀, v_n` is `Π_{v₀} M 0 ⋯ M (n - 1)`, and that of `v_i, v_{i+1}` is `Π_{v_i} M i`, where `v_i`
has distribution `p M 0 ⋯ M (i - 1)`. Under the general Markov model on a tree with positive
marginals and nonsingular matrices, the states along any path form such a chain once the model
is rooted at one end of the path (this rerooting is not formalized here). -/
theorem paralinear_pathProd {p : ι → ℝ} (hp : ∀ i, 0 < p i) {M : ℕ → Matrix ι ι ℝ}
    (hM : ∀ n i j, 0 ≤ M n i j) (hrow : ∀ n i, ∑ j, M n i j = 1) (hdet : ∀ n, (M n).det ≠ 0)
    (n : ℕ) :
    paralinear (diagonal p * pathProd M n) =
      ∑ i ∈ range n, paralinear (diagonal (p ᵥ* pathProd M i) * M i) := by
  have inv : ∀ n, (∀ i j, 0 ≤ pathProd M n i j) ∧ (∀ i, ∑ j, pathProd M n i j = 1) ∧
      (pathProd M n).det ≠ 0 := by
    intro n
    induction n with
    | zero => exact ⟨fun i j => by simp [pathProd, one_apply]; split_ifs <;> norm_num,
        fun i => by simp [pathProd, one_apply], by simp [pathProd]⟩
    | succ n ih =>
      refine ⟨fun i j => ?_, rowSum_mul ih.2.1 (hrow n), ?_⟩
      · simp only [pathProd, mul_apply]
        exact Finset.sum_nonneg fun k _ => mul_nonneg (ih.1 i k) (hM n k j)
      · simp only [pathProd, det_mul]
        exact mul_ne_zero ih.2.2 (hdet n)
  induction n with
  | zero => simp [pathProd, paralinear_diagonal hp]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, pathProd]
    exact paralinear_chain_step hp (inv n).1 (inv n).2.1 (hrow n) (inv n).2.2 (hdet n)

end LogDet

/-! ## The strong law for i.i.d. sites -/

section Sites

/-- **Strong law for finite-valued sites**: for pairwise independent, identically distributed
random variables with values in a finite type, the averages of `f (X i)` converge almost surely
to the mean `∑ a, ℙ(X 0 = a) f a` (Etemadi's form of the strong law,
`ProbabilityTheory.strong_law_ae`). -/
private theorem ae_tendsto_avg_of_fintype {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → α) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ) (f : α → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, f (X i ω)) atTop
      (𝓝 (∑ a, μ.real (X 0 ⁻¹' {a}) * f a)) := by
  have hlim : ∫ x, f x ∂(μ.map (X 0)) = ∑ a, μ.real (X 0 ⁻¹' {a}) * f a := by
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul, map_measureReal_apply (hmeas 0) (measurableSet_singleton _)]
  rw [← hlim]
  exact Cslib.MachineLearning.Sampling.tendsto_mcEstimate (measurable_of_finite f)
    Integrable.of_finite hmeas (fun i => (hident i).map_eq) hindep

/-- If the mean `∑ a, ℙ(X 0 = a) f a` is positive, then almost surely the partial sums of
`f (X i)` are positive for all large `n`. -/
private theorem ae_eventually_sum_pos {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → α) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) μ) (f : α → ℝ)
    (hpos : 0 < ∑ a, μ.real (X 0 ⁻¹' {a}) * f a) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, 0 < ∑ i ∈ range n, f (X i ω) := by
  filter_upwards [ae_tendsto_avg_of_fintype X hmeas hident hindep f] with ω hω
  filter_upwards [hω.eventually_const_lt hpos, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have := (mul_pos_iff_of_pos_left (inv_pos.mpr hn')).mp hn
  exact this

end Sites

/-! ## The Felsenstein zone -/

section Zone

/-- The **symmetric two-state model** on one branch: the state changes with probability `p`.
As a model, `0 ≤ p ≤ 1/2`. -/
def twoState (p : ℝ) (a b : Bool) : ℝ :=
  if a = b then 1 - p else p

/-- The quartet `((A, B), (C, D))` on the taxa `0 = A`, `1 = B`, `2 = C`, `3 = D`, with change
probabilities `pA, pB, pC, pD` on the pendant edges and `pI` on the internal edge. The root
sits at the `AB` end of the internal edge (the edge to the `AB` cherry vertex has change
probability `0`); by the pulley principle its position does not matter. -/
def quartet (pA pB pC pD pI : ℝ) : Tree (Fin 4) Bool ℝ :=
  node (twoState 0) (node (twoState pA) (leaf 0) (twoState pB) (leaf 1)) (twoState pI)
    (node (twoState pC) (leaf 2) (twoState pD) (leaf 3))

/-- The leaf weights of a site pattern `σ`: the indicator of the observed state. -/
def siteObs (σ : Fin 4 → Bool) (l : Fin 4) (s : Bool) : ℝ :=
  if s = σ l then 1 else 0

/-- The probability of the site pattern `σ` on the quartet, with the uniform root distribution
(the stationary distribution of the symmetric model). -/
noncomputable def patternProb (pA pB pC pD pI : ℝ) (σ : Fin 4 → Bool) : ℝ :=
  likelihood (siteObs σ) (quartet pA pB pC pD pI) (fun _ => 1 / 2)

private lemma sum_fun_four (f : (Fin 4 → Bool) → ℝ) :
    ∑ σ, f σ = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a, b, c, d] := by
  have h : ∀ {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ),
      ∑ σ, g σ = ∑ b : Bool, ∑ τ : Fin n → Bool, g (Fin.cons b τ) := by
    intro n g
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
    rfl
  simp only [h, Fintype.sum_unique]
  rfl

private lemma patternProb_eq (pA pB pC pD pI : ℝ) (σ : Fin 4 → Bool) :
    patternProb pA pB pC pD pI σ =
      1 / 2 * ∑ u : Bool, (∑ a : Bool, twoState pA u a * siteObs σ 0 a) *
        (∑ a : Bool, twoState pB u a * siteObs σ 1 a) *
        ∑ v : Bool, twoState pI u v * ((∑ a : Bool, twoState pC v a * siteObs σ 2 a) *
          (∑ a : Bool, twoState pD v a * siteObs σ 3 a)) := by
  simp only [patternProb, likelihood_eq_sum_prune, quartet, prune, Fintype.sum_bool, twoState]
  simp
  ring

/-- The pattern probabilities sum to `1`, for all parameters. -/
theorem sum_patternProb (pA pB pC pD pI : ℝ) :
    ∑ σ, patternProb pA pB pC pD pI σ = 1 := by
  simp only [sum_fun_four, patternProb_eq, Fintype.sum_bool, twoState, siteObs]
  simp
  ring

/-- The pattern probabilities are nonnegative for change probabilities in `[0, 1]`. -/
theorem patternProb_nonneg {pA pB pC pD pI : ℝ} (hA : pA ∈ Set.Icc 0 1) (hB : pB ∈ Set.Icc 0 1)
    (hC : pC ∈ Set.Icc 0 1) (hD : pD ∈ Set.Icc 0 1) (hI : pI ∈ Set.Icc 0 1)
    (σ : Fin 4 → Bool) : 0 ≤ patternProb pA pB pC pD pI σ := by
  have ht : ∀ {p : ℝ}, p ∈ Set.Icc 0 1 → ∀ a b, 0 ≤ twoState p a b := fun hp a b => by
    unfold twoState
    split_ifs <;> linarith [hp.1, hp.2]
  have ho : ∀ l a, 0 ≤ siteObs σ l a := fun l a => by
    unfold siteObs
    split_ifs <;> norm_num
  have hs : ∀ {p : ℝ}, p ∈ Set.Icc 0 1 → ∀ u l, 0 ≤ ∑ a : Bool, twoState p u a * siteObs σ l a :=
    fun hp u l => Finset.sum_nonneg fun a _ => mul_nonneg (ht hp u a) (ho l a)
  rw [patternProb_eq]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => mul_nonneg
    (mul_nonneg (hs hA u 0) (hs hB u 1)) (Finset.sum_nonneg fun v _ => ?_))
  exact mul_nonneg (ht hI u v) (mul_nonneg (hs hC v 2) (hs hD v 3))

/-- The site pattern `σ` **supports the split** `{a, b} | {c, d}`: `a, b` agree, `c, d` agree,
and the two pairs differ (a parsimony-informative pattern for that split). -/
def Supports (σ : Fin 4 → Bool) (a b c d : Fin 4) : Prop :=
  σ a = σ b ∧ σ c = σ d ∧ σ a ≠ σ c

instance (σ : Fin 4 → Bool) (a b c d : Fin 4) : Decidable (Supports σ a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The expected frequency of the patterns supporting the split `{a, b} | {c, d}`. -/
noncomputable def splitFreq (pA pB pC pD pI : ℝ) (a b c d : Fin 4) : ℝ :=
  ∑ σ, if Supports σ a b c d then patternProb pA pB pC pD pI σ else 0

/-- **Felsenstein (1978), the exact comparison**: with change probability `P` on the long
non-sister branches to `A` and `C` and `Q` on the other three branches, the expected frequency
of patterns supporting the wrong split `AC | BD` exceeds that of the true split `AB | CD` by
`(1 - 2 Q) (P ^ 2 - Q (1 - Q))`, for all real `P, Q`. This is Felsenstein's equations (16)–(17)
(his four-species model has equal probabilities of change `0 → 1` and reversion `1 → 0`). -/
theorem splitFreq_wrong_sub_true (P Q : ℝ) :
    splitFreq P Q P Q Q 0 2 1 3 - splitFreq P Q P Q Q 0 1 2 3 =
      (1 - 2 * Q) * (P ^ 2 - Q * (1 - Q)) := by
  simp only [splitFreq, sum_fun_four, patternProb_eq, Fintype.sum_bool, twoState, siteObs,
    Supports]
  simp
  ring

/-- The wrong split `AC | BD` against the third split `AD | BC`: the difference of expected
frequencies is `(1 - 2 Q) (P - Q) ^ 2`. -/
theorem splitFreq_wrong_sub_third (P Q : ℝ) :
    splitFreq P Q P Q Q 0 2 1 3 - splitFreq P Q P Q Q 0 3 1 2 = (1 - 2 * Q) * (P - Q) ^ 2 := by
  simp only [splitFreq, sum_fun_four, patternProb_eq, Fintype.sum_bool, twoState, siteObs,
    Supports]
  simp
  ring

/-- The true split `AB | CD` against the third split `AD | BC`: the difference of expected
frequencies is `Q (1 - 2 Q) (1 - 2 P)`. -/
theorem splitFreq_true_sub_third (P Q : ℝ) :
    splitFreq P Q P Q Q 0 1 2 3 - splitFreq P Q P Q Q 0 3 1 2 =
      Q * (1 - 2 * Q) * (1 - 2 * P) := by
  simp only [splitFreq, sum_fun_four, patternProb_eq, Fintype.sum_bool, twoState, siteObs,
    Supports]
  simp
  ring

open Parsimony

/-- The rooted quartet `((a, b), (c, d))` with unit costs, for Fitch's algorithm. -/
def quartetShape (a b c d : Fin 4) : Tree (Fin 4) Bool Parsimony.Cost :=
  node unitCost (node unitCost (leaf a) unitCost (leaf b)) unitCost
    (node unitCost (leaf c) unitCost (leaf d))

/-- The Fitch parsimony score of the site pattern `σ` on the quartet `((a, b), (c, d))`; it is
the small-parsimony score by `Parsimony.fitch_score_eq`. -/
def parsimonyScore (a b c d : Fin 4) (σ : Fin 4 → Bool) : ℕ :=
  (fitch σ (quartetShape a b c d)).2

/-- On four taxa, the parsimony scores of two quartets differ only on informative patterns: the
score on `AB | CD` minus the score on `AC | BD` is `1` on patterns supporting `AC | BD`, `-1` on
patterns supporting `AB | CD`, and `0` otherwise; likewise for `AD | BC`. -/
theorem parsimonyScore_sub (σ : Fin 4 → Bool) :
    ((parsimonyScore 0 1 2 3 σ : ℤ) - parsimonyScore 0 2 1 3 σ =
        (if Supports σ 0 2 1 3 then 1 else 0) - (if Supports σ 0 1 2 3 then 1 else 0)) ∧
      ((parsimonyScore 0 3 1 2 σ : ℤ) - parsimonyScore 0 2 1 3 σ =
        (if Supports σ 0 2 1 3 then 1 else 0) - (if Supports σ 0 3 1 2 then 1 else 0)) := by
  revert σ
  decide

/-- The expected Fitch parsimony score of one site on the quartet `((a, b), (c, d))`. -/
noncomputable def expectedScore (pA pB pC pD pI : ℝ) (a b c d : Fin 4) : ℝ :=
  ∑ σ, patternProb pA pB pC pD pI σ * parsimonyScore a b c d σ

private lemma expectedScore_sub (P Q : ℝ) :
    (expectedScore P Q P Q Q 0 1 2 3 - expectedScore P Q P Q Q 0 2 1 3 =
        splitFreq P Q P Q Q 0 2 1 3 - splitFreq P Q P Q Q 0 1 2 3) ∧
      (expectedScore P Q P Q Q 0 3 1 2 - expectedScore P Q P Q Q 0 2 1 3 =
        splitFreq P Q P Q Q 0 2 1 3 - splitFreq P Q P Q Q 0 3 1 2) := by
  constructor <;>
  · simp only [expectedScore, splitFreq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 := congrArg (Int.cast : ℤ → ℝ) (parsimonyScore_sub σ).1
    have h2 := congrArg (Int.cast : ℤ → ℝ) (parsimonyScore_sub σ).2
    push_cast at h1 h2
    rw [← mul_sub]
    first | rw [h1] | rw [h2]
    split_ifs <;> ring

/-- **The Felsenstein zone** (Felsenstein 1978): if `0 ≤ Q < 1/2` and `P ^ 2 > Q (1 - Q)`, the
wrong quartet `AC | BD` has strictly smaller expected parsimony score per site than both the
true quartet `AB | CD` and the third quartet `AD | BC`. The statement is algebraic in `P`; the
model has `0 ≤ P ≤ 1/2`. -/
theorem expectedScore_wrong_lt {P Q : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q < 1 / 2)
    (hPQ : Q * (1 - Q) < P ^ 2) :
    expectedScore P Q P Q Q 0 2 1 3 < expectedScore P Q P Q Q 0 1 2 3 ∧
      expectedScore P Q P Q Q 0 2 1 3 < expectedScore P Q P Q Q 0 3 1 2 := by
  obtain ⟨h1, h2⟩ := expectedScore_sub P Q
  have hne : P - Q ≠ 0 := by
    intro h
    have hPQ' : P = Q := by linarith
    subst hPQ'
    nlinarith
  have hq : 0 < 1 - 2 * Q := by linarith
  have e1 := splitFreq_wrong_sub_true P Q
  have e2 := splitFreq_wrong_sub_third P Q
  have p1 : 0 < (1 - 2 * Q) * (P ^ 2 - Q * (1 - Q)) := mul_pos hq (by linarith)
  have p2 : 0 < (1 - 2 * Q) * (P - Q) ^ 2 :=
    mul_pos hq (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)
  constructor <;> linarith

/-- **Parsimony is inconsistent in the Felsenstein zone** (Felsenstein 1978): if the sites
`σ i` are pairwise independent and identically distributed with the pattern distribution of the
quartet, and `0 ≤ Q < 1/2`, `P ^ 2 > Q (1 - Q)`, then almost surely, for all long enough
alignments, the wrong quartet `AC | BD` has a strictly smaller total Fitch score than the true
quartet `AB | CD` and the third quartet `AD | BC`. -/
theorem ae_eventually_parsimony_wrong {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P Q : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q < 1 / 2)
    (hPQ : Q * (1 - Q) < P ^ 2) (σ : ℕ → Ω → Fin 4 → Bool) (hmeas : ∀ i, Measurable (σ i))
    (hident : ∀ i, IdentDistrib (σ i) (σ 0) μ μ)
    (hindep : Pairwise fun i j => IndepFun (σ i) (σ j) μ)
    (hlaw : ∀ τ, μ.real (σ 0 ⁻¹' {τ}) = patternProb P Q P Q Q τ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ∑ i ∈ range n, parsimonyScore 0 2 1 3 (σ i ω) <
          ∑ i ∈ range n, parsimonyScore 0 1 2 3 (σ i ω) ∧
        ∑ i ∈ range n, parsimonyScore 0 2 1 3 (σ i ω) <
          ∑ i ∈ range n, parsimonyScore 0 3 1 2 (σ i ω) := by
  obtain ⟨h1, h2⟩ := expectedScore_wrong_lt hQ0 hQ hPQ
  have hmean : ∀ a b c d : Fin 4, ∑ τ, μ.real (σ 0 ⁻¹' {τ}) *
      ((parsimonyScore a b c d τ : ℝ) - parsimonyScore 0 2 1 3 τ) =
        expectedScore P Q P Q Q a b c d - expectedScore P Q P Q Q 0 2 1 3 := by
    intro a b c d
    simp only [hlaw, expectedScore, mul_sub, Finset.sum_sub_distrib]
  have e1 := ae_eventually_sum_pos σ hmeas hident hindep
    (fun τ => (parsimonyScore 0 1 2 3 τ : ℝ) - parsimonyScore 0 2 1 3 τ)
    (by rw [hmean]; linarith)
  have e2 := ae_eventually_sum_pos σ hmeas hident hindep
    (fun τ => (parsimonyScore 0 3 1 2 τ : ℝ) - parsimonyScore 0 2 1 3 τ)
    (by rw [hmean]; linarith)
  filter_upwards [e1, e2] with ω h1 h2
  filter_upwards [h1, h2] with n hn1 hn2
  simp only [Finset.sum_sub_distrib, sub_pos] at hn1 hn2
  exact ⟨by exact_mod_cast hn1, by exact_mod_cast hn2⟩

end Zone

/-! ## Jukes–Cantor distances and the consistency of neighbor joining -/

section NJ

open MathlibExt.Biology.Phylogenetics.JukesCantor NeighborJoining

/-- The JC transition matrix along a path whose branch lengths are listed in `ts`: the product
of the branch transition matrices `jcProb μ t`. -/
noncomputable def jcPath (μ : ℝ) : List ℝ → Matrix (Fin 4) (Fin 4) ℝ
  | [] => 1
  | t :: ts => Matrix.of (jcProb μ t) * jcPath μ ts

/-- **Chapman–Kolmogorov along a path**: the JC transition matrix along a path is the
transition matrix of the total length. -/
theorem jcPath_eq (μ : ℝ) (ts : List ℝ) : jcPath μ ts = Matrix.of (jcProb μ ts.sum) := by
  induction ts with
  | nil =>
    ext i j
    simp [jcPath, jcProb_zero, Matrix.one_apply]
  | cons t ts ih =>
    ext i j
    rw [jcPath, ih, Matrix.mul_apply, List.sum_cons]
    exact sum_jcProb_mul_jcProb μ t ts.sum i j

/-- **JC-corrected distances are path lengths** (Jukes & Cantor 1969): the JC distance of the
probability that the two ends of a path differ is `μ` times the total branch length. -/
theorem jcDistance_jcPath (μ : ℝ) (ts : List ℝ) (i : Fin 4) :
    jcDistance (∑ j ∈ univ.erase i, jcPath μ ts i j) = μ * ts.sum := by
  rw [jcPath_eq]
  exact jcDistance_pDiff μ ts.sum i

/-- The empirical p-distance of the taxa `x, y` over the first `n` sites of the alignment
`seq` (`seq i x` is the base of taxon `x` at site `i`): the proportion of sites where they
differ. -/
noncomputable def pHat {X : Type*} (seq : ℕ → X → Fin 4) (n : ℕ) (x y : X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, if seq i x = seq i y then 0 else 1

/-- The JC-corrected empirical distance `jcDistance (pHat seq n x y)`. -/
noncomputable def jcHat {X : Type*} (seq : ℕ → X → Fin 4) (n : ℕ) (x y : X) : ℝ :=
  jcDistance (pHat seq n x y)

/-- Neighbor joining **recovers the tree within radius `r`** of the dissimilarity `d`: every
complete run of neighbor joining on a symmetric dissimilarity `D` with zero diagonal and
`|D x y - d x y| < r` for distinct taxa forms exactly the splits of the internal edges of
`(G, ι)`. Atteson's theorem (not proved in this library) gives this for the path-length metric
of a binary phylogenetic tree with `r` half the shortest internal edge length. -/
def NJRecoversWithin {X : Type*} [DecidableEq X] [Fintype X] {V : Type*} (G : SimpleGraph V)
    (ι : X → V) (d : X → X → ℝ) (r : ℝ) : Prop :=
  ∀ D : X → X → ℝ, (∀ x y, D x y = D y x) → (∀ x, D x x = 0) →
    (∀ x y, x ≠ y → |D x y - d x y| < r) →
    ∀ S Dc C, NJRun D S Dc C → S.card ≤ 3 → ∀ A : Finset X,
      ((A ∈ C ∨ univ \ A ∈ C) ↔
        ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
          ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a)

/-- **Strong law for the p-distances**: for pairwise independent, identically distributed
sites, the empirical p-distance of every pair of taxa converges almost surely to the
probability that the two taxa differ at a site. -/
theorem ae_tendsto_pHat {X : Type*} [Finite X] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (site : ℕ → Ω → X → Fin 4)
    (hmeas : ∀ i, Measurable (site i)) (hident : ∀ i, IdentDistrib (site i) (site 0) P P)
    (hindep : Pairwise fun i j => IndepFun (site i) (site j) P) :
    ∀ᵐ ω ∂P, ∀ x y, Tendsto (fun n => pHat (fun i => site i ω) n x y) atTop
      (𝓝 (P.real {ω | site 0 ω x ≠ site 0 ω y})) := by
  have : Fintype X := Fintype.ofFinite X
  classical
  rw [ae_all_iff]
  intro x
  rw [ae_all_iff]
  intro y
  have h := ae_tendsto_avg_of_fintype site hmeas hident hindep
    (fun s => if s x = s y then 0 else 1)
  have hmean : ∑ a, P.real (site 0 ⁻¹' {a}) * (if a x = a y then (0 : ℝ) else 1) =
      P.real {ω | site 0 ω x ≠ site 0 ω y} := by
    have e : ∀ a : X → Fin 4, P.real (site 0 ⁻¹' {a}) * (if a x = a y then (0 : ℝ) else 1) =
        if a x ≠ a y then P.real (site 0 ⁻¹' {a}) else 0 := fun a => by
      split_ifs <;> simp_all
    simp only [e]
    rw [← Finset.sum_filter, sum_measureReal_preimage_singleton _
      (fun a _ => hmeas 0 (measurableSet_singleton a))]
    congr 1
    ext ω
    simp
  rw [hmean] at h
  filter_upwards [h] with ω hω
  simpa [pHat] using hω

/-- **Statistical consistency of neighbor joining under Jukes–Cantor** (Saitou & Nei 1987;
Atteson 1999). Let `(G, ι)` be a binary phylogenetic `X`-tree with path-length metric `d` for
edge lengths `w`, and let the sites be pairwise independent and identically distributed, with
the two-leaf marginals of the JC model with rate `μ` and uniform root: for every path `p` from
`x` to `y`, `ℙ(site x = i, site y = j) = jcPath μ (lengths of p) i j / 4`. If neighbor joining
recovers the tree within some radius `r > 0` of the scaled metric `μ d` (for `μ > 0`, Atteson's
theorem gives `r = μ m / 2`, `m` the shortest internal edge length), then almost surely, for all
long enough alignments, every complete run of neighbor joining on the JC-corrected empirical
distances returns exactly the splits of the internal edges of the tree. -/
theorem ae_eventually_njRun_splits_jcHat {X : Type*} [DecidableEq X] [Fintype X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {μ r : ℝ} (hr : 0 < r) (hNJ : NJRecoversWithin G ι (fun x y => μ * d x y) r)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (site : ℕ → Ω → X → Fin 4) (hmeas : ∀ i, Measurable (site i))
    (hident : ∀ i, IdentDistrib (site i) (site 0) P P)
    (hindep : Pairwise fun i j => IndepFun (site i) (site j) P)
    (hpair : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → ∀ i j,
      P.real {ω | site 0 ω x = i ∧ site 0 ω y = j} = jcPath μ (p.edges.map w) i j / 4) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ S Dc C, NJRun (jcHat (fun i => site i ω) n) S Dc C →
      S.card ≤ 3 → ∀ A : Finset X,
        ((A ∈ C ∨ univ \ A ∈ C) ↔
          ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
            ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a) := by
  classical
  have hdiff : ∀ x y, P.real {ω | site 0 ω x ≠ site 0 ω y} = pDiff μ (d x y) 0 := by
    intro x y
    obtain ⟨p, hp⟩ := (hT.1.connected.preconnected (ι x) (ι y)).exists_isPath
    have hg : Measurable fun ω => (site 0 ω x, site 0 ω y) :=
      ((measurable_pi_apply x).comp (hmeas 0)).prodMk ((measurable_pi_apply y).comp (hmeas 0))
    have hsum := sum_measureReal_preimage_singleton (μ := P)
      (univ.filter fun q : Fin 4 × Fin 4 => q.1 ≠ q.2)
      (fun q _ => hg (measurableSet_singleton q))
    have hset : (fun ω => (site 0 ω x, site 0 ω y)) ⁻¹'
        ↑(univ.filter fun q : Fin 4 × Fin 4 => q.1 ≠ q.2) = {ω | site 0 ω x ≠ site 0 ω y} := by
      ext ω
      simp
    have hfib : ∀ q : Fin 4 × Fin 4, (fun ω => (site 0 ω x, site 0 ω y)) ⁻¹' {q} =
        {ω | site 0 ω x = q.1 ∧ site 0 ω y = q.2} := by
      intro q
      ext ω
      simp [Prod.ext_iff]
    rw [hset] at hsum
    rw [← hsum]
    simp only [hfib, hpair x y p hp, jcPath_eq, ← hd x y p hp, Matrix.of_apply]
    rw [Finset.sum_filter, Fintype.sum_prod_type, pDiff_eq]
    simp [Fin.sum_univ_four, jcProb]
    ring
  filter_upwards [ae_tendsto_pHat site hmeas hident hindep] with ω hω
  have hjc : ∀ x y, Tendsto (fun n => jcHat (fun i => site i ω) n x y) atTop
      (𝓝 (μ * d x y)) := by
    intro x y
    have h1 := hω x y
    rw [hdiff] at h1
    have hpos : 1 - 4 / 3 * pDiff μ (d x y) 0 ≠ 0 := by
      have := pDiff_lt_three_quarters μ (d x y) 0
      linarith
    rw [← jcDistance_pDiff μ (d x y) 0]
    exact ((tendsto_const_nhds.sub (h1.const_mul (4 / 3))).log hpos).const_mul (-(3 / 4))
  have hev : ∀ᶠ n in atTop, ∀ x y, |jcHat (fun i => site i ω) n x y - μ * d x y| < r := by
    rw [eventually_all]
    intro x
    rw [eventually_all]
    intro y
    filter_upwards [(hjc x y).eventually (Metric.ball_mem_nhds _ hr)] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hev] with n hn
  intro S Dc C hrun hS A
  refine hNJ _ (fun x y => ?_) (fun x => ?_) (fun x y _ => hn x y) S Dc C hrun hS A
  · unfold jcHat pHat
    rw [Finset.sum_congr rfl fun i _ => if_congr eq_comm rfl rfl]
  · simp [jcHat, pHat, jcDistance]

end NJ

end Cslib.Bioinformatics.Phylogenetics.FelsensteinZone
