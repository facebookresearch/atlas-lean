/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Probability.PMF
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation
public import Mathlib.Data.Fintype.Perm

/-!
# Expected running time under an input distribution

For a deterministic list algorithm `algo` instrumented with `TimeM Nat`
(comparison counting, as in `quickSort`) and a distribution `dist` on input
lists, `expectedTime algo dist` is the expected value of the running time
under `dist`, defined through `PMF.expectENN` and hence valued in `ℝ≥0∞`,
so a divergent expected time is `∞` rather than `0`.

The main input distribution is `uniformPermutation xs`: the entries of `xs`
rearranged by a uniformly random permutation of the indices. Its expectation
has the average formula `expectedTime_uniformPermutation`, summing the cost
over all `n !` permutations. This makes expected-cost analyses over random
input orderings (randomly ordered inputs for deterministic algorithms)
computable by finite sums.
-/

@[expose] public section

open scoped ENNReal

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α β γ : Type*}

/-- **Expected running time.** Let $A$ be an algorithm on inputs of a type $\gamma$ whose running
time $T_A(x)$ on each input $x$ is a natural number, and let $D$ be a probability mass function on
$\gamma$. The expected running time of $A$ under $D$ is the extended nonnegative expectation
$\sum_{x \in \gamma} D(x)\, T_A(x) \in [0, \infty]$ of the running time, the sum taken over all
inputs.

Valuing the expectation in $[0, \infty]$ records a divergent expected time as $\infty$; a
real-valued integral would collapse it to $0$. -/
noncomputable def expectedTime (algo : γ → TimeM Nat β)
    (dist : PMF γ) : ℝ≥0∞ :=
  dist.expectENN (fun xs => ((algo xs).time : ℝ≥0∞))

/-- **Uniformly random rearrangement of a list.** For a list $x = (x_0, \dots, x_{n-1})$, the
uniform permutation of $x$ is the probability distribution on lists obtained by choosing a
permutation $\sigma$ of $\{0, \dots, n-1\}$ uniformly at random and outputting
$(x_{\sigma(0)}, \dots, x_{\sigma(n-1)})$. -/
noncomputable def uniformPermutation (xs : List α) : PMF (List α) :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin xs.length))).map
    (fun σ => List.ofFn (fun p => xs.get (σ p)))

/-- **Rearrangements preserve length.** For a list $x$, every list in the support of the uniform
permutation of $x$ has the same length as $x$. -/
theorem uniformPermutation_length (xs : List α)
    (ys : List α) (hys : ys ∈ (uniformPermutation xs).support) :
    ys.length = xs.length := by
  rw [uniformPermutation, PMF.mem_support_map_iff] at hys
  obtain ⟨σ, -, rfl⟩ := hys
  exact List.length_ofFn

/-- **Rearrangements are permutations.** For a list $x$, every list in the support of the uniform
permutation of $x$ is a permutation of $x$, that is, it has the same entries with the same
multiplicities. -/
theorem uniformPermutation_perm (xs : List α)
    (ys : List α) (hys : ys ∈ (uniformPermutation xs).support) :
    List.Perm ys xs := by
  rw [uniformPermutation, PMF.mem_support_map_iff] at hys
  obtain ⟨σ, -, rfl⟩ := hys
  have hfin : ((List.finRange xs.length).map σ).Perm
      (List.finRange xs.length) := by
    refine (List.perm_ext_iff_of_nodup
      (List.Nodup.map σ.injective (List.nodup_finRange _))
      (List.nodup_finRange _)).2 fun a => ?_
    constructor
    · intro _; exact List.mem_finRange a
    · intro _
      have hmem : σ (σ.symm a) ∈ (List.finRange xs.length).map σ :=
        List.mem_map_of_mem (List.mem_finRange (σ.symm a))
      rwa [Equiv.apply_symm_apply] at hmem
  have hxs : (List.finRange xs.length).map xs.get = xs :=
    List.ofFn_eq_map.symm.trans (List.ofFn_get xs)
  have hperm : (((List.finRange xs.length).map σ).map xs.get).Perm
      ((List.finRange xs.length).map xs.get) :=
    List.Perm.map xs.get hfin
  rw [hxs] at hperm
  have e1 : List.ofFn (fun p => xs.get (σ p)) =
      ((List.finRange xs.length).map σ).map xs.get :=
    List.ofFn_eq_map.trans List.map_map.symm
  rw [e1]
  exact hperm

/-- **Average formula for the expected time over random orderings.** Let $A$ be an algorithm on
lists whose running time $T_A(y)$ on each list $y$ is a natural number, and let
$x = (x_0, \dots, x_{n-1})$ be a list of length $n$. The expected running time of $A$ when its
input is $x$ rearranged by a uniformly random permutation equals
$$\frac{1}{n!} \sum_{\sigma} T_A(x_{\sigma(0)}, \dots, x_{\sigma(n-1)}),$$
the sum running over all permutations $\sigma$ of $\{0, \dots, n-1\}$ and computed in
$[0, \infty]$. -/
theorem expectedTime_uniformPermutation (algo : List α → TimeM Nat β)
    (xs : List α) :
    expectedTime algo (uniformPermutation xs) =
      (Nat.factorial xs.length : ℝ≥0∞)⁻¹ *
        ∑ σ : Equiv.Perm (Fin xs.length),
          ((algo (List.ofFn (fun p => xs.get (σ p)))).time : ℝ≥0∞) := by
  have hdist :
      Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin xs.length)) =
        PMF.uniformFintype (Equiv.Perm (Fin xs.length)) := by
    ext σ
    simp
  rw [expectedTime, uniformPermutation, hdist, PMF.expectENN_map,
    PMF.expectENN_uniformOfFintype, Fintype.card_perm, Fintype.card_fin]
  exact congrArg _ (Finset.sum_congr rfl fun σ _ => rfl)

/-- **Constant running time on the support gives that expected time.** Let $A$ be an algorithm
on inputs of a type $\gamma$ whose running time $T_A(x)$ on each input $x$ is a natural number,
let $D$ be a probability mass function on $\gamma$, and let $c$ be a natural number. If
$T_A(x) = c$ for every input $x$ in the support of $D$, then the expected running time of $A$
under $D$ equals $c$.

Inputs outside the support have probability $0$, so their running times do not contribute. -/
theorem expectedTime_eq_of_time_eq (algo : γ → TimeM Nat β)
    (dist : PMF γ) (c : ℕ)
    (h : ∀ ys ∈ dist.support, (algo ys).time = c) :
    expectedTime algo dist = (c : ℝ≥0∞) := by
  have hsum : dist.expectENN (fun xs => ((algo xs).time : ℝ≥0∞)) =
      dist.expectENN (fun _ => (c : ℝ≥0∞)) := by
    simp only [PMF.expectENN]
    refine tsum_congr fun ys => ?_
    by_cases hys : ys ∈ dist.support
    · rw [h ys hys]
    · have h0 : dist ys = 0 := (PMF.apply_eq_zero_iff dist ys).2 hys
      rw [h0, zero_mul, zero_mul]
  rw [expectedTime, hsum, PMF.expectENN_const]

/-- **Constant running time on all rearrangements gives that expected time.** Let $A$ be an
algorithm on lists whose running time $T_A(y)$ on each list $y$ is a natural number, let
$x = (x_0, \dots, x_{n-1})$ be a list of length $n$, and let $c$ be a natural number. If
$T_A(x_{\sigma(0)}, \dots, x_{\sigma(n-1)}) = c$ for every permutation $\sigma$ of
$\{0, \dots, n-1\}$, then the expected running time of $A$ when its input is $x$ rearranged by a
uniformly random permutation equals $c$. -/
theorem expectedTime_uniformPermutation_eq_of_time_eq
    (algo : List α → TimeM Nat β) (xs : List α) (c : ℕ)
    (h : ∀ σ : Equiv.Perm (Fin xs.length),
      (algo (List.ofFn (fun p => xs.get (σ p)))).time = c) :
    expectedTime algo (uniformPermutation xs) = (c : ℝ≥0∞) := by
  refine expectedTime_eq_of_time_eq algo _ c fun ys hys => ?_
  rw [uniformPermutation, PMF.mem_support_map_iff] at hys
  obtain ⟨σ, -, rfl⟩ := hys
  exact h σ

/-- **Average formula for the expected time over random orderings, in the reals.** Let $A$ be an
algorithm on lists whose running time $T_A(y)$ on each list $y$ is a natural number, and let
$x = (x_0, \dots, x_{n-1})$ be a list of length $n$. The expected running time of $A$ when its
input is $x$ rearranged by a uniformly random permutation, converted from $[0, \infty]$ to a real
number, equals
$$\frac{1}{n!} \sum_{\sigma} T_A(x_{\sigma(0)}, \dots, x_{\sigma(n-1)}),$$
the sum running over all permutations $\sigma$ of $\{0, \dots, n-1\}$ and computed in $\mathbb{R}$.

Every term of the average is a natural number, so the expected time is finite and the conversion
loses nothing. -/
theorem expectedTime_uniformPermutation_toReal
    (algo : List α → TimeM Nat β) (xs : List α) :
    (expectedTime algo (uniformPermutation xs)).toReal =
      (Nat.factorial xs.length : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin xs.length),
          ((algo (List.ofFn (fun p => xs.get (σ p)))).time : ℝ) := by
  rw [expectedTime_uniformPermutation, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun σ _ => ENNReal.natCast_ne_top _)]
  exact congrArg _ (Finset.sum_congr rfl fun σ _ =>
    ENNReal.toReal_natCast _)

end Cslib.Algorithms.Lean.TimeM
