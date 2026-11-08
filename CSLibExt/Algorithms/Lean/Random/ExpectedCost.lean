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

/-- The **expected running time** of a `TimeM Nat` algorithm under an input
distribution on an arbitrary input type `γ`, valued in `ℝ≥0∞`: the
extended expectation of `algo`'s tick count when the input is drawn from
`dist`. Valuing the
expectation in `ℝ≥0∞` (via `PMF.expectENN`) records a divergent expected
time as `∞`; the real-valued Bochner integral would collapse it to `0`. -/
noncomputable def expectedTime (algo : γ → TimeM Nat β)
    (dist : PMF γ) : ℝ≥0∞ :=
  dist.expectENN (fun xs => ((algo xs).time : ℝ≥0∞))

/-- The distribution of `xs` with its entries rearranged by a uniformly
random permutation of the indices. -/
noncomputable def uniformPermutation (xs : List α) : PMF (List α) :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin xs.length))).map
    (fun σ => List.ofFn (fun p => xs.get (σ p)))

/-- A permuted list has the same length as the original. -/
theorem uniformPermutation_length (xs : List α)
    (ys : List α) (hys : ys ∈ (uniformPermutation xs).support) :
    ys.length = xs.length := by
  rw [uniformPermutation, PMF.mem_support_map_iff] at hys
  obtain ⟨σ, -, rfl⟩ := hys
  exact List.length_ofFn

/-- A permuted list is a permutation of the original. -/
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

/-- The expected running time over the uniform permutation of a list is
the average of the costs over all permutations of the indices. -/
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

/-- If the running time is the same constant `c` on every input in the
support of `dist`, the expected running time is `c`. Terms outside the
support have weight `dist ys = 0`, so the defining `tsum` agrees termwise
with the constant observable and `PMF.expectENN_const` applies. -/
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

/-- If the running time is the same constant `c` on every permutation of
`xs`, the expected running time over the uniform permutation is `c`. -/
theorem expectedTime_uniformPermutation_eq_of_time_eq
    (algo : List α → TimeM Nat β) (xs : List α) (c : ℕ)
    (h : ∀ σ : Equiv.Perm (Fin xs.length),
      (algo (List.ofFn (fun p => xs.get (σ p)))).time = c) :
    expectedTime algo (uniformPermutation xs) = (c : ℝ≥0∞) := by
  refine expectedTime_eq_of_time_eq algo _ c fun ys hys => ?_
  rw [uniformPermutation, PMF.mem_support_map_iff] at hys
  obtain ⟨σ, -, rfl⟩ := hys
  exact h σ

/-- Bridge to real-valued bounds: the `toReal` of the expected running
time over the uniform permutation is the real average of the costs over
all permutations. Derived from the `ℝ≥0∞` average by pushing `toReal`
through the product, inverse and finite sum (every term is a natural
cast, hence finite). -/
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
