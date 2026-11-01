/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Holm

/-!
# The closed testing principle; Holm's procedure as a closed test

For hypotheses `H₁, …, Hₘ` and every index set `J ⊆ {1, …, m}`, let `H_J = ⋂_{j ∈ J} H_j`
be the intersection hypothesis and suppose a *local* test of `H_J` is given. The closed
testing procedure of Marcus, Peritz and Gabriel rejects `Hᵢ` exactly when every local test of
an `H_J` with `i ∈ J` rejects (`closedRejections`).

If `H0` is the set of true nulls, a family-wise error (some `i ∈ H0` rejected) forces the
local test of `H_{H0}` itself to reject, because `H0` contains `i`. So when each local test
has level `α`, the closed procedure controls the family-wise error rate at `α` whatever the
set of true nulls is (strong control; `measure_closed_familywiseError_le`).

With the Bonferroni local tests ("reject `H_J` if some `p_j ≤ α / |J|`",
`bonferroniLocalTest`), the closed procedure rejects exactly the hypotheses Holm's step-down
procedure rejects (`holmRejections_eq_closedRejections`).

Local tests are represented by the decision they take on the observed data:
`φ : Finset (Fin m) → Prop` (deterministic) or `φ : Finset (Fin m) → Ω → Prop` (random).
The decision for `J = ∅` never matters, since `i ∈ J` is required.

## Main results

* `inter_nonempty_closedRejections`: a family-wise error forces the local test of the true
  null set to reject.
* `measure_closed_familywiseError_le`: the closed testing principle.
* `measure_bonferroniLocalTest_le`: the Bonferroni local test has level `α`.
* `holmRejections_eq_closedRejections`: Holm's procedure is the closure of the Bonferroni
  local tests.

## References

* R. Marcus, E. Peritz and K. R. Gabriel, *On closed testing procedures with special
  reference to ordered analysis of variance*, Biometrika 63 (1976), 655–660.
* S. Holm, *A simple sequentially rejective multiple test procedure*, Scand. J. Statist. 6
  (1979), 65–70.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- The closed testing procedure: given the decisions `φ J` of local tests of the intersection
hypotheses `H_J`, reject `Hᵢ` exactly when `φ J` holds for every `J` containing `i`. -/
noncomputable def closedRejections (φ : Finset (Fin m) → Prop) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => ∀ J : Finset (Fin m), i ∈ J → φ J

/-- Membership in the closed rejection set. -/
theorem mem_closedRejections {φ : Finset (Fin m) → Prop} {i : Fin m} :
    i ∈ closedRejections φ ↔ ∀ J : Finset (Fin m), i ∈ J → φ J := by
  classical
  unfold closedRejections
  convert Finset.mem_filter (s := Finset.univ) (p := fun i => ∀ J : Finset (Fin m), i ∈ J → φ J)
  simp

/-- If the closed procedure rejects a hypothesis in `H0`, then the local test of the
intersection hypothesis `H_{H0}` rejects. -/
theorem inter_nonempty_closedRejections {φ : Finset (Fin m) → Prop} {H0 : Finset (Fin m)}
    (h : (closedRejections φ ∩ H0).Nonempty) : φ H0 := by
  obtain ⟨i, hi⟩ := h
  rw [Finset.mem_inter, mem_closedRejections] at hi
  exact hi.1 H0 hi.2

/-- **The closed testing principle.** If `H0` is the set of true nulls and the local test of
`H_{H0}` rejects with probability at most `α`, then the closed procedure rejects some true
null with probability at most `α`. Applied to every possible `H0`, local level-`α` tests give
strong control of the family-wise error rate. No assumption on the dependence between local
tests is made.

Source: Marcus, Peritz and Gabriel (1976). -/
theorem measure_closed_familywiseError_le (μ : Measure Ω) (φ : Finset (Fin m) → Ω → Prop)
    (H0 : Finset (Fin m)) {α : ENNReal} (hlocal : μ {ω | φ H0 ω} ≤ α) :
    μ {ω | (closedRejections (fun J => φ J ω) ∩ H0).Nonempty} ≤ α := by
  refine le_trans (measure_mono ?_) hlocal
  intro ω hω
  exact inter_nonempty_closedRejections hω

/-- The Bonferroni local test of the intersection hypothesis `H_J` at level `α`: reject when
some `j ∈ J` has `p j ≤ α / |J|`. (It never rejects `H_∅`.) -/
def bonferroniLocalTest (α : ℝ) (p : Fin m → ℝ) (J : Finset (Fin m)) : Prop :=
  ∃ j ∈ J, p j ≤ α / J.card

/-- The Bonferroni local test of `H_{H0}` has level `α ∈ [0, 1]` when the p-values in `H0`
are valid. -/
theorem measure_bonferroniLocalTest_le (μ : Measure Ω) (p : Fin m → Ω → ℝ)
    (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) :
    μ {ω | bonferroniLocalTest α (fun i => p i ω) H0} ≤ ENNReal.ofReal α := by
  rcases H0.eq_empty_or_nonempty with rfl | hne
  · simp [bonferroniLocalTest]
  have hc1 : (1 : ℝ) ≤ H0.card := by exact_mod_cast hne.card_pos
  have hc0 : (0 : ℝ) < H0.card := by linarith
  have hc : α / H0.card ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hα₀ hc0.le, (div_le_one hc0).2 (hα₁.trans hc1)⟩
  refine (measure_exists_mem_le_le μ p H0 hnull hc).trans_eq ?_
  rw [mul_div_cancel₀ α hc0.ne']

/-- **Holm's procedure is a closed test.** For `α ≥ 0`, the hypotheses rejected by Holm's
step-down procedure are exactly those rejected by the closed testing procedure built on the
Bonferroni local tests.

Source: Holm (1979) introduces the procedure; the closure is that of Marcus, Peritz and
Gabriel (1976). -/
theorem holmRejections_eq_closedRejections {α : ℝ} (hα : 0 ≤ α) (p : Fin m → ℝ) :
    holmRejections α p = closedRejections (bonferroniLocalTest α p) := by
  classical
  ext i
  rw [mem_closedRejections]
  constructor
  · intro hi J hiJ
    exact exists_le_div_card_of_holmRejections hα p J ⟨i, Finset.mem_inter.mpr ⟨hi, hiJ⟩⟩
  · intro hcl
    by_contra hi
    set r := holmIndex α p with hr_def
    have hcard := card_holmRejections hα p
    have hrm : r < m := by
      have hsub : holmRejections α p ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun h => hi (h ▸ by simp)⟩
      have := Finset.card_lt_card hsub
      rw [Finset.card_univ, Fintype.card_fin, hcard] at this
      exact this
    have hpi : α / ((m : ℝ) - r + 1) < p i := by
      simp only [holmRejections, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      exact hi
    -- the threshold of the failed step `r + 1`
    set t := α / ((m : ℝ) - (r + 1 : ℕ) + 1) with ht_def
    have hfail : numBelow p t ≤ r := by
      by_contra hlt
      have hle : r + 1 ≤ r := le_holmIndex (by omega) fun k hk => by
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        rcases Nat.lt_or_ge k (r + 1) with hkr | hkr
        · exact le_numBelow_of_le_holmIndex hk1 (by omega)
        · have : k = r + 1 := by omega
          subst this
          change r + 1 ≤ numBelow p t
          omega
      omega
    set A := Finset.univ.filter fun l => ¬ p l ≤ t with hA_def
    have hAcard : m - r ≤ A.card := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (fun l => p l ≤ t)
      rw [Finset.card_univ, Fintype.card_fin] at h
      change numBelow p t + A.card = m at h
      omega
    obtain ⟨j, hjJ, hj⟩ := hcl (insert i A) (Finset.mem_insert_self i A)
    have hmr : (0 : ℝ) < (m : ℝ) - r := by
      have : (r : ℝ) < m := by exact_mod_cast hrm
      linarith
    have ht' : t = α / ((m : ℝ) - r) := by rw [ht_def]; push_cast; ring_nf
    have hAle : ((m : ℝ) - r) ≤ A.card := by
      have : ((m - r : ℕ) : ℝ) ≤ A.card := by exact_mod_cast hAcard
      rwa [Nat.cast_sub hrm.le] at this
    have hJle : (A.card : ℝ) ≤ (insert i A).card := by
      exact_mod_cast Finset.card_le_card (Finset.subset_insert i A)
    have hdiv : α / ((insert i A).card : ℝ) ≤ t := by
      rw [ht']
      exact div_le_div_of_nonneg_left hα hmr (hAle.trans hJle)
    rcases Finset.mem_insert.mp hjJ with rfl | hjA
    · by_cases hjA : j ∈ A
      · have : t < p j := lt_of_not_ge (Finset.mem_filter.mp hjA).2
        linarith
      · have hc : ((m : ℝ) - r + 1) ≤ (insert j A).card := by
          rw [Finset.card_insert_of_notMem hjA]
          push_cast
          linarith
        have : α / ((insert j A).card : ℝ) ≤ α / ((m : ℝ) - r + 1) :=
          div_le_div_of_nonneg_left hα (by linarith) hc
        linarith
    · have : t < p j := lt_of_not_ge (Finset.mem_filter.mp hjA).2
      linarith

end MathlibExt.Probability.Statistics.MultipleTesting
