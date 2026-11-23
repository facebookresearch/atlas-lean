/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CompetingRisks
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Aalen–Johansen estimator as a product-integral of transition matrices

For a finite state space `ι` and a matrix-valued cumulative intensity `Λ : ℝ → Matrix ι ι ℝ`, the
**product-integral** of `Λ` over `[s, t]` is the limit, over refinements of partitions
`s = p₀ < p₁ < ⋯ < pₘ = t`, of the time-ordered products

  `(I + Λ(p₁) - Λ(p₀)) (I + Λ(p₂) - Λ(p₁)) ⋯ (I + Λ(pₘ) - Λ(pₘ₋₁))`.

The **Aalen–Johansen estimator** of the transition matrix of a non-homogeneous Markov chain is the
product-integral of the Nelson–Aalen estimator of the cumulative transition intensities. That
estimator is a step function with jumps `ΔΛ(tⱼ) = Aⱼ` at the observation times `t₀ < ⋯ < t_{k-1}`,
`ΔΛ_{hl}(tⱼ) = N_{hl}(tⱼ) / Y_h(tⱼ)` for `h ≠ l` and `ΔΛ_{hh}(tⱼ) = -∑_{l ≠ h} ΔΛ_{hl}(tⱼ)`.

## Main definitions

* `Partition s t`: finite subsets of `[s, t]` containing `s` and `t`, directed by inclusion
  (refinement); `partitionProd Λ P` is the time-ordered product of `I + ΔΛ` over `P`.
* `HasProdIntegral Λ s t M`: `partitionProd Λ P → M` along the refinement net.
* `stepCumHazard time A`: the step function `u ↦ ∑_{tⱼ ≤ u} Aⱼ`; `jumpProd time A s t` is the
  time-ordered product `∏_{s < tⱼ ≤ t} (I + Aⱼ)`, and `jumpProdLT time A s t` the product over
  `s < tⱼ < t` (the left limit `P(s, t-)`).
* `MultiStateData`: grouped multi-state data (`transitions j h l = N_{hl}(tⱼ)`,
  `atRisk j h = Y_h(tⱼ)`), with Nelson–Aalen jumps `naIncrement`, cumulative intensity
  `naCumHazard` and Aalen–Johansen estimator `transitionMatrix s t`.
* `CompetingRisks.CompetingRiskData.toMultiState`: the competing-risks model of
  `CompetingRisks.lean` as a multi-state model on `Option (Fin r)` (`none` is the transient state,
  `some c` is absorption by cause `c`).

## Main results

* `HasProdIntegral.unique`: the product-integral over `[s, t]`, `s ≤ t`, is unique.
* `hasProdIntegral_stepCumHazard`: the product-integral of a step function exists and equals
  `jumpProd`; every partition containing the jump times in `(s, t]` already gives this value.
* `jumpProd_eq_one_add_sum` (and `HasProdIntegral.forward_eq_of_step`): the **forward
  (Kolmogorov / Volterra) integral equation** `P(s, t) = I + ∫_{(s,t]} P(s, u-) dΛ(u)`, which for a
  pure-jump `Λ` reads `P(s, t) = I + ∑_{s < tⱼ ≤ t} P(s, tⱼ-) Aⱼ`.
* `jumpProd_mul`: Chapman–Kolmogorov, `P(s, u) P(u, t) = P(s, t)` for `s ≤ u ≤ t`.
* `MultiStateData.hasProdIntegral_transitionMatrix`: the Aalen–Johansen estimator is the
  product-integral of the Nelson–Aalen estimator; `transitionMatrix_sum_row` and
  `transitionMatrix_nonneg`: it is a stochastic matrix (the latter when at most `Y_h(tⱼ)` subjects
  leave `h` at `tⱼ`).
* `CompetingRiskData.transitionMatrix_none_some`, `transitionMatrix_none_none`: on the
  competing-risks model, starting before the first observation time, the Aalen–Johansen matrix has
  entries `P_{0,c}(s, t) = F̂_c(t)` (the increment-form cumulative incidence
  `CompetingRiskData.cumulativeIncidence`) and `P_{00}(s, t) = Ŝ(t)` (Kaplan–Meier);
  `CompetingRiskData.hasProdIntegral_cumulativeIncidence` and
  `CompetingRiskData.eq_of_hasProdIntegral` state the same for any product-integral of
  the Nelson–Aalen intensity.

## Scope

The product-integral is defined for an arbitrary `Λ`, but existence is proved only for step
functions with finitely many jumps, the case of every Nelson–Aalen / Aalen–Johansen estimate.
Existence for general right-continuous `Λ` of bounded variation (Gill–Johansen), the forward
equation as a Lebesgue–Stieltjes integral for such `Λ`, and large-sample theory are not covered.
The at-risk counts `Y_h(tⱼ)` of `MultiStateData` are data, not derived from individual paths.

## References

* O. O. Aalen and S. Johansen, *An empirical transition matrix for non-homogeneous Markov chains
  based on censored observations*, Scand. J. Statist. 5 (1978), 141–150.
* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Sections II.6 and IV.4.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.AalenJohansenProductIntegral

open Finset Filter Topology Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Products over partitions and the product-integral -/

/-- The time-ordered product of `I + Λ(b) - Λ(a)` over consecutive points `a, b` of a list. -/
noncomputable def chainProd (Λ : ℝ → Matrix ι ι ℝ) : List ℝ → Matrix ι ι ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: l => (1 + (Λ b - Λ a)) * chainProd Λ (b :: l)

@[simp] theorem chainProd_nil (Λ : ℝ → Matrix ι ι ℝ) : chainProd Λ [] = 1 := rfl

@[simp] theorem chainProd_singleton (Λ : ℝ → Matrix ι ι ℝ) (a : ℝ) : chainProd Λ [a] = 1 := rfl

theorem chainProd_cons_cons (Λ : ℝ → Matrix ι ι ℝ) (a b : ℝ) (l : List ℝ) :
    chainProd Λ (a :: b :: l) = (1 + (Λ b - Λ a)) * chainProd Λ (b :: l) := rfl

/-- The time-ordered product `∏ (I + Λ(pᵢ₊₁) - Λ(pᵢ))` over the points of a finite set. -/
noncomputable def partitionProd (Λ : ℝ → Matrix ι ι ℝ) (P : Finset ℝ) : Matrix ι ι ℝ :=
  chainProd Λ (P.sort (· ≤ ·))

/-- Partitions of `[s, t]`: finite subsets of `[s, t]` containing both endpoints, ordered by
inclusion, so that `P ≤ Q` means `Q` refines `P`. -/
abbrev Partition (s t : ℝ) : Type := {P : Finset ℝ // s ∈ P ∧ t ∈ P ∧ ∀ x ∈ P, s ≤ x ∧ x ≤ t}

instance (s t : ℝ) : IsDirected (Partition s t) (· ≤ ·) where
  directed P Q := ⟨⟨P.1 ∪ Q.1, mem_union_left _ P.2.1, mem_union_left _ P.2.2.1, fun x hx =>
    (mem_union.1 hx).elim (P.2.2.2 x) (Q.2.2.2 x)⟩, subset_union_left, subset_union_right⟩

/-- The two-point partition `{s, t}` of `[s, t]`. -/
noncomputable def Partition.endpoints {s t : ℝ} (hst : s ≤ t) : Partition s t :=
  ⟨{s, t}, mem_insert_self _ _, mem_insert_of_mem (mem_singleton_self _), fun x hx => by
    rcases mem_insert.1 hx with rfl | hx
    · exact ⟨le_rfl, hst⟩
    · rw [mem_singleton.1 hx]; exact ⟨hst, le_rfl⟩⟩

/-- `M` is the **product-integral** of `Λ` over `[s, t]`: the time-ordered products of
`I + ΔΛ` over partitions of `[s, t]` converge to `M` along refinements. -/
def HasProdIntegral (Λ : ℝ → Matrix ι ι ℝ) (s t : ℝ) (M : Matrix ι ι ℝ) : Prop :=
  Tendsto (fun P : Partition s t => partitionProd Λ P.1) atTop (𝓝 M)

/-- The product-integral over a non-degenerate interval is unique. -/
theorem HasProdIntegral.unique {Λ : ℝ → Matrix ι ι ℝ} {s t : ℝ} (hst : s ≤ t)
    {M M' : Matrix ι ι ℝ} (h : HasProdIntegral Λ s t M) (h' : HasProdIntegral Λ s t M') :
    M = M' := by
  have : Nonempty (Partition s t) := ⟨Partition.endpoints hst⟩
  exact tendsto_nhds_unique h h'

/-! ### Time-ordered products over a finite grid -/

section Ordered

variable {k : ℕ}

/-- The time-ordered product `∏ⱼ (I + Aⱼ)` over the indices `j` satisfying `act j`, in increasing
order of `j`. -/
noncomputable def orderedProd (A : Fin k → Matrix ι ι ℝ) (act : Fin k → Prop)
    [DecidablePred act] : Matrix ι ι ℝ :=
  (List.ofFn fun j => if act j then 1 + A j else 1).prod

theorem orderedProd_congr (A : Fin k → Matrix ι ι ℝ) {act act' : Fin k → Prop}
    [DecidablePred act] [DecidablePred act'] (h : ∀ j, act j ↔ act' j) :
    orderedProd A act = orderedProd A act' := by
  unfold orderedProd
  congr 1
  exact List.ofFn_inj.2 (funext fun j => if_congr (h j) rfl rfl)

theorem orderedProd_zero (A : Fin 0 → Matrix ι ι ℝ) (act : Fin 0 → Prop) [DecidablePred act] :
    orderedProd A act = 1 := rfl

theorem orderedProd_succ (A : Fin (k + 1) → Matrix ι ι ℝ) (act : Fin (k + 1) → Prop)
    [DecidablePred act] :
    orderedProd A act = orderedProd (fun i => A i.castSucc) (fun i => act i.castSucc) *
      (if act (Fin.last k) then 1 + A (Fin.last k) else 1) := by
  rw [orderedProd, List.ofFn_succ', List.prod_concat]
  rfl

theorem orderedProd_of_forall_not (A : Fin k → Matrix ι ι ℝ) {act : Fin k → Prop}
    [DecidablePred act] (h : ∀ j, ¬ act j) : orderedProd A act = 1 := by
  have : (fun j => if act j then 1 + A j else 1) = fun _ => (1 : Matrix ι ι ℝ) :=
    funext fun j => ite_eq_right (h j)
  rw [orderedProd, this, List.ofFn_const, List.prod_replicate, one_pow]

theorem orderedProd_of_unique : ∀ {k : ℕ} (A : Fin k → Matrix ι ι ℝ) {act : Fin k → Prop}
    [DecidablePred act] (j₀ : Fin k), act j₀ → (∀ j, act j → j = j₀) →
    orderedProd A act = 1 + A j₀
  | 0, _, _, _, j₀, _, _ => j₀.elim0
  | k + 1, A, act, _, j₀, h₀, h => by
    rw [orderedProd_succ]
    by_cases hj : j₀ = Fin.last k
    · subst hj
      rw [orderedProd_of_forall_not _ fun i hi => Fin.castSucc_ne_last i (h _ hi), one_mul,
        ite_eq_left h₀]
    · obtain ⟨j₁, rfl⟩ := Fin.exists_castSucc_eq.2 hj
      rw [orderedProd_of_unique _ j₁ h₀ fun i hi => Fin.castSucc_injective _ (h _ hi),
        ite_eq_right fun hl => hj (h _ hl).symm, mul_one]

end Ordered

/-! ### Step functions -/

section Step

variable {k : ℕ}

/-- The step function `u ↦ ∑_{tⱼ ≤ u} Aⱼ` with jumps `Aⱼ` at the times `tⱼ`. -/
noncomputable def stepCumHazard (time : Fin k → ℝ) (A : Fin k → Matrix ι ι ℝ) (u : ℝ) :
    Matrix ι ι ℝ :=
  ∑ j, if time j ≤ u then A j else 0

/-- The time-ordered product `∏_{s < tⱼ ≤ t} (I + Aⱼ)`. -/
noncomputable def jumpProd (time : Fin k → ℝ) (A : Fin k → Matrix ι ι ℝ) (s t : ℝ) :
    Matrix ι ι ℝ :=
  orderedProd A fun j => s < time j ∧ time j ≤ t

/-- The time-ordered product `∏_{s < tⱼ < t} (I + Aⱼ)`, the left limit `P(s, t-)`. -/
noncomputable def jumpProdLT (time : Fin k → ℝ) (A : Fin k → Matrix ι ι ℝ) (s t : ℝ) :
    Matrix ι ι ℝ :=
  orderedProd A fun j => s < time j ∧ time j < t

omit [Fintype ι] [DecidableEq ι] in
theorem stepCumHazard_sub (time : Fin k → ℝ) (A : Fin k → Matrix ι ι ℝ) {a b : ℝ} (hab : a ≤ b) :
    stepCumHazard time A b - stepCumHazard time A a =
      ∑ j, if a < time j ∧ time j ≤ b then A j else 0 := by
  rw [stepCumHazard, stepCumHazard, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases ha : time j ≤ a
  · simp [ha, ha.trans hab, not_lt.2 ha]
  · by_cases hb : time j ≤ b <;> simp [ha, hb, lt_of_not_ge ha]

theorem jumpProd_self (time : Fin k → ℝ) (A : Fin k → Matrix ι ι ℝ) (a : ℝ) :
    jumpProd time A a a = 1 :=
  orderedProd_of_forall_not _ fun _ h => lt_irrefl _ (h.1.trans_le h.2)

/-- An increment `I + Λ(b) - Λ(a)` of a step function over an interval `(a, b]` that contains no
jump time other than possibly `b` is the time-ordered product of `I + Aⱼ` over `(a, b]`. -/
theorem one_add_stepCumHazard_sub (time : Fin k → ℝ) (htime : Function.Injective time)
    (A : Fin k → Matrix ι ι ℝ) {a b : ℝ} (hab : a ≤ b)
    (hjump : ∀ j, a < time j → time j ≤ b → time j = b) :
    1 + (stepCumHazard time A b - stepCumHazard time A a) = jumpProd time A a b := by
  rw [stepCumHazard_sub time A hab, jumpProd]
  by_cases h : ∃ j, a < time j ∧ time j ≤ b
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j, a < time j ∧ time j ≤ b → j = j₀ := fun j hj =>
      htime ((hjump j hj.1 hj.2).trans (hjump j₀ hj₀.1 hj₀.2).symm)
    rw [orderedProd_of_unique A j₀ hj₀ huniq, sum_eq_single j₀
      (fun j _ hj => ite_eq_right fun h => hj (huniq j h)) (fun h => (h (mem_univ _)).elim),
      ite_eq_left hj₀]
  · push Not at h
    rw [orderedProd_of_forall_not A fun j hj => (h j hj.1).not_ge hj.2,
      sum_eq_zero fun j _ => ite_eq_right fun hj => (h j hj.1).not_ge hj.2, add_zero]

/-- **Chapman–Kolmogorov** for time-ordered jump products: `P(a, b) P(b, c) = P(a, c)`. -/
theorem jumpProd_mul : ∀ {k : ℕ} (time : Fin k → ℝ) (_ : Monotone time)
    (A : Fin k → Matrix ι ι ℝ) {a b c : ℝ}, a ≤ b → b ≤ c →
    jumpProd time A a b * jumpProd time A b c = jumpProd time A a c
  | 0, _, _, _, _, _, _, _, _ => by simp [jumpProd, orderedProd_zero]
  | k + 1, time, hmono, A, a, b, c, hab, hbc => by
    have ih := jumpProd_mul (fun i : Fin k => time i.castSucc)
      (hmono.comp (Fin.strictMono_castSucc).monotone) (fun i => A i.castSucc) hab hbc
    simp only [jumpProd] at ih ⊢
    rw [orderedProd_succ, orderedProd_succ, orderedProd_succ]
    set T := time (Fin.last k)
    by_cases hT : T ≤ b
    · have hone : orderedProd (fun i : Fin k => A i.castSucc)
          (fun i => b < time i.castSucc ∧ time i.castSucc ≤ c) = 1 :=
        orderedProd_of_forall_not _ fun i hi =>
          (hmono (Fin.le_last i.castSucc)).not_gt (hT.trans_lt hi.1)
      have hbc' : (if b < T ∧ T ≤ c then 1 + A (Fin.last k) else 1) = 1 :=
        ite_eq_right fun h => lt_irrefl _ (h.1.trans_le hT)
      have hac : (if a < T ∧ T ≤ c then 1 + A (Fin.last k) else 1) =
          if a < T ∧ T ≤ b then 1 + A (Fin.last k) else 1 :=
        if_congr ⟨fun h => ⟨h.1, hT⟩, fun h => ⟨h.1, h.2.trans hbc⟩⟩ rfl rfl
      rw [hone, mul_one] at ih
      rw [hone, hbc', hac, one_mul, mul_one, ← ih]
    · push Not at hT
      have hab' : (if a < T ∧ T ≤ b then 1 + A (Fin.last k) else 1) = 1 :=
        ite_eq_right fun h => hT.not_ge h.2
      have hac : (if a < T ∧ T ≤ c then 1 + A (Fin.last k) else 1) =
          if b < T ∧ T ≤ c then 1 + A (Fin.last k) else 1 :=
        if_congr ⟨fun h => ⟨hT, h.2⟩, fun h => ⟨hab.trans_lt h.1, h.2⟩⟩ rfl rfl
      rw [hab', hac, mul_one, ← ih, mul_assoc]

/-- A strictly sorted list containing every jump time in `(a, z]`, starting at `a` and ending at
`z`, has chain product equal to the time-ordered jump product over `(a, z]`. -/
theorem chainProd_eq_jumpProd (time : Fin k → ℝ) (htime : StrictMono time)
    (A : Fin k → Matrix ι ι ℝ) :
    ∀ (l : List ℝ) (a z : ℝ), (a :: l).Pairwise (· < ·) → z ∈ a :: l →
      (∀ x ∈ a :: l, x ≤ z) → (∀ j, a < time j → time j ≤ z → time j ∈ a :: l) →
      chainProd (stepCumHazard time A) (a :: l) = jumpProd time A a z
  | [], a, z, _, hz, _, _ => by
    rw [List.mem_singleton.1 hz, chainProd_singleton, jumpProd_self]
  | b :: l, a, z, hsort, hz, hle, hjump => by
    have hab : a < b := List.rel_of_pairwise_cons hsort (List.mem_cons_self ..)
    have hrest : ∀ x ∈ l, b < x := fun x hx =>
      List.rel_of_pairwise_cons (List.pairwise_cons.1 hsort).2 hx
    have hbz : b ≤ z := hle b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hz' : z ∈ b :: l := by
      rcases List.mem_cons.1 hz with rfl | hz
      · exact absurd (hab.trans_le hbz) (lt_irrefl _)
      · exact hz
    have hmem : ∀ j, a < time j → time j ≤ z → time j ∈ b :: l := fun j ha hz => by
      rcases List.mem_cons.1 (hjump j ha hz) with h | h
      · exact absurd h (ne_of_gt ha)
      · exact h
    rw [chainProd_cons_cons, chainProd_eq_jumpProd time htime A l b z
        (List.pairwise_cons.1 hsort).2 hz' (fun x hx => hle x (List.mem_cons_of_mem _ hx))
        (fun j hb hz => hmem j (hab.trans hb) hz),
      one_add_stepCumHazard_sub time htime.injective A hab.le fun j ha hb => ?_,
      jumpProd_mul time htime.monotone A hab.le hbz]
    rcases List.mem_cons.1 (hmem j ha (hb.trans hbz)) with h | h
    · exact h
    · exact absurd hb (not_le.2 (hrest _ h))

/-- The sorted list of a partition of `[s, t]` starts at `s`, ends at `t` and is strictly
increasing. -/
theorem Partition.sort_eq_cons {s t : ℝ} (P : Partition s t) :
    ∃ l, P.1.sort (· ≤ ·) = s :: l := by
  have hlt : (P.1.sort (· ≤ ·)).Pairwise (· < ·) :=
    ((pairwise_sort P.1 (· ≤ ·)).and (sort_nodup P.1 (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2
  match hl : P.1.sort (· ≤ ·), hlt with
  | [], _ => exact absurd ((mem_sort _).2 P.2.1) (by rw [hl]; simp)
  | a :: l, hlt =>
    have hs : s ∈ a :: l := hl ▸ (mem_sort _).2 P.2.1
    have ha : a ∈ P.1 := (mem_sort (· ≤ ·)).1 (hl ▸ List.mem_cons_self ..)
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨l, rfl⟩
    · exact absurd (List.rel_of_pairwise_cons hlt hs) (not_lt.2 (P.2.2.2 a ha).1)

/-- Every partition of `[s, t]` containing the jump times in `(s, t]` has partition product equal
to the time-ordered jump product. -/
theorem partitionProd_stepCumHazard (time : Fin k → ℝ) (htime : StrictMono time)
    (A : Fin k → Matrix ι ι ℝ) {s t : ℝ} (P : Partition s t)
    (hP : ∀ j, s < time j → time j ≤ t → time j ∈ P.1) :
    partitionProd (stepCumHazard time A) P.1 = jumpProd time A s t := by
  obtain ⟨l, hl⟩ := P.sort_eq_cons
  have hlt : (P.1.sort (· ≤ ·)).Pairwise (· < ·) :=
    ((pairwise_sort P.1 (· ≤ ·)).and (sort_nodup P.1 (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2
  rw [partitionProd, hl]
  rw [hl] at hlt
  refine chainProd_eq_jumpProd time htime A l s t hlt ?_ ?_ ?_
  · rw [← hl, mem_sort]; exact P.2.2.1
  · intro x hx
    rw [← hl, mem_sort] at hx
    exact (P.2.2.2 x hx).2
  · intro j hs ht
    rw [← hl, mem_sort]
    exact hP j hs ht

/-- The partition of `[s, t]` by its endpoints and the jump times in `(s, t]`. -/
noncomputable def Partition.ofJumps (time : Fin k → ℝ) {s t : ℝ} (hst : s ≤ t) : Partition s t :=
  ⟨insert s (insert t ((univ.filter fun j => s < time j ∧ time j ≤ t).image time)),
    mem_insert_self _ _, mem_insert_of_mem (mem_insert_self _ _), fun x hx => by
      simp only [mem_insert, mem_image, mem_filter, mem_univ, true_and] at hx
      rcases hx with rfl | rfl | ⟨j, hj, rfl⟩
      · exact ⟨le_rfl, hst⟩
      · exact ⟨hst, le_rfl⟩
      · exact ⟨hj.1.le, hj.2⟩⟩

/-- **The product-integral of a step function** exists and is the time-ordered product
`∏_{s < tⱼ ≤ t} (I + Aⱼ)` of the jumps. -/
theorem hasProdIntegral_stepCumHazard (time : Fin k → ℝ) (htime : StrictMono time)
    (A : Fin k → Matrix ι ι ℝ) {s t : ℝ} (hst : s ≤ t) :
    HasProdIntegral (stepCumHazard time A) s t (jumpProd time A s t) := by
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop (Partition.ofJumps time hst)).mono
    fun P hP => (partitionProd_stepCumHazard time htime A P fun j hs ht => hP ?_).symm)
  simp only [Partition.ofJumps, mem_insert, mem_image, mem_filter, mem_univ, true_and]
  exact Or.inr (Or.inr ⟨j, ⟨hs, ht⟩, rfl⟩)

/-- **Forward equation** for the time-ordered jump product:
`P(s, t) = I + ∑_{s < tⱼ ≤ t} P(s, tⱼ-) Aⱼ`, the integral equation
`P(s, t) = I + ∫_{(s,t]} P(s, u-) dΛ(u)` for the pure-jump `Λ = stepCumHazard time A`. -/
theorem jumpProd_eq_one_add_sum : ∀ {k : ℕ} (time : Fin k → ℝ) (_ : StrictMono time)
    (A : Fin k → Matrix ι ι ℝ) (s t : ℝ),
    jumpProd time A s t =
      1 + ∑ j, if s < time j ∧ time j ≤ t then jumpProdLT time A s (time j) * A j else 0
  | 0, _, _, _, _, _ => by simp [jumpProd, orderedProd_zero]
  | k + 1, time, htime, A, s, t => by
    have ih := jumpProd_eq_one_add_sum (fun i : Fin k => time i.castSucc)
      (htime.comp (Fin.strictMono_castSucc)) (fun i => A i.castSucc) s t
    simp only [jumpProd, jumpProdLT] at ih ⊢
    rw [orderedProd_succ, Fin.sum_univ_castSucc, ← add_assoc]
    have hcs : ∀ i : Fin k, orderedProd A (fun j => s < time j ∧ time j < time i.castSucc) =
        orderedProd (fun i : Fin k => A i.castSucc)
          (fun j => s < time j.castSucc ∧ time j.castSucc < time i.castSucc) := fun i => by
      rw [orderedProd_succ,
        ite_eq_right fun h => lt_irrefl _ (h.2.trans (htime (Fin.castSucc_lt_last i))), mul_one]
    simp only [hcs]
    rw [← ih]
    set T := time (Fin.last k)
    by_cases hT : s < T ∧ T ≤ t
    · have hlast : orderedProd A (fun j => s < time j ∧ time j < T) =
          orderedProd (fun i : Fin k => A i.castSucc)
            (fun i => s < time i.castSucc ∧ time i.castSucc ≤ t) := by
        rw [orderedProd_succ, ite_eq_right fun h => lt_irrefl _ h.2, mul_one]
        refine orderedProd_congr _ fun i => ?_
        have hi : time i.castSucc < T := htime (Fin.castSucc_lt_last i)
        exact ⟨fun h => ⟨h.1, h.2.le.trans hT.2⟩, fun h => ⟨h.1, hi⟩⟩
      rw [ite_eq_left hT, ite_eq_left hT, hlast, mul_add, mul_one]
    · rw [ite_eq_right hT, ite_eq_right hT, mul_one, add_zero]

end Step

/-- **The forward equation for the product-integral of a step function**: any product-integral
`M` of `stepCumHazard time A` over `[s, t]` satisfies `M = I + ∑_{s < tⱼ ≤ t} P(s, tⱼ-) Aⱼ`. -/
theorem HasProdIntegral.forward_eq_of_step {k : ℕ} {time : Fin k → ℝ} (htime : StrictMono time)
    {A : Fin k → Matrix ι ι ℝ} {s t : ℝ} (hst : s ≤ t) {M : Matrix ι ι ℝ}
    (hM : HasProdIntegral (stepCumHazard time A) s t M) :
    M = 1 + ∑ j, if s < time j ∧ time j ≤ t then jumpProdLT time A s (time j) * A j else 0 := by
  rw [hM.unique hst (hasProdIntegral_stepCumHazard time htime A hst),
    jumpProd_eq_one_add_sum time htime]

/-! ### Multi-state data and the Aalen–Johansen estimator -/

/-- Grouped multi-state data on the state space `ι` at `k` distinct increasing observation
times: at `time j`, `transitions j h l` subjects move from state `h` to state `l ≠ h` (diagonal
entries are ignored) and `atRisk j h` subjects are in state `h` just before `time j`. -/
structure MultiStateData (k : ℕ) (ι : Type*) where
  /-- The distinct observation times, in increasing order. -/
  time : Fin k → ℝ
  /-- The observation times are strictly increasing. -/
  strictMono_time : StrictMono time
  /-- The number of `h → l` transitions at each time. -/
  transitions : Fin k → ι → ι → ℕ
  /-- The number of subjects in each state just before each time. -/
  atRisk : Fin k → ι → ℕ

namespace MultiStateData

variable {k : ℕ} (D : MultiStateData k ι)

/-- The Nelson–Aalen jump of the cumulative transition intensities at `time j`:
`N_{hl}/Y_h` off the diagonal and `-∑_{l ≠ h} N_{hl}/Y_h` on it. -/
noncomputable def naIncrement (j : Fin k) : Matrix ι ι ℝ := fun h l =>
  if h = l then -(∑ l' ∈ univ.erase h, (D.transitions j h l' : ℝ)) / D.atRisk j h
  else (D.transitions j h l : ℝ) / D.atRisk j h

/-- The Nelson–Aalen estimator of the cumulative transition-intensity matrix. -/
noncomputable def naCumHazard : ℝ → Matrix ι ι ℝ := stepCumHazard D.time D.naIncrement

/-- The **Aalen–Johansen estimator** `P̂(s, t) = ∏_{s < tⱼ ≤ t} (I + ΔΛ̂(tⱼ))` of the transition
matrix. -/
noncomputable def transitionMatrix (s t : ℝ) : Matrix ι ι ℝ := jumpProd D.time D.naIncrement s t

/-- The Aalen–Johansen estimator is the product-integral of the Nelson–Aalen estimator. -/
theorem hasProdIntegral_transitionMatrix {s t : ℝ} (hst : s ≤ t) :
    HasProdIntegral D.naCumHazard s t (D.transitionMatrix s t) :=
  hasProdIntegral_stepCumHazard D.time D.strictMono_time D.naIncrement hst

/-- The forward equation for the Aalen–Johansen estimator. -/
theorem transitionMatrix_forward (s t : ℝ) :
    D.transitionMatrix s t = 1 + ∑ j, if s < D.time j ∧ D.time j ≤ t then
      jumpProdLT D.time D.naIncrement s (D.time j) * D.naIncrement j else 0 :=
  jumpProd_eq_one_add_sum D.time D.strictMono_time D.naIncrement s t

/-- Chapman–Kolmogorov for the Aalen–Johansen estimator. -/
theorem transitionMatrix_mul {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    D.transitionMatrix s u * D.transitionMatrix u t = D.transitionMatrix s t :=
  jumpProd_mul D.time D.strictMono_time.monotone D.naIncrement hsu hut

/-- The rows of a Nelson–Aalen jump sum to zero. -/
theorem sum_naIncrement_row (j : Fin k) (h : ι) : ∑ l, D.naIncrement j h l = 0 := by
  rw [← add_sum_erase _ _ (mem_univ h)]
  simp only [naIncrement, ↓reduceIte]
  rw [sum_congr rfl fun l hl => ite_eq_right (Ne.symm (ne_of_mem_erase hl)), ← sum_div, neg_div,
    neg_add_cancel]

/-- Time-ordered products of `I + Aⱼ` with zero row sums `Aⱼ` have unit row sums. -/
theorem orderedProd_mulVec_one : ∀ {k : ℕ} (A : Fin k → Matrix ι ι ℝ) (act : Fin k → Prop)
    [DecidablePred act], (∀ j, A j *ᵥ (fun _ => 1) = 0) →
    orderedProd A act *ᵥ (fun _ => 1) = fun _ => 1
  | 0, A, act, _, _ => by rw [orderedProd_zero, one_mulVec]
  | k + 1, A, act, _, hA => by
    rw [orderedProd_succ, ← mulVec_mulVec]
    have hlast : (if act (Fin.last k) then 1 + A (Fin.last k) else 1) *ᵥ (fun _ => (1 : ℝ)) =
        fun _ => 1 := by
      split_ifs
      · rw [add_mulVec, one_mulVec, hA, add_zero]
      · rw [one_mulVec]
    rw [hlast, orderedProd_mulVec_one _ _ fun j => hA _]

/-- **The Aalen–Johansen estimator has unit row sums.** -/
theorem transitionMatrix_sum_row (s t : ℝ) (h : ι) : ∑ l, D.transitionMatrix s t h l = 1 := by
  have := congr_fun (orderedProd_mulVec_one D.naIncrement
    (fun j => s < D.time j ∧ D.time j ≤ t) fun j => funext fun h' => by
      simp only [mulVec, dotProduct, mul_one, Pi.zero_apply]
      exact D.sum_naIncrement_row j h') h
  simpa [mulVec, dotProduct, transitionMatrix, jumpProd] using this

/-- Time-ordered products of entrywise non-negative matrices `I + Aⱼ` are entrywise
non-negative. -/
theorem orderedProd_nonneg : ∀ {k : ℕ} (A : Fin k → Matrix ι ι ℝ) (act : Fin k → Prop)
    [DecidablePred act], (∀ j h l, 0 ≤ (1 + A j) h l) → ∀ h l, 0 ≤ orderedProd A act h l
  | 0, A, act, _, _ => fun h l => by
    rw [orderedProd_zero, one_apply]; split_ifs <;> norm_num
  | k + 1, A, act, _, hA => fun h l => by
    rw [orderedProd_succ, mul_apply]
    refine sum_nonneg fun x _ => mul_nonneg (orderedProd_nonneg _ _ (fun j => hA _) h x) ?_
    split_ifs
    · exact hA _ x l
    · rw [one_apply]; split_ifs <;> norm_num

/-- **The Aalen–Johansen estimator is entrywise non-negative** when at most `Y_h(tⱼ)` subjects
leave each state `h` at each time `tⱼ`. -/
theorem transitionMatrix_nonneg
    (hD : ∀ j h, ∑ l ∈ univ.erase h, D.transitions j h l ≤ D.atRisk j h) (s t : ℝ) (h l : ι) :
    0 ≤ D.transitionMatrix s t h l := by
  refine orderedProd_nonneg _ _ (fun j h l => ?_) h l
  rw [Matrix.add_apply, one_apply, naIncrement]
  by_cases hhl : h = l
  · subst hhl
    simp only [↓reduceIte, neg_div]
    have hle : (∑ l' ∈ univ.erase h, (D.transitions j h l' : ℝ)) / D.atRisk j h ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast hD j h) (Nat.cast_nonneg _)
    linarith
  · simp only [ite_eq_right hhl, zero_add]
    positivity

end MultiStateData

/-! ### The competing-risks model as a multi-state model -/

end MathlibExt.Probability.Statistics.AalenJohansenProductIntegral

namespace MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData

open Finset Filter Matrix
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.AalenJohansenProductIntegral

variable {k r : ℕ} (D : CompetingRiskData k r)

/-- The competing-risks data as multi-state data on `Option (Fin r)`: `none` is the transient
state "no failure yet" and `some c` is absorption by cause `c`. The only transitions are
`none → some c`, `d_{j,c}` of them at `time j`, and `Yⱼ` subjects are in `none` before `time j`;
nobody is at risk of leaving an absorbing state. -/
def toMultiState : MultiStateData k (Option (Fin r)) where
  time := D.time
  strictMono_time := D.strictMono_time
  transitions j h l := Option.elim h (Option.elim l 0 (D.events j)) fun _ => 0
  atRisk j h := Option.elim h (D.atRisk j) fun _ => 0

/-- The Nelson–Aalen jump of the transient-to-transient entry is `-dⱼ / Yⱼ`. -/
theorem naIncrement_none_none (j : Fin k) :
    D.toMultiState.naIncrement j none none = -((D.totalEvents j : ℝ) / D.atRisk j) := by
  have hsum : ∑ l' ∈ univ.erase (none : Option (Fin r)),
      (D.toMultiState.transitions j none l' : ℝ) = D.totalEvents j := by
    rw [sum_erase _ (by simp [toMultiState]), Fintype.sum_option]
    simp [toMultiState, CompetingRiskData.totalEvents]
  rw [MultiStateData.naIncrement, ite_eq_left rfl, hsum, neg_div]
  rfl

/-- The Nelson–Aalen jump of the entry `none → some c` is `d_{j,c} / Yⱼ`. -/
theorem naIncrement_none_some (j : Fin k) (c : Fin r) :
    D.toMultiState.naIncrement j none (some c) = (D.events j c : ℝ) / D.atRisk j := by
  simp [MultiStateData.naIncrement, toMultiState]

/-- The rows of the absorbing states of a Nelson–Aalen jump vanish. -/
theorem naIncrement_some (j : Fin k) (c : Fin r) (l : Option (Fin r)) :
    D.toMultiState.naIncrement j (some c) l = 0 := by
  simp [MultiStateData.naIncrement, toMultiState]

/-- `M` has no transitions from an absorbing state back to the transient state. -/
def NoReturn (M : Matrix (Option (Fin r)) (Option (Fin r)) ℝ) : Prop := ∀ c, M (some c) none = 0

theorem NoReturn.mul {M N : Matrix (Option (Fin r)) (Option (Fin r)) ℝ} (hM : NoReturn M)
    (hN : NoReturn N) : NoReturn (M * N) := fun c => by
  rw [mul_apply, Fintype.sum_option, hM c, zero_mul, zero_add]
  exact sum_eq_zero fun c' _ => by rw [hN c', mul_zero]

theorem mul_none_none {M N : Matrix (Option (Fin r)) (Option (Fin r)) ℝ} (hN : NoReturn N) :
    (M * N) none none = M none none * N none none := by
  rw [mul_apply, Fintype.sum_option, add_eq_left]
  exact sum_eq_zero fun c _ => by rw [hN c, mul_zero]

/-- The transient-to-transient entry of a time-ordered product of no-return factors is the
product of the entries. -/
theorem orderedProd_none_none : ∀ {k : ℕ} (A : Fin k → Matrix (Option (Fin r)) (Option (Fin r)) ℝ)
    (act : Fin k → Prop) [DecidablePred act], (∀ j, NoReturn (A j)) →
    NoReturn (orderedProd A act) ∧
      orderedProd A act none none = ∏ j, if act j then 1 + A j none none else 1
  | 0, A, act, _, _ => by
    refine ⟨fun c => ?_, ?_⟩ <;> simp [orderedProd_zero, one_apply]
  | k + 1, A, act, _, hA => by
    obtain ⟨ih₁, ih₂⟩ := orderedProd_none_none (fun i : Fin k => A i.castSucc)
      (fun i => act i.castSucc) fun j => hA _
    have hlast : NoReturn (if act (Fin.last k) then 1 + A (Fin.last k) else 1) := fun c => by
      split_ifs
      · rw [Matrix.add_apply, hA _ c, one_apply_ne (Option.some_ne_none c), add_zero]
      · exact one_apply_ne (Option.some_ne_none c)
    rw [orderedProd_succ]
    refine ⟨ih₁.mul hlast, ?_⟩
    rw [mul_none_none hlast, ih₂, Fin.prod_univ_castSucc]
    congr 1
    split_ifs <;> simp

theorem noReturn_naIncrement (j : Fin k) : NoReturn (D.toMultiState.naIncrement j) :=
  fun c => D.naIncrement_some j c none

/-- The transient-to-transient entry of `P̂(s, t-)`-type products is a product of Kaplan–Meier
factors. -/
theorem orderedProd_naIncrement_none_none (act : Fin k → Prop) [DecidablePred act] :
    orderedProd D.toMultiState.naIncrement act none none =
      ∏ j, if act j then D.toCensoredData.kmFactor j else 1 := by
  rw [(orderedProd_none_none _ act D.noReturn_naIncrement).2]
  refine prod_congr rfl fun j _ => ?_
  rw [naIncrement_none_none, ← sub_eq_add_neg]
  rfl

/-- **Aalen–Johansen survival = Kaplan–Meier**: starting before the first observation time, the
transient-to-transient entry of the Aalen–Johansen matrix is the Kaplan–Meier survival
`Ŝ(t) = ∏_{tⱼ ≤ t} (1 - dⱼ / Yⱼ)` of the cause-blind data. -/
theorem transitionMatrix_none_none {s : ℝ} (hs : ∀ j, s < D.time j) (t : ℝ) :
    D.toMultiState.transitionMatrix s t none none = D.toCensoredData.kmSurvival t := by
  rw [MultiStateData.transitionMatrix, jumpProd, orderedProd_naIncrement_none_none,
    CensoredData.kmSurvival, prod_filter]
  refine prod_congr rfl fun j _ => ?_
  exact if_congr ⟨fun h => h.2, fun h => ⟨hs j, h⟩⟩ rfl rfl

/-- **Aalen–Johansen product-integral = increment form**: starting before the first observation
time, the entry `none → some c` of the Aalen–Johansen transition matrix is the cumulative
incidence `F̂_c(t) = ∑_{tⱼ ≤ t} Ŝ(tⱼ₋) d_{j,c} / Yⱼ` of `CompetingRisks.lean`. -/
theorem transitionMatrix_none_some {s : ℝ} (hs : ∀ j, s < D.time j) (t : ℝ) (c : Fin r) :
    D.toMultiState.transitionMatrix s t none (some c) = D.cumulativeIncidence c t := by
  rw [MultiStateData.transitionMatrix_forward, Matrix.add_apply,
    one_apply_ne (Option.some_ne_none c).symm, zero_add, Matrix.sum_apply,
    CompetingRiskData.cumulativeIncidence, sum_filter]
  refine sum_congr rfl fun j _ => ?_
  have hact : (s < D.toMultiState.time j ∧ D.toMultiState.time j ≤ t) ↔ D.time j ≤ t :=
    ⟨fun h => h.2, fun h => ⟨hs j, h⟩⟩
  rw [apply_ite (fun M : Matrix _ _ ℝ => M none (some c)), Matrix.zero_apply]
  refine if_congr hact ?_ rfl
  rw [mul_apply, Fintype.sum_option, sum_eq_zero fun c' _ => by rw [D.naIncrement_some, mul_zero],
    add_zero, jumpProdLT, orderedProd_naIncrement_none_none, naIncrement_none_some,
    CompetingRiskData.cifIncrement, CompetingRiskData.survivalBefore, prod_filter]
  congr 1
  refine prod_congr rfl fun i _ => if_congr ?_ rfl rfl
  exact ⟨fun h => D.strictMono_time.lt_iff_lt.1 h.2,
    fun h => ⟨hs i, D.strictMono_time.lt_iff_lt.2 h⟩⟩

/-- The product-integral of the Nelson–Aalen intensity of the competing-risks data exists, and its
entry `none → some c` is the cumulative incidence of cause `c`. -/
theorem hasProdIntegral_cumulativeIncidence {s t : ℝ} (hst : s ≤ t) (hs : ∀ j, s < D.time j)
    (c : Fin r) :
    HasProdIntegral D.toMultiState.naCumHazard s t (D.toMultiState.transitionMatrix s t) ∧
      D.toMultiState.transitionMatrix s t none (some c) = D.cumulativeIncidence c t :=
  ⟨D.toMultiState.hasProdIntegral_transitionMatrix hst, D.transitionMatrix_none_some hs t c⟩

/-- Any product-integral of the Nelson–Aalen intensity of the competing-risks data over `[s, t]`,
`s` before the first observation time, has entry `none → some c` equal to the cumulative
incidence `F̂_c(t)` and entry `none → none` equal to the Kaplan–Meier survival `Ŝ(t)`. -/
theorem eq_of_hasProdIntegral {s t : ℝ} (hst : s ≤ t) (hs : ∀ j, s < D.time j)
    {M : Matrix (Option (Fin r)) (Option (Fin r)) ℝ}
    (hM : HasProdIntegral D.toMultiState.naCumHazard s t M) :
    (∀ c, M none (some c) = D.cumulativeIncidence c t) ∧
      M none none = D.toCensoredData.kmSurvival t := by
  rw [hM.unique hst (D.toMultiState.hasProdIntegral_transitionMatrix hst)]
  exact ⟨D.transitionMatrix_none_some hs t, D.transitionMatrix_none_none hs t⟩

end MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData
