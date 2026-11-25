/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Admixture.QpAdmWeights

/-!
# qpAdm fits do not identify the historical sources

qpAdm sees a drift model only through the `f4` entries of `ADMIXTOOLS.qpAdmSourceMatrix` and
`ADMIXTOOLS.qpAdmTargetVector` (qpWave through `ADMIXTOOLS.f4Matrix`). Three standard failure
modes of reading a fitted qpAdm model as history are made explicit, first as general theorems
and then as concrete weight tables at unit edge lengths (the lineage weights of explicit
admixture graphs; the theorems are stated for all real mixing parameters as second-moment
drift-model statements, the graph reading applying for parameters in `[0, 1]`):

1. **Proxy substitution** (`qpAdm_eq_of_proxy`, `f4Matrix_eq_of_proxy`): a population whose
   lineage weights agree with a source's on every edge seen by the right set gives the
   identical qpAdm system and qpWave matrix, with the same fitted weights, whatever its actual
   history. In `proxy_counterexample` the proxy fits in place of the true source while the
   target is not a mixture of the proxy at all.
2. **Ghost absorption** (`qpAdm_mulVec_eq_of_ghost`): if the true source mixture involves a
   ghost population whose right contrasts lie in the span of the sampled sources' contrasts,
   the sampled system is solved exactly, with weights `α • c` of any sign or size.
   `ghost_counterexample` realizes weights `(-1/2, 3/2)`.
3. **Reversed direction** (`qpAdm_fit_of_reversed`): a source descending from the target fits
   the target with weight `1 / β` and the qpWave matrix has rank at most one (exactly one in
   `reversed_counterexample`), so a fitting rank-one model cannot orient the relationship.
   `reversed_counterexample` realizes weights `(-1, 2)` with an unadmixed target.

A "fitting" model means an exact solution of the qpAdm system (and qpWave rank at most one
where stated). The qpAdm solution vector lists only the non-reference weights (the reference
source's weight is `1` minus their sum, so the full weights always sum to one); nothing
forces them into `[0, 1]`, which is what the ghost and reversed examples exploit.

## Main results

* `qpAdm_eq_of_proxy`, `f4Matrix_eq_of_proxy`: proxy substitution leaves qpAdm and qpWave
  unchanged.
* `qpAdm_mulVec_eq_of_ghost`: a ghost source in the contrast span is absorbed exactly.
* `qpAdm_fit_of_reversed`: a target-descended source fits with weight `1 / β`, qpWave rank
  at most one.
* `proxyWeight`, `ghostWeight`, `reversedWeight` and `proxy_counterexample`,
  `ghost_counterexample`, `reversed_counterexample`: explicit weight tables realizing each.

## References

* É. Harney et al., *Assessing the performance of qpAdm*, Genetics 217 (2021), iyab052.
* R. Maier, P. Flegontov, O. Flegontova, U. Işıldak, P. Changmai, D. Reich, *On the limits
  of fitting complex models of population history to f-statistics*, eLife 12 (2023), e85492
  (proxy sources, ghost admixture and proximal models).
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.Biology.PopulationGenetics
  MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.Admixture

variable {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]

/-! ### General statements -/

/-- Two left pairs with the same right contrasts give the same `f4` against every right pair
`(R j, R 0)`. -/
private theorem f4_right_eq_of_contrast {r : ℕ} (M : DriftModel μ E P) (R : Fin (r + 1) → P)
    {X Y X' Y' : P} (j : Fin (r + 1))
    (hX : ∀ e, (M.weight X' e - M.weight X e) * (M.weight (R j) e - M.weight (R 0) e) = 0)
    (hY : ∀ e, (M.weight Y' e - M.weight Y e) * (M.weight (R j) e - M.weight (R 0) e) = 0) :
    f4 μ M.freq X' Y' (R j) (R 0) = f4 μ M.freq X Y (R j) (R 0) := by
  rw [M.f4_freq, M.f4_freq]
  refine Finset.sum_congr rfl fun e _ => ?_
  linear_combination (M.len e) * (hX e - hY e)

/-- **Proxy substitution.** If each population `S' l` has the same lineage weights as the source
`S l` on every edge seen by the right set (for every edge `e` and right population `R j`,
`(w (S' l) e - w (S l) e) * (w (R j) e - w (R 0) e) = 0`), then replacing the sources `S` by
`S'` leaves the qpAdm source matrix and target vector unchanged: the same fit and the same
weights, whatever the history of `S'`. -/
theorem qpAdm_eq_of_proxy (M : DriftModel μ E P) {k r : ℕ} (T : P) (S S' : Fin (k + 1) → P)
    (R : Fin (r + 1) → P)
    (h : ∀ l e j, (M.weight (S' l) e - M.weight (S l) e) *
      (M.weight (R j) e - M.weight (R 0) e) = 0) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq S' R = ADMIXTOOLS.qpAdmSourceMatrix μ M.freq S R ∧
      ADMIXTOOLS.qpAdmTargetVector μ M.freq T S' R =
        ADMIXTOOLS.qpAdmTargetVector μ M.freq T S R := by
  refine ⟨?_, ?_⟩
  · ext j l
    simp only [ADMIXTOOLS.qpAdmSourceMatrix, Matrix.of_apply]
    exact f4_right_eq_of_contrast M R j.succ (fun e => h l.succ e j.succ) (fun e => h 0 e j.succ)
  · funext j
    simp only [ADMIXTOOLS.qpAdmTargetVector]
    exact f4_right_eq_of_contrast M R j.succ (fun e => by simp) (fun e => h 0 e j.succ)

/-- **Proxy substitution, qpWave form.** If each left population `L' i` has the same lineage
weights as `L i` on every edge seen by the right set (for every edge `e` and right population
`R j`, `(w (L' i) e - w (L i) e) * (w (R j) e - w (R 0) e) = 0`), then replacing `L` by `L'`
leaves the qpWave `f4` matrix unchanged. -/
theorem f4Matrix_eq_of_proxy (M : DriftModel μ E P) {n r : ℕ} (L L' : Fin (n + 1) → P)
    (R : Fin (r + 1) → P)
    (h : ∀ i e j, (M.weight (L' i) e - M.weight (L i) e) *
      (M.weight (R j) e - M.weight (R 0) e) = 0) :
    ADMIXTOOLS.f4Matrix μ M.freq L' R = ADMIXTOOLS.f4Matrix μ M.freq L R := by
  ext i j
  simp only [ADMIXTOOLS.f4Matrix, Matrix.of_apply]
  exact f4_right_eq_of_contrast M R j.succ (fun e => h i.succ e j.succ) (fun e => h 0 e j.succ)

/-- **Ghost absorption.** If, on every edge seen by the right set, the target `T` has the
weights of the mixture `α G + (1 - α) S 0` of a population `G` (in the intended example, a
source that is not sampled), and the right contrasts of `G` lie in the span of those of the
sampled sources,
`f4 (G, S 0; R j, R 0) = ∑ l, c l * f4 (S (l + 1), S 0; R j, R 0)`, then the qpAdm system of the
sampled sources is solved by the weights `α • c` (any sign, any size). -/
theorem qpAdm_mulVec_eq_of_ghost (M : DriftModel μ E P) {k r : ℕ} {T G : P}
    (S : Fin (k + 1) → P) (R : Fin (r + 1) → P) {α : ℝ} (c : Fin k → ℝ)
    (hT : ∀ e j, (M.weight T e - (α * M.weight G e + (1 - α) * M.weight (S 0) e)) *
      (M.weight (R j) e - M.weight (R 0) e) = 0)
    (hG : ∀ j : Fin r, f4 μ M.freq G (S 0) (R j.succ) (R 0) =
      ∑ l, c l * f4 μ M.freq (S l.succ) (S 0) (R j.succ) (R 0)) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq S R *ᵥ (α • c) =
      ADMIXTOOLS.qpAdmTargetVector μ M.freq T S R := by
  funext j
  have h1 : f4 μ M.freq T (S 0) (R j.succ) (R 0) =
      α * f4 μ M.freq G (S 0) (R j.succ) (R 0) := by
    rw [M.f4_freq, M.f4_freq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    linear_combination (M.len e) * hT e j.succ
  simp only [ADMIXTOOLS.qpAdmTargetVector, ADMIXTOOLS.qpAdmSourceMatrix, Matrix.mulVec,
    dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, hG j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **Reversed direction.** If, on every edge seen by the right set, the source `S₁` has the
weights of `β T + (1 - β) S₀` with `β ≠ 0` of either sign (a relation between weight contrasts,
vacuous if every right population has the weights of `R 0`; for `0 < β ≤ 1` on a graph it holds,
for example, when `S₁` descends from such a mixture with private drift elsewhere), then the
target is fitted by the sources `(S₀, S₁)`, with weight `1 / β` on `S₁`, and the qpWave matrix of
the left populations `(S₀, T, S₁)` has rank at most one. -/
theorem qpAdm_fit_of_reversed (M : DriftModel μ E P) {r : ℕ} {T S₀ S₁ : P}
    (R : Fin (r + 1) → P) {β : ℝ} (hβ : β ≠ 0)
    (hS : ∀ e j, (M.weight S₁ e - (β * M.weight T e + (1 - β) * M.weight S₀ e)) *
      (M.weight (R j) e - M.weight (R 0) e) = 0) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![S₀, S₁] R *ᵥ ![1 / β] =
        ADMIXTOOLS.qpAdmTargetVector μ M.freq T ![S₀, S₁] R ∧
      (ADMIXTOOLS.f4Matrix μ M.freq ![S₀, T, S₁] R).rank ≤ 1 := by
  have h1 : ∀ j, f4 μ M.freq S₁ S₀ (R j) (R 0) = β * f4 μ M.freq T S₀ (R j) (R 0) := by
    intro j
    rw [M.f4_freq, M.f4_freq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    linear_combination (M.len e) * hS e j
  refine ⟨?_, ?_⟩
  · funext j
    simp only [ADMIXTOOLS.qpAdmTargetVector, ADMIXTOOLS.qpAdmSourceMatrix, Matrix.mulVec,
      dotProduct, Matrix.of_apply, Fin.sum_univ_one]
    simp only [Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h1]
    field_simp
  · have hF : ADMIXTOOLS.f4Matrix μ M.freq ![S₀, T, S₁] R =
        Matrix.vecMulVec ![1, β] fun j => f4 μ M.freq T S₀ (R j.succ) (R 0) := by
      ext i j
      fin_cases i
      · simp [ADMIXTOOLS.f4Matrix, Matrix.vecMulVec_apply]
      · simp [ADMIXTOOLS.f4Matrix, Matrix.vecMulVec_apply, h1]
    rw [hF]
    exact Matrix.rank_vecMulVec_le _ _

/-! ### Explicit weight tables -/

/-- Proxy-substitution weight table: the lineage weights of the following admixture graph.
Populations `0 = S₀`, `1 = S₁` (the true source), `2 = S₁'`
(a proxy splitting from the lineage of `S₁`), `3 = T`, `4 = R₀`, `5 = R₁`, `6 = R₂`. Edges:
`0` the stem shared by `S₀` and `R₂`, `1` the stem shared by `S₁`, `S₁'` and `R₁`, `2` private
to `S₁`, `3` private to `S₁'`, `4`, `5`, `6` private to `R₀`, `R₁`, `R₂`, `7` private to `S₀`.
The target is the mixture `T = α S₁ + (1 - α) S₀`. The table is defined for every real `α`; it
lists the lineage weights of this graph for `0 ≤ α ≤ 1`. -/
noncomputable def proxyWeight (α : ℝ) : Fin 7 → Fin 8 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0],
    ![1 - α, α, α, 0, 0, 0, 0, 1 - α], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 1, 0]]

/-- Ghost-source weight table: the lineage weights of the following admixture graph.
Populations `0 = S₀`, `1 = S₁`, `2 = G` (the true source, not sampled
as a qpAdm source), `3 = T`, `4 = R₀`, `5 = R₁`, `6 = R₂`. Edges: `0` private to `S₀`, `1` the
stem shared by `S₁`, `G`, `R₁`, `R₂`, `2` the continuation shared by `G`, `R₁`, `R₂`, `3`
private to `S₁`, `4` private to `G`, `5`, `6`, `7` private to `R₀`, `R₁`, `R₂`. The target is
the mixture `T = α G + (1 - α) S₀`. The table is defined for every real `α`; it lists the
lineage weights of this graph for `0 ≤ α ≤ 1`. -/
noncomputable def ghostWeight (α : ℝ) : Fin 7 → Fin 8 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 0],
    ![1 - α, α, α, 0, α, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 0, 0, 0, 1]]

/-- Reversed-direction weight table: the lineage weights of the following admixture graph.
Populations `0 = S₀`, `1 = T` (unadmixed), `2 = S₁` (admixed
from `T` and `S₀`, then private drift), `3 = R₀`, `4 = R₁`, `5 = R₂`. Edges: `0` the stem shared
by `S₀` and `R₂`, `1` the stem shared by `T` and `R₁`, `2` private to `T`, `3` private to `S₁`,
`4`, `5`, `6` private to `R₀`, `R₁`, `R₂`, `7` private to `S₀`. The source is the mixture
`S₁ = β T + (1 - β) S₀` followed by drift on edge `3`. The table is defined for every real `β`;
it lists the lineage weights of this graph for `0 ≤ β ≤ 1`. -/
noncomputable def reversedWeight (β : ℝ) : Fin 6 → Fin 8 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0], ![1 - β, β, β, 1, 0, 0, 0, 1 - β],
    ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0]]

/-- **Counterexample (i), proxy substitution.** In the proxy weight table at unit edge lengths and
`α ≠ 0`, the qpAdm systems with sources `(S₀, S₁')` and `(S₀, S₁)` are identical, as are the
qpWave matrices of `(S₀, T, S₁')` and `(S₀, T, S₁)`; the weights are exactly `α` in both; the
target is the mixture `α S₁ + (1 - α) S₀`, but no mixture of the proxy `S₁'` with `S₀`. -/
theorem proxy_counterexample {α : ℝ} (hα : α ≠ 0) (M : DriftModel μ (Fin 8) (Fin 7))
    (hw : M.weight = proxyWeight α) (hl : M.len = fun _ => 1) :
    ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![4, 5, 6] =
        ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 1] ![4, 5, 6] ∧
      ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 2] ![4, 5, 6] =
        ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 1] ![4, 5, 6] ∧
      ADMIXTOOLS.f4Matrix μ M.freq ![0, 3, 2] ![4, 5, 6] =
        ADMIXTOOLS.f4Matrix μ M.freq ![0, 3, 1] ![4, 5, 6] ∧
      (∀ v, ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![4, 5, 6] *ᵥ v =
        ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 2] ![4, 5, 6] ↔ v = ![α]) ∧
      M.weight 3 = α • M.weight 1 + (1 - α) • M.weight 0 ∧
      ∀ γ : ℝ, M.weight 3 ≠ γ • M.weight 2 + (1 - γ) • M.weight 0 := by
  have hprox : ∀ (l : Fin 2) (e : Fin 8) (j : Fin 3),
      (M.weight (![0, 2] l) e - M.weight (![0, 1] l) e) *
        (M.weight (![4, 5, 6] j) e - M.weight (![4, 5, 6] 0) e) = 0 := by
    intro l e j
    rw [hw]
    fin_cases l <;> fin_cases e <;> fin_cases j <;> simp [proxyWeight]
  obtain ⟨hA, hb⟩ := qpAdm_eq_of_proxy M 3 ![0, 1] ![0, 2] ![4, 5, 6] hprox
  have hL : ADMIXTOOLS.f4Matrix μ M.freq ![0, 3, 2] ![4, 5, 6] =
      ADMIXTOOLS.f4Matrix μ M.freq ![0, 3, 1] ![4, 5, 6] := by
    refine f4Matrix_eq_of_proxy M ![0, 3, 1] ![0, 3, 2] ![4, 5, 6] fun i e j => ?_
    rw [hw]
    fin_cases i <;> fin_cases e <;> fin_cases j <;> simp [proxyWeight]
  have hA' : ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![4, 5, 6] = Matrix.of ![![1], ![-1]] := by
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [ADMIXTOOLS.qpAdmSourceMatrix, M.f4_freq, hw, hl, proxyWeight, Fin.sum_univ_succ]
  have hb' : ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 2] ![4, 5, 6] = ![α, -α] := by
    funext j
    fin_cases j <;>
      simp [ADMIXTOOLS.qpAdmTargetVector, M.f4_freq, hw, hl, proxyWeight, Fin.sum_univ_succ]
  refine ⟨hA, hb, hL, fun v => ?_, ?_, fun γ h => ?_⟩
  · rw [hA', hb']
    constructor
    · intro h
      have h0 := congrFun h 0
      simp [Matrix.mulVec, dotProduct] at h0
      funext i
      fin_cases i
      simpa using h0
    · rintro rfl
      funext j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct]
  · rw [hw]
    funext e
    fin_cases e <;> simp [proxyWeight]
  · have h2 := congrFun h 2
    have h3 := congrFun h 3
    rw [hw] at h2 h3
    simp [proxyWeight] at h2 h3
    exact hα h2

/-- **Counterexample (ii), ghost absorption.** In the ghost weight table at unit edge lengths and
`α ≠ 0`, the right contrasts of the ghost `G` are twice those of `S₁`, the target
`T = α G + (1 - α) S₀` is fitted by the sampled sources `(S₀, S₁)` with weight exactly `2 α` on
`S₁` (so `1 - 2 α` on `S₀`), and the target is no mixture of `S₁` and `S₀`. -/
theorem ghost_counterexample {α : ℝ} (hα : α ≠ 0) (M : DriftModel μ (Fin 8) (Fin 7))
    (hw : M.weight = ghostWeight α) (hl : M.len = fun _ => 1) :
    (∀ j : Fin 2, f4 μ M.freq 2 0 (![4, 5, 6] j.succ) 4 =
      2 * f4 μ M.freq 1 0 (![4, 5, 6] j.succ) 4) ∧
      (∀ v, ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 1] ![4, 5, 6] *ᵥ v =
        ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 1] ![4, 5, 6] ↔ v = ![2 * α]) ∧
      M.weight 3 = α • M.weight 2 + (1 - α) • M.weight 0 ∧
      ∀ γ : ℝ, M.weight 3 ≠ γ • M.weight 1 + (1 - γ) • M.weight 0 := by
  have hA' : ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 1] ![4, 5, 6] = Matrix.of ![![1], ![1]] := by
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [ADMIXTOOLS.qpAdmSourceMatrix, M.f4_freq, hw, hl, ghostWeight, Fin.sum_univ_succ]
  have hb' : ADMIXTOOLS.qpAdmTargetVector μ M.freq 3 ![0, 1] ![4, 5, 6] = ![2 * α, 2 * α] := by
    funext j
    fin_cases j <;>
      simp [ADMIXTOOLS.qpAdmTargetVector, M.f4_freq, hw, hl, ghostWeight, Fin.sum_univ_succ] <;>
      ring
  refine ⟨fun j => ?_, fun v => ?_, ?_, fun γ h => ?_⟩
  · fin_cases j <;> simp [M.f4_freq, hw, hl, ghostWeight, Fin.sum_univ_succ] <;> norm_num
  · rw [hA', hb']
    constructor
    · intro h
      have h0 := congrFun h 0
      simp [Matrix.mulVec, dotProduct] at h0
      funext i
      fin_cases i
      simpa using h0
    · rintro rfl
      funext j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct]
  · rw [hw]
    funext e
    fin_cases e <;> simp [ghostWeight]
  · have h2 := congrFun h 2
    rw [hw] at h2
    simp [ghostWeight] at h2
    exact hα h2

/-- **Counterexample (iii), reversed direction.** In the reversed weight table at unit edge lengths
and `β ≠ 0`, the source `S₁` has the weights of `β T + (1 - β) S₀` plus a private edge (for
`0 < β ≤ 1`, descent from a mixture of the target and `S₀`) and the target has `0`/`1` weights,
yet the target is fitted by the sources `(S₀, S₁)`
with weight exactly `1 / β` on `S₁`, the qpWave matrix of `(S₀, T, S₁)` has rank exactly one,
and the target is no mixture of `S₁` and `S₀`. -/
theorem reversed_counterexample {β : ℝ} (hβ : β ≠ 0) (M : DriftModel μ (Fin 8) (Fin 6))
    (hw : M.weight = reversedWeight β) (hl : M.len = fun _ => 1) :
    (∀ v, ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![3, 4, 5] *ᵥ v =
        ADMIXTOOLS.qpAdmTargetVector μ M.freq 1 ![0, 2] ![3, 4, 5] ↔ v = ![1 / β]) ∧
      (ADMIXTOOLS.f4Matrix μ M.freq ![0, 1, 2] ![3, 4, 5]).rank = 1 ∧
      M.weight 2 = β • M.weight 1 + (1 - β) • M.weight 0 + Pi.single 3 1 ∧
      (∀ e, M.weight 1 e = 0 ∨ M.weight 1 e = 1) ∧
      ∀ γ : ℝ, M.weight 1 ≠ γ • M.weight 2 + (1 - γ) • M.weight 0 := by
  have hS : ∀ (e : Fin 8) (j : Fin 3),
      (M.weight 2 e - (β * M.weight 1 e + (1 - β) * M.weight 0 e)) *
        (M.weight (![3, 4, 5] j) e - M.weight (![3, 4, 5] 0) e) = 0 := by
    intro e j
    rw [hw]
    fin_cases e <;> fin_cases j <;> simp [reversedWeight]
  obtain ⟨hfit, hrank⟩ := qpAdm_fit_of_reversed M (T := 1) (S₀ := 0) (S₁ := 2) ![3, 4, 5] hβ hS
  have hA' : ADMIXTOOLS.qpAdmSourceMatrix μ M.freq ![0, 2] ![3, 4, 5] = Matrix.of ![![β], ![-β]] := by
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [ADMIXTOOLS.qpAdmSourceMatrix, M.f4_freq, hw, hl, reversedWeight, Fin.sum_univ_succ]
  have h00 : ADMIXTOOLS.f4Matrix μ M.freq ![0, 1, 2] ![3, 4, 5] 0 0 = 1 := by
    simp [ADMIXTOOLS.f4Matrix, M.f4_freq, hw, hl, reversedWeight, Fin.sum_univ_succ]
  refine ⟨fun v => ⟨fun h => ?_, fun h => h ▸ hfit⟩, le_antisymm hrank ?_, ?_, ?_, fun γ h => ?_⟩
  · have h1 := congrFun (h.trans hfit.symm) 0
    rw [hA'] at h1
    simp [Matrix.mulVec, dotProduct] at h1
    funext i
    fin_cases i
    simpa [hβ] using h1
  · have hsub := Matrix.rank_submatrix_le (ADMIXTOOLS.f4Matrix μ M.freq ![0, 1, 2] ![3, 4, 5])
      (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (0 : Fin 2))
    have h1 : ((ADMIXTOOLS.f4Matrix μ M.freq ![0, 1, 2] ![3, 4, 5]).submatrix
        (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (0 : Fin 2))).rank = 1 := by
      rw [Matrix.rank_of_det_ne_zero] <;> simp [Matrix.det_unique, h00]
    omega
  · rw [hw]
    funext e
    fin_cases e <;> simp [reversedWeight]
  · intro e
    rw [hw]
    fin_cases e <;> simp [reversedWeight]
  · have h3 := congrFun h 3
    have h1 := congrFun h 1
    rw [hw] at h3 h1
    simp [reversedWeight] at h3 h1
    rw [← h3] at h1
    norm_num at h1

end MathlibExt.Biology.PopulationGenetics.Admixture
