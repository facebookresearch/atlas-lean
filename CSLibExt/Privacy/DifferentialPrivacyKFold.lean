/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacyComposition
public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import Cslib.Foundations.Relation.RelatesInSteps
import CSLibExt.Crypto.Privacy.Basic

/-!
# k-fold adaptive composition and group privacy

Adaptive k-fold composition with additive budgets over nested-pair transcripts,
pure-DP corollary, and pure and approximate group privacy over length-indexed
chains of canonical `ReplaceOne` on fixed-size databases.

Dwork and Roth (2014), Theorem 3.16 (non-adaptive k-fold) and Theorem 2.2
(pure group privacy). Adaptive k-fold generalizes the staged pair theorem;
Theorem 3.16 is recovered as the constant-kernel case.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

universe u

/-- Transcript after `n` adaptive stages with output family `A`.
Zero stages carry `PUnit`; stage `n+1` appends on the right. -/
def Transcript (A : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Transcript A n × A n

/-- Adaptive composition of stage kernels `K` for `k` stages.
Stage `n` sees the prior transcript and the database. -/
noncomputable def kfoldCompose {D : Type*} {A : ℕ → Type u}
    (K : (n : ℕ) → Transcript A n → D → PMF (A n)) (k : ℕ) :
    D → PMF (Transcript A k) :=
  match k with
  | 0 => fun _ => PMF.pure PUnit.unit
  | n + 1 => fun d => ((kfoldCompose K n d).bind fun t =>
      (K n t d).bind fun a => PMF.pure (t, a))

/-- Zero-stage composition is the constant unit mechanism. -/
theorem kfoldCompose_zero {D : Type*} {A : ℕ → Type u}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} :
    kfoldCompose K 0 = fun _ => PMF.pure PUnit.unit :=
  rfl

/-- Successor composition exposes the paired bind. -/
theorem kfoldCompose_succ {D : Type*} {A : ℕ → Type u}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} (n : ℕ) :
    kfoldCompose K (n + 1) = fun d => ((kfoldCompose K n d).bind fun t =>
      (K n t d).bind fun a => PMF.pure (t, a)) :=
  rfl

/-- Adaptive k-fold composition with additive budgets over one fixed adjacency.
Each stage kernel is uniformly private for every fixed prior transcript. -/
theorem isApproxDP_kfold {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} {ε δ : ℕ → ℝ} (k : ℕ)
    (hε : ∀ i, i < k → 0 ≤ ε i) (hδ : ∀ i, i < k → 0 ≤ δ i)
    (hK : ∀ i, i < k → ∀ t, IsApproxDP (fun d => K i t d) adj (ε i) (δ i)) :
    IsApproxDP (kfoldCompose K k) adj
      (Finset.sum (Finset.range k) ε) (Finset.sum (Finset.range k) δ) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    show IsApproxDP (fun _ => PMF.pure PUnit.unit) adj 0 0
    rw [isApproxDP_zero_iff]
    exact isDP_const _ _
  | succ n ih =>
    have hεn : ∀ i, i < n → 0 ≤ ε i :=
      fun i hi => hε i (Nat.lt_succ_of_lt hi)
    have hδn : ∀ i, i < n → 0 ≤ δ i :=
      fun i hi => hδ i (Nat.lt_succ_of_lt hi)
    have hKn : ∀ i, i < n → ∀ t, IsApproxDP (fun d => K i t d) adj (ε i) (δ i) :=
      fun i hi t => hK i (Nat.lt_succ_of_lt hi) t
    have ih' := ih hεn hδn hKn
    have hεn1 : 0 ≤ ε n := hε n (Nat.lt_succ_self n)
    have hδn1 : 0 ≤ δ n := hδ n (Nat.lt_succ_self n)
    have hKn1 : ∀ t, IsApproxDP (fun d => K n t d) adj (ε n) (δ n) :=
      hK n (Nat.lt_succ_self n)
    have hcomp := isApproxDP_comp_bind_pair (M := kfoldCompose K n)
      (K := fun t d => K n t d) ih' hεn1 hδn1 hKn1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact hcomp

/-- Zero-stage boundary: the empty transcript is `(0, 0)`-DP. -/
theorem isApproxDP_kfold_zero {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} :
    IsApproxDP (kfoldCompose K 0) adj 0 0 := by
  have h := isApproxDP_kfold (adj := adj) (K := K)
    (ε := fun _ => 0) (δ := fun _ => 0) 0
    (fun i hi => (Nat.not_lt_zero i hi).elim)
    (fun i hi => (Nat.not_lt_zero i hi).elim)
    (fun i hi _ => (Nat.not_lt_zero i hi).elim)
  simpa using h

/-- One-stage case with its honest carrier `PUnit × A 0`.
No definitional claim to the original output type is made. -/
theorem isApproxDP_kfold_one {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} {ε δ : ℕ → ℝ}
    (hε0 : 0 ≤ ε 0) (hδ0 : 0 ≤ δ 0)
    (hK0 : ∀ t, IsApproxDP (fun d => K 0 t d) adj (ε 0) (δ 0)) :
    IsApproxDP (kfoldCompose K 1) adj (ε 0) (δ 0) := by
  have hε : ∀ i, i < 1 → 0 ≤ ε i := by
    intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    rw [this]
    exact hε0
  have hδ : ∀ i, i < 1 → 0 ≤ δ i := by
    intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    rw [this]
    exact hδ0
  have hK : ∀ i, i < 1 → ∀ t, IsApproxDP (fun d => K i t d) adj (ε i) (δ i) := by
    intro i hi t
    have h0 : i = 0 := Nat.lt_one_iff.mp hi
    subst h0
    exact hK0 t
  have h := isApproxDP_kfold 1 hε hδ hK
  simpa using h

/-- Non-adaptive k-fold (Dwork-Roth Theorem 3.16) as the constant-kernel case.
Kernels ignoring the transcript compose with summed budgets. -/
theorem isApproxDP_kfold_const {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {M : (i : ℕ) → D → PMF (A i)} {ε δ : ℕ → ℝ} (k : ℕ)
    (hε : ∀ i, i < k → 0 ≤ ε i) (hδ : ∀ i, i < k → 0 ≤ δ i)
    (hM : ∀ i, i < k → IsApproxDP (M i) adj (ε i) (δ i)) :
    IsApproxDP (kfoldCompose (fun i _ d => M i d) k) adj
      (Finset.sum (Finset.range k) ε) (Finset.sum (Finset.range k) δ) := by
  apply isApproxDP_kfold k hε hδ
  intro i hi t
  exact hM i hi

/-- Pure k-fold corollary: zero stage deltas give zero total delta.
Via the canonical zero-delta equivalence, over generic adjacency. -/
theorem isDP_kfold {D : Type*} {A : ℕ → Type u} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} {ε : ℕ → ℝ} (k : ℕ)
    (hε : ∀ i, i < k → 0 ≤ ε i)
    (hK : ∀ i, i < k → ∀ t, IsDP (fun d => K i t d) adj (ε i)) :
    IsDP (kfoldCompose K k) adj (Finset.sum (Finset.range k) ε) := by
  have hδ : ∀ i, i < k → 0 ≤ (fun _ : ℕ => (0 : ℝ)) i :=
    fun _ _ => le_refl 0
  have hK' : ∀ i, i < k → ∀ t,
      IsApproxDP (fun d => K i t d) adj (ε i) ((fun _ : ℕ => (0 : ℝ)) i) :=
    fun i hi t => isApproxDP_zero_iff.mpr (hK i hi t)
  have h := isApproxDP_kfold (δ := fun _ => 0) k hε hδ hK'
  simp only [Finset.sum_const_zero] at h
  exact isApproxDP_zero_iff.mp h

/-- Length-indexed chains of canonical `ReplaceOne` on fixed-size databases.
Exactly `k` steps; `ReflTransGen` alone does not track length.

This is bounded replace-one adjacency on `Fin n → X`, not identified with
histogram ℓ₁ distance or add/remove adjacency. No conversion between the
privacy budgets of those notions is asserted here. -/
abbrev ReplaceOneChain {n : ℕ} {X : Type*} (k : ℕ) (d d' : Fin n → X) : Prop :=
  Relation.RelatesInSteps ReplaceOne d d' k

/-- A `ReplaceOneChain` yields a step-indexed neighbour chain. -/
private theorem ReplaceOneChain.to_chain {n : ℕ} {X : Type*} {k : ℕ}
    {d d' : Fin n → X} (h : ReplaceOneChain k d d') :
    ∃ z : ℕ → (Fin n → X), z 0 = d ∧ z k = d' ∧
      ∀ i < k, ReplaceOne (z i) (z (i + 1)) := by
  induction h with
  | refl => exact ⟨fun _ => d, rfl, rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | tail mid fin j _ hstep ih =>
    obtain ⟨z, hz0, hzj, hz⟩ := ih
    refine ⟨fun i => if i ≤ j then z i else fin, ?_, ?_, ?_⟩
    · show (if (0 : ℕ) ≤ j then z 0 else fin) = d
      rw [ite_eq_left (Nat.zero_le j), hz0]
    · show (if j + 1 ≤ j then z (j + 1) else fin) = fin
      rw [ite_eq_right (by omega)]
    · intro i hi
      have h1 : i ≤ j := by omega
      show ReplaceOne (if i ≤ j then z i else fin) (if i + 1 ≤ j then z (i + 1) else fin)
      rw [ite_eq_left h1]
      by_cases h2 : i + 1 ≤ j
      · rw [ite_eq_left h2]
        exact hz i (by omega)
      · have hij : i = j := by omega
        subst hij
        rw [ite_eq_right h2, hzj]
        exact hstep

/-- PMF pure DP gives measure DP with `δ = 0` on the induced measures. -/
private theorem isDP_toDifferentiallyPrivate {D Output : Type*} [MeasurableSpace Output]
    {M : D → PMF Output} {adj : D → D → Prop} {ε : ℝ}
    (hM : IsDP M adj ε) :
    Cslib.Crypto.Privacy.DifferentiallyPrivate adj (fun d => (M d).toMeasure) ε 0 := by
  have hEv := (isDP_iff_isDPEvent.mp hM).2
  intro x y hxy S hS
  show (M x).toMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M y).toMeasure S + 0
  rw [add_zero, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS]
  exact hEv x y hxy S

/-- PMF approximate DP gives measure DP on the induced measures. -/
private theorem isApproxDP_toDifferentiallyPrivate {D Output : Type*}
    [MeasurableSpace Output] {M : D → PMF Output} {adj : D → D → Prop}
    {ε δ : ℝ} (hM : IsApproxDP M adj ε δ) :
    Cslib.Crypto.Privacy.DifferentiallyPrivate adj (fun d => (M d).toMeasure)
      ε (ENNReal.ofReal δ) := by
  intro x y hxy S hS
  show (M x).toMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M y).toMeasure S +
    ENNReal.ofReal δ
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS]
  exact hM.2.2 x y hxy S

/-- Pure group privacy over exactly-`k` chains: factor `exp (k * ε)`. -/
theorem isDP_groupPrivacy {n : ℕ} {X Output : Type*}
    {M : (Fin n → X) → PMF Output} {ε : ℝ}
    (hM : IsDP M ReplaceOne ε) {k : ℕ} {d d' : Fin n → X}
    (hchain : ReplaceOneChain k d d') (o : Output) :
    M d o ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * M d' o := by
  let : MeasurableSpace Output := ⊤
  obtain ⟨z, hz0, hzk, hz⟩ := ReplaceOneChain.to_chain hchain
  have hDP := isDP_toDifferentiallyPrivate hM
  have hS : MeasurableSet ({o} : Set Output) := MeasurableSpace.measurableSet_top
  have h := hDP.group hz hS
  rw [hz0, hzk] at h
  rw [PMF.toMeasure_apply_singleton _ _ hS,
    PMF.toMeasure_apply_singleton _ _ hS] at h
  exact h

/-- Pure group privacy for at-most-`k` chains, by monotonicity with `0 ≤ ε`. -/
theorem isDP_groupPrivacy_le {n : ℕ} {X Output : Type*}
    {M : (Fin n → X) → PMF Output} {ε : ℝ}
    (hM : IsDP M ReplaceOne ε) (hε : 0 ≤ ε)
    {j k : ℕ} {d d' : Fin n → X}
    (hchain : ReplaceOneChain j d d') (hjk : j ≤ k) (o : Output) :
    M d o ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * M d' o := by
  have h := isDP_groupPrivacy hM hchain o
  have hjk' : (j : ℝ) * ε ≤ (k : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjk) hε
  have hexp : Real.exp ((j : ℝ) * ε) ≤ Real.exp ((k : ℝ) * ε) :=
    Real.exp_le_exp.mpr hjk'
  have hof : ENNReal.ofReal (Real.exp ((j : ℝ) * ε)) ≤
      ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) := by
    apply ENNReal.ofReal_le_ofReal hexp
  exact h.trans (mul_le_mul' hof le_rfl)

/-- Approximate group privacy in sum form over exactly-`k` chains.
Error is `δ * ∑ j<k, exp (j * ε)`; no quotient form is used, so `ε = 0` is fine. -/
theorem isApproxDP_groupPrivacy {n : ℕ} {X Output : Type*}
    {M : (Fin n → X) → PMF Output} {ε δ : ℝ}
    (hM : IsApproxDP M ReplaceOne ε δ) {k : ℕ} {d d' : Fin n → X}
    (hchain : ReplaceOneChain k d d') (s : Set Output) :
    (M d).toOuterMeasure s ≤
      ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * (M d').toOuterMeasure s +
        ENNReal.ofReal (δ * Finset.sum (Finset.range k)
          (fun j => Real.exp ((j : ℝ) * ε))) := by
  let : MeasurableSpace Output := ⊤
  obtain ⟨z, hz0, hzk, hz⟩ := ReplaceOneChain.to_chain hchain
  have hDP := isApproxDP_toDifferentiallyPrivate hM
  have hS : MeasurableSet s := MeasurableSpace.measurableSet_top
  have h := hDP.group_sum hz hS
  rw [hz0, hzk] at h
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS] at h
  have herr : Finset.sum (Finset.range k)
        (fun i => ENNReal.ofReal (Real.exp ((i : ℝ) * ε))) * ENNReal.ofReal δ =
      ENNReal.ofReal (δ * Finset.sum (Finset.range k)
        (fun j => Real.exp ((j : ℝ) * ε))) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (Real.exp_pos _).le)]
    rw [← ENNReal.ofReal_mul
      (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)]
    congr 1
    ring
  rw [herr] at h
  exact h

end CSLibExt.Privacy.DifferentialPrivacy
