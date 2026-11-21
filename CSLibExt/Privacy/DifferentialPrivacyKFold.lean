/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacyComposition
public import CSLibExt.Privacy.ApproximateDifferentialPrivacy

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

/-- Transcript after `n` adaptive stages with output family `A`.
Zero stages carry `Unit`; stage `n+1` appends on the right. -/
def Transcript (A : ℕ → Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Transcript A n × A n

/-- Adaptive composition of stage kernels `K` for `k` stages.
Stage `n` sees the prior transcript and the database. -/
noncomputable def kfoldCompose {D : Type*} {A : ℕ → Type}
    (K : (n : ℕ) → Transcript A n → D → PMF (A n)) (k : ℕ) :
    D → PMF (Transcript A k) :=
  match k with
  | 0 => fun _ => PMF.pure Unit.unit
  | n + 1 => fun d => ((kfoldCompose K n d).bind fun t =>
      (K n t d).bind fun a => PMF.pure (t, a))

/-- Zero-stage composition is the constant unit mechanism. -/
theorem kfoldCompose_zero {D : Type*} {A : ℕ → Type}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} :
    kfoldCompose K 0 = fun _ => PMF.pure Unit.unit :=
  rfl

/-- Successor composition exposes the paired bind. -/
theorem kfoldCompose_succ {D : Type*} {A : ℕ → Type}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} (n : ℕ) :
    kfoldCompose K (n + 1) = fun d => ((kfoldCompose K n d).bind fun t =>
      (K n t d).bind fun a => PMF.pure (t, a)) :=
  rfl

/-- Adaptive k-fold composition with additive budgets over one fixed adjacency.
Each stage kernel is uniformly private for every fixed prior transcript. -/
theorem isApproxDP_kfold {D : Type*} {A : ℕ → Type} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} {ε δ : ℕ → ℝ} (k : ℕ)
    (hε : ∀ i, i < k → 0 ≤ ε i) (hδ : ∀ i, i < k → 0 ≤ δ i)
    (hK : ∀ i, i < k → ∀ t, IsApproxDP (fun d => K i t d) adj (ε i) (δ i)) :
    IsApproxDP (kfoldCompose K k) adj
      (Finset.sum (Finset.range k) ε) (Finset.sum (Finset.range k) δ) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    show IsApproxDP (fun _ => PMF.pure Unit.unit) adj 0 0
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
theorem isApproxDP_kfold_zero {D : Type*} {A : ℕ → Type} {adj : D → D → Prop}
    {K : (n : ℕ) → Transcript A n → D → PMF (A n)} :
    IsApproxDP (kfoldCompose K 0) adj 0 0 := by
  have h := isApproxDP_kfold (adj := adj) (K := K)
    (ε := fun _ => 0) (δ := fun _ => 0) 0
    (fun i hi => (Nat.not_lt_zero i hi).elim)
    (fun i hi => (Nat.not_lt_zero i hi).elim)
    (fun i hi _ => (Nat.not_lt_zero i hi).elim)
  simpa using h

/-- One-stage case with its honest carrier `Unit × A 0`.
No definitional claim to the original output type is made. -/
theorem isApproxDP_kfold_one {D : Type*} {A : ℕ → Type} {adj : D → D → Prop}
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
theorem isApproxDP_kfold_const {D : Type*} {A : ℕ → Type} {adj : D → D → Prop}
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
theorem isDP_kfold {D : Type*} {A : ℕ → Type} {adj : D → D → Prop}
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
inductive ReplaceOneChain {n : ℕ} {X : Type*} :
    ℕ → (Fin n → X) → (Fin n → X) → Prop
  | refl (d : Fin n → X) : ReplaceOneChain 0 d d
  | step {k : ℕ} {d d' d'' : Fin n → X} :
      ReplaceOneChain k d d' → ReplaceOne d' d'' →
      ReplaceOneChain (k + 1) d d''

/-- Pure group privacy over exactly-`k` chains: factor `exp (k * ε)`. -/
theorem isDP_groupPrivacy {n : ℕ} {X Output : Type*}
    {M : (Fin n → X) → PMF Output} {ε : ℝ}
    (hM : IsDP M ReplaceOne ε) {k : ℕ} {d d' : Fin n → X}
    (hchain : ReplaceOneChain k d d') (o : Output) :
    M d o ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * M d' o := by
  induction hchain with
  | refl d =>
    simp only [Nat.cast_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      le_refl]
  | @step k d d' d'' hprev hstep ih =>
    have h1 := ih
    have h2 := hM.2 d' d'' hstep o
    have hexp : ((k + 1 : ℕ) : ℝ) * ε = (k : ℝ) * ε + ε := by
      push_cast
      ring
    calc M d o
        ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * M d' o := h1
      _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) *
          (ENNReal.ofReal (Real.exp ε) * M d'' o) :=
          mul_le_mul' le_rfl h2
      _ = ENNReal.ofReal (Real.exp (((k + 1 : ℕ) : ℝ) * ε)) * M d'' o := by
          rw [hexp, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
          rw [mul_assoc]

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
  induction hchain with
  | refl d =>
    simp only [Nat.cast_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      Finset.range_zero, Finset.sum_empty, mul_zero, ENNReal.ofReal_zero, add_zero,
      le_refl]
  | @step k d d' d'' hprev hstep ih =>
    have hδ : 0 ≤ δ := hM.2.1
    have h_single := hM.2.2 d' d'' hstep s
    have hexp_succ : ((k + 1 : ℕ) : ℝ) * ε = (k : ℝ) * ε + ε := by
      push_cast
      ring
    have hsum_succ : Finset.sum (Finset.range (k + 1))
          (fun j => Real.exp ((j : ℝ) * ε)) =
          Finset.sum (Finset.range k) (fun j => Real.exp ((j : ℝ) * ε)) +
            Real.exp ((k : ℝ) * ε) :=
      Finset.sum_range_succ _ _
    have hSk_nonneg : 0 ≤ Finset.sum (Finset.range k)
        (fun j => Real.exp ((j : ℝ) * ε)) := by
      apply Finset.sum_nonneg
      intro j _
      exact (Real.exp_pos _).le
    have hexp_k_nonneg : 0 ≤ Real.exp ((k : ℝ) * ε) :=
      (Real.exp_pos _).le
    have h_err_combine : Real.exp ((k : ℝ) * ε) * δ +
          δ * Finset.sum (Finset.range k) (fun j => Real.exp ((j : ℝ) * ε)) =
          δ * Finset.sum (Finset.range (k + 1))
            (fun j => Real.exp ((j : ℝ) * ε)) := by
      rw [hsum_succ]
      ring
    calc (M d).toOuterMeasure s
        ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * (M d').toOuterMeasure s +
            ENNReal.ofReal (δ * Finset.sum (Finset.range k)
              (fun j => Real.exp ((j : ℝ) * ε))) := ih
      _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) *
            (ENNReal.ofReal (Real.exp ε) * (M d'').toOuterMeasure s +
              ENNReal.ofReal δ) +
            ENNReal.ofReal (δ * Finset.sum (Finset.range k)
              (fun j => Real.exp ((j : ℝ) * ε))) := by
          apply add_le_add _ le_rfl
          apply mul_le_mul' le_rfl h_single
      _ = ENNReal.ofReal (Real.exp (((k + 1 : ℕ) : ℝ) * ε)) *
            (M d'').toOuterMeasure s +
            ENNReal.ofReal (δ * Finset.sum (Finset.range (k + 1))
              (fun j => Real.exp ((j : ℝ) * ε))) := by
          rw [mul_add]
          have hmul : ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) *
              ENNReal.ofReal (Real.exp ε) =
              ENNReal.ofReal (Real.exp (((k + 1 : ℕ) : ℝ) * ε)) := by
            rw [hexp_succ, Real.exp_add,
              ENNReal.ofReal_mul (Real.exp_pos _).le]
          have herr : ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) *
              ENNReal.ofReal δ +
              ENNReal.ofReal (δ * Finset.sum (Finset.range k)
                (fun j => Real.exp ((j : ℝ) * ε))) =
              ENNReal.ofReal (δ * Finset.sum (Finset.range (k + 1))
                (fun j => Real.exp ((j : ℝ) * ε))) := by
            rw [← ENNReal.ofReal_mul hexp_k_nonneg,
              ← ENNReal.ofReal_add (mul_nonneg hexp_k_nonneg hδ)
                (mul_nonneg hδ hSk_nonneg),
              h_err_combine]
          rw [← mul_assoc, hmul, add_assoc, herr]

end CSLibExt.Privacy.DifferentialPrivacy
