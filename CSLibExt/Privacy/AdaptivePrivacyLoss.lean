/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import CSLibExt.Privacy.DifferentialPrivacy
public import CSLibExt.Privacy.MaxDivergenceDecomposition
public import CSLibExt.Privacy.PrivacyLoss
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Adaptive transcript model and privacy-loss decomposition

An adaptive process draws public coins once, then runs a sequence of stages
where each stage kernel chooses an output distribution from the full history
so far. `transcript` is the resulting law over histories, defined by
`PMF.bind`/`PMF.map` recursion so no normalization argument is needed.

The headline results are the real-mass factorization of the transcript law,
equality of transcript supports under two-sided stage guarantees, and the
decomposition of the transcript privacy loss into the sum of stage losses.
The decomposition holds on the transcript support only: `privacyLoss`
totalizes at zero mass, so off support the two sides can disagree.

Stage drift is the stage-kernel loss expectation in finite-sum form, with
the Gibbs lower bound and the `ε * (exp ε - 1)` upper bound, alongside the
one-step expectation and prefix-marginal interface laws.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

open scoped Classical

/-- History after `n` adaptive stages: public coins plus stage outputs. -/
def Hist (C Y : Type*) (n : ℕ) := C × (Fin n → Y)

instance Hist.fintype {C Y : Type*} [Fintype C] [Fintype Y] (n : ℕ) :
    Fintype (Hist C Y n) :=
  inferInstanceAs (Fintype (C × (Fin n → Y)))

/-- Append one stage output to a history. -/
def histExtend {C Y : Type*} {n : ℕ} (h : Hist C Y n) (y : Y) :
    Hist C Y (n + 1) :=
  (h.1, Fin.snoc h.2 y)

/-- Drop the last stage of a history. -/
private def histInit {C Y : Type*} {n : ℕ} (w : Hist C Y (n + 1)) :
    Hist C Y n :=
  (w.1, Fin.init w.2)

/-- Last stage output of a history. -/
private def histLast {C Y : Type*} {n : ℕ} (w : Hist C Y (n + 1)) : Y :=
  w.2 (Fin.last n)

private theorem histInit_histExtend {C Y : Type*} {n : ℕ} (h : Hist C Y n)
    (y : Y) : histInit (histExtend h y) = h := by
  cases h with
  | mk c f =>
    show (c, Fin.init (Fin.snoc (α := fun _ => Y) f y)) = (c, f)
    rw [Fin.init_snoc]

private theorem histLast_histExtend {C Y : Type*} {n : ℕ} (h : Hist C Y n)
    (y : Y) : histLast (histExtend h y) = y := by
  cases h with
  | mk c f =>
    show Fin.snoc (α := fun _ => Y) f y (Fin.last n) = y
    exact Fin.snoc_last _ _

private theorem histExtend_histInit_histLast {C Y : Type*} {n : ℕ}
    (w : Hist C Y (n + 1)) :
    histExtend (histInit w) (histLast w) = w := by
  cases w with
  | mk c f =>
    show (c, Fin.snoc (α := fun _ => Y) (Fin.init f) (f (Fin.last n)))
      = (c, f)
    rw [Fin.snoc_init_self]

/-- The snoc presentation of histories as an equivalence. -/
private def histSnocEquiv {C Y : Type*} (n : ℕ) :
    Hist C Y n × Y ≃ Hist C Y (n + 1) :=
  { toFun := fun p => histExtend p.1 p.2
    invFun := fun w => (histInit w, histLast w)
    left_inv := fun p => by
      cases p with
      | mk h y =>
        show (histInit (histExtend h y), histLast (histExtend h y)) = (h, y)
        exact Prod.ext (histInit_histExtend _ _) (histLast_histExtend _ _)
    right_inv := fun w => histExtend_histInit_histLast w }

/-- Embed coins as stage-zero histories. -/
def histZeroMk {C Y : Type*} (c : C) : Hist C Y 0 :=
  (c, fun i => Fin.elim0 i)

/-- Transcript law after `n` stages: coins from `R`, outputs from `K`. -/
noncomputable def transcript {C Y Database : Type*} [Fintype C] [Fintype Y]
    (R : PMF C) (K : (n : ℕ) → Hist C Y n → Database → PMF Y) :
    (n : ℕ) → Database → PMF (Hist C Y n)
  | 0, _ => R.map histZeroMk
  | (n + 1), d => (transcript R K n d).bind fun h =>
    (K n h d).map (histExtend h)

private theorem transcript_zero {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (d : Database) :
    transcript R K 0 d = R.map histZeroMk := rfl

private theorem transcript_succ {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (n : ℕ)
    (d : Database) :
    transcript R K (n + 1) d
      = (transcript R K n d).bind fun h =>
        (K n h d).map (histExtend h) := rfl

/-- The bind/`pure` presentation of the transcript recursion. -/
theorem transcript_bind_pure_form {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (n : ℕ)
    (d : Database) :
    transcript R K (n + 1) d
      = (transcript R K n d).bind fun h =>
        (K n h d).bind fun y => PMF.pure (histExtend h y) := by
  calc transcript R K (n + 1) d
      = (transcript R K n d).bind fun h =>
        (K n h d).map (histExtend h) := rfl
    _ = (transcript R K n d).bind fun h =>
        (K n h d).bind fun y => PMF.pure (histExtend h y) := by
        have h : ∀ h : Hist C Y n, (K n h d).map (histExtend h)
            = (K n h d).bind fun y => PMF.pure (histExtend h y) :=
          fun h => (PMF.bind_pure_comp (histExtend h) (K n h d)).symm
        simp_rw [h]

/-- Joint mass of a successor history, in `ENNReal`. -/
private theorem transcript_succ_apply {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (n : ℕ)
    (d : Database) (w : Hist C Y (n + 1)) :
    transcript R K (n + 1) d w
      = transcript R K n d (histInit w)
        * K n (histInit w) d (histLast w) := by
  simp only [transcript_succ, PMF.bind_apply, PMF.map_apply, tsum_fintype,
    Finset.mul_sum]
  have hmerge : (∑ h' : Hist C Y n, ∑ y' : Y,
          transcript R K n d h'
            * (if w = histExtend h' y' then K n h' d y' else 0))
        = ∑ p : Hist C Y n × Y, transcript R K n d p.1
          * (if w = histExtend p.1 p.2 then K n p.1 d p.2 else 0) :=
    (Fintype.sum_prod_type (fun p : Hist C Y n × Y =>
      transcript R K n d p.1
        * (if w = histExtend p.1 p.2 then K n p.1 d p.2 else 0))).symm
  rw [hmerge]
  have hmain : (∑ p : Hist C Y n × Y, transcript R K n d p.1
          * (if w = histExtend p.1 p.2 then K n p.1 d p.2 else 0))
        = transcript R K n d (histInit w)
          * (if w = histExtend (histInit w) (histLast w)
            then K n (histInit w) d (histLast w) else 0) := by
    apply Finset.sum_eq_single_of_mem (histInit w, histLast w)
      (Finset.mem_univ _)
    intro b _ hb
    cases b with
    | mk h' y' =>
      show transcript R K n d h'
          * (if w = histExtend h' y' then K n h' d y' else 0) = 0
      have hne : w ≠ histExtend h' y' := by
        intro hcon
        apply hb
        have h1 : histInit w = h' := by
          rw [hcon]
          exact histInit_histExtend _ _
        have h2 : histLast w = y' := by
          rw [hcon]
          exact histLast_histExtend _ _
        exact (Prod.ext h1 h2).symm
      rw [ite_eq_right hne, mul_zero]
  rw [hmain, histExtend_histInit_histLast, ite_eq_left rfl]

/-- Successor mass law: the joint mass of an extended history factors. -/
theorem transcript_extend_apply {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (n : ℕ)
    (d : Database) (h : Hist C Y n) (y : Y) :
    transcript R K (n + 1) d (histExtend h y)
      = transcript R K n d h * K n h d y := by
  have hmass := transcript_succ_apply R K n d (histExtend h y)
  rw [histInit_histExtend, histLast_histExtend] at hmass
  exact hmass

private theorem transcript_zero_apply {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (d : Database)
    (ω : Hist C Y 0) :
    transcript R K 0 d ω = R ω.1 := by
  rw [transcript_zero, PMF.map_apply, tsum_fintype]
  have hif : ∀ c' : C,
      (if ω = histZeroMk c' then R c' else 0)
        = (if ω.1 = c' then R c' else 0) := by
    intro c'
    by_cases h : ω.1 = c'
    · have hω : ω = histZeroMk c' := by
        cases ω with
        | mk c f =>
          change c = c' at h
          subst h
          simp only [histZeroMk]
          congr 1
          exact funext fun i => Fin.elim0 i
      rw [ite_eq_left hω, ite_eq_left h]
    · rw [ite_eq_right, ite_eq_right h]
      intro hcon
      exact h (congrArg Prod.fst hcon)
  simp_rw [hif]
  have hmain : (∑ c' : C, (if ω.1 = c' then R c' else 0))
      = (if ω.1 = ω.1 then R ω.1 else 0) :=
    Finset.sum_eq_single_of_mem ω.1 (Finset.mem_univ ω.1)
      (fun c' _ hc' => ite_eq_right (Ne.symm hc'))
  rw [hmain, ite_eq_left rfl]

/-- Prefix of a transcript before stage `i`. -/
def histPrefix {C Y : Type*} {k : ℕ} (i : Fin k) (ω : Hist C Y k) :
    Hist C Y i.val :=
  (ω.1, fun j => ω.2 (Fin.castLE (Nat.le_of_lt i.isLt) j))

/-- Output of a transcript at stage `i`. -/
def histOut {C Y : Type*} {k : ℕ} (i : Fin k) (ω : Hist C Y k) : Y :=
  ω.2 i

private theorem histPrefix_castSucc {C Y : Type*} {n : ℕ} (i : Fin n)
    (ω : Hist C Y (n + 1)) :
    histPrefix i.castSucc ω = histPrefix i (histInit ω) :=
  rfl

private theorem histOut_castSucc {C Y : Type*} {n : ℕ} (i : Fin n)
    (ω : Hist C Y (n + 1)) :
    histOut i.castSucc ω = histOut i (histInit ω) := by
  cases ω with
  | mk c f =>
    rfl

private theorem histPrefix_last {C Y : Type*} {n : ℕ}
    (ω : Hist C Y (n + 1)) :
    histPrefix (Fin.last n) ω = histInit ω :=
  rfl

private theorem histOut_last {C Y : Type*} {n : ℕ}
    (ω : Hist C Y (n + 1)) :
    histOut (Fin.last n) ω = histLast ω := by
  cases ω with
  | mk c f =>
    rfl

/-- Real-mass factorization of the transcript law. -/
theorem transcript_toReal_factor {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (k : ℕ)
    (d : Database) (ω : Hist C Y k) :
    (transcript R K k d ω).toReal
      = (R ω.1).toReal * ∏ i : Fin k,
        (K i.val (histPrefix i ω) d (histOut i ω)).toReal := by
  induction k with
  | zero =>
    rw [transcript_zero_apply]
    simp
  | succ n ih =>
    rw [transcript_succ_apply R K n d ω, ENNReal.toReal_mul,
      ih (histInit ω)]
    have hR : (R (histInit ω).1).toReal = (R ω.1).toReal := rfl
    rw [hR]
    have hcast : ∀ i : Fin n,
        (K i.castSucc.val (histPrefix i.castSucc ω) d
          (histOut i.castSucc ω)).toReal
        = (K i.val (histPrefix i (histInit ω)) d
          (histOut i (histInit ω))).toReal :=
      fun i => rfl
    have hlast :
        (K (Fin.last n).val (histPrefix (Fin.last n) ω) d
          (histOut (Fin.last n) ω)).toReal
        = (K n (histInit ω) d (histLast ω)).toReal :=
      rfl
    simp only [Fin.prod_univ_castSucc]
    simp_rw [hcast]
    rw [hlast]
    ring

private theorem toReal_ne_zero_of_ne_zero {x : ENNReal} (h0 : x ≠ 0)
    (hT : x ≠ ⊤) : x.toReal ≠ 0 := by
  intro hR
  rw [ENNReal.toReal_eq_zero_iff] at hR
  exact h0 (hR.resolve_right hT)

/-- Stage guarantees give equal transcript supports for adjacent databases. -/
theorem transcript_support_eq {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d) :
    (transcript R K k d).support = (transcript R K k d').support := by
  ext ω
  simp only [PMF.mem_support_iff]
  have hiff : ∀ x : ENNReal, x ≠ ⊤ → (x ≠ 0 ↔ x.toReal ≠ 0) := by
    intro x hx
    constructor
    · intro h0 hR
      exact h0 (((ENNReal.toReal_eq_zero_iff x).mp hR).resolve_right hx)
    · intro hR h0
      exact hR (by simp [h0])
  rw [hiff _ ((transcript R K k d).apply_ne_top ω),
    hiff _ ((transcript R K k d').apply_ne_top ω),
    transcript_toReal_factor R K k d ω,
    transcript_toReal_factor R K k d' ω,
    mul_ne_zero_iff, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.prod_ne_zero_iff]
  have hfactor : ∀ i : Fin k,
      (K i.val (histPrefix i ω) d (histOut i ω)).toReal ≠ 0
        ↔ (K i.val (histPrefix i ω) d' (histOut i ω)).toReal ≠ 0 := by
    intro i
    have hsup := support_eq_of_dp_two_sided
      (K i.val (histPrefix i ω) d) (K i.val (histPrefix i ω) d') ε
      (fun w => (hK i.val (histPrefix i ω)).2 d d' hadj w)
      (fun w => (hK i.val (histPrefix i ω)).2 d' d hadj_symm w)
    have hmem : K i.val (histPrefix i ω) d (histOut i ω) ≠ 0
        ↔ K i.val (histPrefix i ω) d' (histOut i ω) ≠ 0 := by
      have hmem' : histOut i ω ∈ (K i.val (histPrefix i ω) d).support
          ↔ histOut i ω ∈ (K i.val (histPrefix i ω) d').support := by
        rw [hsup]
      simpa only [PMF.mem_support_iff] using hmem'
    have hKd : K i.val (histPrefix i ω) d (histOut i ω) ≠ ⊤ :=
      (K i.val (histPrefix i ω) d).apply_ne_top _
    have hKd' : K i.val (histPrefix i ω) d' (histOut i ω) ≠ ⊤ :=
      (K i.val (histPrefix i ω) d').apply_ne_top _
    rw [← hiff _ hKd, ← hiff _ hKd', hmem]
  constructor
  · rintro ⟨hr, hF⟩
    exact ⟨hr, fun i _ => (hfactor i).mp (hF i (Finset.mem_univ i))⟩
  · rintro ⟨hr, hG⟩
    exact ⟨hr, fun i _ => (hfactor i).mpr (hG i (Finset.mem_univ i))⟩

/-- Privacy-loss decomposition over the transcript.

The identity holds on `(transcript R K k d).support` only: `privacyLoss`
totalizes at zero mass, so off support the two sides can disagree. -/
theorem transcript_loss_decomp {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d)
    (ω : Hist C Y k) (hω : ω ∈ (transcript R K k d).support) :
    Real.log ((transcript R K k d ω).toReal / (transcript R K k d' ω).toReal)
      = ∑ i : Fin k, privacyLoss (K i.val (histPrefix i ω) d)
        (K i.val (histPrefix i ω) d') (histOut i ω) := by
  have hsup := transcript_support_eq R K adj ε k d d' hK hε hadj hadj_symm
  have hω' : ω ∈ (transcript R K k d').support := by
    rw [← hsup]
    exact hω
  rw [PMF.mem_support_iff] at hω hω'
  have hAd : (transcript R K k d ω).toReal ≠ 0 :=
    toReal_ne_zero_of_ne_zero hω ((transcript R K k d).apply_ne_top ω)
  have hBd : (transcript R K k d' ω).toReal ≠ 0 :=
    toReal_ne_zero_of_ne_zero hω' ((transcript R K k d').apply_ne_top ω)
  have hA := transcript_toReal_factor R K k d ω
  have hB := transcript_toReal_factor R K k d' ω
  have hr : (R ω.1).toReal ≠ 0 := by
    have h1 := hAd
    rw [hA, mul_ne_zero_iff] at h1
    exact h1.1
  have hF : ∀ i : Fin k,
      (K i.val (histPrefix i ω) d (histOut i ω)).toReal ≠ 0 := by
    have h1 := hAd
    rw [hA, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at h1
    intro i
    exact h1.2 i (Finset.mem_univ i)
  have hG : ∀ i : Fin k,
      (K i.val (histPrefix i ω) d' (histOut i ω)).toReal ≠ 0 := by
    have h1 := hBd
    rw [hB, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at h1
    intro i
    exact h1.2 i (Finset.mem_univ i)
  have hfg : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (K i.val (histPrefix i ω) d (histOut i ω)).toReal
        / (K i.val (histPrefix i ω) d' (histOut i ω)).toReal ≠ 0 :=
    fun i _ => div_ne_zero (hF i) (hG i)
  rw [hA, hB, mul_div_mul_left _ _ hr, ← Finset.prod_div_distrib]
  simp only [Real.log_prod hfg]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Expected stage loss under the stage kernel, in finite-sum form. -/
noncomputable def stageDrift {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (i : ℕ)
    (h : Hist C Y i) (d d' : Database) : ℝ :=
  ∑ y : Y, (K i h d y).toReal * privacyLoss (K i h d) (K i h d') y

/-- Stage drift is the stage-kernel loss expectation. -/
theorem stageDrift_eq_privacyLossExpectation {C Y Database : Type*}
    [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (i : ℕ)
    (h : Hist C Y i) (d d' : Database) :
    stageDrift K i h d d'
      = privacyLossExpectation (K i h d) (K i h d') := by
  simp only [stageDrift, privacyLossExpectation, tsum_fintype]

/-- Stage drift is nonnegative under two-sided stage guarantees. -/
theorem stageDrift_nonneg {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (i : ℕ)
    (h : Hist C Y i) (d d' : Database)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hadj : adj d d') (hadj_symm : adj d' d) :
    0 ≤ stageDrift K i h d d' := by
  rw [stageDrift_eq_privacyLossExpectation]
  exact privacyLossExpectation_nonneg_of_isDP (fun d => K i h d) adj ε d d'
    (hK i h) hadj hadj_symm

/-- Stage drift is at most `ε * (exp ε - 1)` under stage guarantees. -/
theorem stageDrift_le {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (i : ℕ)
    (h : Hist C Y i) (d d' : Database)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hadj : adj d d') (hadj_symm : adj d' d) :
    stageDrift K i h d d' ≤ ε * (Real.exp ε - 1) := by
  rw [stageDrift_eq_privacyLossExpectation]
  exact privacyLossExpectation_le_of_isDP (fun d => K i h d) adj ε d d'
    (hK i h) hadj hadj_symm

/-- On support, the stage loss is bounded by `ε` in absolute value. -/
theorem abs_stageLoss_le {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (i : ℕ)
    (h : Hist C Y i) (d d' : Database) (y : Y)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hadj : adj d d') (hadj_symm : adj d' d)
    (hy : K i h d y ≠ 0) :
    |privacyLoss (K i h d) (K i h d') y| ≤ ε :=
  abs_privacyLoss_le_of_dp_two_sided (K i h d) (K i h d') ε y (hK i h).1
    (fun w => (hK i h).2 d d' hadj w)
    (fun w => (hK i h).2 d' d hadj_symm w) hy

/-- Stage contribution to the transcript loss at `ω`. -/
noncomputable def stageLoss {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (k : ℕ)
    (d d' : Database) (i : Fin k) (ω : Hist C Y k) : ℝ :=
  privacyLoss (K i.val (histPrefix i ω) d) (K i.val (histPrefix i ω) d')
    (histOut i ω)

/-- Total transcript loss at `ω`. -/
noncomputable def totalLoss {C Y Database : Type*} [Fintype C] [Fintype Y]
    (R : PMF C) (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (k : ℕ)
    (d d' : Database) (ω : Hist C Y k) : ℝ :=
  Real.log ((transcript R K k d ω).toReal / (transcript R K k d' ω).toReal)

/-- Centered loss identity on the transcript support. -/
theorem centered_loss_identity {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d)
    (ω : Hist C Y k) (hω : ω ∈ (transcript R K k d).support) :
    ∑ i : Fin k, (stageLoss K k d d' i ω
        - stageDrift K i.val (histPrefix i ω) d d')
      = totalLoss R K k d d' ω
        - ∑ i : Fin k, stageDrift K i.val (histPrefix i ω) d d' := by
  rw [Finset.sum_sub_distrib]
  have hdecomp :=
    transcript_loss_decomp R K adj ε k d d' hK hε hadj hadj_symm ω hω
  simp only [stageLoss, totalLoss]
  rw [hdecomp]

/-- One-step expectation over the transcript law. -/
theorem transcript_expectation_succ {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (n : ℕ)
    (d : Database) (F : Hist C Y (n + 1) → ℝ) :
    ∑ ω : Hist C Y (n + 1), (transcript R K (n + 1) d ω).toReal * F ω
      = ∑ h : Hist C Y n, (transcript R K n d h).toReal
        * ∑ y : Y, (K n h d y).toReal * F (histExtend h y) := by
  have hreindex : (∑ ω : Hist C Y (n + 1),
          (transcript R K (n + 1) d ω).toReal * F ω)
        = ∑ p : Hist C Y n × Y,
          (transcript R K (n + 1) d (histExtend p.1 p.2)).toReal
            * F (histExtend p.1 p.2) :=
    (Equiv.sum_comp (histSnocEquiv n)
      (fun ω => (transcript R K (n + 1) d ω).toReal * F ω)).symm
  rw [hreindex]
  have hmass : ∀ p : Hist C Y n × Y,
      (transcript R K (n + 1) d (histExtend p.1 p.2)).toReal
        = (transcript R K n d p.1).toReal * (K n p.1 d p.2).toReal := by
    intro p
    rw [transcript_extend_apply R K n d p.1 p.2, ENNReal.toReal_mul]
  simp_rw [hmass]
  have hsplit : (∑ p : Hist C Y n × Y,
          ((transcript R K n d p.1).toReal * (K n p.1 d p.2).toReal)
            * F (histExtend p.1 p.2))
        = ∑ h : Hist C Y n, ∑ y : Y,
          (((transcript R K n d h).toReal * (K n h d y).toReal)
            * F (histExtend h y)) :=
    Fintype.sum_prod_type (fun p : Hist C Y n × Y =>
      ((transcript R K n d p.1).toReal * (K n p.1 d p.2).toReal)
        * F (histExtend p.1 p.2))
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Project a transcript to its first `n` stages. -/
def prefixProj {C Y : Type*} {n m : ℕ} (h : n ≤ m) (w : Hist C Y m) :
    Hist C Y n :=
  (w.1, fun j => w.2 (Fin.castLE h j))

private theorem prefixProj_id {C Y : Type*} {n : ℕ} (h : n ≤ n) :
    prefixProj (C := C) (Y := Y) h = id :=
  rfl

private theorem prefixProj_succ {C Y : Type*} {n k : ℕ} (h₁₃ : n ≤ k + 1)
    (h₁₂ : n ≤ k) :
    prefixProj (C := C) (Y := Y) h₁₃
      = prefixProj (C := C) (Y := Y) h₁₂ ∘ histInit :=
  rfl

private theorem transcript_map_histInit {C Y Database : Type*}
    [Fintype C] [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (k : ℕ)
    (d : Database) :
    (transcript R K (k + 1) d).map histInit = transcript R K k d := by
  rw [transcript_succ]
  simp only [PMF.map_bind]
  have hinner : ∀ h : Hist C Y k,
      PMF.map histInit (PMF.map (histExtend h) (K k h d)) = PMF.pure h := by
    intro h
    rw [PMF.map_comp]
    have hcomp : histInit ∘ histExtend h = Function.const Y h := by
      funext y
      show histInit (histExtend h y) = h
      exact histInit_histExtend _ _
    rw [hcomp]
    exact PMF.map_const _ _
  simp_rw [hinner]
  have heta : (fun h : Hist C Y k => PMF.pure h) = PMF.pure := rfl
  rw [heta]
  exact PMF.bind_pure _

/-- Prefix marginal: restricting a longer transcript recovers the shorter law. -/
theorem transcript_prefix_marginal {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (n m : ℕ)
    (h : n ≤ m) (d : Database) :
    (transcript R K m d).map (prefixProj h) = transcript R K n d := by
  refine Nat.le_induction (m := n) ?base ?step m h
  · rw [prefixProj_id]
    exact PMF.map_id _
  · intro k hle ih
    rw [prefixProj_succ _ hle, ← PMF.map_comp, transcript_map_histInit, ih]

/- Finite-sum concentration for summed privacy loss.

Per-stage Hoeffding bounds from the sub-Gaussian MGF interface feed an
induction over the transcript length, giving a Chernoff tail bound in
finite-sum form plus its outer-measure wrapper and degenerate cases. -/

open scoped NNReal

/-- The Hoeffding variance proxy on `[−ε, ε]` coerces to `ε ^ 2`. -/
private theorem stage_mgf_param_eq (ε : ℝ) (hε : 0 ≤ ε) :
    ((((‖(ε - -ε)‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ) = ε ^ 2 := by
  rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
  simp only [Real.norm_eq_abs]
  rw [sub_neg_eq_add]
  have h2 : |ε + ε| = 2 * ε := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [h2]
  norm_num

/-- Finite-sum stage MGF bound: Hoeffding's lemma at one history. -/
private theorem stage_mgf_le {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (i : ℕ)
    (h : Hist C Y i) (d d' : Database) (lam : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d) :
    ∑ y : Y, (K i h d y).toReal
        * Real.exp (lam * (privacyLoss (K i h d) (K i h d') y
          - stageDrift K i h d d'))
      ≤ Real.exp (lam ^ 2 * ε ^ 2 / 2) := by
  let : MeasurableSpace Y := ⊤
  have hIcc : ∀ y : Y,
      privacyLoss (K i h d) (K i h d') y ∈ Set.Icc (-ε) ε := by
    intro y
    by_cases hy : K i h d y = 0
    · have h0 : privacyLoss (K i h d) (K i h d') y = 0 := by
        simp only [privacyLoss, hy, ENNReal.toReal_zero, zero_div,
          Real.log_zero]
      rw [h0]
      exact ⟨neg_nonpos.mpr hε, hε⟩
    · have habs := abs_stageLoss_le K adj ε i h d d' y hK hadj hadj_symm hy
      rwa [abs_le] at habs
  have hm : AEMeasurable (fun y => privacyLoss (K i h d) (K i h d') y)
      (K i h d).toMeasure :=
    (measurable_of_countable _).aemeasurable
  have hb : ∀ᵐ y ∂(K i h d).toMeasure,
      privacyLoss (K i h d) (K i h d') y ∈ Set.Icc (-ε) ε :=
    Filter.Eventually.of_forall hIcc
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (μ := (K i h d).toMeasure)
    (X := fun y => privacyLoss (K i h d) (K i h d') y) hm hb
  have hmgf := hsub.mgf_le lam
  have hexp : ∫ y, privacyLoss (K i h d) (K i h d') y ∂(K i h d).toMeasure
      = stageDrift K i h d d' := by
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul, stageDrift]
  simp only [ProbabilityTheory.mgf] at hmgf
  simp only [hexp] at hmgf
  rw [PMF.integral_eq_sum] at hmgf
  simp only [smul_eq_mul] at hmgf
  rw [stage_mgf_param_eq ε hε] at hmgf
  have heq : ε ^ 2 * lam ^ 2 / 2 = lam ^ 2 * ε ^ 2 / 2 := by ring
  rw [heq] at hmgf
  exact hmgf

/-- Finite-sum MGF bound for the centered transcript loss. -/
theorem transcript_centered_mgf_le {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (lam : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d) :
    ∑ ω : Hist C Y k, (transcript R K k d ω).toReal
        * Real.exp (lam * ∑ i : Fin k, (stageLoss K k d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d'))
      ≤ Real.exp ((k : ℝ) * lam ^ 2 * ε ^ 2 / 2) := by
  induction k with
  | zero =>
    have htsum := (transcript R K 0 d).tsum_coe
    rw [tsum_fintype] at htsum
    have hfin : ∀ ω ∈ (Finset.univ : Finset (Hist C Y 0)),
        transcript R K 0 d ω ≠ ⊤ :=
      fun ω _ => (transcript R K 0 d).apply_ne_top ω
    have h1 : ∑ ω : Hist C Y 0, (transcript R K 0 d ω).toReal = 1 := by
      have h2 := congrArg ENNReal.toReal htsum
      rw [ENNReal.toReal_sum hfin, ENNReal.toReal_one] at h2
      exact h2
    have hexp1 : ∀ ω : Hist C Y 0, Real.exp (lam * ∑ i : Fin 0,
        (stageLoss K 0 d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) = 1 := by
      intro ω
      have huniv : (Finset.univ : Finset (Fin 0)) = ∅ :=
        Finset.card_eq_zero.mp (by simp)
      have hsum : (∑ i : Fin 0, (stageLoss K 0 d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) = 0 := by
        rw [huniv]
        exact Finset.sum_empty
      rw [hsum, mul_zero, Real.exp_zero]
    simp only [hexp1, mul_one]
    rw [h1]
    simp
  | succ n ih =>
    have hstep := transcript_expectation_succ R K n d
      (fun ω => Real.exp (lam * ∑ i : Fin (n + 1), (stageLoss K (n + 1) d d' i ω
        - stageDrift K i.val (histPrefix i ω) d d')))
    have hsplit : ∀ h : Hist C Y n, ∀ y : Y,
        (∑ i : Fin (n + 1), (stageLoss K (n + 1) d d' i (histExtend h y)
          - stageDrift K i.val (histPrefix i (histExtend h y)) d d'))
        = (∑ i : Fin n, (stageLoss K n d d' i h
            - stageDrift K i.val (histPrefix i h) d d'))
          + (privacyLoss (K n h d) (K n h d') y
            - stageDrift K n h d d') := by
      intro h y
      have hpre : ∀ i : Fin n,
          histPrefix i.castSucc (histExtend h y) = histPrefix i h := by
        intro i
        rw [histPrefix_castSucc, histInit_histExtend]
      have hout : ∀ i : Fin n,
          histOut i.castSucc (histExtend h y) = histOut i h := by
        intro i
        rw [histOut_castSucc, histInit_histExtend]
      have ha : ∀ i : Fin n,
          stageLoss K (n + 1) d d' i.castSucc (histExtend h y)
          = stageLoss K n d d' i h := by
        intro i
        simp only [stageLoss]
        rw [hpre i, hout i]
        exact rfl
      have hbdrift : ∀ i : Fin n, stageDrift K i.castSucc.val
            (histPrefix i.castSucc (histExtend h y)) d d'
          = stageDrift K i.val (histPrefix i h) d d' := by
        intro i
        rw [hpre i]
        exact rfl
      have hclast : stageLoss K (n + 1) d d' (Fin.last n) (histExtend h y)
          = privacyLoss (K n h d) (K n h d') y := by
        simp only [stageLoss]
        rw [histPrefix_last, histInit_histExtend, histOut_last,
          histLast_histExtend]
        exact rfl
      have hddrift : stageDrift K (Fin.last n).val
            (histPrefix (Fin.last n) (histExtend h y)) d d'
          = stageDrift K n h d d' := by
        rw [histPrefix_last, histInit_histExtend]
        exact rfl
      simp only [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [ha i, hbdrift i]
      · rw [hclast, hddrift]
    have hexpsplit : ∀ h : Hist C Y n, ∀ y : Y,
        Real.exp (lam * (∑ i : Fin (n + 1), (stageLoss K (n + 1) d d' i
            (histExtend h y)
            - stageDrift K i.val (histPrefix i (histExtend h y)) d d')))
        = Real.exp (lam * (∑ i : Fin n, (stageLoss K n d d' i h
            - stageDrift K i.val (histPrefix i h) d d')))
          * Real.exp (lam * (privacyLoss (K n h d) (K n h d') y
            - stageDrift K n h d d')) := by
      intro h y
      rw [hsplit h y, mul_add, Real.exp_add]
    have hinner : ∀ h : Hist C Y n,
        (∑ y : Y, (K n h d y).toReal * Real.exp (lam * (∑ i : Fin (n + 1),
          (stageLoss K (n + 1) d d' i (histExtend h y)
            - stageDrift K i.val (histPrefix i (histExtend h y)) d d'))))
        ≤ Real.exp (lam * (∑ i : Fin n, (stageLoss K n d d' i h
            - stageDrift K i.val (histPrefix i h) d d')))
          * Real.exp (lam ^ 2 * ε ^ 2 / 2) := by
      intro h
      have hbridge :=
        stage_mgf_le K adj ε n h d d' lam hK hε hadj hadj_symm
      have hfactor : (∑ y : Y, (K n h d y).toReal * Real.exp (lam *
            (∑ i : Fin (n + 1), (stageLoss K (n + 1) d d' i (histExtend h y)
              - stageDrift K i.val (histPrefix i (histExtend h y)) d d'))))
          = Real.exp (lam * (∑ i : Fin n, (stageLoss K n d d' i h
              - stageDrift K i.val (histPrefix i h) d d')))
            * ∑ y : Y, (K n h d y).toReal * Real.exp (lam *
              (privacyLoss (K n h d) (K n h d') y
                - stageDrift K n h d d')) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [hexpsplit h y]
        ring
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left hbridge (Real.exp_nonneg _)
    calc (∑ ω : Hist C Y (n + 1), (transcript R K (n + 1) d ω).toReal
            * Real.exp (lam * ∑ i : Fin (n + 1), (stageLoss K (n + 1) d d' i ω
              - stageDrift K i.val (histPrefix i ω) d d')))
        = ∑ h : Hist C Y n, (transcript R K n d h).toReal
          * ∑ y : Y, (K n h d y).toReal * Real.exp (lam * (∑ i : Fin (n + 1),
            (stageLoss K (n + 1) d d' i (histExtend h y)
              - stageDrift K i.val (histPrefix i (histExtend h y)) d d'))) :=
          hstep
      _ ≤ ∑ h : Hist C Y n, (transcript R K n d h).toReal
          * (Real.exp (lam * (∑ i : Fin n, (stageLoss K n d d' i h
            - stageDrift K i.val (histPrefix i h) d d')))
            * Real.exp (lam ^ 2 * ε ^ 2 / 2)) :=
          Finset.sum_le_sum fun h _ =>
            mul_le_mul_of_nonneg_left (hinner h) ENNReal.toReal_nonneg
      _ = (∑ h : Hist C Y n, (transcript R K n d h).toReal
          * Real.exp (lam * (∑ i : Fin n, (stageLoss K n d d' i h
            - stageDrift K i.val (histPrefix i h) d d'))))
          * Real.exp (lam ^ 2 * ε ^ 2 / 2) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _
          ring
      _ ≤ Real.exp ((n : ℝ) * lam ^ 2 * ε ^ 2 / 2)
          * Real.exp (lam ^ 2 * ε ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
      _ = Real.exp ((((n + 1 : ℕ)) : ℝ) * lam ^ 2 * ε ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          have hcast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          rw [hcast]
          ring

/-- Summed stage drift is at most `k` times the per-stage upper bound. -/
private theorem summed_drift_le {C Y Database : Type*} [Fintype C] [Fintype Y]
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (ω : Hist C Y k)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hadj : adj d d') (hadj_symm : adj d' d) :
    (∑ i : Fin k, stageDrift K i.val (histPrefix i ω) d d')
      ≤ (k : ℝ) * (ε * (Real.exp ε - 1)) := by
  calc (∑ i : Fin k, stageDrift K i.val (histPrefix i ω) d d')
      ≤ ∑ _i : Fin k, (ε * (Real.exp ε - 1)) :=
        Finset.sum_le_sum fun i _ => stageDrift_le K adj ε i.val
          (histPrefix i ω) d d' hK hadj hadj_symm
    _ = (k : ℝ) * (ε * (Real.exp ε - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- Finite-sum tail bound for the transcript loss (strict event). -/
theorem transcript_tail_le {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (t : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d)
    (hk : 0 < k) (hεpos : 0 < ε) (ht : 0 ≤ t) :
    ∑ ω ∈ Finset.univ.filter
          (fun ω => (k : ℝ) * (ε * (Real.exp ε - 1)) + t
            < totalLoss R K k d d' ω),
        (transcript R K k d ω).toReal
      ≤ Real.exp (-(t ^ 2) / (2 * (k : ℝ) * ε ^ 2)) := by
  set lam : ℝ := t / ((k : ℝ) * ε ^ 2) with hlam_def
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hε2pos : (0 : ℝ) < ε ^ 2 := by
    rw [pow_two]
    exact mul_pos hεpos hεpos
  have hkεpos : (0 : ℝ) < (k : ℝ) * ε ^ 2 := mul_pos hkpos hε2pos
  have hlam : 0 ≤ lam := by
    rw [hlam_def]
    exact div_nonneg ht hkεpos.le
  have hD : ∀ ω : Hist C Y k,
      (∑ i : Fin k, stageDrift K i.val (histPrefix i ω) d d')
        ≤ (k : ℝ) * (ε * (Real.exp ε - 1)) :=
    fun ω => summed_drift_le K adj ε k d d' ω hK hadj hadj_symm
  have hembed : ∀ ω : Hist C Y k, ω ∈ (transcript R K k d).support →
      (k : ℝ) * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω →
      t < ∑ i : Fin k, (stageLoss K k d d' i ω
        - stageDrift K i.val (histPrefix i ω) d d') := by
    intro ω hω hth
    have hci :=
      centered_loss_identity R K adj ε k d d' hK hε hadj hadj_symm ω hω
    rw [hci]
    have hDω := hD ω
    linarith
  have hmarkov : ∀ ω ∈ Finset.univ.filter (fun ω => (k : ℝ)
        * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
      (transcript R K k d ω).toReal ≤ (transcript R K k d ω).toReal
        * Real.exp (lam * ((∑ i : Fin k, (stageLoss K k d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) - t)) := by
    intro ω hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    by_cases h0 : (transcript R K k d ω).toReal = 0
    · simp [h0]
    · have hsup : ω ∈ (transcript R K k d).support := by
        rw [PMF.mem_support_iff]
        intro hcon
        exact h0 (by simp [hcon])
      have hct := hembed ω hsup hmem
      have hnn : (0 : ℝ) ≤ lam * ((∑ i : Fin k, (stageLoss K k d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) - t) :=
        mul_nonneg hlam (sub_nonneg.mpr hct.le)
      have hexp1 : (1 : ℝ) ≤ Real.exp (lam * ((∑ i : Fin k,
          (stageLoss K k d d' i ω
            - stageDrift K i.val (histPrefix i ω) d d')) - t)) :=
        Real.one_le_exp hnn
      calc (transcript R K k d ω).toReal
          = (transcript R K k d ω).toReal * 1 := (mul_one _).symm
        _ ≤ (transcript R K k d ω).toReal * Real.exp (lam *
            ((∑ i : Fin k, (stageLoss K k d d' i ω
              - stageDrift K i.val (histPrefix i ω) d d')) - t)) :=
          mul_le_mul_of_nonneg_left hexp1 ENNReal.toReal_nonneg
  have hsub : (∑ ω ∈ Finset.univ.filter (fun ω => (k : ℝ)
          * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
        (transcript R K k d ω).toReal)
      ≤ ∑ ω : Hist C Y k, (transcript R K k d ω).toReal * Real.exp (lam *
        ((∑ i : Fin k, (stageLoss K k d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) - t)) := by
    calc (∑ ω ∈ Finset.univ.filter (fun ω => (k : ℝ)
            * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
          (transcript R K k d ω).toReal)
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω => (k : ℝ)
            * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
          (transcript R K k d ω).toReal * Real.exp (lam *
            ((∑ i : Fin k, (stageLoss K k d d' i ω
              - stageDrift K i.val (histPrefix i ω) d d')) - t)) :=
          Finset.sum_le_sum hmarkov
      _ ≤ ∑ ω ∈ Finset.univ, (transcript R K k d ω).toReal * Real.exp (lam *
          ((∑ i : Fin k, (stageLoss K k d d' i ω
            - stageDrift K i.val (histPrefix i ω) d d')) - t)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ω _ _ => mul_nonneg ENNReal.toReal_nonneg
              (Real.exp_nonneg _))
  have hexpfac : ∀ ω : Hist C Y k, Real.exp (lam *
        ((∑ i : Fin k, (stageLoss K k d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) - t))
      = Real.exp (lam * (∑ i : Fin k, (stageLoss K k d d' i ω
        - stageDrift K i.val (histPrefix i ω) d d')))
        * Real.exp (-(lam * t)) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor : (∑ ω : Hist C Y k, (transcript R K k d ω).toReal
        * Real.exp (lam * ((∑ i : Fin k, (stageLoss K k d d' i ω
          - stageDrift K i.val (histPrefix i ω) d d')) - t)))
      = (∑ ω : Hist C Y k, (transcript R K k d ω).toReal
          * Real.exp (lam * (∑ i : Fin k, (stageLoss K k d d' i ω
            - stageDrift K i.val (histPrefix i ω) d d'))))
        * Real.exp (-(lam * t)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    rw [hexpfac ω]
    ring
  have hmgf :=
    transcript_centered_mgf_le R K adj ε k d d' lam hK hε hadj hadj_symm
  calc (∑ ω ∈ Finset.univ.filter (fun ω => (k : ℝ)
          * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
        (transcript R K k d ω).toReal)
      ≤ (∑ ω : Hist C Y k, (transcript R K k d ω).toReal
          * Real.exp (lam * (∑ i : Fin k, (stageLoss K k d d' i ω
            - stageDrift K i.val (histPrefix i ω) d d'))))
        * Real.exp (-(lam * t)) := by
        rw [← hfactor]
        exact hsub
    _ ≤ Real.exp ((k : ℝ) * lam ^ 2 * ε ^ 2 / 2) * Real.exp (-(lam * t)) :=
        mul_le_mul_of_nonneg_right hmgf (Real.exp_nonneg _)
    _ = Real.exp (-(t ^ 2) / (2 * (k : ℝ) * ε ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hlam_def]
        have hkε : ((k : ℝ) * ε ^ 2) ≠ 0 := ne_of_gt hkεpos
        have h2kε : (2 * (k : ℝ) * ε ^ 2) ≠ 0 :=
          ne_of_gt (mul_pos (mul_pos (by norm_num) hkpos) hε2pos)
        field_simp
        ring

/-- Outer-measure tail bound for the transcript loss. -/
theorem transcript_tail_outer_le {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (t : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d)
    (hk : 0 < k) (hεpos : 0 < ε) (ht : 0 ≤ t) :
    (transcript R K k d).toOuterMeasure
        {ω | (k : ℝ) * (ε * (Real.exp ε - 1)) + t
          < totalLoss R K k d d' ω}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (k : ℝ) * ε ^ 2))) := by
  have hset : {ω | (k : ℝ) * (ε * (Real.exp ε - 1)) + t
        < totalLoss R K k d d' ω}
      = ↑(Finset.univ.filter (fun ω => (k : ℝ) * (ε * (Real.exp ε - 1)) + t
        < totalLoss R K k d d' ω)) := by
    ext ω
    simp
  rw [hset, PMF.toOuterMeasure_apply_finset]
  have htail :=
    transcript_tail_le R K adj ε k d d' t hK hε hadj hadj_symm hk hεpos ht
  have hfin : (∑ x ∈ Finset.univ.filter (fun ω => (k : ℝ)
        * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
      transcript R K k d x) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr
      (fun x _ => (transcript R K k d).apply_ne_top x)
  have htoReal : ∀ x ∈ Finset.univ.filter (fun ω => (k : ℝ)
        * (ε * (Real.exp ε - 1)) + t < totalLoss R K k d d' ω),
      transcript R K k d x ≠ ⊤ :=
    fun x _ => (transcript R K k d).apply_ne_top x
  rw [ENNReal.le_ofReal_iff_toReal_le hfin (Real.exp_nonneg _),
    ENNReal.toReal_sum htoReal]
  exact htail

/-- At zero length, the transcript loss vanishes identically. -/
private theorem totalLoss_zero_of_zero_length {C Y Database : Type*}
    [Fintype C] [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y) (k : ℕ)
    (d d' : Database) (ω : Hist C Y k) (hk0 : k = 0) :
    totalLoss R K k d d' ω = 0 := by
  subst hk0
  simp only [totalLoss, transcript_zero_apply]
  by_cases hx : (R ω.1).toReal = 0
  · rw [hx, zero_div, Real.log_zero]
  · rw [div_self hx, Real.log_one]

/-- At zero budget, the transcript loss vanishes identically. -/
private theorem totalLoss_zero_of_zero_budget {C Y Database : Type*}
    [Fintype C] [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (ω : Hist C Y k)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d) (hε0 : ε = 0) :
    totalLoss R K k d d' ω = 0 := by
  subst hε0
  by_cases hω : ω ∈ (transcript R K k d).support
  · have hdecomp :=
      transcript_loss_decomp R K adj 0 k d d' hK hε hadj hadj_symm ω hω
    have hstage : ∀ i : Fin k, privacyLoss (K i.val (histPrefix i ω) d)
        (K i.val (histPrefix i ω) d') (histOut i ω) = 0 := by
      intro i
      have hmem : transcript R K k d ω ≠ 0 :=
        (PMF.mem_support_iff _ _).mp hω
      have hAd : (transcript R K k d ω).toReal ≠ 0 :=
        toReal_ne_zero_of_ne_zero hmem ((transcript R K k d).apply_ne_top ω)
      have hA := transcript_toReal_factor R K k d ω
      have hF : (K i.val (histPrefix i ω) d (histOut i ω)).toReal ≠ 0 := by
        have h1 := hAd
        rw [hA, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at h1
        exact h1.2 i (Finset.mem_univ i)
      have hsup : K i.val (histPrefix i ω) d (histOut i ω) ≠ 0 := by
        intro hcon
        exact hF (by simp [hcon])
      have habs := abs_stageLoss_le K adj 0 i.val (histPrefix i ω) d d'
        (histOut i ω) hK hadj hadj_symm hsup
      have h0 : |privacyLoss (K i.val (histPrefix i ω) d)
          (K i.val (histPrefix i ω) d') (histOut i ω)| = 0 :=
        le_antisymm habs (abs_nonneg _)
      rwa [abs_eq_zero] at h0
    simp only [totalLoss]
    rw [hdecomp]
    simp [hstage]
  · simp only [PMF.mem_support_iff, not_not] at hω
    simp only [totalLoss, hω, ENNReal.toReal_zero, zero_div, Real.log_zero]

/-- Degenerate case `k = 0`: the strict tail event has mass zero. -/
theorem transcript_tail_zero_length {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (ε : ℝ) (k : ℕ) (d d' : Database)
    (t : ℝ) (ht : 0 ≤ t) (hk0 : k = 0) :
    ∑ ω ∈ Finset.univ.filter
          (fun ω => (k : ℝ) * (ε * (Real.exp ε - 1)) + t
            < totalLoss R K k d d' ω),
        (transcript R K k d ω).toReal = 0 := by
  have hempty : Finset.univ.filter
        (fun ω : Hist C Y k => (k : ℝ) * (ε * (Real.exp ε - 1)) + t
          < totalLoss R K k d d' ω) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ω hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [totalLoss_zero_of_zero_length R K k d d' ω hk0] at hmem
    rw [hk0] at hmem
    simp only [Nat.cast_zero, zero_mul, zero_add] at hmem
    linarith
  rw [hempty, Finset.sum_empty]

/-- Degenerate case `ε = 0`: the strict tail event has mass zero. -/
theorem transcript_tail_zero_budget {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (t : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d)
    (ht : 0 ≤ t) (hε0 : ε = 0) :
    ∑ ω ∈ Finset.univ.filter
          (fun ω => (k : ℝ) * (ε * (Real.exp ε - 1)) + t
            < totalLoss R K k d d' ω),
        (transcript R K k d ω).toReal = 0 := by
  have hempty : Finset.univ.filter
        (fun ω : Hist C Y k => (k : ℝ) * (ε * (Real.exp ε - 1)) + t
          < totalLoss R K k d d' ω) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ω hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [totalLoss_zero_of_zero_budget R K adj ε k d d' ω hK hε hadj hadj_symm
      hε0] at hmem
    rw [hε0] at hmem
    simp only [zero_mul, mul_zero, zero_add] at hmem
    linarith
  rw [hempty, Finset.sum_empty]

/-- Degenerate case `k = 0`: the strict tail event has outer mass zero. -/
theorem transcript_tail_outer_zero_length {C Y Database : Type*}
    [Fintype C] [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (ε : ℝ) (k : ℕ) (d d' : Database)
    (t : ℝ) (ht : 0 ≤ t) (hk0 : k = 0) :
    (transcript R K k d).toOuterMeasure
        {ω | (k : ℝ) * (ε * (Real.exp ε - 1)) + t
          < totalLoss R K k d d' ω} = 0 := by
  have hset : {ω | (k : ℝ) * (ε * (Real.exp ε - 1)) + t
        < totalLoss R K k d d' ω}
      = (∅ : Set (Hist C Y k)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hmem
    rw [totalLoss_zero_of_zero_length R K k d d' ω hk0] at hmem
    rw [hk0] at hmem
    simp only [Nat.cast_zero, zero_mul, zero_add] at hmem
    linarith
  rw [hset]
  simp

/-- Degenerate case `ε = 0`: the strict tail event has outer mass zero. -/
theorem transcript_tail_outer_zero_budget {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (ε : ℝ) (k : ℕ) (d d' : Database)
    (t : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj ε)
    (hε : 0 ≤ ε) (hadj : adj d d') (hadj_symm : adj d' d)
    (ht : 0 ≤ t) (hε0 : ε = 0) :
    (transcript R K k d).toOuterMeasure
        {ω | (k : ℝ) * (ε * (Real.exp ε - 1)) + t
          < totalLoss R K k d d' ω} = 0 := by
  have hset : {ω | (k : ℝ) * (ε * (Real.exp ε - 1)) + t
        < totalLoss R K k d d' ω}
      = (∅ : Set (Hist C Y k)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hmem
    rw [totalLoss_zero_of_zero_budget R K adj ε k d d' ω hK hε hadj hadj_symm
      hε0] at hmem
    rw [hε0] at hmem
    simp only [zero_mul, mul_zero, zero_add] at hmem
    linarith
  rw [hset]
  simp

/- Pure-stage advanced composition.

A pointwise transcript ratio from a total-loss bound feeds a good/bad
event split: on the good set the ratio is uniform, and the bad tail is
controlled by the finite-sum Chernoff bound. Instantiating the deviation
gives the standard pure-DP advanced-composition guarantee. -/

/-- Pointwise transcript ratio from a total-loss bound.

Off the numerator support the mass is zero; on support both masses are
positive (via `transcript_support_eq`), so the log bound exponentiates. -/
theorem transcript_toReal_le_exp_mul_of_totalLoss_le {C Y Database : Type*}
    [Fintype C] [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (eps : ℝ) (k : ℕ) (d d' : Database)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj eps)
    (hε : 0 ≤ eps) (hadj : adj d d') (hadj_symm : adj d' d)
    (omega : Hist C Y k) (E : ℝ)
    (hLoss : totalLoss R K k d d' omega ≤ E) :
    (transcript R K k d omega).toReal ≤
      Real.exp E * (transcript R K k d' omega).toReal := by
  by_cases hω : transcript R K k d omega = 0
  · rw [show (transcript R K k d omega).toReal = 0 by simp [hω]]
    exact mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  · have hsup := transcript_support_eq R K adj eps k d d' hK hε hadj hadj_symm
    have hmem : omega ∈ (transcript R K k d).support :=
      (PMF.mem_support_iff _ _).mpr hω
    rw [hsup] at hmem
    have hQω : transcript R K k d' omega ≠ 0 :=
      (PMF.mem_support_iff _ _).mp hmem
    have hPpos : 0 < (transcript R K k d omega).toReal :=
      ENNReal.toReal_pos hω ((transcript R K k d).apply_ne_top _)
    have hQpos : 0 < (transcript R K k d' omega).toReal :=
      ENNReal.toReal_pos hQω ((transcript R K k d').apply_ne_top _)
    have hLoss' : Real.log ((transcript R K k d omega).toReal /
        (transcript R K k d' omega).toReal) ≤ E := hLoss
    have hx : 0 < (transcript R K k d omega).toReal /
        (transcript R K k d' omega).toReal := div_pos hPpos hQpos
    have hle : (transcript R K k d omega).toReal /
        (transcript R K k d' omega).toReal ≤ Real.exp E := by
      conv_lhs => rw [← Real.exp_log hx]
      exact Real.exp_le_exp.mpr hLoss'
    have hmul := mul_le_mul_of_nonneg_right hle hQpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hQpos)] at hmul

/-- Approximate DP of the transcript from the tail bound.

With `E` the drift-plus-deviation threshold, split each event into the good
set `{ω | totalLoss ≤ E}` (uniform pointwise ratio) and the strict tail
(`transcript_tail_outer_le`). -/
theorem transcript_isApproxDP_of_tail {C Y Database : Type*} [Fintype C]
    [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (eps : ℝ) (k : ℕ) (t : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj eps)
    (hε : 0 ≤ eps)
    (hadj_symm : ∀ d d', adj d d' → adj d' d)
    (hk : 0 < k) (hεpos : 0 < eps) (ht : 0 ≤ t) :
    IsApproxDP (fun d => transcript R K k d) adj
      ((k : ℝ) * (eps * (Real.exp eps - 1)) + t)
      (Real.exp (-(t ^ 2) / (2 * (k : ℝ) * eps ^ 2))) := by
  have hE : (0 : ℝ) ≤ (k : ℝ) * (eps * (Real.exp eps - 1)) + t := by
    have h1 : (1 : ℝ) ≤ Real.exp eps := Real.one_le_exp hε
    have h2 : (0 : ℝ) ≤ eps * (Real.exp eps - 1) :=
      mul_nonneg hε (by linarith)
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg k) h2) ht
  refine ⟨hE, Real.exp_nonneg _, fun d d' hadj s => ?_⟩
  set E : ℝ := (k : ℝ) * (eps * (Real.exp eps - 1)) + t with hEdef
  set G : Set (Hist C Y k) :=
    {ω | totalLoss R K k d d' ω ≤ E} with hGdef
  show (transcript R K k d).toOuterMeasure s ≤
    ENNReal.ofReal (Real.exp E) * (transcript R K k d').toOuterMeasure s +
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (k : ℝ) * eps ^ 2)))
  have hadj' : adj d' d := hadj_symm d d' hadj
  have hpt : ∀ ω ∈ G, transcript R K k d ω ≤
      ENNReal.ofReal (Real.exp E) * transcript R K k d' ω := by
    intro ω hω
    rw [hGdef] at hω
    simp only [Set.mem_ofPred_eq] at hω
    have h1 := transcript_toReal_le_exp_mul_of_totalLoss_le R K adj eps k d d'
      hK hε hadj hadj' ω E hω
    have hPfin : transcript R K k d ω ≠ ⊤ :=
      (transcript R K k d).apply_ne_top ω
    have hQfin : transcript R K k d' ω ≠ ⊤ :=
      (transcript R K k d').apply_ne_top ω
    conv_lhs => rw [← ENNReal.ofReal_toReal hPfin]
    rw [← ENNReal.ofReal_toReal hQfin,
      ← ENNReal.ofReal_mul (Real.exp_nonneg E)]
    exact ENNReal.ofReal_le_ofReal h1
  have hsplit := MeasureTheory.measure_le_inter_add_sdiff
    ((transcript R K k d).toOuterMeasure) s G
  have hgood : (transcript R K k d).toOuterMeasure (s ∩ G) ≤
      ENNReal.ofReal (Real.exp E) *
        (transcript R K k d').toOuterMeasure s := by
    rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hωG : ω ∈ G
    · by_cases hωs : ω ∈ s
      · rw [Set.indicator_of_mem ((Set.mem_inter_iff ω s G).mpr ⟨hωs, hωG⟩),
          Set.indicator_of_mem hωs]
        exact hpt ω hωG
      · rw [Set.indicator_of_notMem (fun h => hωs ((Set.mem_inter_iff ω s G).mp h).1),
          Set.indicator_of_notMem hωs, mul_zero]
    · rw [Set.indicator_of_notMem (fun h => hωG ((Set.mem_inter_iff ω s G).mp h).2)]
      by_cases hωs : ω ∈ s
      · rw [Set.indicator_of_mem hωs]
        exact zero_le
      · rw [Set.indicator_of_notMem hωs, mul_zero]
  have hbad : (transcript R K k d).toOuterMeasure (s \ G) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (k : ℝ) * eps ^ 2))) := by
    have hsub : s \ G ⊆
        {ω | (k : ℝ) * (eps * (Real.exp eps - 1)) + t <
          totalLoss R K k d d' ω} := by
      intro ω hω
      have hnot : ω ∉ G := hω.2
      rw [hGdef] at hnot
      simp only [Set.mem_ofPred_eq] at hnot
      simp only [Set.mem_ofPred_eq]
      rw [← hEdef]
      exact not_le.mp hnot
    calc (transcript R K k d).toOuterMeasure (s \ G)
        ≤ (transcript R K k d).toOuterMeasure
          {ω | (k : ℝ) * (eps * (Real.exp eps - 1)) + t <
            totalLoss R K k d d' ω} :=
          MeasureTheory.measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (k : ℝ) * eps ^ 2))) :=
          transcript_tail_outer_le R K adj eps k d d' t hK hε hadj hadj'
            hk hεpos ht
  calc (transcript R K k d).toOuterMeasure s
      ≤ (transcript R K k d).toOuterMeasure (s ∩ G) +
        (transcript R K k d).toOuterMeasure (s \ G) := hsplit
    _ ≤ ENNReal.ofReal (Real.exp E) *
          (transcript R K k d').toOuterMeasure s +
        ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * (k : ℝ) * eps ^ 2))) :=
        add_le_add hgood hbad

/-- Pure-stage advanced composition.

This is the pure-stage (per-stage `δ = 0`) specialization of advanced
composition (Dwork and Roth, *The Algorithmic Foundations of Differential
Privacy*, 2014, Theorem 3.20) for adaptive discrete PMF transcripts;
per-stage `δ > 0` is not covered here. Each stage is pure-DP; the transcript is approximately DP with deviation
`t = eps * sqrt (2 * k * log (1 / δ'))` on top of the summed drift
`k * eps * (exp eps - 1)`. The degenerate cases are exact with zero budget:
at `k = 0` the transcript law does not depend on the database, and at
`eps = 0` adjacent databases give equal transcript laws. -/
theorem transcript_isApproxDP_advanced_composition_pure {C Y Database : Type*}
    [Fintype C] [Fintype Y] (R : PMF C)
    (K : (n : ℕ) → Hist C Y n → Database → PMF Y)
    (adj : Database → Database → Prop) (eps : ℝ) (k : ℕ) (δ' : ℝ)
    (hK : ∀ (n : ℕ) (h : Hist C Y n), IsDP (fun d => K n h d) adj eps)
    (hε : 0 ≤ eps)
    (hadj_symm : ∀ d d', adj d d' → adj d' d)
    (hδpos : 0 < δ') (hδlt : δ' < 1) :
    IsApproxDP (fun d => transcript R K k d) adj
      (eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ')) +
        (k : ℝ) * (eps * (Real.exp eps - 1)))
      δ' := by
  by_cases hk0 : k = 0
  · subst hk0
    have hbudget : eps * Real.sqrt (2 * ((0 : ℕ) : ℝ) * Real.log (1 / δ')) +
        ((0 : ℕ) : ℝ) * (eps * (Real.exp eps - 1)) = 0 := by
      simp [Real.sqrt_zero]
    rw [hbudget]
    refine ⟨le_refl 0, hδpos.le, fun d d' hadj s => ?_⟩
    show (transcript R K 0 d).toOuterMeasure s ≤
      ENNReal.ofReal (Real.exp 0) * (transcript R K 0 d').toOuterMeasure s +
        ENNReal.ofReal δ'
    have h0 : ∀ d, transcript R K 0 d = R.map histZeroMk := fun d => rfl
    rw [h0 d, h0 d', Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_add_of_nonneg_right zero_le
  · by_cases hε0 : eps = 0
    · subst hε0
      clear hk0
      have hstage : ∀ n h d d', adj d d' → K n h d = K n h d' := by
        intro n h d d' hadj
        apply PMF.ext
        intro o
        have h1 := (hK n h).2 d d' hadj o
        have h2 := (hK n h).2 d' d (hadj_symm d d' hadj) o
        simp only [Real.exp_zero, ENNReal.ofReal_one, one_mul] at h1 h2
        exact le_antisymm h1 h2
      have hlaw : ∀ d d', adj d d' → transcript R K k d = transcript R K k d' := by
        intro d d' hadj
        induction k with
        | zero => rfl
        | succ n ih =>
          have hfun : (fun h => (K n h d).map (histExtend h)) =
              (fun h => (K n h d').map (histExtend h)) := by
            funext h
            rw [hstage n h d d' hadj]
          show (transcript R K n d).bind
              (fun h => (K n h d).map (histExtend h)) =
            (transcript R K n d').bind
              (fun h => (K n h d').map (histExtend h))
          rw [ih, hfun]
      have hbudget : (0 : ℝ) *
          Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ')) +
          (k : ℝ) * (0 * (Real.exp 0 - 1)) = 0 := by simp
      rw [hbudget]
      refine ⟨le_refl 0, hδpos.le, fun d d' hadj s => ?_⟩
      show (transcript R K k d).toOuterMeasure s ≤
        ENNReal.ofReal (Real.exp 0) * (transcript R K k d').toOuterMeasure s +
          ENNReal.ofReal δ'
      rw [hlaw d d' hadj, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      exact le_add_of_nonneg_right zero_le
    · have hk' : 0 < k := Nat.pos_of_ne_zero hk0
      have hεpos' : 0 < eps := lt_of_le_of_ne hε (Ne.symm hε0)
      have h1δ : (1 : ℝ) ≤ 1 / δ' := (one_le_div hδpos).mpr hδlt.le
      have hlog : (0 : ℝ) ≤ Real.log (1 / δ') := Real.log_nonneg h1δ
      have hu : (0 : ℝ) ≤ 2 * (k : ℝ) * Real.log (1 / δ') :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hlog
      have ht : (0 : ℝ) ≤ eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ')) :=
        mul_nonneg hε (Real.sqrt_nonneg _)
      have hmain := transcript_isApproxDP_of_tail R K adj eps k
        (eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ')))
        hK hε hadj_symm hk' hεpos' ht
      have hE : (k : ℝ) * (eps * (Real.exp eps - 1)) +
            eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ')) =
          eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ')) +
            (k : ℝ) * (eps * (Real.exp eps - 1)) :=
        add_comm _ _
      have htsq : (eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / δ'))) ^ 2 =
          eps ^ 2 * (2 * (k : ℝ) * Real.log (1 / δ')) := by
        rw [mul_pow, Real.sq_sqrt hu]
      have hdenom : (2 : ℝ) * (k : ℝ) * eps ^ 2 ≠ 0 := by
        have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk'
        have heps2 : (0 : ℝ) < eps ^ 2 := pow_pos hεpos' 2
        exact ne_of_gt (mul_pos (mul_pos (by norm_num) hkpos) heps2)
      have hexp_arg : -((eps * Real.sqrt (2 * (k : ℝ) *
          Real.log (1 / δ'))) ^ 2) / (2 * (k : ℝ) * eps ^ 2) =
          -Real.log (1 / δ') := by
        rw [htsq, div_eq_iff hdenom]
        ring
      have hδ : Real.exp (-((eps * Real.sqrt (2 * (k : ℝ) *
          Real.log (1 / δ'))) ^ 2) / (2 * (k : ℝ) * eps ^ 2)) = δ' := by
        rw [hexp_arg, Real.exp_neg, Real.exp_log (div_pos zero_lt_one hδpos),
          one_div, inv_inv]
      rw [hE, hδ] at hmain
      exact hmain

/-- Domination transport: per-stage domination scales to transcript laws. -/
theorem transcript_domination {C Y D E : Type*} [Fintype C] [Fintype Y]
    (R : PMF C) (K : (n : ℕ) → Hist C Y n → D → PMF Y)
    (L : (n : ℕ) → Hist C Y n → E → PMF Y) (d : D) (e : E) (k : ℕ)
    (m : ℝ) (hm : 0 ≤ m) (hm_one : m ≤ 1)
    (hstage : ∀ n, n < k → ∀ (h : Hist C Y n) (y : Y),
      m * (L n h e y).toReal ≤ (K n h d y).toReal) :
    ∀ w : Hist C Y k,
      m ^ k * (transcript R L k e w).toReal
        ≤ (transcript R K k d w).toReal := by
  intro w
  rw [transcript_toReal_factor R L k e w, transcript_toReal_factor R K k d w]
  have hpow : (∏ _i : Fin k, m) = m ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hle : (∏ i : Fin k, m * (L i.val (histPrefix i w) e (histOut i w)).toReal)
      ≤ ∏ i : Fin k, (K i.val (histPrefix i w) d (histOut i w)).toReal :=
    Finset.prod_le_prod₀ (fun i _ => mul_nonneg hm ENNReal.toReal_nonneg)
      (fun i _ => hstage i.val i.isLt _ _)
  calc m ^ k * ((R w.1).toReal
          * ∏ i : Fin k, (L i.val (histPrefix i w) e (histOut i w)).toReal)
      = (R w.1).toReal * ((∏ _i : Fin k, m)
          * ∏ i : Fin k, (L i.val (histPrefix i w) e (histOut i w)).toReal) := by
        rw [hpow]
        ring
    _ = (R w.1).toReal
          * ∏ i : Fin k, m * (L i.val (histPrefix i w) e (histOut i w)).toReal := by
        rw [Finset.prod_mul_distrib]
    _ ≤ (R w.1).toReal
          * ∏ i : Fin k, (K i.val (histPrefix i w) d (histOut i w)).toReal :=
        mul_le_mul_of_nonneg_left hle ENNReal.toReal_nonneg

open CSLibExt.Privacy.MaxDivergenceDecomposition

instance Hist.nonempty {C Y : Type*} [Nonempty C] [Nonempty Y] (k : ℕ) :
    Nonempty (Hist C Y k) := by
  obtain ⟨c⟩ := (inferInstance : Nonempty C)
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  refine ⟨?_⟩
  show C × (Fin k → Y)
  exact (c, fun _ => y)

private theorem isDP_bool_of_maxDivLE_both {Y : Type*} [Fintype Y] [Nonempty Y]
    (P Q : PMF Y) (eps : ℝ) (heps : 0 ≤ eps)
    (hPQ : maxDivLE P Q eps) (hQP : maxDivLE Q P eps) :
    IsDP (fun b : Bool => if b = false then P else Q) (fun b b' => b ≠ b') eps := by
  have hconv : ∀ A B : PMF Y, maxDivLE A B eps →
      ∀ o, A o ≤ ENNReal.ofReal (Real.exp eps) * B o := by
    intro A B h o
    have hAfin : A o ≠ ⊤ := (A.apply_ne_top o)
    have hBfin : B o ≠ ⊤ := (B.apply_ne_top o)
    conv_lhs => rw [← ENNReal.ofReal_toReal hAfin]
    rw [← ENNReal.ofReal_toReal hBfin, ← ENNReal.ofReal_mul (Real.exp_nonneg eps)]
    exact ENNReal.ofReal_le_ofReal (h o)
  refine ⟨heps, fun b b' hadj o => ?_⟩
  cases b <;> cases b'
  · exact (hadj rfl).elim
  · simpa using hconv P Q hPQ o
  · simpa using hconv Q P hQP o
  · exact (hadj rfl).elim

theorem transcript_approxMaxDivLE_advanced_composition_pair {C Y : Type*}
    [Fintype C] [Fintype Y] [Nonempty C] [Nonempty Y]
    (R : PMF C) (L : (n : ℕ) → Hist C Y n → Bool → PMF Y) (eps : ℝ) (k : ℕ)
    (delta' : ℝ) (heps : 0 ≤ eps)
    (hL : ∀ n h, maxDivLE (L n h false) (L n h true) eps ∧
      maxDivLE (L n h true) (L n h false) eps)
    (hdelta'pos : 0 < delta') (hdelta'lt : delta' < 1) :
    approxMaxDivLE (transcript R L k false) (transcript R L k true)
        (eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / delta')) +
          (k : ℝ) * (eps * (Real.exp eps - 1))) delta' ∧
      approxMaxDivLE (transcript R L k true) (transcript R L k false)
        (eps * Real.sqrt (2 * (k : ℝ) * Real.log (1 / delta')) +
          (k : ℝ) * (eps * (Real.exp eps - 1))) delta' := by
  have hK : ∀ (n : ℕ) (h : Hist C Y n),
      IsDP (fun d => L n h d) (fun b b' => b ≠ b') eps := by
    intro n h
    obtain ⟨h1, h2⟩ := hL n h
    have hfun : (fun b : Bool => if b = false then L n h false else L n h true) =
        fun d => L n h d := by
      funext b
      cases b <;> simp
    rw [← hfun]
    exact isDP_bool_of_maxDivLE_both (L n h false) (L n h true) eps heps h1 h2
  have hadj_symm : ∀ d d' : Bool, d ≠ d' → d' ≠ d := fun d d' h => Ne.symm h
  have hmain := transcript_isApproxDP_advanced_composition_pure R L
    (fun b b' => b ≠ b') eps k delta' hK heps hadj_symm hdelta'pos hdelta'lt
  constructor
  · exact approxMaxDivLE_of_isApproxDP hmain (by decide : false ≠ true)
  · exact approxMaxDivLE_of_isApproxDP hmain (by decide : true ≠ false)

end CSLibExt.Privacy.DifferentialPrivacy
