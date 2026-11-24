/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy
public import CSLibExt.Privacy.PrivacyLoss
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

end CSLibExt.Privacy.DifferentialPrivacy
