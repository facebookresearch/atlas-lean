/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.Compact

/-!
# Discrete key renewal theorem and the ladder-height limit for a score walk

Let `f` be the law of a strictly positive integer interarrival time (`f 0 = 0`,
`∑ f = 1`) and let `u` be its **renewal sequence**, `u 0 = 1`,
`u n = ∑_{k=1}^{n} f k * u (n - k)`; `u n` is the probability that some renewal epoch
equals `n`.

* **Erdős–Feller–Pollard** (`tendsto_renewalSeq`): if the support of `f` has gcd `1`
  and `f` has finite mean `μ`, then `u n → 1 / μ`.
* **Discrete key renewal theorem** (`tendsto_of_isRenewalSolution`): the solution of
  `Z n = z n + ∑_{k ≤ n} f k * Z (n - k)` with summable `z` satisfies
  `Z n → (∑ z) / μ`.
* **Exponentially tilted (defective) key renewal theorem**
  (`tendsto_exp_mul_of_isRenewalSolution`): if `g` is a possibly defective law with
  `∑ g k e^{θ k} = 1`, aperiodic support and finite tilted mean `μ_θ`, the solution of the
  `g`-renewal equation satisfies `e^{θ n} Z n → (∑ e^{θ k} z k) / μ_θ`.
* **Ladder-height limit for a negative-drift score walk**
  (`tendsto_exp_mul_maxTail`): for the maximum `M` of an i.i.d. integer score walk with
  negative drift, write `g j = P(τ₊ < ∞, S_{τ₊} = j)` for the (defective) law of the first
  strict ascending ladder height. If `T k = P(M > k)` satisfies the ladder decomposition
  `T k = P(τ₊ < ∞, S_{τ₊} > k) + ∑_{j ≤ k} g j * T (k - j)` and `θ > 0` is the Cramér
  root `∑ g j e^{θ j} = 1`, then
  `e^{θ k} P(M > k) → (1 - P(τ₊ < ∞)) / ((e^θ - 1) * ∑ j g j e^{θ j})`,
  the constant of the Cramér–Lundberg / Karlin–Dembo tail asymptotics (Feller, Vol. II,
  Chapters XI–XII; Karlin and Dembo 1992).

## Scope

The renewal theory (first three bullets) is proved from scratch. For the score walk, the
two probabilistic identities that link the walk to its ladder law are explicit hypotheses
of `tendsto_exp_mul_maxTail`: the ladder decomposition of `P(M > k)` (strong Markov
property at the defective ladder epoch `τ₊`) and the identity `∑ g j e^{θ j} = 1` for the
root `θ` of the score MGF (Wiener–Hopf / optional stopping of `e^{θ S_n}`). The excluded
boundary cases are explicit: a proper ladder law (nonnegative drift, `P(τ₊ < ∞) = 1`)
admits no positive Cramér root (`not_hasSum_exp_mul_of_hasSum_one`), and the Cramér root
forces a defective ladder law (`tsum_lt_one_of_hasSum_exp_mul`). The lattice
(non-aperiodic) case is not treated here.

## Relation to Mathlib

Mathlib and MathlibExt contain no renewal theorem (searched for `renewal` and `ladder`
in Mathlib, and `renewal`/`ladder` in MathlibExt: the only hits are the exponential
solutions of the Euler–Lotka renewal equation in `MathlibExt.Biology.Epidemiology.EulerLotka`,
which do not address convergence). The aperiodicity input uses Mathlib's
`Nat.exists_mem_closure_of_ge` (Frobenius / numerical-semigroup lemma), the
uniqueness of renewal solutions uses `PowerSeries` multiplication, and the limit passages use
`tendsto_tsum_of_dominated_convergence` and `continuousOn_tsum`.

## Proof of Erdős–Feller–Pollard

We follow Feller's elementary argument (Vol. I, Chapter XIII), recast with cluster points. The
windows `σ n = (u (n - j))_{j ≤ n}` (padded with `0`) live in the compact cube
`[0, 1]^ℕ`. Every cluster point `w` of `σ` is harmonic, `w j = ∑ f (k + 1) w (j + k + 1)`,
and the set of cluster points is closed under shifts. A cluster point maximizing `w 0`
attains its maximum `λ` on the additive closure of the support, hence (gcd `1`) on a
whole tail, so a shift of it is the constant `λ`. Passing the identity
`∑_{k ≤ n} P(T > k) u (n - k) = 1` to that limit gives `λ μ = 1`; symmetrically for the
minimum. So all cluster points equal `1 / μ`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Chapter XIII; Vol. II, 2nd ed., Chapters XI and XII.
* P. Erdős, W. Feller, H. Pollard, *A property of power series with positive coefficients*,
  Bull. AMS 55 (1949), 201–204.
* S. Karlin, A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
-/

@[expose] public section

open Filter Topology Finset

namespace MathlibExt.Probability.Renewal

/-- The **renewal sequence** of an interarrival law `f : ℕ → ℝ` (only `f 1, f 2, …` are
used): `u 0 = 1` and `u (n + 1) = ∑_{k = 0}^{n} f (k + 1) * u (n - k)`. When `f` is the law
of a strictly positive integer waiting time, `u n` is the probability that some renewal
epoch equals `n`. -/
noncomputable def renewalSeq (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ k ∈ Finset.range (n + 1), f (k + 1) * renewalSeq f (n - k)
decreasing_by omega

/-- `Z` solves the **discrete renewal equation** with interarrival weights `f` and forcing
`z`: `Z n = z n + ∑_{k = 0}^{n} f k * Z (n - k)` for every `n`. With `f 0 = 0` this is the
recursion `Z n = z n + ∑_{k = 1}^{n} f k * Z (n - k)`. -/
def IsRenewalSolution (f z Z : ℕ → ℝ) : Prop :=
  ∀ n, Z n = z n + ∑ k ∈ Finset.range (n + 1), f k * Z (n - k)

/-- The **ladder tail** `∑_{j > k} g j` of a (possibly defective) ladder-height law `g`.
For the first strict ascending ladder height of a random walk this is
`P(τ₊ < ∞, S_{τ₊} > k)`. -/
noncomputable def ladderTail (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' j, g (j + k + 1)

section RenewalSeq

variable {f : ℕ → ℝ}

@[simp] theorem renewalSeq_zero (f : ℕ → ℝ) : renewalSeq f 0 = 1 := by
  rw [renewalSeq]

theorem renewalSeq_succ (f : ℕ → ℝ) (n : ℕ) :
    renewalSeq f (n + 1) = ∑ k ∈ Finset.range (n + 1), f (k + 1) * renewalSeq f (n - k) := by
  rw [renewalSeq]

/-- The renewal sequence solves the renewal equation with forcing `δ₀`. -/
theorem isRenewalSolution_renewalSeq (hf0 : f 0 = 0) :
    IsRenewalSolution f (fun n => if n = 0 then 1 else 0) (renewalSeq f) := by
  intro n
  cases n with
  | zero => simp [hf0]
  | succ n =>
    rw [Finset.sum_range_succ', renewalSeq_succ]
    simp [hf0]

/-- The renewal sequence of a probability law on `{1, 2, …}` takes values in `[0, 1]`. -/
theorem renewalSeq_mem_Icc (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) (n : ℕ) :
    renewalSeq f n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hle : ∑ k ∈ Finset.range (n + 1), f (k + 1) ≤ 1 := by
        have h := sum_le_hasSum (Finset.range (n + 2)) (fun i _ => hf i) hsum
        rw [Finset.sum_range_succ'] at h
        linarith [hf 0]
      rw [renewalSeq_succ]
      refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (hf _) (ih _ (by omega)).1, ?_⟩
      calc ∑ k ∈ Finset.range (n + 1), f (k + 1) * renewalSeq f (n - k)
          ≤ ∑ k ∈ Finset.range (n + 1), f (k + 1) :=
            Finset.sum_le_sum fun k _ =>
              mul_le_of_le_one_right (hf _) (ih _ (by omega)).2
        _ ≤ 1 := hle

end RenewalSeq

/-! ### Tail masses and the mean -/

section Tail

variable {f : ℕ → ℝ}

/-- `1 - ∑_{j ≤ k} f j`, i.e. `P(T > k)`. -/
private noncomputable def tailMass (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  1 - ∑ j ∈ Finset.range (k + 1), f j

private lemma tailMass_succ (f : ℕ → ℝ) (k : ℕ) :
    tailMass f (k + 1) = tailMass f k - f (k + 1) := by
  simp only [tailMass, Finset.sum_range_succ _ (k + 1)]
  ring

private lemma tailMass_eq_tsum (hsum : HasSum f 1) (k : ℕ) :
    tailMass f k = ∑' j, f (j + (k + 1)) := by
  have h := hsum.summable.sum_add_tsum_nat_add (k + 1)
  rw [hsum.tsum_eq] at h
  simp only [tailMass]
  linarith

private lemma tailMass_nonneg (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) (k : ℕ) :
    0 ≤ tailMass f k := by
  rw [tailMass_eq_tsum hsum]
  exact tsum_nonneg fun j => hf _

/-- `∑_{k ≤ n} P(T > k) u (n - k) = 1`: the last renewal epoch before `n` exists. -/
private lemma sum_tailMass_mul_renewalSeq (hf0 : f 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), tailMass f k * renewalSeq f (n - k) = 1 := by
  induction n with
  | zero => simp [tailMass, hf0]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [tailMass_succ, sub_mul, Finset.sum_sub_distrib, Nat.add_sub_add_right]
    rw [ih, ← renewalSeq_succ]
    simp [tailMass, hf0]

/-- Partial sums of the tail masses: `∑_{k < N} P(T > k) = ∑_{j ≤ N} j f j + N P(T > N)`. -/
private lemma sum_range_tailMass (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, tailMass f k =
      ∑ j ∈ Finset.range (N + 1), (j : ℝ) * f j + N * tailMass f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (N + 1), tailMass_succ]
    push_cast
    ring

/-- With finite mean `μ = ∑ k f k`, the tail masses sum to `μ`. -/
private lemma hasSum_tailMass (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) {μ : ℝ}
    (hmean : HasSum (fun k : ℕ => (k : ℝ) * f k) μ) : HasSum (tailMass f) μ := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (tailMass_nonneg hf hsum)]
  have hlow : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), (j : ℝ) * f j) atTop (𝓝 μ) :=
    hmean.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_)
    (fun N => ?_)
  · rw [sum_range_tailMass]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (tailMass_nonneg hf hsum N))
  · rw [sum_range_tailMass]
    have hshift := (hasSum_nat_add_iff' (N + 1)).2 hmean
    have hle : (N : ℝ) * tailMass f N ≤ ∑' j, ((j + (N + 1) : ℕ) : ℝ) * f (j + (N + 1)) := by
      have hs : Summable fun j => f (j + (N + 1)) :=
        (summable_nat_add_iff (N + 1)).2 hsum.summable
      rw [tailMass_eq_tsum hsum, ← hs.tsum_mul_left]
      refine hs.mul_left _ |>.tsum_le_tsum (fun j => ?_) hshift.summable
      exact mul_le_mul_of_nonneg_right (by push_cast; linarith) (hf _)
    rw [hshift.tsum_eq] at hle
    linarith

end Tail

/-! ### Erdős–Feller–Pollard via cluster points of the windows -/

section EFP

variable {f : ℕ → ℝ}

/-- The window `(u (n - j))_{j ≤ n}`, padded with `0`. -/
private def window (u : ℕ → ℝ) (n : ℕ) : ℕ → ℝ := fun j => if j ≤ n then u (n - j) else 0

/-- The cube `[0, 1]^ℕ`. -/
private def cube : Set (ℕ → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

private lemma isCompact_cube : IsCompact cube := isCompact_univ_pi fun _ => isCompact_Icc

private lemma isClosed_cube : IsClosed cube := isClosed_set_pi fun _ _ => isClosed_Icc

private lemma window_mem_cube (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) (n : ℕ) :
    window (renewalSeq f) n ∈ cube := by
  intro j _
  simp only [window]
  split_ifs
  · exact renewalSeq_mem_Icc hf hsum _
  · exact ⟨le_rfl, zero_le_one⟩

/-- The cluster points of the windows. -/
private def clusterSet (f : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {w | MapClusterPt w atTop (window (renewalSeq f))}

private lemma window_mem_map (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) :
    cube ∈ map (window (renewalSeq f)) atTop :=
  Filter.mem_map.2 (Filter.univ_mem' fun n => window_mem_cube hf hsum n)

private lemma clusterSet_subset_cube (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) :
    clusterSet f ⊆ cube := fun _ hw =>
  isClosed_cube.closure_subset (ClusterPt.mem_closure_of_mem hw _ (window_mem_map hf hsum))

private lemma isCompact_clusterSet (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) :
    IsCompact (clusterSet f) :=
  isCompact_cube.of_isClosed_subset isClosed_setOfPred_clusterPt
    (clusterSet_subset_cube hf hsum)

private lemma clusterSet_nonempty (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1) :
    (clusterSet f).Nonempty := by
  obtain ⟨w, -, hw⟩ := isCompact_cube.exists_clusterPt
    (f := map (window (renewalSeq f)) atTop) (le_principal_iff.2 (window_mem_map hf hsum))
  exact ⟨w, hw⟩

private lemma shift_mem_clusterSet {w : ℕ → ℝ} (hw : w ∈ clusterSet f) (a : ℕ) :
    (fun j => w (j + a)) ∈ clusterSet f := by
  have hc : Continuous fun x : ℕ → ℝ => fun j => x (j + a) :=
    continuous_pi fun j => continuous_apply _
  have h1 := MapClusterPt.tendsto_comp (hc.tendsto w) hw
  have heq : (fun x : ℕ → ℝ => fun j => x (j + a)) ∘ window (renewalSeq f) =ᶠ[atTop]
      window (renewalSeq f) ∘ fun n => n - a := by
    filter_upwards [eventually_ge_atTop a] with n hn
    funext j
    simp only [Function.comp, window]
    split_ifs with h₁ h₂ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  have h2 : ClusterPt (fun j => w (j + a))
      (map (window (renewalSeq f)) (map (fun n => n - a) atTop)) := by
    rw [Filter.map_map, ← Filter.map_congr heq]
    exact h1
  exact h2.mono (map_mono (tendsto_sub_atTop_nat a))

private lemma harmonic_of_mem_clusterSet (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1)
    {w : ℕ → ℝ} (hw : w ∈ clusterSet f) (j : ℕ) :
    w j = ∑' k, f (k + 1) * w (j + k + 1) := by
  set φ : (ℕ → ℝ) → ℝ := fun x => x j - ∑' k, f (k + 1) * x (j + k + 1) with hφdef
  have hs : Summable fun k => f (k + 1) := (summable_nat_add_iff 1).2 hsum.summable
  have hφ : ContinuousOn φ cube := by
    refine (continuous_apply j).continuousOn.sub (continuousOn_tsum
      (fun k => (continuous_const.mul (continuous_apply _)).continuousOn) hs ?_)
    intro k x hx
    have hx' := hx (j + k + 1) (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf _), abs_of_nonneg hx'.1]
    exact mul_le_of_le_one_right (hf _) hx'.2
  have hclosed : IsClosed (cube ∩ φ ⁻¹' {0}) :=
    hφ.preimage_isClosed_of_isClosed isClosed_cube isClosed_singleton
  have hmem : cube ∩ φ ⁻¹' {0} ∈ map (window (renewalSeq f)) atTop := by
    rw [Filter.mem_map]
    filter_upwards [eventually_ge_atTop (j + 1)] with n hn
    refine ⟨window_mem_cube hf hsum n, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hφdef, sub_eq_zero]
    obtain ⟨m, rfl⟩ : ∃ m, n = j + m + 1 := ⟨n - j - 1, by omega⟩
    rw [tsum_eq_sum (s := Finset.range (m + 1))]
    · simp only [window]
      rw [ite_eq_left (by omega), show j + m + 1 - j = m + 1 by omega, renewalSeq_succ]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [ite_eq_left (by omega)]
      congr 2
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      simp only [window]
      rw [ite_eq_right (by omega), mul_zero]
  have h := hclosed.closure_subset (ClusterPt.mem_closure_of_mem hw _ hmem)
  simpa [hφdef, sub_eq_zero] using h.2

private lemma tsum_tailMass_mul_of_mem_clusterSet (hf0 : f 0 = 0) (hf : ∀ k, 0 ≤ f k)
    (hsum : HasSum f 1) {μ : ℝ} (hmean : HasSum (fun k : ℕ => (k : ℝ) * f k) μ)
    {w : ℕ → ℝ} (hw : w ∈ clusterSet f) :
    ∑' k, tailMass f k * w k = 1 := by
  have hr := hasSum_tailMass hf hsum hmean
  set φ : (ℕ → ℝ) → ℝ := fun x => ∑' k, tailMass f k * x k with hφdef
  have hφ : ContinuousOn φ cube := by
    refine continuousOn_tsum (fun k => (continuous_const.mul (continuous_apply k)).continuousOn)
      hr.summable ?_
    intro k x hx
    have hx' := hx k (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tailMass_nonneg hf hsum k),
      abs_of_nonneg hx'.1]
    exact mul_le_of_le_one_right (tailMass_nonneg hf hsum k) hx'.2
  have hclosed : IsClosed (cube ∩ φ ⁻¹' {1}) :=
    hφ.preimage_isClosed_of_isClosed isClosed_cube isClosed_singleton
  have hmem : cube ∩ φ ⁻¹' {1} ∈ map (window (renewalSeq f)) atTop := by
    rw [Filter.mem_map]
    refine Filter.univ_mem' fun n => ⟨window_mem_cube hf hsum n, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hφdef]
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · rw [← sum_tailMass_mul_renewalSeq hf0 n]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [window, ite_eq_left (show k ≤ n by omega)]
    · intro k hk
      rw [Finset.mem_range] at hk
      simp only [window, ite_eq_right (show ¬ k ≤ n by omega), mul_zero]
  exact (hclosed.closure_subset (ClusterPt.mem_closure_of_mem hw _ hmem)).2

/-- Maximum propagation for a shift-invariant family of bounded harmonic sequences: if
`s * w ≤ s * c` on the family and `w 0 = c`, then `w a = c` on the additive closure of the
support of `f`. -/
private lemma propagate (hf0 : f 0 = 0) (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1)
    (W : Set (ℕ → ℝ)) (hshift : ∀ w ∈ W, ∀ a, (fun j => w (j + a)) ∈ W)
    (hharm : ∀ w ∈ W, w 0 = ∑' k, f (k + 1) * w (0 + k + 1))
    (hbdd : ∀ w ∈ W, ∀ j, w j ∈ Set.Icc (0 : ℝ) 1)
    (s c : ℝ) (hs : s ≠ 0) (hc : ∀ w ∈ W, ∀ j, s * w j ≤ s * c) :
    ∀ a ∈ AddSubmonoid.closure {k | 0 < f k}, ∀ w ∈ W, w 0 = c → w a = c := by
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem k hk =>
    intro w hw hw0
    by_contra hne
    have hk' : 0 < f k := hk
    have hk0 : k ≠ 0 := by rintro rfl; simp [hf0] at hk'
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hlt : s * w (m + 1) < s * c :=
      lt_of_le_of_ne (hc w hw _) fun h => hne (mul_left_cancel₀ hs h)
    have hsf : Summable fun i => f (i + 1) := (summable_nat_add_iff 1).2 hsum.summable
    have hsum1 : ∑' i, f (i + 1) = 1 := by
      have h := hsum.summable.tsum_eq_zero_add
      rw [hsum.tsum_eq, hf0, zero_add] at h
      exact h.symm
    have hsw : Summable fun i => f (i + 1) * (s * w (0 + i + 1)) := by
      refine Summable.of_norm_bounded (hsf.mul_left |s|) fun i => ?_
      have hb := hbdd w hw (0 + i + 1)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hf _), abs_of_nonneg hb.1]
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg s) (hf (i + 1))) (sub_nonneg.2 hb.2)]
    have key : ∑' i, f (i + 1) * (s * w (0 + i + 1)) < ∑' i, f (i + 1) * (s * c) := by
      refine Summable.tsum_lt_tsum (i := m)
        (fun i => mul_le_mul_of_nonneg_left (hc w hw _) (hf _)) ?_ hsw (hsf.mul_right _)
      simpa using mul_lt_mul_of_pos_left hlt hk'
    rw [hsf.tsum_mul_right, hsum1, one_mul] at key
    have hl : ∑' i, f (i + 1) * (s * w (0 + i + 1)) = s * w 0 := by
      rw [hharm w hw, ← tsum_mul_left]
      congr 1
      funext i
      ring
    rw [hl, hw0] at key
    exact lt_irrefl _ key
  | zero => intro w _ hw0; exact hw0
  | add a b _ _ iha ihb =>
    intro w hw hw0
    have h1 := iha w hw hw0
    have h2 := ihb _ (hshift w hw a) (by simpa using h1)
    simpa [add_comm] using h2

/-- **Erdős–Feller–Pollard renewal theorem.** Let `f` be the law of a strictly positive
integer waiting time with aperiodic support (`gcd {k | f k > 0} = 1`) and finite mean `μ`.
Then the renewal sequence converges to `1 / μ`. -/
theorem tendsto_renewalSeq (hf0 : f 0 = 0) (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1)
    (haper : Nat.setGcd {k | 0 < f k} = 1) {μ : ℝ}
    (hmean : HasSum (fun k : ℕ => (k : ℝ) * f k) μ) :
    Tendsto (renewalSeq f) atTop (𝓝 μ⁻¹) := by
  set W := clusterSet f with hWdef
  have hWc := isCompact_clusterSet hf hsum
  have hWne := clusterSet_nonempty hf hsum
  have hbdd : ∀ w ∈ W, ∀ j, w j ∈ Set.Icc (0 : ℝ) 1 := fun w hw j =>
    clusterSet_subset_cube hf hsum hw j (Set.mem_univ _)
  have hshift : ∀ w ∈ W, ∀ a, (fun j => w (j + a)) ∈ W := fun w hw a =>
    shift_mem_clusterSet hw a
  have hharm : ∀ w ∈ W, w 0 = ∑' k, f (k + 1) * w (0 + k + 1) := fun w hw =>
    harmonic_of_mem_clusterSet hf hsum hw 0
  obtain ⟨N0, hN0⟩ := Nat.exists_mem_closure_of_ge {k | 0 < f k}
  have hcl : ∀ j, j + N0 ∈ AddSubmonoid.closure {k | 0 < f k} := fun j =>
    hN0 _ (by omega) (by rw [haper]; exact one_dvd _)
  have hcont : ContinuousOn (fun w : ℕ → ℝ => w 0) W := (continuous_apply 0).continuousOn
  obtain ⟨wM, hwM, hmax⟩ := hWc.exists_isMaxOn hWne hcont
  obtain ⟨wm, hwm, hmin⟩ := hWc.exists_isMinOn hWne hcont
  have hle : ∀ w ∈ W, ∀ j, w j ≤ wM 0 := fun w hw j => by
    simpa using isMaxOn_iff.1 hmax _ (hshift w hw j)
  have hge : ∀ w ∈ W, ∀ j, wm 0 ≤ w j := fun w hw j => by
    simpa using isMinOn_iff.1 hmin _ (hshift w hw j)
  have hconstM : ∀ j, wM (j + N0) = wM 0 := fun j =>
    propagate hf0 hf hsum W hshift hharm hbdd 1 (wM 0) one_ne_zero (by simpa using hle) _
      (hcl j) wM hwM rfl
  have hconstm : ∀ j, wm (j + N0) = wm 0 := fun j =>
    propagate hf0 hf hsum W hshift hharm hbdd (-1) (wm 0) (by norm_num)
      (fun w hw j => by have := hge w hw j; linarith) _ (hcl j) wm hwm rfl
  have hr := hasSum_tailMass hf hsum hmean
  have hM : μ * wM 0 = 1 := by
    have h := tsum_tailMass_mul_of_mem_clusterSet hf0 hf hsum hmean (hshift wM hwM N0)
    simp only [hconstM] at h
    rwa [hr.summable.tsum_mul_right, hr.tsum_eq] at h
  have hm : μ * wm 0 = 1 := by
    have h := tsum_tailMass_mul_of_mem_clusterSet hf0 hf hsum hmean (hshift wm hwm N0)
    simp only [hconstm] at h
    rwa [hr.summable.tsum_mul_right, hr.tsum_eq] at h
  have hMv : wM 0 = μ⁻¹ := eq_inv_of_mul_eq_one_right hM
  have hmv : wm 0 = μ⁻¹ := eq_inv_of_mul_eq_one_right hm
  have hσ : Tendsto (window (renewalSeq f)) atTop (𝓝 fun _ => μ⁻¹) := by
    refine isCompact_cube.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall (window_mem_cube hf hsum)) fun w _ hw => ?_
    funext j
    exact le_antisymm (hMv ▸ hle w hw j) (hmv ▸ hge w hw j)
  have h0 : Tendsto (fun n => window (renewalSeq f) n 0) atTop (𝓝 μ⁻¹) :=
    ((continuous_apply 0).tendsto _).comp hσ
  refine h0.congr fun n => ?_
  simp [window]

end EFP

/-! ### The key renewal theorem -/

section KeyRenewal

variable {f : ℕ → ℝ}

private lemma isRenewalSolution_iff_mk (f z Z : ℕ → ℝ) :
    IsRenewalSolution f z Z ↔
      PowerSeries.mk Z = PowerSeries.mk z + PowerSeries.mk f * PowerSeries.mk Z := by
  constructor
  · intro h
    ext n
    rw [map_add, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (PowerSeries.mk f) * PowerSeries.coeff b (PowerSeries.mk Z))]
    simpa using h n
  · intro h n
    have h' := congrArg (PowerSeries.coeff n) h
    rw [map_add, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (PowerSeries.mk f) * PowerSeries.coeff b (PowerSeries.mk Z))]
      at h'
    simpa using h'

/-- Every solution of the renewal equation is the convolution of the forcing with the
renewal sequence: `Z n = ∑_{k ≤ n} z k * u (n - k)`. -/
theorem IsRenewalSolution.eq_sum_renewalSeq (hf0 : f 0 = 0) {z Z : ℕ → ℝ}
    (hZ : IsRenewalSolution f z Z) (n : ℕ) :
    Z n = ∑ k ∈ Finset.range (n + 1), z k * renewalSeq f (n - k) := by
  set F := PowerSeries.mk f
  set U := PowerSeries.mk (renewalSeq f)
  have hU : U = 1 + F * U := by
    have h := (isRenewalSolution_iff_mk _ _ _).1 (isRenewalSolution_renewalSeq hf0)
    convert h using 2
    ext n
    simp [PowerSeries.coeff_one]
  have hZ' := (isRenewalSolution_iff_mk _ _ _).1 hZ
  have key : PowerSeries.mk Z = PowerSeries.mk z * U := by
    have h1 : U - F * U = 1 := sub_eq_iff_eq_add.2 hU
    have h2 : PowerSeries.mk Z - F * PowerSeries.mk Z = PowerSeries.mk z :=
      sub_eq_iff_eq_add.2 hZ'
    calc PowerSeries.mk Z = PowerSeries.mk Z * (U - F * U) := by rw [h1, mul_one]
      _ = (PowerSeries.mk Z - F * PowerSeries.mk Z) * U := by ring
      _ = PowerSeries.mk z * U := by rw [h2]
  have h := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (PowerSeries.mk z) * PowerSeries.coeff b U)] at h
  simpa [U] using h

/-- **Discrete key renewal theorem.** For an aperiodic interarrival law `f` on `{1, 2, …}`
with finite mean `μ` and a summable forcing `z`, every solution of the renewal equation
`Z n = z n + ∑_{k ≤ n} f k * Z (n - k)` converges to `(∑ z) / μ`. -/
theorem tendsto_of_isRenewalSolution (hf0 : f 0 = 0) (hf : ∀ k, 0 ≤ f k) (hsum : HasSum f 1)
    (haper : Nat.setGcd {k | 0 < f k} = 1) {μ : ℝ}
    (hmean : HasSum (fun k : ℕ => (k : ℝ) * f k) μ) {z Z : ℕ → ℝ} (hz : Summable z)
    (hZ : IsRenewalSolution f z Z) :
    Tendsto Z atTop (𝓝 ((∑' k, z k) / μ)) := by
  have hu := tendsto_renewalSeq hf0 hf hsum haper hmean
  have hconv : ∀ n, Z n = ∑' k, (if k ≤ n then z k * renewalSeq f (n - k) else 0) := by
    intro n
    rw [hZ.eq_sum_renewalSeq hf0 n, tsum_eq_sum (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [ite_eq_left (by omega)]
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [ite_eq_right (by omega)]
  rw [show (∑' k, z k) / μ = ∑' k, z k * μ⁻¹ by rw [tsum_mul_right, div_eq_mul_inv]]
  rw [show Z = fun n => ∑' k, (if k ≤ n then z k * renewalSeq f (n - k) else 0) from
    funext hconv]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖z k‖)
    (by simpa [Real.norm_eq_abs] using hz.abs)
    (fun k => ?_) (Filter.Eventually.of_forall fun n k => ?_)
  · have hk : Tendsto (fun n => z k * renewalSeq f (n - k)) atTop (𝓝 (z k * μ⁻¹)) :=
      (hu.comp (tendsto_sub_atTop_nat k)).const_mul _
    refine hk.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [ite_eq_left hn]
  · split_ifs
    · rw [norm_mul]
      have hb := renewalSeq_mem_Icc hf hsum (n - k)
      rw [Real.norm_of_nonneg hb.1]
      exact mul_le_of_le_one_right (norm_nonneg _) hb.2
    · simp

/-- **Exponentially tilted key renewal theorem** for a possibly defective law `g`. If
`∑ g k e^{θ k} = 1`, the tilted law `g k e^{θ k}` is aperiodic with finite mean `μ`, and
`e^{θ k} z k` is summable, then every solution of the `g`-renewal equation satisfies
`e^{θ n} Z n → (∑ e^{θ k} z k) / μ`. -/
theorem tendsto_exp_mul_of_isRenewalSolution {g z Z : ℕ → ℝ} {θ μ : ℝ} (hg0 : g 0 = 0)
    (hg : ∀ k, 0 ≤ g k) (hcramer : HasSum (fun k : ℕ => g k * Real.exp (θ * k)) 1)
    (haper : Nat.setGcd {k | 0 < g k} = 1)
    (hmean : HasSum (fun k : ℕ => (k : ℝ) * (g k * Real.exp (θ * k))) μ)
    (hz : Summable fun k : ℕ => Real.exp (θ * k) * z k) (hZ : IsRenewalSolution g z Z) :
    Tendsto (fun n : ℕ => Real.exp (θ * n) * Z n) atTop
      (𝓝 ((∑' k : ℕ, Real.exp (θ * k) * z k) / μ)) := by
  refine tendsto_of_isRenewalSolution (f := fun k => g k * Real.exp (θ * k)) (by simp [hg0])
    (fun k => mul_nonneg (hg k) (Real.exp_pos _).le) hcramer ?_ hmean hz ?_
  · have hset : {k : ℕ | 0 < g k * Real.exp (θ * k)} = {k | 0 < g k} := by
      ext k
      exact mul_pos_iff_of_pos_right (Real.exp_pos _)
    change Nat.setGcd {k : ℕ | 0 < g k * Real.exp (θ * k)} = 1
    rw [hset, haper]
  · intro n
    simp only
    rw [hZ n, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [Nat.cast_sub (by omega), mul_sub, Real.exp_sub]
    field_simp

end KeyRenewal

/-! ### The ladder-height limit for a negative-drift score walk -/

section ScoreLadder

variable {g : ℕ → ℝ} {θ : ℝ}

private lemma summable_of_hasSum_exp_mul (hθ : 0 < θ) (hg : ∀ k, 0 ≤ g k)
    (hcramer : HasSum (fun k : ℕ => g k * Real.exp (θ * k)) 1) : Summable g :=
  Summable.of_nonneg_of_le hg
    (fun k => le_mul_of_one_le_right (hg k) (Real.one_le_exp (mul_nonneg hθ.le k.cast_nonneg)))
    hcramer.summable

/-- **The Cramér root forces a defective ladder law** (negative drift): if
`∑ g k e^{θ k} = 1` with `θ > 0`, then `∑ g k < 1`, i.e. `P(τ₊ < ∞) < 1`. -/
theorem tsum_lt_one_of_hasSum_exp_mul (hθ : 0 < θ) (hg0 : g 0 = 0) (hg : ∀ k, 0 ≤ g k)
    (hcramer : HasSum (fun k : ℕ => g k * Real.exp (θ * k)) 1) : ∑' k, g k < 1 := by
  have hgs := summable_of_hasSum_exp_mul hθ hg hcramer
  obtain ⟨k, hk⟩ : ∃ k, 0 < g k := by
    by_contra h
    push Not at h
    have h0 : ∀ k, g k = 0 := fun k => le_antisymm (h k) (hg k)
    have h1 := hcramer.tsum_eq
    simp [h0] at h1
  have hk0 : k ≠ 0 := by rintro rfl; simp [hg0] at hk
  rw [← hcramer.tsum_eq]
  refine hgs.tsum_lt_tsum (i := k)
    (fun j => le_mul_of_one_le_right (hg j) (Real.one_le_exp (mul_nonneg hθ.le j.cast_nonneg)))
    ?_ hcramer.summable
  exact lt_mul_of_one_lt_right hk
    (Real.one_lt_exp_iff.2 (mul_pos hθ (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk0))))

/-- **Nonnegative drift is excluded**: a proper ladder law (`∑ g = 1`, i.e.
`P(τ₊ < ∞) = 1`) admits no positive Cramér root. -/
theorem not_hasSum_exp_mul_of_hasSum_one (hθ : 0 < θ) (hg0 : g 0 = 0) (hg : ∀ k, 0 ≤ g k)
    (hproper : HasSum g 1) : ¬ HasSum (fun k : ℕ => g k * Real.exp (θ * k)) 1 := by
  intro hcramer
  have h := tsum_lt_one_of_hasSum_exp_mul hθ hg0 hg hcramer
  rw [hproper.tsum_eq] at h
  exact lt_irrefl _ h

/-- The exponentially weighted ladder tails sum in closed form:
`∑_k e^{θ k} P(τ₊ < ∞, S_{τ₊} > k) = (1 - P(τ₊ < ∞)) / (e^θ - 1)` at the Cramér root. -/
theorem hasSum_exp_mul_ladderTail (hθ : 0 < θ) (hg : ∀ k, 0 ≤ g k)
    (hcramer : HasSum (fun k : ℕ => g k * Real.exp (θ * k)) 1) :
    HasSum (fun k : ℕ => Real.exp (θ * k) * ladderTail g k)
      ((1 - ∑' k, g k) / (Real.exp θ - 1)) := by
  have hgs := summable_of_hasSum_exp_mul hθ hg hcramer
  set Q : ℕ → ℝ := fun n => ∑' j, g (j + n) with hQdef
  have hQ : ∀ n, Q n = g n + Q (n + 1) := by
    intro n
    have h := ((summable_nat_add_iff n).2 hgs).tsum_eq_zero_add
    simp only [hQdef, h, zero_add]
    congr 1
    exact tsum_congr fun j => by rw [show j + 1 + n = j + (n + 1) by omega]
  have hQnn : ∀ n, 0 ≤ Q n := fun n => tsum_nonneg fun j => hg _
  have htail : ∀ k, ladderTail g k = Q (k + 1) := fun k => rfl
  have hE : 0 < Real.exp θ - 1 := by linarith [Real.add_one_lt_exp hθ.ne']
  have hid : ∀ N, (Real.exp θ - 1) * ∑ k ∈ Finset.range N, Real.exp (θ * k) * Q (k + 1) =
      ∑ k ∈ Finset.range (N + 1), g k * Real.exp (θ * k) + Real.exp (θ * N) * Q (N + 1) - Q 0 := by
    intro N
    induction N with
    | zero =>
      rw [hQ 0]
      simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (N + 1), hQ (N + 1)]
      push_cast
      rw [show θ * ((N : ℝ) + 1) = θ * N + θ by ring, Real.exp_add]
      ring
  have h1 : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), g k * Real.exp (θ * k)) atTop (𝓝 1) :=
    hcramer.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N : ℕ => Real.exp (θ * N) * Q (N + 1)) atTop (𝓝 0) := by
    have htl := (tendsto_sum_nat_add fun k : ℕ => g k * Real.exp (θ * k)).comp
      (tendsto_add_atTop_nat 1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htl
      (fun N => mul_nonneg (Real.exp_pos _).le (hQnn _)) fun N => ?_
    have hs : Summable fun j => g (j + (N + 1)) := (summable_nat_add_iff (N + 1)).2 hgs
    simp only [Function.comp, hQdef]
    rw [← hs.tsum_mul_left]
    refine (hs.mul_left _).tsum_le_tsum (fun j => ?_)
      ((summable_nat_add_iff (N + 1)).2 hcramer.summable)
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hg _)
    push_cast
    nlinarith [j.cast_nonneg (α := ℝ)]
  rw [show (fun k : ℕ => Real.exp (θ * k) * ladderTail g k) =
      fun k : ℕ => Real.exp (θ * k) * Q (k + 1) from funext fun k => by rw [htail],
    hasSum_iff_tendsto_nat_of_nonneg (fun k => mul_nonneg (Real.exp_pos _).le (hQnn _))]
  have hQ0 : Q 0 = ∑' k, g k := by simp [hQdef]
  have hlim := ((h1.add h2).sub_const (Q 0)).div_const (Real.exp θ - 1)
  rw [add_zero, hQ0] at hlim
  refine hlim.congr fun N => ?_
  rw [← hQ0, ← hid N]
  field_simp

/-- **Ladder-height (Cramér–Lundberg / Karlin–Dembo) limit for a negative-drift score
walk.** Let `g j = P(τ₊ < ∞, S_{τ₊} = j)` be the defective law of the first strict ascending
ladder height of an i.i.d. integer score walk with negative drift, and `T k = P(M > k)` the
tail of its maximum `M = sup_n S_n`. Assume (explicit probabilistic inputs)

* the ladder decomposition `T k = P(τ₊ < ∞, S_{τ₊} > k) + ∑_{j ≤ k} g j * T (k - j)`,
  i.e. `IsRenewalSolution g (ladderTail g) T`;
* the Cramér root `θ > 0`: `∑ g j e^{θ j} = 1`;
* finite tilted ladder mean `μ = ∑ j g j e^{θ j}` and aperiodic ladder support.

Then `e^{θ k} P(M > k) → (1 - P(τ₊ < ∞)) / ((e^θ - 1) μ)`. -/
theorem tendsto_exp_mul_maxTail {T : ℕ → ℝ} {μ : ℝ} (hθ : 0 < θ) (hg0 : g 0 = 0)
    (hg : ∀ k, 0 ≤ g k) (hcramer : HasSum (fun k : ℕ => g k * Real.exp (θ * k)) 1)
    (haper : Nat.setGcd {k | 0 < g k} = 1)
    (hmean : HasSum (fun k : ℕ => (k : ℝ) * (g k * Real.exp (θ * k))) μ)
    (hladder : IsRenewalSolution g (ladderTail g) T) :
    Tendsto (fun k : ℕ => Real.exp (θ * k) * T k) atTop
      (𝓝 ((1 - ∑' k, g k) / ((Real.exp θ - 1) * μ))) := by
  have h := hasSum_exp_mul_ladderTail hθ hg hcramer
  have hlim := tendsto_exp_mul_of_isRenewalSolution hg0 hg hcramer haper hmean h.summable hladder
  rwa [h.tsum_eq, div_div] at hlim

end ScoreLadder

end MathlibExt.Probability.Renewal
