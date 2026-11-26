/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GenericChainingGaussian
import MathlibExt.Probability.SudakovMinoration
import MathlibExt.Probability.GaussianLipschitzConcentration
import MathlibExt.Probability.Statistics.MultivariateCLT
import Mathlib.Analysis.Convex.Integral
import Mathlib.Data.Nat.Log

/-!
# The majorizing measure theorem

For a centred Gaussian process `(X_t)_{t ∈ T}` with its canonical distance
`d(s, t) = (E(X_s - X_t)²)^{1/2}`, the generic chaining bound `E sup_t X_t ≤ L γ₂(T, d)`
(`MathlibExt.Probability.GenericChaining.integral_iSup_le_gammaTwo`; for Gaussian processes
`integral_iSup_le_gammaTwo_canonicalDist`, stated with the canonical distance
`MathlibExt.Probability.GenericChaining.canonicalDist` used below) can be reversed: Fernique and
Talagrand's majorizing measure theorem says `γ₂(T, d) / L ≤ E sup_t X_t ≤ L γ₂(T, d)`. The lower
bound rests on Sudakov's minoration. The theorem is stated for a finite index set, which is the
setting of the source (its (2.2) defines the supremum over an infinite set through finite subsets).

A Gaussian process is encoded by its law on `T → ℝ`, which must be a Gaussian measure
(`ProbabilityTheory.IsGaussian`: every continuous linear functional has a Gaussian image law), and
"centred" by `E X_t = 0` (the source's convention, its (2.1)).

## Proof outline

Represent the process by a finite family of linear forms of a standard Gaussian vector.
Sudakov minoration and concentration give a growth estimate for the expected maximum on
separated clusters. A greedy sequence of partitions uses this estimate at each scale. Coding
the ranks of the children gives the required admissible cardinalities, and a telescoping sum
bounds the chaining cost. The upper bound applies generic chaining to the set of distinct
linear forms, which preserves the maximum and the partition functional.

## References

* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes: Decomposition Theorems*,
  2nd ed., Ergebnisse 60, Springer 2021, Theorem 2.10.1 and Lemma 2.10.2.
-/

namespace MathlibExt.Probability.MajorizingMeasureWanted

open MeasureTheory ProbabilityTheory Set Metric Finset GenericChaining
open scoped ENNReal NNReal InnerProductSpace

section AdmissiblePartitions

variable {T : Type*} [PseudoMetricSpace T] [Finite T] [Nonempty T]

/-- The center is chosen to maximize the value on a small ball in the unassigned set. -/
private noncomputable def chooseCenter (F : Set T → ℝ) (δ : ℝ) (A : Set T) : T := by
  classical
  exact if h : A.Nonempty then
    ((Set.toFinite A).toFinset.exists_max_image (fun x => F (A ∩ closedBall x δ))
      ((Set.toFinite A).toFinset_nonempty.mpr h)).choose
  else Classical.choice ‹Nonempty T›

private lemma chooseCenter_spec (F : Set T → ℝ) (δ : ℝ) {A : Set T} (h : A.Nonempty) :
    chooseCenter F δ A ∈ A ∧
      ∀ x ∈ A, F (A ∩ closedBall x δ) ≤ F (A ∩ closedBall (chooseCenter F δ A) δ) := by
  classical
  rw [chooseCenter, dite_eq_left h]
  simpa only [Set.Finite.mem_toFinset] using
    ((Set.toFinite A).toFinset.exists_max_image (fun x => F (A ∩ closedBall x δ))
      ((Set.toFinite A).toFinset_nonempty.mpr h)).choose_spec

private noncomputable def unassigned (F : Set T → ℝ) (r δ : ℝ) (A : Set T) :
    ℕ → Set T
  | 0 => A
  | i + 1 =>
    let B := unassigned F r δ A i
    B \ closedBall (chooseCenter F δ B) r

private lemma unassigned_antitone (F : Set T → ℝ) (r δ : ℝ) (A : Set T) :
    Antitone (unassigned F r δ A) :=
  antitone_nat_of_succ_le fun _ => Set.sdiff_subset

private lemma unassigned_subset (F : Set T → ℝ) (r δ : ℝ) (A : Set T) (i : ℕ) :
    unassigned F r δ A i ⊆ A :=
  unassigned_antitone F r δ A (Nat.zero_le i)

private lemma unassigned_ncard_lt (F : Set T → ℝ) {r : ℝ} (hr : 0 ≤ r) (δ : ℝ)
    (A : Set T) (i : ℕ) (hi : (unassigned F r δ A i).Nonempty) :
    (unassigned F r δ A (i + 1)).ncard < (unassigned F r δ A i).ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine (Set.ssubset_iff_subset_ne).mpr ⟨Set.sdiff_subset, ?_⟩
  intro heq
  have hmem := (chooseCenter_spec F δ hi).1
  have hout : chooseCenter F δ (unassigned F r δ A i) ∈ unassigned F r δ A (i + 1) :=
    heq ▸ hmem
  exact hout.2 (mem_closedBall_self hr)

private lemma exists_removed (F : Set T → ℝ) {r : ℝ} (hr : 0 ≤ r) (δ : ℝ)
    (A : Set T) (t : T) : ∃ i, t ∉ unassigned F r δ A (i + 1) := by
  by_contra! h
  have hn : ∀ i, t ∈ unassigned F r δ A i :=
    fun i => unassigned_antitone F r δ A (Nat.le_succ i) (h i)
  have hcard : ∀ i, (unassigned F r δ A i).ncard + i ≤ A.ncard := by
    intro i
    induction i with
    | zero => simp [unassigned]
    | succ i ih =>
      have := unassigned_ncard_lt F hr δ A i ⟨t, hn i⟩
      omega
  have := hcard (A.ncard + 1)
  omega

/-- The rank is the index of the first ball that removes the point. -/
private noncomputable def greedyRank (F : Set T → ℝ) {r : ℝ} (hr : 0 ≤ r) (δ : ℝ)
    (A : Set T) (t : T) : ℕ :=
  open Classical in Nat.find (exists_removed F hr δ A t)

private lemma mem_unassigned_of_le_rank (F : Set T → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (δ : ℝ) {A : Set T} {t : T} (ht : t ∈ A) {i : ℕ}
    (hi : i ≤ greedyRank F hr δ A t) : t ∈ unassigned F r δ A i := by
  classical
  cases i with
  | zero => exact ht
  | succ i =>
    exact Classical.not_not.mp (Nat.find_min (exists_removed F hr δ A t)
      (lt_of_lt_of_le (Nat.lt_succ_self i) hi))

private lemma mem_closedBall_rank (F : Set T → ℝ) {r : ℝ} (hr : 0 ≤ r) (δ : ℝ)
    {A : Set T} {t : T} (ht : t ∈ A) :
    t ∈ closedBall (chooseCenter F δ (unassigned F r δ A (greedyRank F hr δ A t))) r := by
  classical
  have hm := mem_unassigned_of_le_rank F hr δ ht le_rfl
  by_contra hn
  exact Nat.find_spec (exists_removed F hr δ A t) ⟨hm, hn⟩

variable (F : Set T → ℝ) (radius : ℕ → ℝ) (hR : ∀ n, 0 ≤ radius n)

private noncomputable def splitRank (n : ℕ) (A : Set T) (t : T) : ℕ :=
  greedyRank F (hR (n + 1)) (2 * radius (n + 2)) A t

private noncomputable def greedyCell : ℕ → T → Set T
  | 0, _ => Set.univ
  | n + 1, t =>
    let A := greedyCell n t
    {s ∈ A | splitRank F radius hR n A s = splitRank F radius hR n A t}

private lemma mem_greedyCell (n : ℕ) (t : T) : t ∈ greedyCell F radius hR n t := by
  induction n with
  | zero => exact Set.mem_univ t
  | succ n ih => exact ⟨ih, rfl⟩

private lemma greedyCell_eq_of_mem (n : ℕ) {s t : T}
    (hst : s ∈ greedyCell F radius hR n t) :
    greedyCell F radius hR n s = greedyCell F radius hR n t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change s ∈ greedyCell F radius hR n t ∧
      splitRank F radius hR n (greedyCell F radius hR n t) s =
        splitRank F radius hR n (greedyCell F radius hR n t) t at hst
    simp only [greedyCell, ih hst.1, hst.2]

private lemma greedyCell_succ_subset (n : ℕ) (t : T) :
    greedyCell F radius hR (n + 1) t ⊆ greedyCell F radius hR n t :=
  fun _ h => h.1

private lemma greedyCell_diameter
    (hD : ∀ s t : T, dist s t ≤ 2 * radius 0) (n : ℕ) (t : T) :
    ∀ s ∈ greedyCell F radius hR n t, ∀ u ∈ greedyCell F radius hR n t,
      dist s u ≤ 2 * radius n := by
  cases n with
  | zero => exact fun s _ u _ => hD s u
  | succ n =>
    let A := greedyCell F radius hR n t
    let k := splitRank F radius hR n A t
    let c := chooseCenter F (2 * radius (n + 2))
      (unassigned F (radius (n + 1)) (2 * radius (n + 2)) A k)
    have hc : ∀ s ∈ greedyCell F radius hR (n + 1) t, dist s c ≤ radius (n + 1) := by
      intro s hs
      change s ∈ A ∧ splitRank F radius hR n A s = k at hs
      have h := mem_closedBall_rank F (hR (n + 1)) (2 * radius (n + 2)) hs.1
      change dist s (chooseCenter F (2 * radius (n + 2))
        (unassigned F (radius (n + 1)) (2 * radius (n + 2)) A
          (splitRank F radius hR n A s))) ≤ radius (n + 1) at h
      rwa [hs.2] at h
    intro s hs u hu
    calc
      dist s u ≤ dist s c + dist u c := dist_triangle_right _ _ _
      _ ≤ 2 * radius (n + 1) := by linarith [hc s hs, hc u hu]

/-- The growth estimate combines small clusters around separated centers. -/
private def HasGrowth (F : Set T → ℝ) (q K : ℝ) : Prop :=
  ∀ (A : Set T) (r : ℝ) (m : ℕ) (c : Fin (m + 1) → T) (B : Fin (m + 1) → Set T) (b : ℝ),
    0 ≤ r → (∀ i j, i ≠ j → r ≤ dist (c i) (c j)) →
    (∀ i, (B i).Nonempty ∧ B i ⊆ A ∧ B i ⊆ closedBall (c i) (q * r) ∧ b ≤ F (B i)) →
    b + r * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ)) / K ≤ F A

private lemma greedyCell_growth {q K : ℝ} (hF : Monotone F) (hg : HasGrowth F q K)
    (hD : ∀ s t : T, dist s t ≤ 2 * radius 0)
    (hq : ∀ n, 2 * radius (n + 2) = q * radius (n + 1)) (hq0 : 0 ≤ q)
    (n : ℕ) (t : T) :
    let A := greedyCell F radius hR n t
    let k := splitRank F radius hR n A t
    F (greedyCell F radius hR (n + 2) t) +
        radius (n + 1) * Real.sqrt (Real.log ((k + 1 : ℕ) : ℝ)) / K ≤ F A := by
  let A := greedyCell F radius hR n t
  let k := splitRank F radius hR n A t
  let B := greedyCell F radius hR (n + 2) t
  let r := radius (n + 1)
  let U := unassigned F r (q * r) A
  let c (i : Fin (k + 1)) := chooseCenter F (q * r) (U i)
  have htk : ∀ i ≤ k, t ∈ U i := by
    intro i hi
    have h := mem_unassigned_of_le_rank F (hR (n + 1)) (2 * radius (n + 2))
      (mem_greedyCell F radius hR n t) (show i ≤ k from hi)
    rwa [hq n] at h
  have hc (i : Fin (k + 1)) : c i ∈ U i :=
    (chooseCenter_spec F _ ⟨t, htk i (Nat.le_of_lt_succ i.isLt)⟩).1
  apply hg A r k c (fun i => U i ∩ closedBall (c i) (q * r)) (F B) (hR (n + 1))
  · suffices hordered : ∀ i j : Fin (k + 1), i < j → r ≤ dist (c i) (c j) by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hordered i j hlt
      · rw [dist_comm]; exact hordered j i hgt
    intro i j hij
    have hm : c j ∈ U (i.val + 1) :=
      unassigned_antitone F r (q * r) A (show i.val + 1 ≤ j.val from hij) (hc j)
    have hl : r < dist (c j) (c i) := lt_of_not_ge hm.2
    rw [dist_comm]; exact hl.le
  · intro i
    refine ⟨⟨c i, hc i, mem_closedBall_self (mul_nonneg hq0 (hR (n + 1)))⟩,
      fun _ hs => unassigned_subset F r (q * r) A i hs.1, inter_subset_right, ?_⟩
    have hBig : B ⊆ U i ∩ closedBall t (q * r) := by
      intro s hs
      have hs' := greedyCell_succ_subset F radius hR (n + 1) t hs
      change s ∈ A ∧ splitRank F radius hR n A s = k at hs'
      have hu := mem_unassigned_of_le_rank F (hR (n + 1)) (2 * radius (n + 2)) hs'.1
        (i := i) (by
          change i.val ≤ splitRank F radius hR n A s
          rw [hs'.2]
          exact Nat.le_of_lt_succ i.isLt)
      refine ⟨?_, ?_⟩
      · rwa [hq n] at hu
      · rw [mem_closedBall, ← hq n]
        exact greedyCell_diameter F radius hR hD (n + 2) t s hs t
          (mem_greedyCell F radius hR (n + 2) t)
    exact (hF hBig).trans ((chooseCenter_spec F _ ⟨t, htk i (Nat.le_of_lt_succ i.isLt)⟩).2
      t (htk i (Nat.le_of_lt_succ i.isLt)))


private def rankBits (i : ℕ) : ℕ := (i + 1).log2 + 1

private lemma lt_pow_rankBits (i : ℕ) : i < 2 ^ rankBits i :=
  (Nat.lt_succ_self i).trans (by
    simpa [rankBits, Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two (i + 1))

private lemma pow_rankBits_le (i : ℕ) : 2 ^ rankBits i ≤ 2 * (i + 1) := by
  rw [rankBits, pow_succ, Nat.mul_comm, Nat.log2_eq_log_two]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.succ_ne_zero _))

/-- Appending a rank puts its bits and a delimiter after the parent's code.
The number of trailing zeroes records the width of the rank's bits. -/
private def appendRank (p i : ℕ) : ℕ :=
  2 ^ rankBits i * (2 * (2 ^ rankBits i * p + i) + 1)

private lemma appendRank_injective {p p' i i' : ℕ}
    (h : appendRank p i = appendRank p' i') : p = p' ∧ i = i' := by
  have sameWidth (k l a b : ℕ) (he : 2 ^ k * (2 * a + 1) = 2 ^ l * (2 * b + 1))
      (hk : k ≤ l) : k = l := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    cases d with
    | zero => simp
    | succ d =>
      rw [pow_add, mul_assoc] at he
      have he' := Nat.mul_left_cancel (pow_pos (show 0 < (2 : ℕ) by decide) k) he
      rw [pow_succ, mul_assoc, mul_left_comm (2 ^ d)] at he'
      omega
  unfold appendRank at h
  have hw : rankBits i = rankBits i' := by
    rcases le_total (rankBits i) (rankBits i') with hl | hr
    · exact sameWidth _ _ _ _ h hl
    · exact (sameWidth _ _ _ _ h.symm hr).symm
  set k := rankBits i with hk
  have hi := lt_pow_rankBits i
  have hi' := lt_pow_rankBits i'
  rw [← hw] at hi' h
  rw [← hk] at hi
  have he := Nat.mul_left_cancel (pow_pos (show 0 < (2 : ℕ) by decide) k) h
  have hp : 2 ^ k * p + i = 2 ^ k * p' + i' := by omega
  have hpdiv : (2 ^ k * p + i) / 2 ^ k = (2 ^ k * p' + i') / 2 ^ k :=
    congrArg (fun x : ℕ => x / 2 ^ k) hp
  have hpmod : (2 ^ k * p + i) % 2 ^ k = (2 ^ k * p' + i') % 2 ^ k :=
    congrArg (fun x : ℕ => x % 2 ^ k) hp
  rw [Nat.add_comm (2 ^ k * p) i, Nat.add_comm (2 ^ k * p') i'] at hpdiv hpmod
  have hk0 : 0 < 2 ^ k := by positivity
  simp only [Nat.add_mul_div_left _ _ hk0, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hi',
    zero_add] at hpdiv
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hpmod
  exact ⟨hpdiv, hpmod⟩

private lemma two_le_rankPow (i : ℕ) : 2 ≤ 2 ^ rankBits i := by
  rw [rankBits, pow_succ]
  have h : 0 < (2 : ℕ) ^ (i + 1).log2 := by positivity
  omega

private lemma appendRank_ge (p i : ℕ) : 2 * p + 2 ≤ appendRank p i := by
  unfold appendRank
  have hk := two_le_rankPow i
  calc 2 * p + 2 = 2 * (p + 1) := by omega
    _ ≤ 2 ^ rankBits i * (2 * (2 ^ rankBits i * p + i) + 1) := by
      gcongr
      calc p ≤ 2 ^ rankBits i * p := by
            simpa using Nat.mul_le_mul_right p (by omega : 1 ≤ 2 ^ rankBits i)
        _ ≤ 2 * (2 ^ rankBits i * p + i) := by omega

private lemma appendRank_le {p : ℕ} (hp : 0 < p) (i : ℕ) :
    appendRank p i ≤ 16 * (i + 1)^2 * p := by
  have hi := lt_pow_rankBits i
  have hb := pow_rankBits_le i
  unfold appendRank
  calc
    2 ^ rankBits i * (2 * (2 ^ rankBits i * p + i) + 1) ≤
        2 ^ rankBits i * (2 * (2 ^ rankBits i * (p + 1))) := by
      apply Nat.mul_le_mul_left
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ (2 * (i + 1)) * (2 * ((2 * (i + 1)) * (p + 1))) := by gcongr
    _ ≤ (2 * (i + 1)) * (2 * ((2 * (i + 1)) * (2 * p))) := by
      gcongr
      omega
    _ = 16 * (i + 1)^2 * p := by ring

private noncomputable def cellCode : ℕ → T → ℕ
  | 0, _ => 1
  | j + 1, t => appendRank (cellCode j t)
    (splitRank F radius hR j (greedyCell F radius hR j t) t)

private lemma pow_le_cellCode (j : ℕ) (t : T) : 2 ^ j ≤ cellCode F radius hR j t := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Nat.mul_comm, cellCode]
    exact (Nat.mul_le_mul_left 2 ih).trans
      ((Nat.le_add_right _ _).trans (appendRank_ge _ _))

private lemma cellCode_strictMono (t : T) : StrictMono (fun j => cellCode F radius hR j t) :=
  strictMono_nat_of_lt_succ fun j => by
    rw [cellCode]
    have h := appendRank_ge (cellCode F radius hR j t)
      (splitRank F radius hR j (greedyCell F radius hR j t) t)
    omega

private lemma cellCode_eq_of_mem (j : ℕ) {s t : T} (h : s ∈ greedyCell F radius hR j t) :
    cellCode F radius hR j s = cellCode F radius hR j t := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change s ∈ greedyCell F radius hR j t ∧
      splitRank F radius hR j (greedyCell F radius hR j t) s =
        splitRank F radius hR j (greedyCell F radius hR j t) t at h
    simp only [cellCode, ih h.1, greedyCell_eq_of_mem F radius hR j h.1, h.2]

private lemma greedyCell_eq_of_cellCode_eq (j k : ℕ) (s t : T)
    (h : cellCode F radius hR j s = cellCode F radius hR k t) :
    j = k ∧ greedyCell F radius hR j s = greedyCell F radius hR k t := by
  induction j generalizing k with
  | zero =>
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k =>
      have hp := pow_le_cellCode F radius hR (k + 1) t
      rw [← h, cellCode, pow_succ] at hp
      have hpos : 0 < (2 : ℕ)^k := by positivity
      omega
  | succ j ih =>
    cases k with
    | zero =>
      have hp := pow_le_cellCode F radius hR (j + 1) s
      rw [h, cellCode, pow_succ] at hp
      have hpos : 0 < (2 : ℕ)^j := by positivity
      omega
    | succ k =>
      rw [cellCode, cellCode] at h
      obtain ⟨hp, hr⟩ := appendRank_injective h
      obtain ⟨rfl, he⟩ := ih k hp
      exact ⟨rfl, by simp only [greedyCell, he, ← hr]⟩

private lemma exists_code_ge (n : ℕ) (t : T) :
    ∃ k, 2 ^ 2 ^ n ≤ cellCode F radius hR (k + 1) t :=
  ⟨2 ^ n - 1, by
    rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := n))]
    exact pow_le_cellCode F radius hR (2 ^ n) t⟩

/-- The cut stops just before the code first exceeds the budget at this level. -/
private noncomputable def cutDepth (n : ℕ) (t : T) : ℕ :=
  open Classical in Nat.find (exists_code_ge F radius hR n t)

private lemma code_cut_lt (n : ℕ) (t : T) :
    cellCode F radius hR (cutDepth F radius hR n t) t < 2 ^ 2 ^ n := by
  classical
  generalize he : cutDepth F radius hR n t = j
  cases j with
  | zero => exact one_lt_pow₀ (by decide) (by positivity)
  | succ j =>
    exact lt_of_not_ge (Nat.find_min (exists_code_ge F radius hR n t)
      (show j < cutDepth F radius hR n t by omega))

private lemma le_code_succ_cut (n : ℕ) (t : T) :
    2 ^ 2 ^ n ≤ cellCode F radius hR (cutDepth F radius hR n t + 1) t :=
  open Classical in Nat.find_spec (exists_code_ge F radius hR n t)

private lemma cutDepth_mono (t : T) : Monotone (fun n => cutDepth F radius hR n t) := by
  intro m n hmn
  classical
  apply Nat.find_min' (exists_code_ge F radius hR m t)
  exact (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.pow_le_pow_right Nat.zero_lt_two hmn)).trans
    (le_code_succ_cut F radius hR n t)

private lemma cutDepth_lt (n : ℕ) (t : T) : cutDepth F radius hR n t < 2 ^ n := by
  have h := (pow_le_cellCode F radius hR _ t).trans_lt (code_cut_lt F radius hR n t)
  exact (pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp h

private lemma greedyCell_subset_of_le {j k : ℕ} (h : j ≤ k) (t : T) :
    greedyCell F radius hR k t ⊆ greedyCell F radius hR j t := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (greedyCell_succ_subset F radius hR k t).trans ih

private noncomputable def cutCode (n : ℕ) (t : T) : ℕ :=
  cellCode F radius hR (cutDepth F radius hR n t) t

private lemma cutCode_eq_of_succ_eq (n : ℕ) {s t : T}
    (h : cutCode F radius hR (n + 1) s = cutCode F radius hR (n + 1) t) :
    cutCode F radius hR n s = cutCode F radius hR n t := by
  obtain ⟨he, hc⟩ := greedyCell_eq_of_cellCode_eq F radius hR _ _ _ _ h
  have hm : s ∈ greedyCell F radius hR (cutDepth F radius hR (n + 1) t) t :=
    hc ▸ mem_greedyCell F radius hR _ _
  have hs : cutDepth F radius hR n s ≤ cutDepth F radius hR (n + 1) t :=
    he ▸ cutDepth_mono F radius hR s (Nat.le_succ n)
  have ht : cutDepth F radius hR n t ≤ cutDepth F radius hR (n + 1) t :=
    cutDepth_mono F radius hR t (Nat.le_succ n)
  have hagree (j : ℕ) (hj : j ≤ cutDepth F radius hR (n + 1) t) :
      cellCode F radius hR j s = cellCode F radius hR j t :=
    cellCode_eq_of_mem F radius hR j (greedyCell_subset_of_le F radius hR hj t hm)
  have hdepth : cutDepth F radius hR n s = cutDepth F radius hR n t := by
    rcases lt_trichotomy (cutDepth F radius hR n s) (cutDepth F radius hR n t) with hlt | he | hgt
    · have hnext := hagree _ ((Nat.succ_le_of_lt hlt).trans ht)
      have h := le_code_succ_cut F radius hR n s
      rw [hnext] at h
      classical
      exact (Nat.find_min (exists_code_ge F radius hR n t) hlt h).elim
    · exact he
    · have hnext := hagree _ ((Nat.succ_le_of_lt hgt).trans hs)
      have h := le_code_succ_cut F radius hR n t
      rw [← hnext] at h
      classical
      exact (Nat.find_min (exists_code_ge F radius hR n s) hgt h).elim
  unfold cutCode
  rw [hdepth]
  exact hagree _ ht

private noncomputable def cutPartitions : AdmissibleSequence T where
  cell n t := {s | cutCode F radius hR n s = cutCode F radius hR n t}
  mem_cell _ _ := rfl
  cell_eq_of_mem n s t h := by
    change cutCode F radius hR n s = cutCode F radius hR n t at h
    rw [h]
  cell_succ_subset n t := fun _ h => cutCode_eq_of_succ_eq F radius hR n h
  encard_range_le n := by
    cases n with
    | zero =>
      have h : ∀ t, cutCode F radius hR 0 t = 1 := by
        intro t
        have he : cutDepth F radius hR 0 t = 0 :=
          Nat.lt_one_iff.mp (by simpa using cutDepth_lt F radius hR 0 t)
        simp [cutCode, he, cellCode]
      simp [h, chainingCard, Set.range_const]
    | succ n =>
      let f := cutCode F radius hR (n + 1)
      change (Set.range ((fun k => {s | f s = k}) ∘ f)).encard ≤ chainingCard (n + 1)
      rw [Set.range_comp]
      refine (Set.encard_image_le _ _).trans ?_
      rw [chainingCard, ite_eq_right (Nat.succ_ne_zero _), ← Nat.encard_range]
      exact Set.encard_le_encard (fun _ ⟨t, ht⟩ => ht ▸ code_cut_lt F radius hR _ t)

private lemma cutPartitions_subset (n : ℕ) (t : T) :
    (cutPartitions F radius hR).cell n t ⊆
      greedyCell F radius hR (cutDepth F radius hR n t) t := by
  intro s hs
  obtain ⟨he, hc⟩ := greedyCell_eq_of_cellCode_eq F radius hR _ _ _ _
    (show cutCode F radius hR n s = cutCode F radius hR n t from hs)
  exact hc ▸ mem_greedyCell F radius hR _ s


private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 :=
  Real.log_two_gt_d9.le.trans' (by norm_num)

/-- This is the square root of the binary logarithm of the code. -/
private noncomputable def codeScale (c : ℕ) : ℝ :=
  Real.sqrt (Real.log (c : ℝ) / Real.log 2)

private noncomputable def rankScale (i : ℕ) : ℝ :=
  Real.sqrt (Real.log ((i + 1 : ℕ) : ℝ))

private lemma appendRank_scale {p : ℕ} (hp : 0 < p) (i : ℕ) :
    codeScale (appendRank p i) ≤ codeScale p + 2 + 2 * rankScale i := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hi1 : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
  have hlp := Real.log_nonneg hp1
  have hli := Real.log_nonneg hi1
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hc : (0 : ℝ) < (appendRank p i : ℝ) := by
    exact_mod_cast (show 0 < appendRank p i from (by omega : 0 < 2 * p + 2)
      |>.trans_le (appendRank_ge p i))
  have hle : (appendRank p i : ℝ) ≤ 16 * ((i + 1 : ℕ) : ℝ)^2 * p := by
    exact_mod_cast appendRank_le hp i
  have hlog := Real.log_le_log hc hle
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    show (16 : ℝ) = 2^4 by norm_num, Real.log_pow] at hlog
  have hquo : Real.log (appendRank p i : ℝ) / Real.log 2 ≤
      Real.log (p : ℝ) / Real.log 2 + 4 + 4 * Real.log ((i + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ h2).mpr
    have hb := mul_le_mul_of_nonneg_left half_le_log_two
      (show 0 ≤ 4 * Real.log ((i + 1 : ℕ) : ℝ) by positivity)
    have hdiv := div_mul_cancel₀ (Real.log (p : ℝ)) h2.ne'
    push_cast at hlog hb ⊢
    rw [add_mul, add_mul, hdiv]
    linarith
  refine (Real.sqrt_le_sqrt hquo).trans ?_
  have hp0 : 0 ≤ codeScale p := Real.sqrt_nonneg _
  have hi0 : 0 ≤ rankScale i := Real.sqrt_nonneg _
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hpSq : codeScale p ^ 2 = Real.log (p : ℝ) / Real.log 2 :=
    Real.sq_sqrt (div_nonneg hlp h2.le)
  have hiSq : rankScale i ^ 2 = Real.log ((i + 1 : ℕ) : ℝ) := Real.sq_sqrt hli
  nlinarith [mul_nonneg hp0 hi0]

private lemma weight_le_codeScale {n c : ℕ} (hc : 2 ^ 2 ^ n ≤ c) :
    Real.sqrt 2 ^ n ≤ codeScale c := by
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hle : (2 : ℝ) ^ (2 ^ n : ℕ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hl := Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at hl
  have hpow : (2 ^ n : ℝ) ≤ Real.log (c : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ h2).mpr
    exact_mod_cast hl
  unfold codeScale
  have hs : (Real.sqrt 2 ^ n)^2 = (2 : ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num)]
  have hh := Real.sqrt_le_sqrt hpow
  rwa [← hs, Real.sqrt_sq (by positivity)] at hh

private lemma sum_weight_le (u : Finset ℕ) (c : ℕ)
    (hc : ∀ n ∈ u, 2 ^ 2 ^ n ≤ c) :
    (∑ n ∈ u, Real.sqrt 2 ^ n) ≤ 4 * codeScale c := by
  rcases u.eq_empty_or_nonempty with rfl | hu
  · simp [codeScale]
  let m := u.max' hu
  have hmem : m ∈ u := u.max'_mem hu
  have hsubset : u ⊆ range (m + 1) :=
    fun n hn => mem_range.mpr (Nat.lt_succ_of_le (u.le_max' n hn))
  have hg : ∀ j, ∑ n ∈ range (j + 1), Real.sqrt 2 ^ n ≤ 4 * Real.sqrt 2 ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
        (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      have hn := mul_nonneg (show 0 ≤ Real.sqrt 2 ^ j by positivity)
        (show 0 ≤ 3 * Real.sqrt 2 - 4 by linarith)
      nlinarith only [ih, hn]
  calc
    (∑ n ∈ u, Real.sqrt 2 ^ n) ≤ ∑ n ∈ range (m + 1), Real.sqrt 2 ^ n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ ≤ 4 * Real.sqrt 2 ^ m := hg m
    _ ≤ 4 * codeScale c := by gcongr; exact weight_le_codeScale (hc m hmem)

private lemma ofReal_weight (n : ℕ) :
    ENNReal.ofReal (Real.sqrt 2 ^ n) = (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) := by
  symm
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

omit [Finite T] [Nonempty T] in
private lemma diam_le_of_growth {q K : ℝ} (hq : 0 ≤ q) (hK : 0 < K)
    (hF : ∀ A, 0 ≤ F A) (hg : HasGrowth F q K) (s t : T) :
    dist s t ≤ 2 * K * F Set.univ := by
  let c : Fin 2 → T := ![s, t]
  have hs (i j : Fin 2) (hij : i ≠ j) : dist s t ≤ dist (c i) (c j) := by
    fin_cases i <;> fin_cases j <;> simp_all [c, dist_comm]
  have hg' := hg Set.univ (dist s t) 1 c (fun i => {c i}) 0 dist_nonneg hs
    (fun i => ⟨Set.singleton_nonempty _, Set.subset_univ _,
      Set.singleton_subset_iff.mpr (mem_closedBall_self (mul_nonneg hq dist_nonneg)), hF _⟩)
  norm_num at hg'
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log 2) :=
    (Real.le_sqrt (by norm_num) (by linarith [half_le_log_two])).mpr
      (by linarith [half_le_log_two])
  have hm := mul_le_mul_of_nonneg_left hsqrt (dist_nonneg (x := s) (y := t))
  have hg'' := (div_le_iff₀ hK).mp hg'
  nlinarith only [hm, hg'']

/-- The separated-cluster growth estimate controls the admissible partition functional. -/
private lemma growth_gamma_bound {a K : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hK : 0 < K)
    (hF0 : ∀ A, 0 ≤ F A) (hF : Monotone F) (hg : HasGrowth F (2 * a) K) :
    gammaFunctional 2 (edist : T → T → ℝ≥0∞) ≤
      ENNReal.ofReal ((128 * K + 64 * K / a) * F Set.univ) := by
  let D := 2 * K * F Set.univ
  have hD0 : 0 ≤ D := by dsimp [D]; positivity [hF0 Set.univ]
  let r (j : ℕ) := D * a ^ j
  have hr (j : ℕ) : 0 ≤ r j := by dsimp [r]; positivity
  have hr_succ (j : ℕ) : r (j + 1) = a * r j := by simp only [r, pow_succ]; ring
  have hr_half (j : ℕ) : r (j + 1) ≤ r j / 2 := by
    rw [hr_succ]; nlinarith [mul_le_mul_of_nonneg_right ha2 (hr j)]
  have hD (s t : T) : dist s t ≤ 2 * r 0 := by
    have h := diam_le_of_growth F (by positivity : 0 ≤ 2 * a) hK hF0 hg s t
    simp only [r, pow_zero, mul_one]
    linarith only [h, hD0]
  let A := cutPartitions F r hr
  refine (iInf_le _ A).trans (iSup_le fun t => ?_)
  let cell j := greedyCell F r hr j t
  let v j := F (cell j)
  let k n := cutDepth F r hr n t
  let code j := cellCode F r hr j t
  let cost j := codeScale (code j)
  let x j := r j * cost (j + 1)
  let y j := r j * cost j
  have y0 : y 0 = 0 := by simp [y, cost, code, cellCode, codeScale]
  have hy (j : ℕ) : 0 ≤ y j := mul_nonneg (hr j) (Real.sqrt_nonneg _)
  have hv (j : ℕ) : 0 ≤ v j := hF0 _
  have hv0 : v 0 = F Set.univ := rfl
  have hv1 : v 1 ≤ F Set.univ := hF (Set.subset_univ _)
  have hstep (j : ℕ) :
      x j + 2 * y (j + 1) ≤ 2 * y j +
        (8 * (r j - r (j + 1)) + (4 * K / a) * (v j - v (j + 2))) := by
    let i := splitRank F r hr j (cell j) t
    have hcode : code (j + 1) = appendRank (code j) i := rfl
    have hcode_pos : 0 < code j := (by positivity : 0 < 2 ^ j).trans_le
      (pow_le_cellCode F r hr j t)
    have hscale := appendRank_scale hcode_pos i
    rw [← hcode] at hscale
    have hscale' := mul_le_mul_of_nonneg_left hscale (hr j)
    change r j * cost (j + 1) ≤ r j * (cost j + 2 + 2 * rankScale i) at hscale'
    have hdec := mul_le_mul_of_nonneg_right (hr_half j) (Real.sqrt_nonneg
      (Real.log (code (j + 1) : ℝ) / Real.log 2))
    change y (j + 1) ≤ r j / 2 * cost (j + 1) at hdec
    have hgr := greedyCell_growth F r hr hF hg hD
      (fun n => by rw [hr_succ (n + 1)]; ring) (by positivity) j t
    change v (j + 2) + r (j + 1) * rankScale i / K ≤ v j at hgr
    have hbound : 4 * (r j * rankScale i) ≤ (4 * K / a) * (v j - v (j + 2)) := by
      have h : r (j + 1) * rankScale i / K ≤ v j - v (j + 2) := by linarith only [hgr]
      have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4 * K / a)
      rw [hr_succ] at h'
      convert h' using 1
      field_simp [ha.ne', hK.ne']
    dsimp only [x, y] at *
    nlinarith only [hscale', hdec, hbound, hr_half j]
  have hfinite (N : ℕ) :
      (∑ j ∈ range N, x j) + 2 * y N ≤
        8 * (D - r N) + (4 * K / a) * (v 0 + v 1 - v N - v (N + 1)) := by
    induction N with
    | zero => simp [y0, r]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith only [ih, hstep N]
  have hsum (N : ℕ) :
      (∑ j ∈ range N, x j) ≤ 8 * D + (8 * K / a) * F Set.univ := by
    have h : v 0 + v 1 - v N - v (N + 1) ≤ 2 * F Set.univ := by
      linarith only [hv0, hv1, hv N, hv (N + 1)]
    have hb := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4 * K / a)
    rw [show 4 * K / a * (2 * F Set.univ) = 8 * K / a * F Set.univ by ring] at hb
    linarith only [hfinite N, hb, hr N, hy N]
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have hmap : ∀ n ∈ range N, k n ∈ range (2 ^ N) := by
    intro n hn
    exact mem_range.mpr ((cutDepth_lt F r hr n t).trans_le
      (Nat.pow_le_pow_right Nat.zero_lt_two (mem_range.mp hn).le))
  have hweight :
      (∑ n ∈ range N, Real.sqrt 2 ^ n * (2 * r (k n))) ≤
        8 * (8 * D + (8 * K / a) * F Set.univ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc
      (∑ j ∈ range (2 ^ N), ∑ n ∈ (range N).filter (fun n => k n = j),
        Real.sqrt 2 ^ n * (2 * r (k n))) ≤ ∑ j ∈ range (2 ^ N), 8 * x j := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc
            _ = (∑ n ∈ (range N).filter (fun n => k n = j), Real.sqrt 2 ^ n) *
                (2 * r j) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun n hn => by rw [(Finset.mem_filter.mp hn).2]
            _ ≤ (4 * cost (j + 1)) * (2 * r j) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              apply sum_weight_le
              intro n hn
              have h := le_code_succ_cut F r hr n t
              change 2 ^ 2 ^ n ≤ code (k n + 1) at h
              rwa [(Finset.mem_filter.mp hn).2] at h
            _ = 8 * x j := by dsimp [x]; ring
      _ ≤ 8 * (8 * D + (8 * K / a) * F Set.univ) := by
        rw [← Finset.mul_sum]
        gcongr
        exact hsum _
  have hdiam (n : ℕ) : diamWith edist (A.cell n t) ≤ ENNReal.ofReal (2 * r (k n)) := by
    apply iSup₂_le
    intro s hs
    apply iSup₂_le
    intro u hu
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    exact greedyCell_diameter F r hr hD _ t s (cutPartitions_subset F r hr _ _ hs) u
      (cutPartitions_subset F r hr _ _ hu)
  calc
    (∑ n ∈ range N, (2 : ℝ≥0∞) ^ ((n : ℝ) / 2) * diamWith edist (A.cell n t)) ≤
        ∑ n ∈ range N, ENNReal.ofReal (Real.sqrt 2 ^ n * (2 * r (k n))) := by
      refine Finset.sum_le_sum fun n _ => ?_
      rw [ENNReal.ofReal_mul (by positivity), ofReal_weight]
      gcongr
      exact hdiam _
    _ ≤ ENNReal.ofReal (8 * (8 * D + (8 * K / a) * F Set.univ)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      exact ENNReal.ofReal_le_ofReal hweight
    _ = _ := by congr 1; dsimp [D]; ring

end AdmissiblePartitions

private lemma gamma_le_pullback_bound {S T : Type*} (f : T → S)
    (d : S → S → ℝ≥0∞) :
    gammaFunctional 2 (fun s t => d (f s) (f t)) ≤ gammaFunctional 2 d := by
  refine le_iInf fun A => ?_
  let B : AdmissibleSequence T :=
    { cell := fun n t => f ⁻¹' A.cell n (f t)
      mem_cell := fun n t => A.mem_cell n (f t)
      cell_eq_of_mem := fun n s t h => congrArg (Set.preimage f) (A.cell_eq_of_mem n _ _ h)
      cell_succ_subset := fun n t => Set.preimage_mono (A.cell_succ_subset n (f t))
      encard_range_le := fun n => by
        have hsub : Set.range (fun t => f ⁻¹' A.cell n (f t)) ⊆
            Set.preimage f '' Set.range (A.cell n) :=
          fun _ ⟨t, ht⟩ => ⟨A.cell n (f t), ⟨f t, rfl⟩, ht⟩
        exact (Set.encard_le_encard hsub).trans
          ((Set.encard_image_le _ _).trans (A.encard_range_le n)) }
  refine (iInf_le _ B).trans (iSup_le fun t => ?_)
  apply le_iSup_of_le (f t)
  apply tsum_le_tsum
  intro n
  apply mul_le_mul_right
  exact iSup₂_le fun s hs => iSup₂_le fun u hu => le_diamWith d hs hu

private lemma gamma_pullback_eq {S T : Type*} {f : T → S} (hs : Function.Surjective f)
    (d : S → S → ℝ≥0∞) :
    gammaFunctional 2 (fun s t => d (f s) (f t)) = gammaFunctional 2 d := by
  refine le_antisymm (gamma_le_pullback_bound f d) ?_
  simpa only [Function.surjInv_eq hs] using
    gamma_le_pullback_bound (Function.surjInv hs) (fun s t => d (f s) (f t))

private lemma le_finiteSup {ι : Type*} [Finite ι] (v : ι → ℝ) (i : ι) :
    v i ≤ ⨆ j, v j :=
  le_ciSup (Set.finite_range _).bddAbove i

private lemma integrable_finiteSup {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    [Nonempty ι] {P : Measure Ω} {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) P) :
    Integrable (fun x => ⨆ i, f i x) P := by
  classical
  have := Fintype.ofFinite ι
  refine (integrable_finsetSum Finset.univ (fun i _ => (hf i).norm)).mono'
    (AEMeasurable.iSup (fun i => (hf i).aemeasurable)).aestronglyMeasurable ?_
  refine ae_of_all _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => f i x)
  change ‖⨆ i, f i x‖ ≤ ∑ i, ‖f i x‖
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => norm_nonneg (f j x)) (Finset.mem_univ i)

section StandardGaussian

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "γ" => stdGaussian E

private lemma integrable_linear (L : StrongDual ℝ E) : Integrable L γ :=
  IsGaussian.integrable_dual _ L

private lemma integral_linear (L : StrongDual ℝ E) : ∫ x, L x ∂γ = 0 :=
  integral_strongDual_stdGaussian L

private lemma linear_canonicalDist {T : Type*} (v : T → StrongDual ℝ E) (s t : T) :
    canonicalDist γ (fun t x => v t x) s t = ENNReal.ofReal (dist (v s) (v t)) := by
  let L := v s - v t
  have hL : MemLp L 2 γ := IsGaussian.memLp_dual _ L 2 (by simp)
  rw [canonicalDist_eq_ofReal_sqrt (s := s) (t := t)
    (show MemLp (fun x => v s x - v t x) 2 γ from hL)]
  change ENNReal.ofReal (Real.sqrt (∫ x, L x ^ 2 ∂γ)) = _
  have hvar := variance_dual_stdGaussian L
  rw [variance_eq_integral L.continuous.measurable.aemeasurable, integral_linear L] at hvar
  simp only [sub_zero] at hvar
  rw [hvar, Real.sqrt_sq (norm_nonneg L), dist_eq_norm]

private lemma gaussian_family {T : Type*} [Finite T] (v : T → StrongDual ℝ E) :
    IsGaussian ((γ).map fun x t => v t x) := by
  let L : E →L[ℝ] (T → ℝ) := ContinuousLinearMap.pi v
  exact isGaussian_map_of_measurable (L := L) (Measurable.of_eval
    (fun t => (v t).continuous.measurable))

/-- The expected maximum on a finite subset of a family of linear Gaussian variables. -/
private noncomputable def gaussianWidth {T : Type*} (v : T → StrongDual ℝ E) (A : Set T) : ℝ :=
  ∫ x, ⨆ i : A, v i x ∂γ

private lemma gaussianWidth_nonneg {T : Type*} [Finite T] (v : T → StrongDual ℝ E) (A : Set T) :
    0 ≤ gaussianWidth v A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simp [gaussianWidth]
  · let : Nonempty A := ⟨⟨t, ht⟩⟩
    rw [← integral_linear (v t)]
    exact integral_mono (integrable_linear _) (integrable_finiteSup (fun i : A =>
      integrable_linear (v i))) (fun x => le_finiteSup (fun i : A => v i x) ⟨t, ht⟩)

private lemma gaussianWidth_mono {T : Type*} [Finite T] (v : T → StrongDual ℝ E) :
    Monotone (gaussianWidth v) := by
  intro A B h
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simpa [gaussianWidth] using gaussianWidth_nonneg v B
  · let : Nonempty A := hA.to_subtype
    let : Nonempty B := (hA.mono h).to_subtype
    apply integral_mono (integrable_finiteSup (fun i : A => integrable_linear (v i)))
      (integrable_finiteSup (fun i : B => integrable_linear (v i)))
    intro x
    exact ciSup_le fun i => le_finiteSup (fun j : B => v j x) ⟨i, h i.2⟩

private lemma lipschitz_finiteSup_linear {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → StrongDual ℝ E) {b : ℝ≥0} (hb : ∀ i, ‖v i‖ ≤ b) :
    LipschitzWith b (fun x => ⨆ i, v i x) := by
  refine lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_
  rw [Real.dist_eq, abs_le]
  have h (x y : E) (i : ι) : v i x - v i y ≤ (b : ℝ) * dist x y :=
    ((le_abs_self _).trans ((v i).dist_le_opNorm x y)).trans
      (mul_le_mul_of_nonneg_right (hb i) dist_nonneg)
  have hmax (x y : E) : (⨆ i, v i x) ≤ (⨆ i, v i y) + (b : ℝ) * dist x y := by
    apply ciSup_le
    intro i
    linarith only [h x y i, le_finiteSup (fun i => v i y) i]
  have hrev := hmax y x
  rw [dist_comm y x] at hrev
  constructor <;> linarith only [hmax x y, hrev]

private lemma expected_finiteSup_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) γ) {b : ℝ≥0}
    (hsub : ∀ i, HasSubgaussianMGF (f i) (b ^ 2) γ)
    (hb : 0 < b) (hcard : 1 < Fintype.card ι) :
    (∫ x, ⨆ i, f i x ∂γ) ≤ 2 * b * Real.sqrt (Real.log (Fintype.card ι)) := by
  let d : ℝ := Fintype.card ι
  let M (x : E) := ⨆ i, f i x
  let z : ℝ := Real.sqrt (Real.log d)
  let u : ℝ := z / b
  have hd : 1 < d := by
    dsimp [d]; exact_mod_cast hcard
  have hz : 0 < z := Real.sqrt_pos.mpr (Real.log_pos hd)
  have hb' : 0 < (b : ℝ) := hb
  have hu : 0 < u := div_pos hz hb'
  have hM := integrable_finiteSup hf
  have hexp_le (x : E) : Real.exp (u * M x) ≤ ∑ i, Real.exp (u * f i x) := by
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => f i x)
    rw [show M x = f i x from hi.symm]
    exact Finset.single_le_sum (f := fun j => Real.exp (u * f j x))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hi (i : ι) : Integrable (fun x => Real.exp (u * f i x)) γ :=
    (hsub i).integrable_exp_mul u
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have he : Integrable (fun x => Real.exp (u * M x)) γ :=
    hs.mono' ((hM.const_mul u).aemeasurable.exp.aestronglyMeasurable) (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp_le x)
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all γ fun _ => Set.mem_univ _) (hM.const_mul u) he
  rw [integral_const_mul] at hJ
  have hmgf (i : ι) :
      (∫ x, Real.exp (u * f i x) ∂γ) ≤ Real.exp ((b : ℝ)^2 * u^2 / 2) := by
    simpa only [mgf, NNReal.coe_pow] using (hsub i).mgf_le u
  have hE := hJ.trans (integral_mono he hs hexp_le)
  simp only [integral_finsetSum _ (fun i _ => hi i)] at hE
  have hsum : (∑ i, ∫ x, Real.exp (u * f i x) ∂γ) ≤
      d * Real.exp ((b : ℝ)^2 * u^2 / 2) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) fun i _ => hmgf i)
  have hL := hE.trans hsum
  rw [← Real.exp_log (show 0 < d by linarith), ← Real.exp_add, Real.exp_le_exp] at hL
  have hsquare : z^2 = Real.log d := Real.sq_sqrt (Real.log_nonneg hd.le)
  have hu' : u * b = z := div_mul_cancel₀ _ hb'.ne'
  have hsq' : (b : ℝ)^2 * u^2 = z^2 := by rw [mul_comm, ← mul_pow, hu']
  have heq : u * (2 * (b : ℝ) * z) = 2 * z^2 := by
    calc
      _ = 2 * (u * b) * z := by ring
      _ = _ := by rw [hu']; ring
  rw [hsq', ← hsquare] at hL
  apply le_of_mul_le_mul_left _ hu
  rw [heq]
  linarith only [hL, sq_nonneg z]


/-- The form of Sudakov minoration used for the Gaussian centers of the clusters. -/
private def SudakovConstant (L : ℝ) : Prop :=
  ∀ (n m : ℕ) (v : Fin (m + 1) → StrongDual ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ),
    0 ≤ r → (∀ i j, i ≠ j → r ≤ dist (v i) (v j)) →
    r / L * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ)) ≤
      ∫ x, ⨆ i, v i x ∂stdGaussian (EuclideanSpace ℝ (Fin n))

private lemma exists_sudakovConstant : ∃ L > 0, SudakovConstant L := by
  obtain ⟨L, hL, h⟩ := sudakov_minoration
  refine ⟨L, hL, ?_⟩
  intro n m v r hr hsep
  let V := EuclideanSpace ℝ (Fin n)
  have hs := h V (stdGaussian V) (Fin (m + 1)) (fun i x => v i x) r
    (fun i => (v i).continuous.measurable) (gaussian_family v) (fun i => integral_linear (v i))
    hr (fun i j hij => by rw [linear_canonicalDist]; exact ENNReal.ofReal_le_ofReal (hsep i j hij))
  simpa only [Fintype.card_fin] using hs

private lemma sup_sub_eq {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) (a : ℝ) :
    (⨆ i, f i - a) = (⨆ i, f i) - a := by
  apply le_antisymm
  · exact ciSup_le fun i => sub_le_sub_right (le_finiteSup f i) a
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := f)
    rw [← hi]
    exact le_finiteSup (fun i => f i - a) i

/-- Concentration bounds the loss when each center is replaced by its cluster maximum. -/
private lemma gaussianWidth_growth {T : Type*} [MetricSpace T] [Finite T]
    (v : T → StrongDual ℝ E) (hv : ∀ s t, dist (v s) (v t) = dist s t)
    {L q : ℝ} (hSud : SudakovConstant L) (hq : 0 < q)
    (hqL : 2 * q ≤ (1 / 2) / L) :
    ∀ (A : Set T) (r : ℝ) (m : ℕ) (c : Fin (m + 1) → T) (B : Fin (m + 1) → Set T) (b : ℝ),
    0 ≤ r → (∀ i j, i ≠ j → r ≤ dist (c i) (c j)) →
    (∀ i, (B i).Nonempty ∧ B i ⊆ A ∧ B i ⊆ Metric.closedBall (c i) (q * r) ∧
      b ≤ gaussianWidth v (B i)) →
    b + r * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ)) / (2 * L) ≤ gaussianWidth v A := by
  intro A r m c B b hr hsep hB
  have hbA : b ≤ gaussianWidth v A :=
    (hB 0).2.2.2.trans (gaussianWidth_mono v (hB 0).2.1)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hbA
  rcases hr.eq_or_lt with hr | hr
  · simpa [← hr] using hbA
  let (i : Fin (m + 1)) : Nonempty (B i) := (hB i).1.to_subtype
  let : Nonempty A := ((hB 0).1.mono (hB 0).2.1).to_subtype
  let w (i : Fin (m + 1)) (t : B i) := v t - v (c i)
  let g (i : Fin (m + 1)) (x : E) := ⨆ t : B i, w i t x
  let err (i : Fin (m + 1)) (x : E) := gaussianWidth v (B i) - g i x
  let δ : ℝ≥0 := ⟨q * r, (mul_pos hq hr).le⟩
  have hg (i : Fin (m + 1)) : Integrable (g i) γ :=
    integrable_finiteSup (fun t => integrable_linear (w i t))
  have hg_eq (i : Fin (m + 1)) (x : E) :
      g i x = (⨆ t : B i, v t x) - v (c i) x :=
    sup_sub_eq (fun t : B i => v t x) (v (c i) x)
  have hmean (i : Fin (m + 1)) : (∫ x, g i x ∂γ) = gaussianWidth v (B i) := by
    simp_rw [hg_eq]
    rw [integral_sub (integrable_finiteSup (fun t : B i => integrable_linear (v t)))
      (integrable_linear (v (c i))), integral_linear, sub_zero]
    rfl
  have herr (i : Fin (m + 1)) : Integrable (err i) γ :=
    (integrable_const _).sub (hg i)
  have hlip (i : Fin (m + 1)) : LipschitzWith δ (g i) := by
    refine lipschitz_finiteSup_linear (w i) fun t => ?_
    change ‖v t - v (c i)‖ ≤ q * r
    rw [← dist_eq_norm, hv]
    exact (hB i).2.2.1 t.2
  have hsub (i : Fin (m + 1)) : HasSubgaussianMGF (err i) (δ ^ 2) γ := by
    have h := (HighDimensionalStatisticsWanted.lipschitz_concentration_stdGaussian (hlip i)).1.neg
    rw [hmean i] at h
    simpa only [Pi.neg_def, neg_sub] using h
  have herr_bound :=
    expected_finiteSup_le err herr hsub (show 0 < δ from mul_pos hq hr)
      (by simpa only [Fintype.card_fin] using (show 1 < m + 1 by omega))
  rw [Fintype.card_fin] at herr_bound
  have hcenter := hSud n m (fun i => v (c i)) r hr.le fun i j hij => by
    rw [hv]; exact hsep i j hij
  have hpt (x : E) :
      (⨆ i, v (c i) x) + b - (⨆ i, err i x) ≤ (⨆ t : A, v t x) := by
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => v (c i) x)
    rw [← hi]
    have hsub : (⨆ t : B i, v t x) ≤ (⨆ t : A, v t x) :=
      ciSup_le fun t => le_finiteSup (fun j : A => v j x) ⟨t, (hB i).2.1 t.2⟩
    have he := le_finiteSup (fun j => err j x) i
    change gaussianWidth v (B i) - g i x ≤ ⨆ j, err j x at he
    linarith only [hsub, he, hg_eq i x, (hB i).2.2.2]
  have hci : Integrable (fun x => ⨆ i, v (c i) x) γ :=
    integrable_finiteSup (fun i => integrable_linear (v (c i)))
  have hei : Integrable (fun x => ⨆ i, err i x) γ := integrable_finiteSup herr
  have hI := integral_mono ((hci.add (integrable_const b)).sub hei)
    (integrable_finiteSup (fun i : A => integrable_linear (v i))) hpt
  rw [integral_sub' (hci.add (integrable_const b)) hei,
    integral_add' hci (integrable_const b), integral_const, probReal_univ, one_smul] at hI
  change (∫ x, ⨆ i, v (c i) x ∂γ) + b - (∫ x, ⨆ i, err i x ∂γ) ≤ gaussianWidth v A at hI
  have hmul := mul_le_mul_of_nonneg_right hqL
    (show 0 ≤ r * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ)) by positivity)
  change (∫ x, ⨆ i, err i x ∂γ) ≤ 2 * (q * r) * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ))
    at herr_bound
  have heq : r * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ)) / (2 * L) =
      r / L * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ)) -
        (1 / 2 / L) * (r * Real.sqrt (Real.log ((m + 1 : ℕ) : ℝ))) := by
    ring
  rw [heq]
  linarith only [hI, hcenter, herr_bound, hmul]

end StandardGaussian


/-- Represent a centered finite Gaussian process by continuous linear forms of a standard
Gaussian vector. The equality concerns the entire vector law, including singular laws. -/
private lemma exists_gaussian_linear_law {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : T → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hG : IsGaussian (P.map fun ω t => X t ω))
    (hcen : ∀ t, ∫ ω, X t ω ∂P = 0) :
    ∃ v : T → StrongDual ℝ (EuclideanSpace ℝ (Fin (Fintype.card T))),
      (stdGaussian (EuclideanSpace ℝ (Fin (Fintype.card T)))).map (fun x t => v t x) =
        P.map (fun ω t => X t ω) := by
  classical
  let Z : Ω → T → ℝ := fun ω t => X t ω
  let V := EuclideanSpace ℝ (Fin (Fintype.card T))
  let e₁ := Fintype.equivFin T
  let e : (T → ℝ) ≃L[ℝ] V :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) e₁).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ => ℝ)).symm
  let Y : Ω → V := fun ω => e (Z ω)
  have hZ : Measurable Z := Measurable.of_eval hX
  have hY : Measurable Y := e.continuous.measurable.comp hZ
  have hY_map : P.map Y = (P.map Z).map e := by
    rw [Measure.map_map e.continuous.measurable hZ]
    rfl
  have hGY : IsGaussian (P.map Y) := hY_map ▸
    (isGaussian_map_of_measurable (L := e.toContinuousLinearMap) e.continuous.measurable)
  have hYlaw : HasGaussianLaw Y P := ⟨hY.aemeasurable, hGY⟩
  have hYmean : ∫ ω, Y ω ∂P = 0 := by
    change (∫ ω, e (Z ω) ∂P) = 0
    have hZ_i (t : T) : Integrable (X t) P := by
      let L : (T → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj t
      exact (integrable_map_measure L.continuous.aestronglyMeasurable hZ.aemeasurable).mp
        (IsGaussian.integrable_dual (P.map Z) L)
    have hZ0 : (∫ ω, Z ω ∂P) = 0 := by
      funext t
      rw [eval_integral hZ_i t]
      exact hcen t
    rw [e.integral_comp_comm, hZ0, map_zero]
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal hYlaw.memLp_two
  have hmap : (stdGaussian V).map A = P.map Y := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_map_eq_charFun_map_inner_one A.continuous.aemeasurable,
      charFun_map_eq_charFun_map_inner_one hY.aemeasurable, (hA t).map_eq]
    have hP : P.map (fun ω => ⟪Y ω, t⟫_ℝ) =
        gaussianReal 0 (Var[fun ω => ⟪Y ω, t⟫_ℝ; P]).toNNReal := by
      let L := innerSL ℝ t
      change P.map (fun ω => ⟪Y ω, t⟫_ℝ) = _
      simp_rw [real_inner_comm t]
      change P.map (L ∘ Y) = gaussianReal 0 (Var[L ∘ Y; P]).toNNReal
      have hLm : Measurable L := L.continuous.measurable
      have hYmean' : (P.map Y)[L] = 0 := by
        rw [integral_map hY.aemeasurable L.continuous.aestronglyMeasurable,
          L.integral_comp_comm hYlaw.integrable, hYmean, map_zero]
      rw [← Measure.map_map hLm hY, IsGaussian.map_eq_gaussianReal, hYmean',
        variance_map hLm.aemeasurable hY.aemeasurable]
    rw [hP]
  refine ⟨fun t => (ContinuousLinearMap.proj t) ∘L e.symm.toContinuousLinearMap ∘L A, ?_⟩
  have he : (fun (x : V) t =>
      ((ContinuousLinearMap.proj t) ∘L e.symm.toContinuousLinearMap ∘L A) x) = e.symm ∘ A := rfl
  rw [he, ← Measure.map_map e.symm.continuous.measurable A.continuous.measurable, hmap,
    Measure.map_map e.symm.continuous.measurable hY]
  congr 1
  funext ω
  exact e.symm_apply_apply (Z ω)

/-- Equal finite process laws give equal expected maxima and equal canonical distances. -/
private lemma eq_integral_sup_and_canonicalDist_of_law {Ω Ω' T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Finite T] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hG : IsGaussian (P.map fun ω t => X t ω))
    (h : P.map (fun ω t => X t ω) = Q.map (fun ω t => Y t ω)) :
    (∫ ω, ⨆ t, X t ω ∂P) = (∫ ω, ⨆ t, Y t ω ∂Q) ∧
      canonicalDist P X = canonicalDist Q Y := by
  have hXv : Measurable (fun ω t => X t ω) := Measurable.of_eval hX
  have hYv : Measurable (fun ω t => Y t ω) := Measurable.of_eval hY
  have hG' : IsGaussian (Q.map fun ω t => Y t ω) := h ▸ hG
  constructor
  · have hs : Measurable (fun x : T → ℝ => ⨆ t, x t) :=
      Measurable.iSup fun t => measurable_pi_apply t
    have hE := congrArg (fun (μ : Measure (T → ℝ)) => ∫ x, (⨆ t, x t) ∂μ) h
    rwa [integral_map hXv.aemeasurable hs.aestronglyMeasurable,
      integral_map hYv.aemeasurable hs.aestronglyMeasurable] at hE
  · funext s t
    rw [canonicalDist_eq_ofReal_sqrt (memLp_sub_of_isGaussian P X hX hG s t),
      canonicalDist_eq_ofReal_sqrt (memLp_sub_of_isGaussian Q Y hY hG' s t)]
    have hE := congrArg (fun (μ : Measure (T → ℝ)) => ∫ x, (x s - x t)^2 ∂μ) h
    have hm : Measurable (fun x : T → ℝ => (x s - x t)^2) :=
      ((measurable_pi_apply s).sub (measurable_pi_apply t)).pow_const 2
    rw [integral_map hXv.aemeasurable hm.aestronglyMeasurable,
      integral_map hYv.aemeasurable hm.aestronglyMeasurable] at hE
    simp only [hE]
/-- Repeated linear forms give the same maximum and canonical distance as the set of forms. -/
private lemma bounds_for_linear_family {T : Type*} [Finite T] [Nonempty T] {n : ℕ}
    (v : T → StrongDual ℝ (EuclideanSpace ℝ (Fin n))) {L a : ℝ}
    (hL : 0 < L) (hSud : SudakovConstant L) (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (haL : 2 * (2 * a) ≤ 1 / 2 / L) :
    let P := stdGaussian (EuclideanSpace ℝ (Fin n))
    let X := fun t x => v t x
    gammaFunctional 2 (canonicalDist P X) ≤
        ENNReal.ofReal (128 * (2 * L) + 64 * (2 * L) / a) *
          ENNReal.ofReal (∫ x, ⨆ t, X t x ∂P) ∧
      ENNReal.ofReal (∫ x, ⨆ t, X t x ∂P) ≤ 10 * gammaFunctional 2 (canonicalDist P X) := by
  let P := stdGaussian (EuclideanSpace ℝ (Fin n))
  let S := Set.range v
  let f : T → S := fun t => ⟨v t, Set.mem_range_self t⟩
  have hf : Function.Surjective f := fun ⟨s, t, ht⟩ => ⟨t, Subtype.ext ht⟩
  let : Nonempty S := Nonempty.map f ‹Nonempty T›
  let w : S → StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := Subtype.val
  let Y := fun (s : S) x => w s x
  have hv : ∀ s t, dist (w s) (w t) = dist s t := fun _ _ => rfl
  have hY (s : S) : Measurable (Y s) := (w s).continuous.measurable
  have hG : IsGaussian (P.map fun x s => Y s x) := gaussian_family w
  have hg : HasGrowth (gaussianWidth w) (2 * a) (2 * L) :=
    gaussianWidth_growth w hv hSud (by positivity) haL
  have hlow :=
    growth_gamma_bound (gaussianWidth w) ha ha2 (show 0 < 2 * L by positivity)
      (gaussianWidth_nonneg w) (gaussianWidth_mono w) hg
  have hmax (x : EuclideanSpace ℝ (Fin n)) : (⨆ t, v t x) = ⨆ s, Y s x :=
    hf.iSup_congr f (fun _ => rfl)
  have hwidth : gaussianWidth w Set.univ = ∫ x, ⨆ s, Y s x ∂P := by
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    have hs : Function.Surjective (Subtype.val : ↥(Set.univ : Set S) → S) :=
      fun s => ⟨⟨s, Set.mem_univ s⟩, rfl⟩
    exact hs.iSup_congr Subtype.val (fun _ => rfl)
  rw [hwidth, ENNReal.ofReal_mul (by positivity)] at hlow
  have hdist (s t : S) : dist s t = Real.sqrt (∫ x, (Y s x - Y t x)^2 ∂P) := by
    have h := linear_canonicalDist w s t
    rw [hv, canonicalDist_eq_ofReal_sqrt (memLp_sub_of_isGaussian P Y hY hG s t)] at h
    exact ((ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp h.ge).antisymm
      ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h.le)
  have hupp := integral_iSup_le_gammaTwo_of_isGaussian P Y hY hG
    (fun s => integral_linear (w s)) hdist
  have hcanon : canonicalDist P (fun t x => v t x) = fun s t => edist (f s) (f t) := by
    funext s t
    rw [linear_canonicalDist, edist_dist]
    rfl
  change gammaFunctional 2 (canonicalDist P (fun t x => v t x)) ≤
      ENNReal.ofReal (128 * (2 * L) + 64 * (2 * L) / a) *
        ENNReal.ofReal (∫ x, ⨆ t, v t x ∂P) ∧
    ENNReal.ofReal (∫ x, ⨆ t, v t x ∂P) ≤
      10 * gammaFunctional 2 (canonicalDist P (fun t x => v t x))
  simp_rw [hmax, hcanon, gamma_pullback_eq hf]
  exact ⟨hlow, hupp⟩

@[expose] public section

/-- **Majorizing measure theorem** (Fernique–Talagrand; Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, Theorem 2.10.1). There is a universal constant `L > 0`
such that for every centred Gaussian process `(X_t)_{t ∈ T}` indexed by a finite nonempty set,
with canonical distance `d`, `γ₂(T, d) / L ≤ E sup_{t ∈ T} X_t ≤ L γ₂(T, d)`. The right-hand
inequality is the generic chaining bound; the left-hand one is the content of the theorem. -/
theorem majorizing_measure :
    ∃ L : ℝ, 0 < L ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (T : Type*) [Fintype T] [Nonempty T] (X : T → Ω → ℝ),
      (∀ t, Measurable (X t)) → IsGaussian (P.map fun ω t => X t ω) →
      (∀ t, ∫ ω, X t ω ∂P = 0) →
        gammaFunctional 2 (canonicalDist P X) ≤
            ENNReal.ofReal L * ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ∧
          ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤
            ENNReal.ofReal L * gammaFunctional 2 (canonicalDist P X) := by
  obtain ⟨L₁, hL₁, hSud⟩ := exists_sudakovConstant
  let a : ℝ := min (1 / 4) (1 / (8 * L₁))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha2 : a ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have haL : 2 * (2 * a) ≤ 1 / 2 / L₁ := by
    apply (le_div_iff₀ hL₁).mpr
    have h := (le_div_iff₀ (show 0 < 8 * L₁ by positivity)).mp
      (min_le_right (1 / 4 : ℝ) (1 / (8 * L₁)))
    change a * (8 * L₁) ≤ 1 at h
    nlinarith only [h]
  let C := 128 * (2 * L₁) + 64 * (2 * L₁) / a
  refine ⟨max 10 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Ω _ P _ T _ _ X hX hG hcen
  obtain ⟨v, hv⟩ := exists_gaussian_linear_law P X hX hG hcen
  obtain ⟨hmean, hdist⟩ := eq_integral_sup_and_canonicalDist_of_law X (fun t x => v t x)
    hX (fun t => (v t).continuous.measurable) hG hv.symm
  rw [hmean, hdist]
  obtain ⟨hlo, hup⟩ := bounds_for_linear_family v hL₁ hSud ha ha2 haL
  refine ⟨hlo.trans ?_, hup.trans ?_⟩
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right 10 C)) _
  · exact mul_le_mul_left (by
      rw [← ENNReal.ofReal_ofNat (n := 10)]
      exact ENNReal.ofReal_le_ofReal (le_max_left 10 C)) _

end

end MathlibExt.Probability.MajorizingMeasureWanted
