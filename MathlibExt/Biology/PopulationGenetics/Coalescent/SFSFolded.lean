/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Total branch length and the folded site frequency spectrum

The total branch length decomposes over the frequency classes of the site
frequency spectrum: pathwise, the sum of `L_i = sfsLength n i ps T` over
`1 ≤ i < n` equals `KingmanTimes.totalLength`.

Without an outgroup, derived counts are folded by
`η_i = ξ_i + ξ_{n-i}` for `2i < n` and `η_{n/2} = ξ_{n/2}`. From Fu's
`E ξ_i = θ / i`, linearity gives
`E η_i = θ (1 / i + 1 / (n - i)) / (1 + δ_{i, n-i})`.

## References

* Y.-X. Fu, *Statistical properties of segregating sites*, Theoretical
  Population Biology 48 (1995), 172–197.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-- Counting blocks by size over `[1, n)` counts every block once: if a list of
block sizes has positive entries summing to `n` and at least two blocks, every
entry lies in `[1, n - 1]`, so `∑_{i=1}^{n-1} #{blocks of size i}` is the number
of blocks. -/
theorem sum_count_Ico_eq_length {n : ℕ} {b : List ℕ} (hpos : ∀ x ∈ b, 1 ≤ x)
    (hsum : b.sum = n) (hlen : 2 ≤ b.length) :
    ∑ i ∈ Finset.Ico 1 n, b.count i = b.length := by
  have hle : ∀ (l : List ℕ), (∀ y ∈ l, 1 ≤ y) → l.length ≤ l.sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha : 1 ≤ a := hl a (by simp)
      have ht : t.length ≤ t.sum := ih (fun y hy => hl y (by simp [hy]))
      simp only [List.length_cons, List.sum_cons]
      omega
  have hmem : ∀ x ∈ b, x ∈ Finset.Ico 1 n := by
    intro x hx
    rw [Finset.mem_Ico]
    refine ⟨hpos x hx, ?_⟩
    have h1 : x + (b.erase x).sum = b.sum := List.sum_erase hx
    have hlen' : (b.erase x).length = b.length - 1 := List.length_erase_of_mem hx
    have hle' : (b.erase x).length ≤ (b.erase x).sum :=
      hle _ (fun y hy => hpos y (List.mem_of_mem_erase hy))
    omega
  have key : ∀ (l : List ℕ), (∀ x ∈ l, x ∈ Finset.Ico 1 n) →
      ∑ i ∈ Finset.Ico 1 n, l.count i = l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      have ha : a ∈ Finset.Ico 1 n := hl a (by simp)
      have ht : ∀ x ∈ t, x ∈ Finset.Ico 1 n :=
        fun x hx => hl x (by simp [hx])
      have hcount : ∀ i : ℕ, (a :: t).count i = t.count i + (if a = i then 1 else 0) := by
        intro i
        rw [List.count_cons]
        by_cases h : a = i
        · subst h
          simp
        · simp [h]
      calc ∑ i ∈ Finset.Ico 1 n, (a :: t).count i
          = ∑ i ∈ Finset.Ico 1 n, (t.count i + (if a = i then 1 else 0)) :=
            Finset.sum_congr rfl (fun i _ => hcount i)
        _ = (∑ i ∈ Finset.Ico 1 n, t.count i) + ∑ i ∈ Finset.Ico 1 n, (if a = i then 1 else 0) :=
            Finset.sum_add_distrib
        _ = t.length + 1 := by rw [ih ht, Finset.sum_ite_eq _ _ _]; simp [ha]
        _ = (a :: t).length := by simp
  exact key b hmem

/-- Pathwise decomposition of the total branch length over frequency classes,
in the unfolded form of `sfsLength` and `KingmanTimes.totalLength`: if for every
`k ∈ [2, n]` the block-size list `ps.getD (n - k) []` has `k` positive entries
summing to `n` (as every list visited by random joining from `n` singletons
does), then for all holding times `T`,
`∑_{i=1}^{n-1} ∑_{k=2}^{n} #{blocks of size i among k} · T k = ∑_{k=2}^{n} k · T k`,
i.e. `∑_i L_i = L`. -/
theorem sum_sum_count_mul_eq_sum_mul {n : ℕ} (ps : List (List ℕ)) (T : ℕ → ℝ)
    (hpos : ∀ k ∈ Finset.Icc 2 n, ∀ x ∈ ps.getD (n - k) [], 1 ≤ x)
    (hsum : ∀ k ∈ Finset.Icc 2 n, (ps.getD (n - k) []).sum = n)
    (hlen : ∀ k ∈ Finset.Icc 2 n, (ps.getD (n - k) []).length = k) :
    ∑ i ∈ Finset.Ico 1 n, ∑ k ∈ Finset.Icc 2 n, ((ps.getD (n - k) []).count i : ℝ) * T k =
      ∑ k ∈ Finset.Icc 2 n, (k : ℝ) * T k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have h1 := hlen k hk
  have hinner : ∑ i ∈ Finset.Ico 1 n, ((ps.getD (n - k) []).count i : ℝ)
      = ((ps.getD (n - k) []).length : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    exact sum_count_Ico_eq_length (hpos k hk) (hsum k hk) (by omega)
  calc ∑ i ∈ Finset.Ico 1 n, ((ps.getD (n - k) []).count i : ℝ) * T k
      = (∑ i ∈ Finset.Ico 1 n, ((ps.getD (n - k) []).count i : ℝ)) * T k :=
        (Finset.sum_mul _ _ _).symm
    _ = (k : ℝ) * T k := by rw [hinner, h1]

/-- The folded site frequency spectrum (Fu 1995) of the unfolded counts `ξ`:
for `1 ≤ i ≤ n / 2`, `η_i = ξ_i + ξ_{n-i}` when `2 * i < n` and
`η_{n/2} = ξ_{n/2}` when `2 * i = n`. Values outside `1 ≤ i ≤ n / 2` are not
meaningful. -/
def foldedCount {Ω : Type*} (n : ℕ) (ξ : ℕ → Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  fun ω => if 2 * i = n then ξ i ω else ξ i ω + ξ (n - i) ω

/-- Expected folded site frequency spectrum: if the unfolded counts are
integrable with `E ξ_j = θ / j` for `1 ≤ j ≤ n - 1` (Fu's expected spectrum),
then for `1 ≤ i ≤ n / 2`,
`E η_i = θ (1 / i + 1 / (n - i)) / (1 + δ_{i, n - i})`. -/
theorem integral_foldedCount {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n i : ℕ} {θ : ℝ} {ξ : ℕ → Ω → ℝ} (hξ_int : ∀ j, Integrable (ξ j) μ)
    (hmean : ∀ j, 1 ≤ j → j < n → ∫ ω, ξ j ω ∂μ = θ / j) (hi : 1 ≤ i) (hin : 2 * i ≤ n) :
    ∫ ω, foldedCount n ξ i ω ∂μ =
      θ * (1 / (i : ℝ) + 1 / ((n : ℝ) - i)) / (1 + if i = n - i then (1 : ℝ) else 0) := by
  have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have hin_le : i ≤ n := by omega
  have hilt : i < n := by omega
  by_cases h : 2 * i = n
  · have heq : i = n - i := by omega
    have hnsub : (n : ℝ) - (i : ℝ) = (i : ℝ) := by
      have h2 : (n : ℝ) = 2 * (i : ℝ) := by exact_mod_cast h.symm
      rw [h2]
      ring
    have hfc : foldedCount n ξ i = ξ i := by
      unfold foldedCount
      simp [h]
    have hite : (if i = n - i then (1 : ℝ) else 0) = 1 := by simp [eq_true heq]
    rw [hfc, hite, hmean i hi hilt, hnsub]
    field_simp [hi0]
  · have hne : i ≠ n - i := by omega
    have h1ni : 1 ≤ n - i := by omega
    have hni_lt : n - i < n := by omega
    have hfc : foldedCount n ξ i = fun ω => ξ i ω + ξ (n - i) ω := by
      unfold foldedCount
      simp [h]
    have hite : (if i = n - i then (1 : ℝ) else 0) = 0 := by simp [eq_false hne]
    rw [hfc, hite]
    rw [integral_add (hξ_int i) (hξ_int (n - i))]
    rw [hmean i hi hilt, hmean (n - i) h1ni hni_lt, Nat.cast_sub hin_le]
    ring

/-! ### Atlas glue -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Pathwise total-length decomposition for a block-size history satisfying
the random-joining support invariant at every level. -/
theorem sum_sfsLength_eq_totalLength_of_invariant {μ : Measure Ω} {n : ℕ}
    (K : KingmanTimes μ n) (ω : Ω) (ps : List (List ℕ))
    (hpos : ∀ k ∈ Finset.Icc 2 n, ∀ x ∈ ps.getD (n - k) [], 1 ≤ x)
    (hsum : ∀ k ∈ Finset.Icc 2 n, (ps.getD (n - k) []).sum = n)
    (hlen : ∀ k ∈ Finset.Icc 2 n, (ps.getD (n - k) []).length = k) :
    ∑ i ∈ Finset.Ico 1 n, sfsLength n i ps (fun k => K.T k ω) = K.totalLength ω := by
  simp only [sfsLength, KingmanTimes.totalLength]
  exact sum_sum_count_mul_eq_sum_mul ps (fun k => K.T k ω) hpos hsum hlen

/-- The support invariant of a random-joining block-size list: all blocks are
positive, their sizes sum to the sample size `n`, and there are `k` blocks. -/
private def levelInvariant (n k : ℕ) (b : List ℕ) : Prop :=
  (∀ x ∈ b, 1 ≤ x) ∧ b.sum = n ∧ b.length = k

private noncomputable instance decidableLevelInvariant (n k : ℕ) (b : List ℕ) :
    Decidable (levelInvariant n k b) :=
  Classical.propDecidable _

private noncomputable instance decidableBadHistory (n : ℕ) :
    DecidablePred fun ps : List (List ℕ) =>
      ¬ ∀ k ∈ Finset.Icc 2 n, levelInvariant n k (ps.getD (n - k) []) :=
  fun _ => Classical.propDecidable _

/-- Indicator of failure of the level invariant. -/
private noncomputable def badIndicator (n k : ℕ) (b : List ℕ) : ℝ :=
  if levelInvariant n k b then 0 else 1

private lemma levelInvariant_perm {n k : ℕ} {l l' : List ℕ} (h : l.Perm l') :
    levelInvariant n k l ↔ levelInvariant n k l' := by
  unfold levelInvariant
  constructor
  · rintro ⟨hpos, hsum, hlen⟩
    refine ⟨fun x hx => hpos x ((List.Perm.mem_iff h).mpr hx), ?_, ?_⟩
    · rw [← hsum]; exact h.sum_eq.symm
    · rw [← hlen]; exact h.length_eq.symm
  · rintro ⟨hpos, hsum, hlen⟩
    refine ⟨fun x hx => hpos x ((List.Perm.mem_iff h).mp hx), ?_, ?_⟩
    · rw [← hsum]; exact h.sum_eq
    · rw [← hlen]; exact h.length_eq

private lemma isSymm_badIndicator (n k : ℕ) : IsSymm (badIndicator n k) := by
  intro l l' h
  by_cases hl : levelInvariant n k l
  · have hl' : levelInvariant n k l' := (levelInvariant_perm h).mp hl
    simp [badIndicator, hl, hl']
  · have hl' : ¬ levelInvariant n k l' :=
      fun h' => hl ((levelInvariant_perm h).mpr h')
    simp [badIndicator, hl, hl']

private lemma joinStep_iterate_badIndicator {n j : ℕ} (hn : 2 ≤ n)
    (hj : j ≤ n - 2) :
    (joinStep^[j] (badIndicator n (n - j))) (List.replicate n 1) = 0 := by
  have h := joinStep_iterate_replicate (N := n) j (by omega)
    (badIndicator n (n - j)) (isSymm_badIndicator n (n - j))
  have hsum : ∑ c ∈ comps n (n - j), badIndicator n (n - j) (List.ofFn c) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := mem_comps.mp hc
    have hInv : levelInvariant n (n - j) (List.ofFn c) := by
      refine ⟨fun x hx => ?_, ?_, ?_⟩
      · obtain ⟨t, ht⟩ := List.mem_ofFn.mp hx
        rw [← ht]
        exact hc'.1 t
      · rw [List.sum_ofFn]; exact hc'.2
      · exact List.length_ofFn ..
    simp [badIndicator, hInv]
  rw [hsum] at h
  have hchoose : (((n - 1).choose j : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (n - 1).choose j := Nat.choose_pos (by omega)
    exact_mod_cast hpos.ne'
  exact (mul_eq_zero.mp h).resolve_right hchoose

private lemma ae_levelInvariant {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {τ : Ω → List (List ℕ)}
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) =
      randomJoining (n - 1) (List.replicate n 1) ps) :
    ∀ᵐ ω ∂μ, ∀ k ∈ Finset.Icc 2 n,
      levelInvariant n k ((τ ω).getD (n - k) []) := by
  obtain ⟨F, hF0, hF⟩ := exists_finset_randomJoining (n - 1) (List.replicate n 1)
  have haeF : ∀ᵐ ω ∂μ, τ ω ∈ F := by
    rw [ae_iff]
    have hset : {ω | ¬ τ ω ∈ F} =
        ⋃ ps : {ps // ps ∉ F}, τ ⁻¹' {ps.1} := by
      ext ω
      simp
    rw [hset]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hF0 _ ps.2]
  have hBad0 : ∀ ps ∈ F.filter (fun ps =>
      ¬ ∀ k ∈ Finset.Icc 2 n, levelInvariant n k (ps.getD (n - k) [])),
      randomJoining (n - 1) (List.replicate n 1) ps = 0 := by
    intro ps hps
    obtain ⟨hpsF, hbad⟩ := Finset.mem_filter.mp hps
    push Not at hbad
    obtain ⟨k, hk, hkbad⟩ := hbad
    have hsum := hF (n - k) (by
      have hkI := Finset.mem_Icc.mp hk
      omega) (badIndicator n k)
    have hnk : n - (n - k) = k := by
      have hkI := Finset.mem_Icc.mp hk
      omega
    have hrhs := joinStep_iterate_badIndicator (n := n) (j := n - k) hn (by
      have hkI := Finset.mem_Icc.mp hk
      omega)
    rw [hnk] at hrhs
    rw [hrhs] at hsum
    have hnonneg : ∀ q ∈ F, 0 ≤
        randomJoining (n - 1) (List.replicate n 1) q *
          badIndicator n k (q.getD (n - k) []) := by
      intro q _
      have hp : 0 ≤ randomJoining (n - 1) (List.replicate n 1) q := by
        rw [← hτ_law q]
        exact measureReal_nonneg
      have hb : 0 ≤ badIndicator n k (q.getD (n - k) []) := by
        unfold badIndicator
        split_ifs <;> norm_num
      exact mul_nonneg hp hb
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum ps hpsF
    have hbad1 : badIndicator n k (ps.getD (n - k) []) = 1 := by
      unfold badIndicator
      rw [if_neg hkbad]
    rwa [hbad1, mul_one] at hterm
  have haeBad : ∀ᵐ ω ∂μ, τ ω ∉ F.filter (fun ps =>
      ¬ ∀ k ∈ Finset.Icc 2 n, levelInvariant n k (ps.getD (n - k) [])) := by
    rw [ae_iff]
    have hset : {ω | ¬ τ ω ∉ F.filter (fun ps =>
        ¬ ∀ k ∈ Finset.Icc 2 n, levelInvariant n k (ps.getD (n - k) []))} =
        ⋃ ps : {ps // ps ∈ F.filter (fun ps =>
          ¬ ∀ k ∈ Finset.Icc 2 n, levelInvariant n k (ps.getD (n - k) []))},
          τ ⁻¹' {ps.1} := by
      ext ω
      simp
    rw [hset]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hBad0 _ ps.2]
  filter_upwards [haeF, haeBad] with ω hFω hBadω
  intro k hk
  by_contra hnot
  apply hBadω
  refine Finset.mem_filter.mpr ⟨hFω, ?_⟩
  push Not
  exact ⟨k, hk, hnot⟩

/-- Pathwise decomposition of total branch length over SFS classes for a
history with the random-joining law, almost surely. This closes the
`∑ i, L_i = L` gap noted for `SFSCovariance`. -/
theorem sum_sfsLength_ae_eq_totalLength {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (K : KingmanTimes μ n) {τ : Ω → List (List ℕ)}
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) =
      randomJoining (n - 1) (List.replicate n 1) ps) :
    ∀ᵐ ω ∂μ, ∑ i ∈ Finset.Ico 1 n,
      sfsLength n i (τ ω) (fun k => K.T k ω) = K.totalLength ω := by
  by_cases hn : 2 ≤ n
  · filter_upwards [ae_levelInvariant hn hτ_law] with ω hω
    exact sum_sfsLength_eq_totalLength_of_invariant K ω (τ ω)
      (fun k hk => (hω k hk).1) (fun k hk => (hω k hk).2.1)
      (fun k hk => (hω k hk).2.2)
  · have hIco : Finset.Ico 1 n = ∅ := Finset.Ico_eq_empty (by omega)
    have hIcc : Finset.Icc 2 n = ∅ := Finset.Icc_eq_empty (by omega)
    filter_upwards with ω
    simp [sfsLength, KingmanTimes.totalLength, hIco, hIcc]

/-- Expected folded site frequency spectrum under the hypotheses of
`integral_sfs`. -/
theorem integral_foldedCount_kingman {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (K : KingmanTimes μ n) (hT : ∀ k, Measurable (K.T k))
    {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) =
      randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : ProbabilityTheory.Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} {ξ : ℕ → Ω → ℝ} (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => K.T k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : 2 * i ≤ n) :
    ∫ ω, foldedCount n ξ i ω ∂μ =
      θ * (1 / (i : ℝ) + 1 / ((n : ℝ) - i)) /
        (1 + if i = n - i then (1 : ℝ) else 0) :=
  integral_foldedCount hξ_int
    (fun j hj hjn => integral_sfs K hT hτ hτ_law h_indep hξ_int hξ hj hjn) hi hin

end MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
