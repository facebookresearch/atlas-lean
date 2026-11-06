/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Analysis.FunctionalAnalysis.PittWanted

/-- `0 < q.toReal` for `1 ≤ q` with `q ≠ ⊤`. -/
private lemma toReal_pos_of_one_le {q : ENNReal} [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    0 < q.toReal := by
  apply ENNReal.toReal_pos _ hq
  exact (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'

/-- `1 ≤ q.toReal` for `1 ≤ q` with `q ≠ ⊤`. -/
private lemma one_le_toReal_of_one_le {q : ENNReal} [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    1 ≤ q.toReal := by
  have h := ENNReal.toReal_le_toReal ENNReal.one_ne_top hq
  simpa using h.mpr (Fact.out : 1 ≤ q)

/-- Head truncation on `ℓ^q`: sum of the first `N` coordinate projections. -/
private noncomputable def truncCLM {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (N : ℕ) : lp (fun _ : ℕ => 𝕜) q →L[𝕜] lp (fun _ : ℕ => 𝕜) q :=
  ∑ i ∈ Finset.range N,
    ((lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) q i).comp
      (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) q i))

/-- Evaluation map applied to a vector is just function application. -/
private lemma evalCLM_apply_eq {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (i : ℕ) (f : lp (fun _ : ℕ => 𝕜) q) :
    (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) q i) f = (f : ∀ _ : ℕ, 𝕜) i := rfl

/-- Pointwise description of the head truncation. -/
private lemma truncCLM_apply {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (N : ℕ) (f : lp (fun _ : ℕ => 𝕜) q) :
    truncCLM (𝕜 := 𝕜) q N f
      = ∑ i ∈ Finset.range N, lp.single q i ((f : ∀ _ : ℕ, 𝕜) i) := by
  unfold truncCLM
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    evalCLM_apply_eq]

/-- A finite sum of compact operators is compact. -/
private lemma isCompactOperator_finset_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (s : Finset ι) (G : ι → E →L[𝕜] F)
    (h : ∀ i ∈ s, IsCompactOperator (G i)) :
    IsCompactOperator ⇑(∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isCompactOperator_zero
  | @insert a s _ ih =>
    rw [Finset.sum_insert ‹_›]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Each head truncation is compact (finite rank). -/
private lemma isCompact_truncCLM {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (N : ℕ) : IsCompactOperator (truncCLM (𝕜 := 𝕜) q N) := by
  unfold truncCLM
  apply isCompactOperator_finset_sum
  intro i _
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) q i)).comp_clm _

/-- Head truncation composed with `T` is compact. -/
private lemma isCompact_trunc_comp {𝕜 : Type*} [RCLike 𝕜] (p q : ENNReal)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (N : ℕ)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q) :
    IsCompactOperator ((truncCLM (𝕜 := 𝕜) q N).comp T) :=
  (isCompact_truncCLM (𝕜 := 𝕜) q N).comp_clm T

/-- Reduction: it suffices that the tail operator norm tends to zero. -/
private lemma pitt_of_tail_opNorm {𝕜 : Type*} [RCLike 𝕜] (p q : ENNReal)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q)
    (h : Filter.Tendsto (fun N => ‖(truncCLM (𝕜 := 𝕜) q N).comp T - T‖)
      Filter.atTop (nhds 0)) :
    IsCompactOperator T := by
  have hT : Filter.Tendsto (fun N => (truncCLM (𝕜 := 𝕜) q N).comp T)
      Filter.atTop (nhds T) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [dist_eq_norm] using h
  exact isCompactOperator_of_tendsto hT
    (Filter.Eventually.of_forall fun N => isCompact_trunc_comp (𝕜 := 𝕜) p q N T)

/-- A finitely supported restriction is norm-nonincreasing. -/
private lemma norm_restrict_le {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (S : Finset ℕ) (f : lp (fun _ : ℕ => 𝕜) q) :
    ‖∑ i ∈ S, lp.single q i ((f : ∀ _ : ℕ, 𝕜) i)‖ ≤ ‖f‖ := by
  have hr : 0 < q.toReal := toReal_pos_of_one_le hq
  have h1 : ‖∑ i ∈ S, lp.single q i ((f : ∀ _ : ℕ, 𝕜) i)‖ ^ q.toReal
      = ∑ i ∈ S, ‖(f : ∀ _ : ℕ, 𝕜) i‖ ^ q.toReal :=
    lp.norm_sum_single hr _ S
  have h2 : ∑ i ∈ S, ‖(f : ∀ _ : ℕ, 𝕜) i‖ ^ q.toReal ≤ ‖f‖ ^ q.toReal :=
    lp.sum_rpow_le_norm_rpow hr f S
  have h3 := (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr).mp
    (h1 ▸ h2)
  exact h3

/-- Head truncations converge pointwise to the identity. -/
private lemma trunc_tendsto {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (f : lp (fun _ : ℕ => 𝕜) q) :
    Filter.Tendsto (fun N => truncCLM (𝕜 := 𝕜) q N f) Filter.atTop (nhds f) := by
  have h : HasSum (fun i => lp.single q i ((f : ∀ _ : ℕ, 𝕜) i)) f :=
    lp.hasSum_single hq f
  rw [show (fun N => truncCLM (𝕜 := 𝕜) q N f)
      = (fun N => ∑ i ∈ Finset.range N, lp.single q i ((f : ∀ _ : ℕ, 𝕜) i))
    from funext fun N => truncCLM_apply (𝕜 := 𝕜) q N f]
  exact h.tendsto_sum_nat

/-- Head truncations are contractions in operator norm. -/
private lemma opNorm_trunc_le_one {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (N : ℕ) : ‖truncCLM (𝕜 := 𝕜) q N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [truncCLM_apply]
  simpa using norm_restrict_le (𝕜 := 𝕜) q hq (Finset.range N) x

/-- A vector equals the sum of its singles over any finite set containing its support. -/
private lemma vec_eq_sum_support {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (t : Finset ℕ) (v : lp (fun _ : ℕ => 𝕜) q)
    (h : ∀ i, ((v : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t) :
    v = ∑ i ∈ t, lp.single q i ((v : ∀ _ : ℕ, 𝕜) i) := by
  have hs : HasSum (fun i => lp.single (E := fun _ : ℕ => 𝕜) q i ((v : ∀ _ : ℕ, 𝕜) i)) v :=
    lp.hasSum_single hq v
  have hz : ∀ b ∉ t, (fun i => lp.single (E := fun _ : ℕ => 𝕜) q i ((v : ∀ _ : ℕ, 𝕜) i)) b
      = 0 := by
    intro b hb
    simp only
    by_cases hvb : ((v : ∀ _ : ℕ, 𝕜) b) = 0
    · rw [hvb]
      have hz2 := map_zero (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) q b)
      rwa [lp.singleContinuousLinearMap_apply] at hz2
    · exact absurd (h b hvb) hb
  exact hs.unique (hasSum_sum_of_ne_finset_zero hz)

/-- A nonzero coordinate of an explicit finite restriction lies in the index set. -/
private lemma mem_of_restrict_ne_zero {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal)
    (S : Finset ℕ) (x : ∀ _ : ℕ, 𝕜) (j : ℕ)
    (hj : (((∑ i ∈ S, lp.single q i (x i) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) j
      ≠ 0)) :
    j ∈ S := by
  by_contra hjS
  apply hj
  have h1 : (((∑ i ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i (x i) : lp (fun _ : ℕ => 𝕜) q)
        : ∀ _ : ℕ, 𝕜))
      = ∑ i ∈ S, Pi.single i (x i) := by
    rw [lp.coeFn_sum]
    apply Finset.sum_congr rfl
    intro i _
    funext k
    exact lp.single_apply (E := fun _ : ℕ => 𝕜) q i (x i) k
  rw [h1]
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact Pi.single_eq_of_ne (M := fun _ : ℕ => 𝕜) (fun he : j = i => hjS (he ▸ hi)) (x i)

/-- Coordinates of a finite sum of `ℓ^q` vectors. -/
private lemma sum_coords {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal)
    {ι : Type*} (S : Finset ι) (v : ι → lp (fun _ : ℕ => 𝕜) q) (i : ℕ) :
    ((((∑ k ∈ S, v k) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i)
      = ∑ k ∈ S, ((v k : ∀ _ : ℕ, 𝕜) i) := by
  rw [lp.coeFn_sum, Finset.sum_apply]

/-- Norm of a sum of vectors with pairwise disjoint finite supports. -/
private lemma norm_sum_disjoint {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {ι : Type*} (S : Finset ι) (t : ι → Finset ℕ)
    (hdisj : (↑S : Set ι).PairwiseDisjoint t)
    (v : ι → lp (fun _ : ℕ => 𝕜) q)
    (hsupp : ∀ k ∈ S, ∀ i, ((v k : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k) :
    ‖∑ k ∈ S, v k‖ ^ q.toReal = ∑ k ∈ S, ‖v k‖ ^ q.toReal := by
  classical
  have hr : 0 < q.toReal := toReal_pos_of_one_le hq
  have hW : ∀ i, ((((∑ k ∈ S, v k) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i) ≠ 0 →
      i ∈ S.biUnion t := by
    intro i hi
    rw [sum_coords (𝕜 := 𝕜) q S v i] at hi
    rw [Finset.mem_biUnion]
    by_contra habs
    apply hi
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hk0 : ((v k : ∀ _ : ℕ, 𝕜) i) = 0
    · exact hk0
    · exact absurd ⟨k, hk, hsupp k hk i hk0⟩ habs
  have hsum := vec_eq_sum_support (𝕜 := 𝕜) q hq (S.biUnion t) (∑ k ∈ S, v k) hW
  rw [hsum, lp.norm_sum_single hr, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro k hk
  have hpt : ∀ i ∈ t k, ((((∑ k' ∈ S, v k') : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i)
      = ((v k : ∀ _ : ℕ, 𝕜) i) := by
    intro i hi
    rw [sum_coords (𝕜 := 𝕜) q S v i, Finset.sum_eq_single k]
    · intro k' hk' hne
      have hdk : Disjoint (t k) (t k') :=
        (hdisj (Finset.mem_coe.mpr hk') (Finset.mem_coe.mpr hk) hne).symm
      have hi' : i ∉ t k' := Finset.disjoint_left.mp hdk hi
      by_cases h0 : ((v k' : ∀ _ : ℕ, 𝕜) i) = 0
      · exact h0
      · exact absurd (hsupp k' hk' i h0) hi'
    · intro hkS
      exact absurd hk hkS
  have hnorm : ‖v k‖ ^ q.toReal
      = ∑ i ∈ t k, ‖((v k : ∀ _ : ℕ, 𝕜) i)‖ ^ q.toReal := by
    conv_lhs => rw [vec_eq_sum_support (𝕜 := 𝕜) q hq (t k) (v k) (hsupp k hk)]
    exact lp.norm_sum_single hr _ _
  rw [hnorm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hpt i hi]

/-- Unimodular scalar rotating `c` onto its norm. -/
private lemma unimodular_rot {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (hc : c ≠ 0) :
    ∃ σ : 𝕜, ‖σ‖ = 1 ∧ σ * c = ((‖c‖ : ℝ) : 𝕜) := by
  have h0 : ((‖c‖ : ℝ) : 𝕜) ≠ 0 := by
    intro hcon
    exact norm_ne_zero_iff.mpr hc (RCLike.ofReal_eq_zero.mp hcon)
  refine ⟨(starRingEnd 𝕜) c / ((‖c‖ : ℝ) : 𝕜), ?_, ?_⟩
  · have habs : |‖c‖| = ‖c‖ := abs_of_nonneg (norm_nonneg c)
    rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal, habs]
    exact div_self (norm_ne_zero_iff.mpr hc)
  · rw [div_mul_eq_mul_div, RCLike.conj_mul, sq, mul_div_cancel_right₀ _ h0]

/-- Quantitative heart of the domain-side hump: disjoint unit blocks on which a continuous
linear functional is large force `(card)^(1 - 1/r) ≤ ‖φ‖ / η`. -/
private lemma card_rpow_le_of_bad_blocks {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {ι : Type*} (S : Finset ι) (t : ι → Finset ℕ)
    (hdisj : (↑S : Set ι).PairwiseDisjoint t)
    (u : ι → lp (fun _ : ℕ => 𝕜) p)
    (hsupp : ∀ k ∈ S, ∀ i, ((u k : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k)
    (φ : lp (fun _ : ℕ => 𝕜) p →L[𝕜] 𝕜) (η : ℝ) (hη : 0 < η)
    (hS : S.Nonempty)
    (hbad : ∀ k ∈ S, η < ‖φ (u k)‖)
    (hunit : ∀ k ∈ S, ‖u k‖ ≤ 1) :
    (S.card : ℝ) ^ (1 - 1 / p.toReal) ≤ ‖φ‖ / η := by
  have hr : 0 < p.toReal := toReal_pos_of_one_le hp
  have hKpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hσ : ∀ k, ∃ σ : 𝕜, (k ∈ S → ‖σ‖ = 1) ∧
      (k ∈ S → σ * φ (u k) = ((‖φ (u k)‖ : ℝ) : 𝕜)) := by
    intro k
    by_cases hk : k ∈ S
    · obtain ⟨σ, hn, he⟩ := unimodular_rot (φ (u k))
        (norm_ne_zero_iff.mp (lt_trans hη (hbad k hk)).ne')
      exact ⟨σ, fun _ => hn, fun _ => he⟩
    · exact ⟨1, fun h => absurd h hk, fun h => absurd h hk⟩
  choose σ hσn hσe using hσ
  have hsupp_s : ∀ k ∈ S, ∀ i,
      ((((σ k • u k) : lp (fun _ : ℕ => 𝕜) p) : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k := by
    intro k hk i hi
    apply hsupp k hk i
    have hσ0 : σ k ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [hσn k hk]; exact one_ne_zero)
    have h1 : ((((σ k • u k) : lp (fun _ : ℕ => 𝕜) p) : ∀ _ : ℕ, 𝕜) i)
        = σ k • ((u k : ∀ _ : ℕ, 𝕜) i) := rfl
    rw [h1] at hi
    by_contra hx0
    apply hi
    rw [hx0, smul_zero]
  have hWnorm : ‖∑ k ∈ S, σ k • u k‖ ^ p.toReal ≤ (S.card : ℝ) := by
    rw [norm_sum_disjoint (𝕜 := 𝕜) p hp S t hdisj _ hsupp_s]
    calc ∑ k ∈ S, ‖σ k • u k‖ ^ p.toReal
        = ∑ k ∈ S, ‖u k‖ ^ p.toReal := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [norm_smul, hσn k hk, one_mul]
      _ ≤ ∑ _k ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          calc ‖u k‖ ^ p.toReal ≤ (1 : ℝ) ^ p.toReal :=
                Real.rpow_le_rpow (norm_nonneg _) (hunit k hk) hr.le
            _ = 1 := Real.one_rpow _
      _ = S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hφW : φ (∑ k ∈ S, σ k • u k) = ((∑ k ∈ S, ‖φ (u k)‖ : ℝ) : 𝕜) := by
    rw [map_sum, RCLike.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul, smul_eq_mul]
    exact hσe k hk
  have hpos : (0 : ℝ) < ∑ k ∈ S, ‖φ (u k)‖ :=
    Finset.sum_pos (fun k hk => lt_trans hη (hbad k hk)) hS
  have hlow : (S.card : ℝ) * η < ‖φ (∑ k ∈ S, σ k • u k)‖ := by
    rw [hφW, RCLike.norm_ofReal, abs_of_pos hpos]
    have hconst : ∑ _k ∈ S, η = (S.card : ℝ) * η := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    apply Finset.sum_lt_sum (fun k hk => (hbad k hk).le)
    obtain ⟨k, hk⟩ := hS
    exact ⟨k, hk, hbad k hk⟩
  have hKr : ((S.card : ℝ) ^ (1 / p.toReal)) ^ p.toReal = S.card := by
    rw [one_div]
    exact Real.rpow_inv_rpow hKpos.le (ne_of_gt hr)
  have hWle : ‖∑ k ∈ S, σ k • u k‖ ≤ (S.card : ℝ) ^ (1 / p.toReal) := by
    have h := (Real.rpow_le_rpow_iff (norm_nonneg _)
      (Real.rpow_nonneg hKpos.le _) hr).mp (by rw [hKr]; exact hWnorm)
    exact h
  have hlt : (S.card : ℝ) * η < ‖φ‖ * (S.card : ℝ) ^ (1 / p.toReal) :=
    lt_of_lt_of_le hlow
      (le_trans (φ.le_opNorm _)
        (mul_le_mul_of_nonneg_left hWle (norm_nonneg _)))
  have hKrpos : (0 : ℝ) < (S.card : ℝ) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos hKpos _
  have hrw : (S.card : ℝ) ^ (1 - 1 / p.toReal)
      = S.card / (S.card : ℝ) ^ (1 / p.toReal) := by
    rw [Real.rpow_sub hKpos, Real.rpow_one]
  rw [hrw, div_le_iff₀ hKrpos, div_mul_eq_mul_div, le_div_iff₀ hη]
  exact hlt.le

/-- Range-side estimate (Step 2): tails of `T` over a fixed head `P_M` are eventually
uniformly small on the unit ball. -/
private lemma eventually_tail_on_range {𝕜 : Type*} [RCLike 𝕜] (p q : ENNReal)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q)
    (M : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a in Filter.atTop, ∀ x : lp (fun _ : ℕ => 𝕜) p, ‖x‖ ≤ 1 →
      ‖T (truncCLM (𝕜 := 𝕜) p M x)
        - truncCLM (𝕜 := 𝕜) q a (T (truncCLM (𝕜 := 𝕜) p M x))‖ ≤ η := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have htail : ∀ i, Filter.Tendsto
      (fun a => ‖T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
        - truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))‖)
      Filter.atTop (nhds 0) := by
    intro i
    have h := trunc_tendsto (𝕜 := 𝕜) q hq
      (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))
    have h2 : Filter.Tendsto
        (fun a => T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
          - truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)))
        Filter.atTop
        (nhds (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
          - T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))) :=
      tendsto_const_nhds.sub h
    simpa using h2.norm
  have hper : ∀ i ∈ Finset.range M, ∀ᶠ a in Filter.atTop,
      ‖T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
        - truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))‖
        ≤ η / ((M : ℝ) + 1) := by
    intro i _
    have hb : (0 : ℝ) < η / ((M : ℝ) + 1) := div_pos hη hM1
    exact ((htail i).eventually (Iio_mem_nhds hb)).mono fun a ha => ha.le
  have hall : ∀ᶠ a in Filter.atTop, ∀ i ∈ Finset.range M,
      ‖T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
        - truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))‖
        ≤ η / ((M : ℝ) + 1) :=
    Finset.eventually_all (Finset.range M) |>.mpr hper
  have hTP : ∀ x : lp (fun _ : ℕ => 𝕜) p,
      T (truncCLM (𝕜 := 𝕜) p M x)
        = ∑ i ∈ Finset.range M,
          ((x : ∀ _ : ℕ, 𝕜) i) • T (lp.single (E := fun _ : ℕ => 𝕜) p i 1) := by
    intro x
    rw [truncCLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e1 : (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) p i) ((x : ∀ _ : ℕ, 𝕜) i)
        = lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i) :=
      lp.singleContinuousLinearMap_apply _ _
    have e2 : (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) p i) 1
        = lp.single (E := fun _ : ℕ => 𝕜) p i 1 :=
      lp.singleContinuousLinearMap_apply _ _
    have h1 : ((x : ∀ _ : ℕ, 𝕜) i) • (1 : 𝕜) = (x : ∀ _ : ℕ, 𝕜) i := by
      rw [smul_eq_mul, mul_one]
    have hthis : lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i)
        = ((x : ∀ _ : ℕ, 𝕜) i) • lp.single (E := fun _ : ℕ => 𝕜) p i 1 := by
      calc lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i)
          = (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) p i)
            (((x : ∀ _ : ℕ, 𝕜) i) • 1) := by rw [h1]; exact e1.symm
        _ = ((x : ∀ _ : ℕ, 𝕜) i) •
            (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) p i) 1 :=
          map_smul _ _ _
        _ = ((x : ∀ _ : ℕ, 𝕜) i) • lp.single (E := fun _ : ℕ => 𝕜) p i 1 := by
          rw [e2]
    rw [hthis, map_smul]
  filter_upwards [hall] with a ha x hx
  have hPa : truncCLM (𝕜 := 𝕜) q a
        (∑ i ∈ Finset.range M,
          ((x : ∀ _ : ℕ, 𝕜) i) • T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))
      = ∑ i ∈ Finset.range M, ((x : ∀ _ : ℕ, 𝕜) i) •
        truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_smul _ _ _
  rw [hTP x, hPa, ← Finset.sum_sub_distrib]
  have hsm : ∀ i ∈ Finset.range M,
      (((x : ∀ _ : ℕ, 𝕜) i) • T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
      - ((x : ∀ _ : ℕ, 𝕜) i) •
        truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)))
      = ((x : ∀ _ : ℕ, 𝕜) i) •
        (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
        - truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))) :=
    fun i _ => (smul_sub _ _ _).symm
  calc ‖∑ i ∈ Finset.range M, (((x : ∀ _ : ℕ, 𝕜) i) •
        T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
        - ((x : ∀ _ : ℕ, 𝕜) i) •
        truncCLM (𝕜 := 𝕜) q a (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)))‖
      ≤ ∑ i ∈ Finset.range M, ‖((x : ∀ _ : ℕ, 𝕜) i) •
        (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
        - truncCLM (𝕜 := 𝕜) q a
          (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)))‖ :=
        le_trans (norm_sum_le _ _)
          (Finset.sum_le_sum (fun i hi =>
            le_of_eq (congrArg (fun z => ‖z‖) (hsm i hi))))
    _ ≤ ∑ _i ∈ Finset.range M, (η / ((M : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        calc ‖((x : ∀ _ : ℕ, 𝕜) i) •
              (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
              - truncCLM (𝕜 := 𝕜) q a
                (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)))‖
            = ‖((x : ∀ _ : ℕ, 𝕜) i)‖ *
              ‖T (lp.single (E := fun _ : ℕ => 𝕜) p i 1)
              - truncCLM (𝕜 := 𝕜) q a
                (T (lp.single (E := fun _ : ℕ => 𝕜) p i 1))‖ := norm_smul _ _
          _ ≤ 1 * (η / ((M : ℝ) + 1)) :=
              mul_le_mul (le_trans (lp.norm_apply_le_norm hp0 x i) hx) (ha i hi)
                (norm_nonneg _) zero_le_one
          _ = η / ((M : ℝ) + 1) := one_mul _
    _ ≤ η := by
        have hsum : ∑ _i ∈ Finset.range M, (η / ((M : ℝ) + 1))
            = (M : ℝ) * (η / ((M : ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [hsum, ← mul_div_assoc, div_le_iff₀ hM1]
        calc (M : ℝ) * η ≤ (M : ℝ) * η + η := le_add_of_nonneg_right hη.le
          _ = η * ((M : ℝ) + 1) := by ring

/-- Coordinates of a head truncation. -/
private lemma truncCLM_coord {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (m i : ℕ) (z : lp (fun _ : ℕ => 𝕜) q) :
    (((truncCLM (𝕜 := 𝕜) q m z : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i)
      = if i < m then ((z : ∀ _ : ℕ, 𝕜) i) else 0 := by
  have hconv : (∑ i' ∈ Finset.range m,
        (((lp.single (E := fun _ : ℕ => 𝕜) q i' ((z : ∀ _ : ℕ, 𝕜) i') :
          lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i))
      = ∑ j ∈ Finset.range m,
        Pi.single (M := fun _ : ℕ => 𝕜) j ((z : ∀ _ : ℕ, 𝕜) j) i := by
    apply Finset.sum_congr rfl
    intro j _
    exact lp.single_apply (E := fun _ : ℕ => 𝕜) _ _ _ _
  rw [truncCLM_apply, sum_coords, hconv]
  by_cases him : i < m
  · simp only [him, ite_true]
    rw [show ((z : ∀ _ : ℕ, 𝕜) i)
        = Pi.single (M := fun _ : ℕ => 𝕜) i ((z : ∀ _ : ℕ, 𝕜) i) i
      from (Pi.single_eq_same (M := fun _ : ℕ => 𝕜) i _).symm]
    apply Finset.sum_eq_single i
    · intro j hj hne
      exact Pi.single_eq_of_ne (M := fun _ : ℕ => 𝕜)
        (fun he : i = j => hne he.symm) _
    · intro habs
      exact absurd (Finset.mem_range.mpr him) habs
  · simp only [him, ite_false]
    apply Finset.sum_eq_zero
    intro j hj
    exact Pi.single_eq_of_ne (M := fun _ : ℕ => 𝕜)
      (fun he : i = j => him (he.symm ▸ Finset.mem_range.mp hj)) _

/-- Tails are norm-nonincreasing. -/
private lemma norm_tail_le {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (n : ℕ) (y : lp (fun _ : ℕ => 𝕜) q) :
    ‖y - truncCLM (𝕜 := 𝕜) q n y‖ ≤ ‖y‖ := by
  have heq : (fun m => truncCLM (𝕜 := 𝕜) q m y - truncCLM (𝕜 := 𝕜) q n y)
      =ᶠ[Filter.atTop]
      (fun m => ∑ i ∈ Finset.Ico n m,
        lp.single (E := fun _ : ℕ => 𝕜) q i ((y : ∀ _ : ℕ, 𝕜) i)) := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hnm
    rw [truncCLM_apply, truncCLM_apply,
      ← Finset.sum_Ico_eq_sub _ hnm]
  have hlim : Filter.Tendsto
      (fun m => ∑ i ∈ Finset.Ico n m,
        lp.single (E := fun _ : ℕ => 𝕜) q i ((y : ∀ _ : ℕ, 𝕜) i))
      Filter.atTop (nhds (y - truncCLM (𝕜 := 𝕜) q n y)) :=
    Filter.Tendsto.congr' heq
      ((trunc_tendsto (𝕜 := 𝕜) q hq y).sub tendsto_const_nhds)
  have hle : ∀ᶠ m in Filter.atTop,
      ‖∑ i ∈ Finset.Ico n m,
        lp.single (E := fun _ : ℕ => 𝕜) q i ((y : ∀ _ : ℕ, 𝕜) i)‖ ≤ ‖y‖ :=
    Filter.Eventually.of_forall fun m => norm_restrict_le _ hq _ _
  exact le_of_tendsto hlim.norm hle

/-- Tails shrink with the truncation index. -/
private lemma antitone_tail_norm {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) {n m : ℕ} (hnm : n ≤ m) (y : lp (fun _ : ℕ => 𝕜) q) :
    ‖y - truncCLM (𝕜 := 𝕜) q m y‖ ≤ ‖y - truncCLM (𝕜 := 𝕜) q n y‖ := by
  have heq : y - truncCLM (𝕜 := 𝕜) q m y
      = (y - truncCLM (𝕜 := 𝕜) q n y)
        - truncCLM (𝕜 := 𝕜) q m (y - truncCLM (𝕜 := 𝕜) q n y) := by
    rw [lp.ext_iff]
    funext i
    simp only [lp.coeFn_sub, Pi.sub_apply, truncCLM_coord]
    by_cases him : i < m
    · by_cases hin : i < n
      · simp only [him, hin, ite_true]
        abel
      · simp only [him, hin, ite_false]
        abel_nf
    · have hin : ¬ i < n := fun h => him (lt_of_lt_of_le h hnm)
      simp only [him, hin, ite_false]
      abel
  rw [heq]
  exact norm_tail_le _ hq _ _

/-- Tail operator norms shrink with the truncation index. -/
private lemma antitone_tail_opNorm {𝕜 : Type*} [RCLike 𝕜] (p q : ENNReal)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q)
    {n m : ℕ} (hnm : n ≤ m) :
    ‖(truncCLM (𝕜 := 𝕜) q m).comp T - T‖
      ≤ ‖(truncCLM (𝕜 := 𝕜) q n).comp T - T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc ‖((truncCLM (𝕜 := 𝕜) q m).comp T - T) x‖
      = ‖T x - truncCLM (𝕜 := 𝕜) q m (T x)‖ := by
        rw [sub_apply, ContinuousLinearMap.comp_apply, norm_sub_rev]
    _ ≤ ‖T x - truncCLM (𝕜 := 𝕜) q n (T x)‖ :=
        antitone_tail_norm _ hq hnm _
    _ ≤ ‖(truncCLM (𝕜 := 𝕜) q n).comp T - T‖ * ‖x‖ := by
        have hle := ContinuousLinearMap.le_opNorm
          ((truncCLM (𝕜 := 𝕜) q n).comp T - T) x
        rwa [sub_apply, ContinuousLinearMap.comp_apply, norm_sub_rev] at hle

/-- Interval restrictions converge to the tail. -/
private lemma ival_tendsto_tail {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    (hq : p ≠ ⊤) (M : ℕ) (x : lp (fun _ : ℕ => 𝕜) p) :
    Filter.Tendsto (fun m => ∑ i ∈ Finset.Ico M m,
      lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i))
      Filter.atTop (nhds (x - truncCLM (𝕜 := 𝕜) p M x)) := by
  have heq : (fun m => truncCLM (𝕜 := 𝕜) p m x - truncCLM (𝕜 := 𝕜) p M x)
      =ᶠ[Filter.atTop] (fun m => ∑ i ∈ Finset.Ico M m,
        lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i)) := by
    filter_upwards [Filter.eventually_ge_atTop M] with m hm
    rw [truncCLM_apply, truncCLM_apply, ← Finset.sum_Ico_eq_sub _ hm]
  exact Filter.Tendsto.congr' heq
    (Filter.Tendsto.sub (trunc_tendsto (𝕜 := 𝕜) p hq x) tendsto_const_nhds)

/-- Head of a tail vanishes. -/
private lemma trunc_of_tail_eq_zero {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    {n m : ℕ} (hnm : n ≤ m) (x : lp (fun _ : ℕ => 𝕜) p) :
    truncCLM (𝕜 := 𝕜) p n (x - truncCLM (𝕜 := 𝕜) p m x) = 0 := by
  rw [lp.ext_iff]
  change (((truncCLM (𝕜 := 𝕜) p n (x - truncCLM (𝕜 := 𝕜) p m x) : lp _ p) : ∀ _ : ℕ, 𝕜)) = _
  funext i
  rw [truncCLM_coord (𝕜 := 𝕜) p n i]
  by_cases hin : i < n
  · have him : i < m := lt_of_lt_of_le hin hnm
    rw [ite_eq_left hin, lp.coeFn_sub, Pi.sub_apply, truncCLM_coord (𝕜 := 𝕜) p m i,
      ite_eq_left him, sub_self]
    simp
  · rw [ite_eq_right hin]
    simp

/-- Tails nest. -/
private lemma tail_tail_eq {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    {M M' : ℕ} (h : M ≤ M') (x : lp (fun _ : ℕ => 𝕜) p) :
    (x - truncCLM (𝕜 := 𝕜) p M' x) - truncCLM (𝕜 := 𝕜) p M (x - truncCLM (𝕜 := 𝕜) p M' x)
      = x - truncCLM (𝕜 := 𝕜) p M' x := by
  rw [trunc_of_tail_eq_zero (𝕜 := 𝕜) p h x, sub_zero]

/-- Good indices are upward closed. -/
private lemma mono_good_domain {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    (hq : p ≠ ⊤) (φ : lp (fun _ : ℕ => 𝕜) p →L[𝕜] 𝕜) (η : ℝ)
    {M M' : ℕ} (h : M ≤ M')
    (hM : ∀ x : lp (fun _ : ℕ => 𝕜) p, ‖x‖ ≤ 1 → ‖φ (x - truncCLM (𝕜 := 𝕜) p M x)‖ ≤ η)
    (x : lp (fun _ : ℕ => 𝕜) p) (hx : ‖x‖ ≤ 1) :
    ‖φ (x - truncCLM (𝕜 := 𝕜) p M' x)‖ ≤ η := by
  have hle : ‖x - truncCLM (𝕜 := 𝕜) p M' x‖ ≤ 1 :=
    le_trans (norm_tail_le (𝕜 := 𝕜) p hq _ _) hx
  have h2 := hM _ hle
  rwa [tail_tail_eq (𝕜 := 𝕜) p h x] at h2

/-- Failure of eventual goodness gives bad vectors everywhere. -/
private lemma bad_all_domain {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    (hq : p ≠ ⊤) (φ : lp (fun _ : ℕ => 𝕜) p →L[𝕜] 𝕜) (η : ℝ)
    (h : ¬ ∀ᶠ M in Filter.atTop, ∀ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 → ‖φ (x - truncCLM (𝕜 := 𝕜) p M x)‖ ≤ η)
    (M : ℕ) : ∃ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 ∧ η < ‖φ (x - truncCLM (𝕜 := 𝕜) p M x)‖ := by
  rw [Filter.not_eventually] at h
  rw [Filter.frequently_atTop] at h
  obtain ⟨M', hMM', hbad⟩ := h M
  have hex : ∃ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 ∧ ¬ ‖φ (x - truncCLM (𝕜 := 𝕜) p M' x)‖ ≤ η := by
    by_contra hcon
    apply hbad
    intro x hx
    by_contra hle
    exact hcon ⟨x, hx, hle⟩
  obtain ⟨x, hx, hle⟩ := hex
  rw [not_le] at hle
  refine ⟨x - truncCLM (𝕜 := 𝕜) p M' x,
    le_trans (norm_tail_le (𝕜 := 𝕜) p hq _ _) hx, ?_⟩
  rwa [tail_tail_eq (𝕜 := 𝕜) p hMM' x]

/-- Domain-side hump: tails are eventually uniformly small for each functional. -/
private lemma domain_eventually {𝕜 : Type*} [RCLike 𝕜] (p : ENNReal) [Fact (1 ≤ p)]
    (hq : p ≠ ⊤) (hr : 1 < p.toReal)
    (φ : lp (fun _ : ℕ => 𝕜) p →L[𝕜] 𝕜) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M in Filter.atTop, ∀ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 → ‖φ (x - truncCLM (𝕜 := 𝕜) p M x)‖ ≤ η := by
  by_contra h
  have hbad : ∀ M : ℕ, ∃ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 ∧ η < ‖φ (x - truncCLM (𝕜 := 𝕜) p M x)‖ :=
    fun M => bad_all_domain (𝕜 := 𝕜) p hq φ η h M
  have hpos : 0 < p.toReal := lt_trans zero_lt_one hr
  have hexp : (0 : ℝ) < 1 - 1 / p.toReal := by
    have h1 : 1 / p.toReal < 1 := (div_lt_one hpos).mpr hr
    linarith
  have htop : Filter.Tendsto (fun K : ℕ => ((K : ℝ) ^ (1 - 1 / p.toReal)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hKev : ∀ᶠ K : ℕ in Filter.atTop, ‖φ‖ / η < ((K : ℝ) ^ (1 - 1 / p.toReal)) :=
    htop.eventually (Filter.eventually_gt_atTop _)
  obtain ⟨K, hKlt, hK1⟩ := (hKev.and (Filter.eventually_ge_atTop 1)).exists
  have build : ∀ J, J ≤ K → ∃ (u : ℕ → lp (fun _ : ℕ => 𝕜) p) (t : ℕ → Finset ℕ) (m : ℕ),
      (∀ k < J, ∀ i, ((u k : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k) ∧
      (∀ k < J, t k ⊆ Finset.range m) ∧
      (∀ k₁ < J, ∀ k₂ < J, k₁ ≠ k₂ → Disjoint (t k₁) (t k₂)) ∧
      (∀ k < J, η < ‖φ (u k)‖) ∧
      (∀ k < J, ‖u k‖ ≤ 1) := by
    intro J
    induction J with
    | zero =>
      intro _
      refine ⟨fun _ => 0, fun _ => ∅, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
    | succ J ih =>
      intro hJ
      have hJle : J ≤ K := by omega
      obtain ⟨u, t, m, hsupp, hsub, hdisj, hbadJ, hunit⟩ := ih hJle
      obtain ⟨x, hx, hlt⟩ := hbad m
      have hlim := ival_tendsto_tail (𝕜 := 𝕜) p hq m x
      have hφlim : Filter.Tendsto
          (fun m' => φ (∑ i ∈ Finset.Ico m m',
            lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i)))
          Filter.atTop (nhds (φ (x - truncCLM (𝕜 := 𝕜) p m x))) :=
        (φ.cont.tendsto _).comp hlim
      have hgap : (0 : ℝ) < ‖φ (x - truncCLM (𝕜 := 𝕜) p m x)‖ - η :=
        sub_pos.mpr hlt
      have hev : ∀ᶠ m' in Filter.atTop,
          dist (φ (∑ i ∈ Finset.Ico m m',
            lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i)))
            (φ (x - truncCLM (𝕜 := 𝕜) p m x)) < ‖φ (x - truncCLM (𝕜 := 𝕜) p m x)‖ - η :=
        (Metric.tendsto_nhds.mp hφlim) _ hgap
      have hev2 := hev.and (Filter.eventually_ge_atTop m)
      obtain ⟨m', hsmall, hmm'⟩ := hev2.exists
      rw [dist_eq_norm] at hsmall
      set blk : lp (fun _ : ℕ => 𝕜) p :=
        ∑ i ∈ Finset.Ico m m', lp.single (E := fun _ : ℕ => 𝕜) p i ((x : ∀ _ : ℕ, 𝕜) i) with hblk
      have hblk_norm : ‖blk‖ ≤ 1 :=
        le_trans (norm_restrict_le (𝕜 := 𝕜) p hq _ _) hx
      have hblk_bad : η < ‖φ blk‖ := by
        have htri : ‖φ (x - truncCLM (𝕜 := 𝕜) p m x)‖
            ≤ ‖φ (x - truncCLM (𝕜 := 𝕜) p m x) - φ blk‖ + ‖φ blk‖ := by
          have hle := norm_add_le (φ (x - truncCLM (𝕜 := 𝕜) p m x) - φ blk) (φ blk)
          rwa [sub_add_cancel] at hle
        rw [norm_sub_rev] at htri
        linarith
      have hD : Disjoint (Finset.range m) (Finset.Ico m m') := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 : i < m := Finset.mem_range.mp hi1
        have h2 : m ≤ i := (Finset.mem_Ico.mp hi2).1
        omega
      have hIcosub : Finset.Ico m m' ⊆ Finset.range m' := by
        intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      refine ⟨Function.update u J blk, Function.update t J (Finset.Ico m m'), m',
        ?_, ?_, ?_, ?_, ?_⟩
      · intro k hk i hi
        by_cases hJJ : k = J
        · rw [hJJ] at hi ⊢
          simp only [Function.update_self] at hi ⊢
          rw [hblk] at hi
          exact mem_of_restrict_ne_zero (𝕜 := 𝕜) p _ _ _ hi
        · have hkJ : k < J := by omega
          rw [Function.update_of_ne hJJ _ _] at hi
          rw [Function.update_of_ne hJJ _ _] at ⊢
          exact hsupp k hkJ i hi
      · intro k hk
        by_cases hJJ : k = J
        · rw [hJJ]
          simp only [Function.update_self]
          exact hIcosub
        · have hkJ : k < J := by omega
          rw [Function.update_of_ne hJJ _ _]
          exact subset_trans (hsub k hkJ) (Finset.range_mono hmm')
      · intro k₁ hk₁ k₂ hk₂ hne
        by_cases h1 : k₁ = J <;> by_cases h2 : k₂ = J
        · exact absurd (h1.trans h2.symm) hne
        · rw [h1, Function.update_self, Function.update_of_ne h2 _ _]
          exact (hD.symm.mono subset_rfl (hsub k₂ (by omega)))
        · rw [h2, Function.update_self, Function.update_of_ne h1 _ _]
          exact (hD.mono (hsub k₁ (by omega)) subset_rfl)
        · rw [Function.update_of_ne h1 _ _, Function.update_of_ne h2 _ _]
          exact hdisj k₁ (by omega) k₂ (by omega) hne
      · intro k hk
        by_cases hJJ : k = J
        · rw [hJJ]
          simp only [Function.update_self]
          exact hblk_bad
        · have hkJ : k < J := by omega
          rw [Function.update_of_ne hJJ _ _]
          exact hbadJ k hkJ
      · intro k hk
        by_cases hJJ : k = J
        · rw [hJJ]
          simp only [Function.update_self]
          exact hblk_norm
        · have hkJ : k < J := by omega
          rw [Function.update_of_ne hJJ _ _]
          exact hunit k hkJ
  obtain ⟨u, t, m, hsupp, hsub, hdisj, hbadK, hunit⟩ := build K le_rfl
  have hS : (Finset.range K).Nonempty :=
    Finset.nonempty_range_iff.mpr (by omega)
  have hdisjS : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) t := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    exact hdisj a ha b hb hab
  have hsuppS : ∀ k ∈ Finset.range K, ∀ i, ((u k : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k :=
    fun k hk => hsupp k (Finset.mem_range.mp hk)
  have hbadS : ∀ k ∈ Finset.range K, η < ‖φ (u k)‖ :=
    fun k hk => hbadK k (Finset.mem_range.mp hk)
  have hunitS : ∀ k ∈ Finset.range K, ‖u k‖ ≤ 1 :=
    fun k hk => hunit k (Finset.mem_range.mp hk)
  have hle := card_rpow_le_of_bad_blocks (𝕜 := 𝕜) p hq _ t hdisjS u hsuppS φ η hη hS hbadS hunitS
  rw [Finset.card_range] at hle
  exact (not_le.mpr hKlt) hle

/-- Finite heads of `T` on domain tails are eventually uniformly small. -/
private lemma head_on_tail {𝕜 : Type*} [RCLike 𝕜] (p q : ENNReal)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hr : 1 < p.toReal)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q)
    (c : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M in Filter.atTop, ∀ x : lp (fun _ : ℕ => 𝕜) p, ‖x‖ ≤ 1 →
      ‖truncCLM (𝕜 := 𝕜) q c (T (x - truncCLM (𝕜 := 𝕜) p M x))‖ ≤ η := by
  have hq0 : (0 : ENNReal) < q := zero_lt_one.trans_le (Fact.out : 1 ≤ q)
  have hM1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hηc : (0 : ℝ) < η / ((c : ℝ) + 1) := div_pos hη hM1
  have hper : ∀ i ∈ Finset.range c, ∀ᶠ M in Filter.atTop, ∀ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 → ‖(((T (x - truncCLM (𝕜 := 𝕜) p M x) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i)‖
        ≤ η / ((c : ℝ) + 1) := by
    intro i _
    have h := domain_eventually (𝕜 := 𝕜) p hp hr
      ((lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) q i).comp T) hηc
    filter_upwards [h] with M hM x hx
    exact hM x hx
  have hall : ∀ᶠ M in Filter.atTop, ∀ i ∈ Finset.range c, ∀ x : lp (fun _ : ℕ => 𝕜) p,
      ‖x‖ ≤ 1 → ‖(((T (x - truncCLM (𝕜 := 𝕜) p M x) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i)‖
        ≤ η / ((c : ℝ) + 1) :=
    Finset.eventually_all (Finset.range c) |>.mpr hper
  filter_upwards [hall] with M hM x hx
  rw [truncCLM_apply]
  calc ‖∑ i ∈ Finset.range c,
        lp.single (E := fun _ : ℕ => 𝕜) q i
          ((((T (x - truncCLM (𝕜 := 𝕜) p M x) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i))‖
      ≤ ∑ i ∈ Finset.range c,
        ‖lp.single (E := fun _ : ℕ => 𝕜) q i
          ((((T (x - truncCLM (𝕜 := 𝕜) p M x) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i))‖ :=
        norm_sum_le _ _
    _ = ∑ i ∈ Finset.range c,
        ‖((((T (x - truncCLM (𝕜 := 𝕜) p M x) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜) i))‖ := by
        apply Finset.sum_congr rfl
        intro i _
        exact lp.norm_single (E := fun _ : ℕ => 𝕜) hq0 i _
    _ ≤ ∑ _i ∈ Finset.range c, (η / ((c : ℝ) + 1)) :=
        Finset.sum_le_sum (fun i hi => hM i hi x hx)
    _ ≤ η := by
        have hsum : ∑ _i ∈ Finset.range c, (η / ((c : ℝ) + 1))
            = (c : ℝ) * (η / ((c : ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [hsum, ← mul_div_assoc, div_le_iff₀ hM1]
        calc (c : ℝ) * η ≤ (c : ℝ) * η + η := le_add_of_nonneg_right hη.le
          _ = η * ((c : ℝ) + 1) := by ring

/-- Values of a continuous linear map along a convergent sequence are eventually close to the
limit value from below in norm. -/
private lemma eventually_norm_sub_lt {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (u : ℕ → E) (y₀ : E)
    (hlim : Filter.Tendsto u Filter.atTop (nhds y₀))
    {gap : ℝ} (hgap : 0 < gap) :
    ∀ᶠ m' in Filter.atTop, ‖f y₀‖ - gap < ‖f (u m')‖ := by
  have h : Filter.Tendsto (fun m' => f (u m')) Filter.atTop (nhds (f y₀)) :=
    (f.cont.tendsto _).comp hlim
  have hev : ∀ᶠ m' in Filter.atTop, dist (f (u m')) (f y₀) < gap :=
    (Metric.tendsto_nhds.mp h _ hgap)
  filter_upwards [hev] with m' hm'
  rw [dist_eq_norm] at hm'
  have htri : ‖f y₀‖ ≤ ‖f y₀ - f (u m')‖ + ‖f (u m')‖ := by
    have hle := norm_add_le (f y₀ - f (u m')) (f (u m'))
    rwa [sub_add_cancel] at hle
  rw [norm_sub_rev] at htri
  linarith [hm', htri]

/-- Values of a continuous linear map along a convergent sequence are eventually close to the
limit value from above in norm. -/
private lemma eventually_norm_le_add {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (u : ℕ → E) (y₀ : E)
    (hlim : Filter.Tendsto u Filter.atTop (nhds y₀))
    {gap : ℝ} (hgap : 0 < gap) :
    ∀ᶠ m' in Filter.atTop, ‖f (u m')‖ ≤ ‖f y₀‖ + gap := by
  have h : Filter.Tendsto (fun m' => f (u m')) Filter.atTop (nhds (f y₀)) :=
    (f.cont.tendsto _).comp hlim
  have hev : ∀ᶠ m' in Filter.atTop, dist (f (u m')) (f y₀) < gap :=
    (Metric.tendsto_nhds.mp h _ hgap)
  filter_upwards [hev] with m' hm'
  rw [dist_eq_norm] at hm'
  have htri : ‖f (u m')‖ ≤ ‖f (u m') - f y₀‖ + ‖f y₀‖ := by
    have hle := norm_add_le (f (u m') - f y₀) (f y₀)
    rwa [sub_add_cancel] at hle
  linarith [hm', htri]

/-- Tails at a fixed vector are eventually uniformly small. -/
private lemma eventually_tail_small {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (y : lp (fun _ : ℕ => 𝕜) q) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in Filter.atTop, ‖y - truncCLM (𝕜 := 𝕜) q n y‖ ≤ η := by
  have h := trunc_tendsto (𝕜 := 𝕜) q hq y
  have h2 : Filter.Tendsto (fun n => y - truncCLM (𝕜 := 𝕜) q n y)
      Filter.atTop (nhds 0) := by
    have h3 : Filter.Tendsto (fun n => y - truncCLM (𝕜 := 𝕜) q n y)
        Filter.atTop (nhds (y - y)) :=
      tendsto_const_nhds.sub h
    simpa using h3
  have h4 : Filter.Tendsto (fun n => ‖y - truncCLM (𝕜 := 𝕜) q n y‖)
      Filter.atTop (nhds 0) := by
    simpa using h2.norm
  exact (h4.eventually (Iio_mem_nhds hη)).mono fun n hn => hn.le

/-- The difference of two head truncations is the interval restriction. -/
private lemma trunc_sub_eq_ival {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    {a b : ℕ} (hab : a ≤ b) (y : lp (fun _ : ℕ => 𝕜) q) :
    truncCLM (𝕜 := 𝕜) q b y - truncCLM (𝕜 := 𝕜) q a y
      = ∑ i ∈ Finset.Ico a b,
        lp.single (E := fun _ : ℕ => 𝕜) q i (((y : ∀ _ : ℕ, 𝕜)) i) := by
  rw [truncCLM_apply, truncCLM_apply, ← Finset.sum_Ico_eq_sub _ hab]

/-- A head interval is disjoint from the tail interval starting at its end. -/
private lemma disjoint_range_Ico (n m : ℕ) :
    Disjoint (Finset.range n) (Finset.Ico n m) := by
  rw [Finset.disjoint_left]
  intro i hi1 hi2
  have h1 : i < n := Finset.mem_range.mp hi1
  have h2 : n ≤ i := (Finset.mem_Ico.mp hi2).1
  omega

/-- A restriction inside a head is bounded by the head truncation. -/
private lemma restrict_le_trunc {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (S : Finset ℕ) (n : ℕ) (f : lp (fun _ : ℕ => 𝕜) q)
    (h : S ⊆ Finset.range n) :
    ‖∑ i ∈ S, lp.single q i (((f : ∀ _ : ℕ, 𝕜)) i)‖
      ≤ ‖truncCLM (𝕜 := 𝕜) q n f‖ := by
  have hcoord : ∀ i ∈ S,
      ((((truncCLM (𝕜 := 𝕜) q n f : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)
        = ((f : ∀ _ : ℕ, 𝕜) i) := by
    intro i hi
    rw [truncCLM_coord]
    have hin : i < n := Finset.mem_range.mp (h hi)
    simp only [hin, ite_true]
  have heq : (∑ i ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i (((f : ∀ _ : ℕ, 𝕜)) i))
      = ∑ i ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((truncCLM (𝕜 := 𝕜) q n f : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i hi]
  rw [heq]
  exact norm_restrict_le (𝕜 := 𝕜) q hq S _

/-- A restriction above a cutoff is bounded by the tail. -/
private lemma restrict_le_tail {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (S : Finset ℕ) (n : ℕ) (f : lp (fun _ : ℕ => 𝕜) q)
    (h : Disjoint S (Finset.range n)) :
    ‖∑ i ∈ S, lp.single q i (((f : ∀ _ : ℕ, 𝕜)) i)‖
      ≤ ‖f - truncCLM (𝕜 := 𝕜) q n f‖ := by
  have hcoord : ∀ i ∈ S,
      ((((f - truncCLM (𝕜 := 𝕜) q n f : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)
        = ((f : ∀ _ : ℕ, 𝕜) i) := by
    intro i hi
    have hin : i ∉ Finset.range n := Finset.disjoint_left.mp h hi
    have hlt : ¬ i < n := fun hh => hin (Finset.mem_range.mpr hh)
    rw [lp.coeFn_sub, Pi.sub_apply, truncCLM_coord]
    simp only [hlt, ite_false, sub_zero]
  have heq : (∑ i ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i (((f : ∀ _ : ℕ, 𝕜)) i))
      = ∑ i ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((f - truncCLM (𝕜 := 𝕜) q n f : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i hi]
  rw [heq]
  exact norm_restrict_le (𝕜 := 𝕜) q hq S _

/-- Restriction commutes with finite sums of vectors. -/
private lemma restrict_sum {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    {ι : Type*} (W : Finset ℕ) (S : Finset ι) (g : ι → lp (fun _ : ℕ => 𝕜) q) :
    (∑ i ∈ W, lp.single q i
        ((((∑ k ∈ S, g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i))
      = ∑ k ∈ S, ∑ i ∈ W,
        lp.single q i ((((g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i) := by
  have hpt : ∀ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((∑ k ∈ S, g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)
      = ∑ k ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i) := by
    intro i _
    have h1 : ((((∑ k ∈ S, g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)
        = ∑ k ∈ S, ((((g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i) :=
      sum_coords (𝕜 := 𝕜) q S g i
    have e : ∀ a : 𝕜, lp.single (E := fun _ : ℕ => 𝕜) q i a
        = (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) q i) a :=
      fun a => (lp.singleContinuousLinearMap_apply (E := fun _ : ℕ => 𝕜) i a).symm
    rw [h1, e, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact lp.singleContinuousLinearMap_apply (E := fun _ : ℕ => 𝕜) i _
  trans ∑ i ∈ W, ∑ k ∈ S, lp.single (E := fun _ : ℕ => 𝕜) q i
      ((((g k : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)
  · exact Finset.sum_congr rfl hpt
  · exact Finset.sum_comm

/-- A restriction splits over a subset and its complement. -/
private lemma restrict_split_subset {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal)
    [Fact (1 ≤ q)] (W' W : Finset ℕ) (h : W' ⊆ W) (y : ∀ _ : ℕ, 𝕜) :
    (∑ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i (y i))
      = (∑ i ∈ W', lp.single (E := fun _ : ℕ => 𝕜) q i (y i))
        + (∑ i ∈ W \ W', lp.single (E := fun _ : ℕ => 𝕜) q i (y i)) := by
  have hU : W' ∪ W \ W' = W := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h1 | ⟨h1, -⟩)
      · exact h h1
      · exact h1
    · intro h1
      by_cases hi : i ∈ W'
      · exact Or.inl hi
      · exact Or.inr ⟨h1, hi⟩
  have hD : Disjoint W' (W \ W') := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_sdiff.mp hi2).2 hi1
  conv_lhs => rw [← hU, Finset.sum_union hD]

/-- A restriction splits over the intersection with a set and the remainder. -/
private lemma restrict_inter_sdiff {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal)
    [Fact (1 ≤ q)] (E B : Finset ℕ) (y : ∀ _ : ℕ, 𝕜) :
    (∑ i ∈ E, lp.single (E := fun _ : ℕ => 𝕜) q i (y i))
      = (∑ i ∈ E ∩ B, lp.single (E := fun _ : ℕ => 𝕜) q i (y i))
        + (∑ i ∈ E \ B, lp.single (E := fun _ : ℕ => 𝕜) q i (y i)) := by
  have hU : E ∩ B ∪ E \ B = E := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact h1
      · exact h1
    · intro h1
      by_cases hi : i ∈ B
      · exact Or.inl ⟨h1, hi⟩
      · exact Or.inr ⟨h1, hi⟩
  have hD : Disjoint (E ∩ B) (E \ B) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_sdiff.mp hi2).2 (Finset.mem_inter.mp hi1).2
  conv_lhs => rw [← hU, Finset.sum_union hD]

/-- Gliding-hump contradiction: bad tail witnesses at every scale are impossible. -/
private lemma gliding_hump {𝕜 : Type*} [RCLike 𝕜] (p q : ENNReal)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp_top : p ≠ ⊤) (hq_ne : q ≠ ⊤) (hsr : q.toReal < p.toReal)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q)
    {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ N, ∃ x : lp (fun _ : ℕ => 𝕜) p, ‖x‖ < 1 ∧
      ε / 2 < ‖T x - truncCLM (𝕜 := 𝕜) q N (T x)‖)
    (K : ℕ) (hK1 : 1 ≤ K)
    (hKbig : 16 * ‖T‖ / ε < (K : ℝ) ^ (1 / q.toReal - 1 / p.toReal))
    {η θ : ℝ} (hη : 0 < η) (hθdef : θ = ε / 4 - η)
    (hθ8 : ε / 8 ≤ θ) (hθ0 : 0 < θ) (h2Kη : 2 * (K : ℝ) * η = ε / 16) :
    False := by
  have hs : 0 < q.toReal := toReal_pos_of_one_le hq_ne
  have hrpos : 0 < p.toReal := toReal_pos_of_one_le hp_top
  have hs1 : 1 ≤ q.toReal := one_le_toReal_of_one_le hq_ne
  have hr : 1 < p.toReal := lt_of_le_of_lt hs1 hsr
  have hK0 : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le zero_lt_one hK1
  have hη2 : (0 : ℝ) < η / 2 := by linarith [hη]
  have hε8 : (0 : ℝ) < ε / 8 := by linarith [hε]
  have build : ∀ J, J ≤ K → ∃ (u : ℕ → lp (fun _ : ℕ => 𝕜) p)
      (t w : ℕ → Finset ℕ) (lo cc : ℕ → ℕ) (m c : ℕ),
      (∀ k < J, (∀ i, ((u k : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k)
        ∧ t k ⊆ Finset.range m ∧ ‖u k‖ ≤ 1)
      ∧ (∀ k₁ < J, ∀ k₂ < J, k₁ ≠ k₂ → Disjoint (t k₁) (t k₂))
      ∧ (∀ k < J, Disjoint (w k) (Finset.range (lo k))
        ∧ w k ⊆ Finset.range (cc k) ∧ cc k ≤ c
        ∧ ‖truncCLM (𝕜 := 𝕜) q (lo k) (T (u k))‖ ≤ η
        ∧ ‖T (u k) - truncCLM (𝕜 := 𝕜) q (cc k) (T (u k))‖ ≤ η
        ∧ θ ≤ ‖∑ i ∈ w k, lp.single (E := fun _ : ℕ => 𝕜) q i
          (((T (u k) : ∀ _ : ℕ, 𝕜)) i)‖)
      ∧ (∀ k < J, ∀ k' < J, k < k' → cc k ≤ lo k') := by
    intro J
    induction J with
    | zero =>
      intro _
      refine ⟨fun _ => 0, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 0, 0, 0,
        ?_, ?_, ?_, ?_⟩ <;>
        simp
    | succ J ih =>
      intro hJ
      have hJle : J ≤ K := by omega
      obtain ⟨u, t, w, lo, cc, m, c, hD, hDdisj, hW, hcoup⟩ := ih hJle
      have hStep1 := head_on_tail (𝕜 := 𝕜) p q hp_top hr T c hη2
      obtain ⟨M, hM, hMge⟩ := (hStep1.and (Filter.eventually_ge_atTop m)).exists
      have hStep2 := eventually_tail_on_range (𝕜 := 𝕜) p q hq_ne T M hε8
      obtain ⟨a, ha, hage⟩ := (hStep2.and (Filter.eventually_ge_atTop c)).exists
      obtain ⟨x, hx1, hxbig⟩ := hbad a
      have hx1le : ‖x‖ ≤ 1 := hx1.le
      have hQa0 : (T (x - truncCLM (𝕜 := 𝕜) p M x)
          - truncCLM (𝕜 := 𝕜) q a (T (x - truncCLM (𝕜 := 𝕜) p M x)))
          = (T x - truncCLM (𝕜 := 𝕜) q a (T x))
            - (T (truncCLM (𝕜 := 𝕜) p M x)
              - truncCLM (𝕜 := 𝕜) q a (T (truncCLM (𝕜 := 𝕜) p M x))) := by
        rw [map_sub T, map_sub (truncCLM (𝕜 := 𝕜) q a)]
        abel
      have hQa0big : 3 * ε / 8 < ‖T (x - truncCLM (𝕜 := 𝕜) p M x)
          - truncCLM (𝕜 := 𝕜) q a (T (x - truncCLM (𝕜 := 𝕜) p M x))‖ := by
        have htri := norm_sub_norm_le (T x - truncCLM (𝕜 := 𝕜) q a (T x))
          (T (truncCLM (𝕜 := 𝕜) p M x)
            - truncCLM (𝕜 := 𝕜) q a (T (truncCLM (𝕜 := 𝕜) p M x)))
        rw [← hQa0] at htri
        have hB := ha x hx1le
        linarith [hxbig, htri, hB]
      have hlim := ival_tendsto_tail (𝕜 := 𝕜) p hp_top M x
      have hevQ := eventually_norm_sub_lt
        ((ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) q)
          - truncCLM (𝕜 := 𝕜) q a).comp T)
        (fun m' => ∑ i ∈ Finset.Ico M m',
          lp.single (E := fun _ : ℕ => 𝕜) p i (((x : ∀ _ : ℕ, 𝕜)) i))
        (x - truncCLM (𝕜 := 𝕜) p M x) hlim hε8
      have hevP := eventually_norm_le_add
        ((truncCLM (𝕜 := 𝕜) q c).comp T)
        (fun m' => ∑ i ∈ Finset.Ico M m',
          lp.single (E := fun _ : ℕ => 𝕜) p i (((x : ∀ _ : ℕ, 𝕜)) i))
        (x - truncCLM (𝕜 := 𝕜) p M x) hlim hη2
      obtain ⟨m', hQm', hPm', hMm'⟩ :=
        (hevQ.and (hevP.and (Filter.eventually_ge_atTop M))).exists
      simp only [ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply] at hQm'
      simp only [ContinuousLinearMap.comp_apply] at hPm'
      set blk : lp (fun _ : ℕ => 𝕜) p :=
        ∑ i ∈ Finset.Ico M m', lp.single (E := fun _ : ℕ => 𝕜) p i
          (((x : ∀ _ : ℕ, 𝕜)) i) with hblk
      have hblk_norm : ‖blk‖ ≤ 1 :=
        le_trans (norm_restrict_le (𝕜 := 𝕜) p hp_top _ _) hx1le
      have hQbig : ε / 4 < ‖T blk - truncCLM (𝕜 := 𝕜) q a (T blk)‖ := by
        linarith [hQm', hQa0big]
      have hhead : ‖truncCLM (𝕜 := 𝕜) q c (T blk)‖ ≤ η := by
        have h0 := hM x hx1le
        linarith [hPm', h0]
      have hc'ev := eventually_tail_small (𝕜 := 𝕜) q hq_ne (T blk) hη
      obtain ⟨c', hc'small, hc'ge⟩ :=
        (hc'ev.and (Filter.eventually_ge_atTop a)).exists
      have hR : (∑ i ∈ Finset.Ico a c',
          lp.single (E := fun _ : ℕ => 𝕜) q i (((T blk : ∀ _ : ℕ, 𝕜)) i))
          = (T blk - truncCLM (𝕜 := 𝕜) q a (T blk))
            - (T blk - truncCLM (𝕜 := 𝕜) q c' (T blk)) := by
        rw [← trunc_sub_eq_ival (𝕜 := 𝕜) q hc'ge (T blk)]
        abel
      have hlarge : θ ≤ ‖∑ i ∈ Finset.Ico a c',
          lp.single (E := fun _ : ℕ => 𝕜) q i (((T blk : ∀ _ : ℕ, 𝕜)) i)‖ := by
        have htri := norm_sub_norm_le (T blk - truncCLM (𝕜 := 𝕜) q a (T blk))
          (T blk - truncCLM (𝕜 := 𝕜) q c' (T blk))
        rw [← hR] at htri
        linarith [htri, hQbig, hc'small, hθdef]
      have hmle : m ≤ m' := le_trans hMge hMm'
      have hcle : c ≤ c' := le_trans hage hc'ge
      have hDnew2 : Finset.Ico M m' ⊆ Finset.range m' := by
        intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      have hDdisj_new : ∀ k < J, Disjoint (t k) (Finset.Ico M m') := by
        intro k hk
        have hsub : t k ⊆ Finset.range M :=
          subset_trans (hD k hk).2.1 (Finset.range_mono hMge)
        exact Disjoint.mono hsub subset_rfl (disjoint_range_Ico M m')
      have hW1new : Disjoint (Finset.Ico a c') (Finset.range c) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 : a ≤ i := (Finset.mem_Ico.mp hi1).1
        have h2 : i < c := Finset.mem_range.mp hi2
        omega
      have hW2new : Finset.Ico a c' ⊆ Finset.range c' := by
        intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      refine ⟨Function.update u J blk, Function.update t J (Finset.Ico M m'),
        Function.update w J (Finset.Ico a c'), Function.update lo J c,
        Function.update cc J c', m', c', ?_, ?_, ?_, ?_⟩
      · intro k hk
        by_cases hJJ : k = J
        · subst hJJ
          simp only [Function.update_self]
          refine ⟨?_, hDnew2, hblk_norm⟩
          intro i hi
          rw [hblk] at hi
          exact mem_of_restrict_ne_zero (𝕜 := 𝕜) p _ _ _ hi
        · have hkJ : k < J := by omega
          rw [Function.update_of_ne hJJ _ _, Function.update_of_ne hJJ _ _]
          obtain ⟨hsupp, hsub, hunit⟩ := hD k hkJ
          exact ⟨hsupp, subset_trans hsub (Finset.range_mono hmle), hunit⟩
      · intro k₁ hk₁ k₂ hk₂ hne
        by_cases h1 : k₁ = J <;> by_cases h2 : k₂ = J
        · exact absurd (h1.trans h2.symm) hne
        · subst h1
          rw [Function.update_of_ne h2 _ _]
          simp only [Function.update_self]
          exact (hDdisj_new k₂ (by omega)).symm
        · subst h2
          rw [Function.update_of_ne h1 _ _]
          simp only [Function.update_self]
          exact hDdisj_new k₁ (by omega)
        · rw [Function.update_of_ne h1 _ _, Function.update_of_ne h2 _ _]
          exact hDdisj k₁ (by omega) k₂ (by omega) hne
      · intro k hk
        by_cases hJJ : k = J
        · subst hJJ
          simp only [Function.update_self]
          exact ⟨hW1new, hW2new, le_rfl, hhead, hc'small, hlarge⟩
        · have hkJ : k < J := by omega
          rw [Function.update_of_ne hJJ _ _, Function.update_of_ne hJJ _ _,
            Function.update_of_ne hJJ _ _, Function.update_of_ne hJJ _ _]
          obtain ⟨hw1, hw2, hw4, hh, ht, hl⟩ := hW k hkJ
          exact ⟨hw1, hw2, le_trans hw4 hcle, hh, ht, hl⟩
      · intro k hk k' hk' hlt
        by_cases h1 : k = J <;> by_cases h2 : k' = J
        · omega
        · omega
        · subst h2
          rw [Function.update_of_ne h1 _ _]
          simp only [Function.update_self]
          exact (hW k (by omega)).2.2.1
        · rw [Function.update_of_ne h1 _ _, Function.update_of_ne h2 _ _]
          exact hcoup k (by omega) k' (by omega) hlt
  obtain ⟨u, t, w, lo, cc, _, _, hD, hDdisj, hW, hcoup⟩ := build K le_rfl
  have hsuppD : ∀ k ∈ Finset.range K, ∀ i,
      ((u k : ∀ _ : ℕ, 𝕜) i) ≠ 0 → i ∈ t k :=
    fun k hk => (hD k (Finset.mem_range.mp hk)).1
  have hdisjD : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) t := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    exact hDdisj a ha b hb hab
  have hunitD : ∀ k ∈ Finset.range K, ‖u k‖ ≤ 1 :=
    fun k hk => (hD k (Finset.mem_range.mp hk)).2.2
  have hW1 : ∀ k ∈ Finset.range K, Disjoint (w k) (Finset.range (lo k)) :=
    fun k hk => (hW k (Finset.mem_range.mp hk)).1
  have hW2 : ∀ k ∈ Finset.range K, w k ⊆ Finset.range (cc k) :=
    fun k hk => (hW k (Finset.mem_range.mp hk)).2.1
  have hhead : ∀ k ∈ Finset.range K,
      ‖truncCLM (𝕜 := 𝕜) q (lo k) (T (u k))‖ ≤ η :=
    fun k hk => (hW k (Finset.mem_range.mp hk)).2.2.2.1
  have htail : ∀ k ∈ Finset.range K,
      ‖T (u k) - truncCLM (𝕜 := 𝕜) q (cc k) (T (u k))‖ ≤ η :=
    fun k hk => (hW k (Finset.mem_range.mp hk)).2.2.2.2.1
  have hlarge : ∀ k ∈ Finset.range K, θ ≤ ‖∑ i ∈ w k,
      lp.single (E := fun _ : ℕ => 𝕜) q i (((T (u k) : ∀ _ : ℕ, 𝕜)) i)‖ :=
    fun k hk => (hW k (Finset.mem_range.mp hk)).2.2.2.2.2
  have hcoupK : ∀ k ∈ Finset.range K, ∀ k' ∈ Finset.range K,
      k < k' → cc k ≤ lo k' :=
    fun k hk k' hk' hlt =>
      hcoup k (Finset.mem_range.mp hk) k' (Finset.mem_range.mp hk') hlt
  have hdisjW : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) w := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · have hsub : w a ⊆ Finset.range (lo b) :=
        subset_trans (hW2 a (Finset.mem_range.mpr ha))
          (Finset.range_mono (hcoupK a (Finset.mem_range.mpr ha)
            b (Finset.mem_range.mpr hb) hlt))
      exact Disjoint.mono hsub subset_rfl (hW1 b (Finset.mem_range.mpr hb)).symm
    · have hsub : w b ⊆ Finset.range (lo a) :=
        subset_trans (hW2 b (Finset.mem_range.mpr hb))
          (Finset.range_mono (hcoupK b (Finset.mem_range.mpr hb)
            a (Finset.mem_range.mpr ha) hlt))
      exact (Disjoint.mono hsub subset_rfl
        (hW1 a (Finset.mem_range.mpr ha)).symm).symm
  set v : lp (fun _ : ℕ => 𝕜) p := ∑ k ∈ Finset.range K, u k with hvdef
  have hVnorm : ‖v‖ ^ p.toReal ≤ (K : ℝ) := by
    rw [hvdef, norm_sum_disjoint (𝕜 := 𝕜) p hp_top _ _ hdisjD _ hsuppD]
    calc ∑ k ∈ Finset.range K, ‖u k‖ ^ p.toReal
        ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          calc ‖u k‖ ^ p.toReal ≤ (1 : ℝ) ^ p.toReal :=
                Real.rpow_le_rpow (norm_nonneg _) (hunitD k hk) hrpos.le
            _ = 1 := Real.one_rpow _
      _ = (K : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hVle : ‖v‖ ≤ (K : ℝ) ^ (1 / p.toReal) := by
    have hKr : (((K : ℝ) ^ (1 / p.toReal)) ^ p.toReal) = K := by
      rw [one_div]
      exact Real.rpow_inv_rpow hK0.le (ne_of_gt hrpos)
    have h := (Real.rpow_le_rpow_iff (norm_nonneg _)
      (Real.rpow_nonneg hK0.le _) hrpos).mp (by rw [hKr]; exact hVnorm)
    exact h
  have hUpper : ‖T v‖ ≤ ‖T‖ * (K : ℝ) ^ (1 / p.toReal) :=
    le_trans (T.le_opNorm v) (mul_le_mul_of_nonneg_left hVle (norm_nonneg _))
  set W : Finset ℕ := (Finset.range K).biUnion w with hWdef
  set Z : lp (fun _ : ℕ => 𝕜) q := ∑ k ∈ Finset.range K, ∑ i ∈ w k,
    lp.single (E := fun _ : ℕ => 𝕜) q i (((T (u k) : ∀ _ : ℕ, 𝕜)) i) with hZdef
  set Err : lp (fun _ : ℕ => 𝕜) q := ∑ k ∈ Finset.range K, ∑ i ∈ W \ w k,
    lp.single (E := fun _ : ℕ => 𝕜) q i (((T (u k) : ∀ _ : ℕ, 𝕜)) i) with hEdef
  have hTv : T v = ∑ k ∈ Finset.range K, T (u k) := by
    rw [hvdef, map_sum]
  have hRW : (∑ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i
      ((((T v : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)) = Z + Err := by
    rw [hTv, restrict_sum (𝕜 := 𝕜) q W (Finset.range K) (fun k => T (u k))]
    have hsplit : ∀ k ∈ Finset.range K,
        (∑ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i
          (((T (u k) : ∀ _ : ℕ, 𝕜)) i))
        = (∑ i ∈ w k, lp.single (E := fun _ : ℕ => 𝕜) q i
            (((T (u k) : ∀ _ : ℕ, 𝕜)) i))
          + (∑ i ∈ W \ w k, lp.single (E := fun _ : ℕ => 𝕜) q i
            (((T (u k) : ∀ _ : ℕ, 𝕜)) i)) := by
      intro k hk
      have hsub : w k ⊆ W := by
        rw [hWdef]
        exact Finset.subset_biUnion_of_mem w hk
      exact restrict_split_subset (𝕜 := 𝕜) q (w k) W hsub _
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hZdef, hEdef]
  have hsuppZ : ∀ k ∈ Finset.range K, ∀ i,
      ((((∑ i ∈ w k, lp.single (E := fun _ : ℕ => 𝕜) q i
        (((T (u k) : ∀ _ : ℕ, 𝕜)) i) : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)
        ≠ 0 → i ∈ w k := by
    intro k hk i hi
    exact mem_of_restrict_ne_zero (𝕜 := 𝕜) q _ _ _ hi
  have hZpow : ‖Z‖ ^ q.toReal = ∑ k ∈ Finset.range K,
      ‖∑ i ∈ w k, lp.single (E := fun _ : ℕ => 𝕜) q i
        (((T (u k) : ∀ _ : ℕ, 𝕜)) i)‖ ^ q.toReal := by
    rw [hZdef]
    exact norm_sum_disjoint (𝕜 := 𝕜) q hq_ne _ _ hdisjW _ hsuppZ
  have hZle : (K : ℝ) * θ ^ q.toReal ≤ ‖Z‖ ^ q.toReal := by
    rw [hZpow]
    have hsum : ∑ _k ∈ Finset.range K, θ ^ q.toReal
        = (K : ℝ) * θ ^ q.toReal := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hsum]
    apply Finset.sum_le_sum
    intro k hk
    exact Real.rpow_le_rpow hθ0.le (hlarge k hk) hs.le
  have hZ : (K : ℝ) ^ (1 / q.toReal) * θ ≤ ‖Z‖ := by
    have hKθ : (((K : ℝ) ^ (1 / q.toReal) * θ) ^ q.toReal)
        = (K : ℝ) * θ ^ q.toReal := by
      rw [Real.mul_rpow (Real.rpow_nonneg hK0.le (1 / q.toReal)) hθ0.le, one_div,
        Real.rpow_inv_rpow hK0.le (ne_of_gt hs)]
    have h : (K : ℝ) ^ (1 / q.toReal) * θ ≤ ‖Z‖ :=
      (Real.rpow_le_rpow_iff
        (mul_nonneg (Real.rpow_nonneg hK0.le _) hθ0.le) (norm_nonneg _)
        hs).mp (by rw [hKθ]; exact hZle)
    exact h
  have herr : ∀ j ∈ Finset.range K,
      ‖∑ i ∈ W \ w j, lp.single (E := fun _ : ℕ => 𝕜) q i
        (((T (u j) : ∀ _ : ℕ, 𝕜)) i)‖ ≤ 2 * η := by
    intro j hj
    have hsplit := restrict_inter_sdiff (𝕜 := 𝕜) q (W \ w j)
      (Finset.range (lo j)) ⇑(T (u j))
    rw [hsplit]
    have hA : ‖∑ i ∈ (W \ w j) ∩ Finset.range (lo j),
        lp.single (E := fun _ : ℕ => 𝕜) q i
          (((T (u j) : ∀ _ : ℕ, 𝕜)) i)‖ ≤ η :=
      le_trans
        (restrict_le_trunc (𝕜 := 𝕜) q hq_ne ((W \ w j) ∩ Finset.range (lo j))
          (lo j) (T (u j)) Finset.inter_subset_right)
        (hhead j hj)
    have hdisjB : Disjoint ((W \ w j) \ Finset.range (lo j))
        (Finset.range (cc j)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      obtain ⟨hiW, hinlo⟩ := Finset.mem_sdiff.mp hi1
      obtain ⟨hiW', hiwj⟩ := Finset.mem_sdiff.mp hiW
      rw [hWdef] at hiW'
      obtain ⟨k, hkK, hiwk⟩ := Finset.mem_biUnion.mp hiW'
      rcases lt_trichotomy k j with hlt | heq | hgt
      · have hsub : w k ⊆ Finset.range (lo j) :=
          subset_trans (hW2 k hkK)
            (Finset.range_mono (hcoupK k hkK j hj hlt))
        exact hinlo (hsub hiwk)
      · subst heq
        exact hiwj hiwk
      · have hle : cc j ≤ lo k := hcoupK j hj k hkK hgt
        have hiR : i ∈ Finset.range (lo k) :=
          Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hi2) hle)
        exact (Finset.disjoint_left.mp (hW1 k hkK) hiwk) hiR
    have hB : ‖∑ i ∈ (W \ w j) \ Finset.range (lo j),
        lp.single (E := fun _ : ℕ => 𝕜) q i
          (((T (u j) : ∀ _ : ℕ, 𝕜)) i)‖ ≤ η :=
      le_trans
        (restrict_le_tail (𝕜 := 𝕜) q hq_ne ((W \ w j) \ Finset.range (lo j))
          (cc j) (T (u j)) hdisjB)
        (htail j hj)
    calc ‖(∑ i ∈ (W \ w j) ∩ Finset.range (lo j),
            lp.single (E := fun _ : ℕ => 𝕜) q i
              (((T (u j) : ∀ _ : ℕ, 𝕜)) i))
          + (∑ i ∈ (W \ w j) \ Finset.range (lo j),
            lp.single (E := fun _ : ℕ => 𝕜) q i
              (((T (u j) : ∀ _ : ℕ, 𝕜)) i))‖
        ≤ ‖∑ i ∈ (W \ w j) ∩ Finset.range (lo j),
              lp.single (E := fun _ : ℕ => 𝕜) q i
                (((T (u j) : ∀ _ : ℕ, 𝕜)) i)‖
            + ‖∑ i ∈ (W \ w j) \ Finset.range (lo j),
              lp.single (E := fun _ : ℕ => 𝕜) q i
                (((T (u j) : ∀ _ : ℕ, 𝕜)) i)‖ := norm_add_le _ _
      _ ≤ η + η := add_le_add hA hB
      _ = 2 * η := by ring
  have hErr : ‖Err‖ ≤ 2 * (K : ℝ) * η := by
    rw [hEdef]
    calc ‖∑ k ∈ Finset.range K, ∑ i ∈ W \ w k,
            lp.single (E := fun _ : ℕ => 𝕜) q i
              (((T (u k) : ∀ _ : ℕ, 𝕜)) i)‖
        ≤ ∑ k ∈ Finset.range K, ‖∑ i ∈ W \ w k,
            lp.single (E := fun _ : ℕ => 𝕜) q i
              (((T (u k) : ∀ _ : ℕ, 𝕜)) i)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range K, (2 * η) :=
          Finset.sum_le_sum (fun k hk => herr k hk)
      _ = 2 * (K : ℝ) * η := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hchain : (K : ℝ) ^ (1 / q.toReal) * θ - 2 * (K : ℝ) * η ≤ ‖T v‖ := by
    have hRle : ‖∑ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((T v : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)‖ ≤ ‖T v‖ :=
      norm_restrict_le (𝕜 := 𝕜) q hq_ne W (T v)
    have hZeq : Z = (∑ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((T v : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)) - Err := by
      rw [hRW]
      abel
    have htri : ‖Z‖ ≤ ‖∑ i ∈ W, lp.single (E := fun _ : ℕ => 𝕜) q i
        ((((T v : lp (fun _ : ℕ => 𝕜) q) : ∀ _ : ℕ, 𝕜)) i)‖ + ‖Err‖ := by
      rw [hZeq]
      exact norm_sub_le _ _
    linarith [hZ, htri, hRle, hErr]
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK1s : (1 : ℝ) ≤ (K : ℝ) ^ (1 / q.toReal) :=
    Real.one_le_rpow hK1r (one_div_pos.mpr hs).le
  have hθKs : θ ≤ (K : ℝ) ^ (1 / q.toReal) * θ :=
    le_mul_of_one_le_left hθ0.le hK1s
  have hLower : (K : ℝ) ^ (1 / q.toReal) * θ / 2 ≤ ‖T v‖ := by
    linarith [hchain, hθKs, hθ8, h2Kη]
  have hKr0 : (0 : ℝ) < (K : ℝ) ^ (1 / p.toReal) := Real.rpow_pos_of_pos hK0 _
  have hdiv : (K : ℝ) ^ (1 / q.toReal - 1 / p.toReal) * (θ / 2) ≤ ‖T‖ := by
    have hrw : (K : ℝ) ^ (1 / q.toReal - 1 / p.toReal)
        = (K : ℝ) ^ (1 / q.toReal) / (K : ℝ) ^ (1 / p.toReal) := by
      rw [Real.rpow_sub hK0]
    rw [hrw, div_mul_eq_mul_div, div_le_iff₀ hKr0, ← mul_div_assoc]
    exact le_trans hLower hUpper
  have hθ2 : (0 : ℝ) < θ / 2 := by linarith [hθ0]
  have hle1 : (K : ℝ) ^ (1 / q.toReal - 1 / p.toReal) ≤ 2 * ‖T‖ / θ := by
    have h := (le_div_iff₀ hθ2).mpr hdiv
    have hθne : θ ≠ 0 := ne_of_gt hθ0
    have heq : ‖T‖ / (θ / 2) = 2 * ‖T‖ / θ := by
      have hθ2ne : θ / 2 ≠ 0 := ne_of_gt hθ2
      rw [div_eq_div_iff hθ2ne hθne]
      ring
    rw [heq] at h
    exact h
  have hle2 : 2 * ‖T‖ / θ ≤ 16 * ‖T‖ / ε := by
    rw [div_le_div_iff₀ hθ0 hε]
    have h8 : ε ≤ 8 * θ := by linarith [hθ8]
    calc (2 * ‖T‖) * ε = ‖T‖ * (2 * ε) := by ring
      _ ≤ ‖T‖ * (16 * θ) :=
          mul_le_mul_of_nonneg_left (by linarith [h8]) (norm_nonneg _)
      _ = (16 * ‖T‖) * θ := by ring
  linarith [hKbig, hle1, hle2]

/--
**Pitt's theorem.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let
$1 \le q < p < \infty$. Then every bounded linear operator
$T : \ell^p(\mathbb{N}, \mathbb{K}) \to \ell^q(\mathbb{N}, \mathbb{K})$ is compact.

Proves `Wanted` entry `pitt`.

Source: H. R. Pitt,
A Note on Bilinear Forms, J. London Math. Soc. s1-11 (1936), 174–180,
DOI 10.1112/JLMS/S1-11.3.174, compactness of operators `ℓ^p → ℓ^q` for `q<p`; textbook Albiac
and Kalton, Topics in Banach Space Theory Prop 2.1.6; Lean states `RCLike` `lp _ p →L[𝕜] lp _ q`
with `q<p<∞` compact specialization via `IsCompactOperator`.
-/
theorem pitt
    {𝕜 : Type*} [RCLike 𝕜]
    (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hq_lt : q < p) (hp_lt : p < ⊤)
    (T : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) q) :
    IsCompactOperator T := by
  have hq_ne : q ≠ ⊤ := ne_of_lt (lt_trans hq_lt hp_lt)
  apply pitt_of_tail_opNorm (𝕜 := 𝕜) p q T
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmono : ∀ N n : ℕ, N ≤ n →
      ‖(truncCLM (𝕜 := 𝕜) q n).comp T - T‖
        ≤ ‖(truncCLM (𝕜 := 𝕜) q N).comp T - T‖ :=
    fun N n hNn => antitone_tail_opNorm (𝕜 := 𝕜) p q hq_ne T hNn
  suffices h : ∃ N, ‖(truncCLM (𝕜 := 𝕜) q N).comp T - T‖ < ε by
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun n hn => ?_⟩
    have hle : ‖(truncCLM (𝕜 := 𝕜) q n).comp T - T‖ < ε :=
      lt_of_le_of_lt (hmono N n hn) hN
    have habs : |‖(truncCLM (𝕜 := 𝕜) q n).comp T - T‖|
        = ‖(truncCLM (𝕜 := 𝕜) q n).comp T - T‖ :=
      abs_of_nonneg (norm_nonneg _)
    rwa [dist_eq_norm, sub_zero, Real.norm_eq_abs, habs]
  by_contra hcon
  push Not at hcon
  have hbad : ∀ N, ∃ x : lp (fun _ : ℕ => 𝕜) p, ‖x‖ < 1 ∧
      ε / 2 < ‖T x - truncCLM (𝕜 := 𝕜) q N (T x)‖ := by
    intro N
    have hN : ε / 2 < ‖(truncCLM (𝕜 := 𝕜) q N).comp T - T‖ := by
      have hle := hcon N
      linarith
    obtain ⟨x, hx1, hx2⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm _ hN
    refine ⟨x, hx1, ?_⟩
    have e : ((truncCLM (𝕜 := 𝕜) q N).comp T - T) x
        = truncCLM (𝕜 := 𝕜) q N (T x) - T x := by
      rw [sub_apply, ContinuousLinearMap.comp_apply]
    rw [e, norm_sub_rev] at hx2
    exact hx2
  have hp_top : p ≠ ⊤ := ne_of_lt hp_lt
  have hsr : q.toReal < p.toReal :=
    (ENNReal.toReal_lt_toReal hq_ne hp_top).mpr hq_lt
  have hs : 0 < q.toReal := toReal_pos_of_one_le hq_ne
  have hexp : (0 : ℝ) < 1 / q.toReal - 1 / p.toReal := by
    have h1 : 1 / p.toReal < 1 / q.toReal := one_div_lt_one_div_of_lt hs hsr
    linarith
  have htop : Filter.Tendsto
      (fun K : ℕ => ((K : ℝ) ^ (1 / q.toReal - 1 / p.toReal)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hKev : ∀ᶠ K : ℕ in Filter.atTop,
      16 * ‖T‖ / ε < ((K : ℝ) ^ (1 / q.toReal - 1 / p.toReal)) :=
    htop.eventually (Filter.eventually_gt_atTop _)
  obtain ⟨K, hKbig, hK1⟩ := (hKev.and (Filter.eventually_ge_atTop 1)).exists
  have hK0 : (0 : ℝ) < K := by exact_mod_cast lt_of_lt_of_le zero_lt_one hK1
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have h32K : (0 : ℝ) < 32 * K := mul_pos (by norm_num) hK0
  set η : ℝ := ε / (32 * K) with hηdef
  have hη : 0 < η := by rw [hηdef]; exact div_pos hε h32K
  have hη8 : η ≤ ε / 8 := by
    have h8 : (8 : ℝ) ≤ 32 * K := by
      calc (8 : ℝ) ≤ 32 * 1 := by norm_num
        _ ≤ 32 * K := mul_le_mul_of_nonneg_left hK1r (by norm_num)
    rw [hηdef, div_le_div_iff₀ h32K (by norm_num)]
    exact mul_le_mul_of_nonneg_left h8 hε.le
  set θ : ℝ := ε / 4 - η with hθdef
  obtain ⟨hθ8, hθ0⟩ : ε / 8 ≤ θ ∧ 0 < θ := by
    rw [hθdef]
    constructor <;> linarith [hε, hη8, hη]
  have h2Kη : 2 * (K : ℝ) * η = ε / 16 := by
    have hKne : (K : ℝ) ≠ 0 := ne_of_gt hK0
    have h32Kne : (32 : ℝ) * K ≠ 0 := mul_ne_zero (by norm_num) hKne
    rw [hηdef, ← mul_div_assoc, div_eq_div_iff h32Kne (by norm_num)]
    ring
  exact gliding_hump (𝕜 := 𝕜) p q hp_top hq_ne hsr T hε hbad K hK1 hKbig
    hη hθdef hθ8 hθ0 h2Kη

end MathlibExt.Analysis.FunctionalAnalysis.PittWanted
end
