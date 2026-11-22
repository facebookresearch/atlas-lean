/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.HeineCantor

open scoped BoundedContinuousFunction

@[expose] public section

private noncomputable def stepRamp (c a : ℕ → ℝ) (K : ℕ) (z : ℝ) : ℝ :=
  c 0 + ∑ i ∈ Finset.range K, (c (i + 1) - c i) * min 1 (max 0 (z - a i))

private lemma continuous_stepRamp (c a : ℕ → ℝ) (K : ℕ) : Continuous (stepRamp c a K) := by
  unfold stepRamp
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul continuous_const
  exact continuous_const.min (continuous_const.max (continuous_id'.sub continuous_const))

private lemma stepRamp_eq_of_between (c a : ℕ → ℝ) (K k : ℕ) (z : ℝ)
    (hkK : k ≤ K)
    (hlo : ∀ i < k, a i + 1 ≤ z)
    (hhi : ∀ i, k ≤ i → i < K → z ≤ a i) :
    stepRamp c a K z = c k := by
  unfold stepRamp
  have hclamp_lo : ∀ i ∈ Finset.range K, i < k →
      min 1 (max 0 (z - a i)) = 1 := by
    intro i _ hi
    have h1 : 1 ≤ max 0 (z - a i) := by
      have : 1 ≤ z - a i := by linarith [hlo i hi]
      exact le_max_of_le_right this
    exact min_eq_left h1
  have hclamp_hi : ∀ i ∈ Finset.range K, k ≤ i →
      min 1 (max 0 (z - a i)) = 0 := by
    intro i hi_mem hi
    have hiK : i < K := Finset.mem_range.mp hi_mem
    have h1 : z - a i ≤ 0 := by
      by_cases hkk : k = i
      · subst hkk
        -- need z ≤ a k; from hhi with i=k if k<K, else k=K and i=K impossible
        have : z ≤ a k := by
          by_cases hkK' : k < K
          · exact hhi k le_rfl hkK'
          · have : k = K := by omega
            subst this
            -- i = K, but i < K contradiction; this branch impossible
            omega
        linarith
      · have hlt : k < i ∨ k = i := by omega
        rcases hlt with hlt | heq
        · have : z ≤ a i := hhi i (by omega) hiK
          linarith
        · omega
    have h2 : max 0 (z - a i) = 0 := max_eq_left (by linarith)
    rw [h2, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  -- split sum range K = range k + rest
  have hA : ∑ i ∈ Finset.range k, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = ∑ i ∈ Finset.range k, (c (i + 1) - c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    rw [hclamp_lo i (Finset.mem_range.mpr (lt_of_lt_of_le hik hkK)) hik]
    ring
  have hB : ∑ i ∈ Finset.Ico k K, (c (i + 1) - c i) * min 1 (max 0 (z - a i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [hclamp_hi i (Finset.mem_range.mpr (by omega : i < K)) hi.1]
    ring
  have hsplit : ∑ i ∈ Finset.range K, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = ∑ i ∈ Finset.range k, (c (i + 1) - c i) := by
    have h := Finset.sum_range_add_sum_Ico
      (fun i => (c (i + 1) - c i) * min 1 (max 0 (z - a i))) hkK
    rw [hA, hB, add_zero] at h
    exact h.symm
  rw [hsplit, Finset.sum_range_sub]
  ring

private lemma stepRamp_mem_segment (c a : ℕ → ℝ) (K k : ℕ) (z : ℝ)
    (hkK : k < K)
    (hlo : ∀ i < k, a i + 1 ≤ z)
    (hmid_lo : a k ≤ z) (hmid_hi : z ≤ a k + 1)
    (hhi : ∀ i, k < i → i < K → z ≤ a i) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ stepRamp c a K z = c k + s * (c (k + 1) - c k) := by
  have hs_mem : 0 ≤ z - a k ∧ z - a k ≤ 1 := by constructor <;> linarith
  set s : ℝ := min 1 (max 0 (z - a k)) with hs_def
  have hs_eq : s = z - a k := by
    rw [hs_def, max_eq_right hs_mem.1, min_eq_right hs_mem.2]
  have hs0 : 0 ≤ s := by rw [hs_eq]; linarith
  have hs1 : s ≤ 1 := by rw [hs_eq]; linarith
  refine ⟨s, hs0, hs1, ?_⟩
  unfold stepRamp
  have hclamp_lo : ∀ i ∈ Finset.range K, i < k →
      min 1 (max 0 (z - a i)) = 1 := by
    intro i _ hi
    have h1 : 1 ≤ max 0 (z - a i) := by
      have : 1 ≤ z - a i := by linarith [hlo i hi]
      exact le_max_of_le_right this
    exact min_eq_left h1
  have hclamp_hi : ∀ i ∈ Finset.range K, k < i →
      min 1 (max 0 (z - a i)) = 0 := by
    intro i hi_mem hi
    have hiK : i < K := Finset.mem_range.mp hi_mem
    have h1 : z - a i ≤ 0 := by linarith [hhi i hi hiK]
    have h2 : max 0 (z - a i) = 0 := max_eq_left (by linarith)
    rw [h2, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  have hpart : Finset.range K = Finset.range k ∪ ({k} ∪ Finset.Ico (k + 1) K) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
    omega
  have hdisj1 : Disjoint (Finset.range k) ({k} ∪ Finset.Ico (k + 1) K) := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_range] at hx
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
    omega
  have hdisj2 : Disjoint ({k} : Finset ℕ) (Finset.Ico (k + 1) K) := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hA : ∑ i ∈ Finset.range k, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = ∑ i ∈ Finset.range k, (c (i + 1) - c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hikK : i < K := by omega
    rw [hclamp_lo i (Finset.mem_range.mpr hikK) hik]
    ring
  have hmid : ∑ x ∈ ({k} : Finset ℕ), (c (x + 1) - c x) * min 1 (max 0 (z - a x))
      = (c (k + 1) - c k) * s := by
    simp only [Finset.sum_singleton, hs_def]
  have htail : ∑ i ∈ Finset.Ico (k + 1) K, (c (i + 1) - c i) * min 1 (max 0 (z - a i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hiK : i < K := hi.2
    rw [hclamp_hi i (Finset.mem_range.mpr hiK) hi.1]
    ring
  have hsplit : ∑ i ∈ Finset.range K, (c (i + 1) - c i) * min 1 (max 0 (z - a i))
      = (∑ i ∈ Finset.range k, (c (i + 1) - c i)) + (c (k + 1) - c k) * s := by
    rw [hpart, Finset.sum_union hdisj1, Finset.sum_union hdisj2, hA, hmid, htail, add_zero]
  rw [hsplit, Finset.sum_range_sub]
  ring

private lemma stepRamp_abs_le_max (c : ℕ → ℝ) (k : ℕ) (v y : ℝ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hv : v = c k + s * (c (k + 1) - c k)) :
    |v - y| ≤ max |c k - y| |c (k + 1) - y| := by
  have h1s : 0 ≤ 1 - s := by linarith
  have hdecomp : v - y = (1 - s) * (c k - y) + s * (c (k + 1) - y) := by
    rw [hv]; ring
  rw [hdecomp]
  calc |(1 - s) * (c k - y) + s * (c (k + 1) - y)|
      ≤ (1 - s) * |c k - y| + s * |c (k + 1) - y| := by
        have h := abs_add_le ((1 - s) * (c k - y)) (s * (c (k + 1) - y))
        rwa [abs_mul, abs_mul, abs_of_nonneg h1s, abs_of_nonneg hs0] at h
    _ ≤ (1 - s) * max |c k - y| |c (k + 1) - y| + s * max |c k - y| |c (k + 1) - y| := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max |c k - y| |c (k + 1) - y| := by ring

private lemma exists_small_injective_perturbation {Q J : Type*} [Finite Q] [Finite J]
    (A : Q → J → ℝ) (E : J → ℕ) (hE : Function.Injective E)
    {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ η, 0 < η ∧ η < η₀ ∧ ∀ q, Function.Injective (fun j => A q j + η * (E j : ℝ)) := by
  have := Fintype.ofFinite (Q × J × J)
  let B : Finset ℝ := Finset.univ.image (fun p : Q × J × J =>
    (A p.1 p.2.2 - A p.1 p.2.1) / ((E p.2.1 : ℝ) - E p.2.2))
  have hinf : (Set.Ioo 0 η₀).Infinite := Set.Ioo_infinite hη₀
  obtain ⟨η, hηmem, hηnot⟩ := hinf.exists_notMem_finset B
  refine ⟨η, hηmem.1, hηmem.2, fun q j j' h => ?_⟩
  by_contra hne
  have hEj : (E j : ℝ) ≠ E j' := by
    exact_mod_cast hE.ne hne
  have hηeq : η = (A q j' - A q j) / ((E j : ℝ) - E j') := by
    field_simp
    linarith [h]
  have hmem : η ∈ B := by
    simp only [B, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨(q, j, j'), hηeq.symm⟩
  exact hηnot hmem

private lemma exists_bcf_interpolate {J : Type*} [Finite J]
    (v : J → ℝ) (hv : Function.Injective v) (y : J → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hy : ∀ j, |y j| ≤ B) :
    ∃ g : BoundedContinuousFunction ℝ ℝ, ‖g‖ ≤ B ∧ ∀ j, g (v j) = y j := by
  classical
  let S : Set ℝ := Set.range v
  have hSfin : S.Finite := Set.finite_range v
  have hSclosed : IsClosed S := hSfin.isClosed
  let e : J ≃ S := Equiv.ofInjective v hv
  let F : S → ℝ := fun s => y (e.symm s)
  have hFcont : Continuous F := continuous_of_discreteTopology
  let Fb : C(S, ℝ) := ⟨F, hFcont⟩
  let F₀ : BoundedContinuousFunction S ℝ := BoundedContinuousFunction.mkOfCompact Fb
  have hF₀norm : ‖F₀‖ ≤ B := by
    rw [BoundedContinuousFunction.norm_le hB]
    intro s
    rw [Real.norm_eq_abs, BoundedContinuousFunction.mkOfCompact_apply]
    obtain ⟨j, hj⟩ := e.surjective s
    subst hj
    change |F (e j)| ≤ B
    change |y (e.symm (e j))| ≤ B
    rw [Equiv.symm_apply_apply]
    exact hy j
  obtain ⟨g, hg_norm, hg_eq⟩ :=
    BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding F₀
      (IsClosed.isClosedEmbedding_subtypeVal hSclosed)
  refine ⟨g, hg_norm ▸ hF₀norm, fun j => ?_⟩
  have h := congrFun hg_eq (e j)
  simp only [Function.comp_apply] at h
  have hval : (((e j : S)) : ℝ) = v j := rfl
  rw [hval] at h
  rw [h]
  change (BoundedContinuousFunction.mkOfCompact Fb) (e j) = y j
  rw [BoundedContinuousFunction.mkOfCompact_apply]
  change F (e j) = y j
  change y (e.symm (e j)) = y j
  rw [Equiv.symm_apply_apply]

private lemma abs_sub_sum_le_of_good {n : ℕ} {Q : Type*} [Fintype Q]
    (hQ : Fintype.card Q = 2 * n + 1)
    (G : Finset Q) (hG : n + 1 ≤ G.card)
    (M η F : ℝ) (hη : 0 ≤ η) (hF : |F| ≤ M)
    (a : Q → ℝ)
    (hgood : ∀ q ∈ G, |a q - F / (n + 1)| ≤ η / (n + 1))
    (hbound : ∀ q, |a q| ≤ M / (n + 1)) :
    |F - ∑ q, a q| ≤ n * M / (n + 1) + (2 * n + 1) * η / (n + 1) := by
  classical
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  -- card bounds as reals
  have hcardQ : (Finset.univ (α := Q)).card = 2 * n + 1 := by rw [Finset.card_univ, hQ]
  have hGsub : G.card ≤ 2 * n + 1 := by rw [← hcardQ]; exact Finset.card_le_univ G
  have hk_le : (G.card : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hGsub
  have hk_ge : ((n : ℝ) + 1) ≤ (G.card : ℝ) := by
    have : (n + 1 : ℕ) ≤ G.card := hG
    calc ((n : ℝ) + 1) = (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
      _ ≤ (G.card : ℝ) := by exact_mod_cast this
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg F) hF
  have hdivM : 0 ≤ M / (n + 1) := by positivity
  have hdivη : 0 ≤ η / (n + 1) := by positivity
  -- split the sum
  have hsplit : ∑ q, a q = ∑ q ∈ G, a q + ∑ q ∈ Gᶜ, a q := by
    rw [← Finset.sum_add_sum_compl G (fun q => a q)]
  -- key algebraic identity
  have hid : F - ∑ q, a q =
      F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
      - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
      - (∑ q ∈ Gᶜ, a q) := by
    rw [hsplit]
    have hsumF : ∑ _q ∈ G, (F / ((n : ℝ) + 1)) = (G.card : ℝ) * (F / ((n : ℝ) + 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    -- rewrite sums
    have hsub : (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
        = (∑ q ∈ G, a q) - (G.card : ℝ) * (F / ((n : ℝ) + 1)) := by
      rw [Finset.sum_sub_distrib, hsumF]
    rw [hsub]
    have hmul : F * ((G.card : ℝ) / ((n : ℝ) + 1))
        = (G.card : ℝ) * (F / ((n : ℝ) + 1)) := by ring
    have hexpand : F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        = F - F * ((G.card : ℝ) / ((n : ℝ) + 1)) := by ring
    rw [hexpand, hmul]
    ring
  rw [hid]
  -- triangle inequality
  have htri : |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
      - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
      - (∑ q ∈ Gᶜ, a q)|
      ≤ |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))|
        + |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))|
        + |∑ q ∈ Gᶜ, a q| := by
    have hA : |(F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))) - (∑ q ∈ Gᶜ, a q)|
        ≤ |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
          - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))| + |∑ q ∈ Gᶜ, a q| := by
      have h := abs_sub_le (F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))) 0 (∑ q ∈ Gᶜ, a q)
      simp only [sub_zero, zero_sub, abs_neg] at h
      exact h
    have hB : |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))
        - (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))|
        ≤ |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))|
          + |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))| := by
      have h := abs_sub_le (F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))) 0
        (∑ q ∈ G, (a q - F / ((n : ℝ) + 1)))
      simp only [sub_zero, zero_sub, abs_neg] at h
      exact h
    exact le_trans hA (by linarith [hB])
  refine le_trans htri ?_
  -- bound each piece
  have h1 : |F * (1 - (G.card : ℝ) / ((n : ℝ) + 1))|
      ≤ M * ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    rw [abs_mul]
    have hF' : |F| ≤ M := hF
    have hge1 : (1 : ℝ) ≤ (G.card : ℝ) / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ hn1]
      linarith [hk_ge]
    have habs : |1 - (G.card : ℝ) / ((n : ℝ) + 1)|
        = ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      rw [abs_sub_comm, abs_of_nonneg]
      · field_simp
      · linarith [hge1]
    rw [habs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hF'
      (by positivity : (0:ℝ) ≤ ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1))
  have h2 : |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))| ≤ (G.card : ℝ) * (η / ((n : ℝ) + 1)) := by
    calc |∑ q ∈ G, (a q - F / ((n : ℝ) + 1))|
        ≤ ∑ q ∈ G, |a q - F / ((n : ℝ) + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ G, (η / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro q hq
          have := hgood q hq
          -- convert F/(n+1 : ℕ) vs F/((n:ℝ)+1): they are equal by cast
          simpa using this
      _ = (G.card : ℝ) * (η / ((n : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcompl : (Gᶜ.card : ℝ) = (2 * (n : ℝ) + 1) - (G.card : ℝ) := by
    have hcc : Gᶜ.card = Fintype.card Q - G.card := Finset.card_compl G
    rw [hcc, hQ]
    rw [Nat.cast_sub (by omega : G.card ≤ 2 * n + 1)]
    push_cast
    ring
  have h3 : |∑ q ∈ Gᶜ, a q| ≤ ((2 * (n : ℝ) + 1) - (G.card : ℝ)) * (M / ((n : ℝ) + 1)) := by
    calc |∑ q ∈ Gᶜ, a q| ≤ ∑ q ∈ Gᶜ, |a q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ Gᶜ, (M / ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro q _
          have := hbound q
          simpa using this
      _ = (Gᶜ.card : ℝ) * (M / ((n : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((2 * (n : ℝ) + 1) - (G.card : ℝ)) * (M / ((n : ℝ) + 1)) := by rw [hcompl]
  -- combine: M-terms telescope to n*M/(n+1), η-term bounded by (2n+1)*η/(n+1)
  have h2' : (G.card : ℝ) * (η / ((n : ℝ) + 1)) ≤ (2 * (n : ℝ) + 1) * (η / ((n : ℝ) + 1)) := by
    apply mul_le_mul_of_nonneg_right hk_le (by positivity)
  calc |F * (1 - ↑G.card / (↑n + 1))| + |∑ q ∈ G, (a q - F / (↑n + 1))| + |∑ q ∈ Gᶜ, a q|
      ≤ M * ((G.card : ℝ) - ((n : ℝ) + 1)) / ((n : ℝ) + 1)
        + (G.card : ℝ) * (η / ((n : ℝ) + 1))
        + ((2 * (n : ℝ) + 1) - (G.card : ℝ)) * (M / ((n : ℝ) + 1)) := by gcongr
    _ ≤ n * M / (n + 1) + (2 * n + 1) * η / (n + 1) := by
        have hN : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        -- normalize divisions
        field_simp
        nlinarith [hk_ge, hk_le, hM_nonneg, hη, sq_nonneg ((G.card : ℝ) - ((n : ℝ) + 1))]

/-- The unit interval as a type. -/
private abbrev ksI : Type := Set.Icc (0 : ℝ) 1

/-- The cube `I ^ n`. -/
private abbrev ksX (n : ℕ) : Type := Fin n → ksI

/-- The space of inner-function families. -/
private abbrev ksPsi (n : ℕ) : Type := Fin (2 * n + 1) → Fin n → C(ksI, ℝ)

/-- The contraction factor `θ = (2n+1)/(2n+2)`. -/
private noncomputable def ksTheta (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)

/-- Inner sum of family `q` at `x`. -/
private noncomputable def kolmogorovInner (n : ℕ) (ψ : ksPsi n)
    (q : Fin (2 * n + 1)) (x : ksX n) : ℝ :=
  ∑ p, ψ q p (x p)

/-- Superposition operator: `x ↦ ∑ q, g q (inner ψ q x)`. -/
private noncomputable def kolmogorovSuperpose (n : ℕ) (ψ : ksPsi n)
    (g : Fin (2 * n + 1) → ℝ →ᵇ ℝ) : C(ksX n, ℝ) where
  toFun x := ∑ q, g q (kolmogorovInner n ψ q x)
  continuous_toFun := by
    apply continuous_finsetSum
    intro q _
    apply Continuous.comp (g q).continuous
    apply continuous_finsetSum
    intro p _
    exact (ψ q p).continuous.comp (continuous_apply p)

/-- Good set of inner families for `f`: those admitting a bounded outer
family `g` with `‖f - T g‖ < θ‖f‖`. -/
private noncomputable def kolmogorovGoodSet (n : ℕ) (f : C(ksX n, ℝ)) : Set (ksPsi n) :=
  {ψ | ∃ g : Fin (2 * n + 1) → ℝ →ᵇ ℝ,
    (∀ q, ‖g q‖ ≤ ‖f‖ / ((n : ℝ) + 1))
      ∧ ‖f - kolmogorovSuperpose n ψ g‖ < ksTheta n * ‖f‖}

/-- Left end of gap cell `i` of family `q`, in z-units. -/
private noncomputable def ksGap (n : ℕ) (q : Fin (2 * n + 1)) (i : ℕ) : ℝ :=
  (i : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ)

/-- `t` lies in an open gap cell of family `q` at scale `N`. -/
private def ksBad (n N : ℕ) (q : Fin (2 * n + 1)) (t : ℝ) : Prop :=
  ∃ m : ℤ, m % ((2 * n + 1 : ℕ) : ℤ) = (q.val : ℤ)
    ∧ (m : ℝ) < (N : ℝ) * t ∧ (N : ℝ) * t < (m : ℝ) + 1

/-- Index of the good interval containing `t` for family `q`. -/
private noncomputable def ksIdx (n N : ℕ) (q : Fin (2 * n + 1)) (t : ℝ) : ℕ :=
  ⌊((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1)⌋₊

/-- Left end of good interval `k` of family `q`, clamped into `I`. -/
private noncomputable def ksRep (n N : ℕ) (q : Fin (2 * n + 1)) (k : ℕ) : ksI :=
  Set.projIcc 0 1 zero_le_one
    (((k : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) - 2 * (n : ℝ)) / (N : ℝ))

private lemma kolmogorovSuperpose_apply (n : ℕ) (ψ : ksPsi n)
    (g : Fin (2 * n + 1) → ℝ →ᵇ ℝ) (x : ksX n) :
    kolmogorovSuperpose n ψ g x = ∑ q, g q (kolmogorovInner n ψ q x) := rfl

private lemma kolmogorovInner_apply (n : ℕ) (ψ : ksPsi n)
    (q : Fin (2 * n + 1)) (x : ksX n) :
    kolmogorovInner n ψ q x = ∑ p, ψ q p (x p) := rfl

/-- For fixed outer `g`, superposition is continuous in `ψ`. -/
private lemma continuous_kolmogorovSuperpose_ψ (n : ℕ)
    (g : Fin (2 * n + 1) → ℝ →ᵇ ℝ) :
    Continuous fun ψ : ksPsi n => kolmogorovSuperpose n ψ g := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun s : ksPsi n × ksX n => ∑ q, g q (∑ p, s.1 q p (s.2 p))
  apply continuous_finsetSum
  intro q _
  refine Continuous.comp (g q).continuous ?_
  apply continuous_finsetSum
  intro p _
  apply Continuous.eval
  · exact (continuous_apply p).comp ((continuous_apply q).comp continuous_fst)
  · exact (continuous_apply p).comp continuous_snd

/-- The good set is open. -/
private lemma isOpen_kolmogorovGoodSet (n : ℕ) (f : C(ksX n, ℝ)) :
    IsOpen (kolmogorovGoodSet n f) := by
  have hunion : kolmogorovGoodSet n f
      = ⋃ (g : Fin (2 * n + 1) → ℝ →ᵇ ℝ)
        (_ : ∀ q, ‖g q‖ ≤ ‖f‖ / ((n : ℝ) + 1)),
        (fun ψ : ksPsi n => kolmogorovSuperpose n ψ g) ⁻¹'
          Metric.ball f (ksTheta n * ‖f‖) := by
    ext ψ
    simp only [kolmogorovGoodSet, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_preimage, Metric.mem_ball]
    constructor
    · rintro ⟨g, hg, hlt⟩
      refine ⟨g, hg, ?_⟩
      rwa [dist_eq_norm, norm_sub_rev]
    · rintro ⟨g, hg, hmem⟩
      refine ⟨g, hg, ?_⟩
      rwa [dist_eq_norm, norm_sub_rev] at hmem
  rw [hunion]
  apply isOpen_iUnion
  intro g
  apply isOpen_iUnion
  intro _
  exact IsOpen.preimage (continuous_kolmogorovSuperpose_ψ n g) Metric.isOpen_ball

/-- Floor bounds for the grid index argument. -/
private lemma ksGrid_floor {n N : ℕ} (q : Fin (2 * n + 1)) {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ ((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1)
      ∧ ((ksIdx n N q t : ℕ) : ℝ)
        ≤ ((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1)
      ∧ ((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1)
        < ((ksIdx n N q t : ℕ) : ℝ) + 1 := by
  have hq : (q.val : ℝ) ≤ 2 * (n : ℝ) := by
    have hqlt := q.isLt
    have h1 : q.val ≤ 2 * n := by omega
    have h2 : (q.val : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_cast
    linarith
  have hM : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hNt : (0 : ℝ) ≤ (N : ℝ) * t := by positivity
  have hy0 : 0 ≤ ((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1) := by
    apply div_nonneg _ hM.le
    linarith [hq, hNt]
  exact ⟨hy0, Nat.floor_le hy0, Nat.lt_floor_add_one _⟩

/-- Grid index bounds: (i)-(iv). -/
private lemma ksGrid_mem {n N : ℕ} (hN : 1 ≤ N) (q : Fin (2 * n + 1)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ksIdx n N q t ≤ N
      ∧ (∀ i < ksIdx n N q t, ksGap n q i + 1 ≤ (N : ℝ) * t)
      ∧ (∀ i, ksIdx n N q t < i → (N : ℝ) * t ≤ ksGap n q i)
      ∧ ksGap n q (ksIdx n N q t) - 2 * (n : ℝ) ≤ (N : ℝ) * t
      ∧ (N : ℝ) * t < ksGap n q (ksIdx n N q t) + 1 := by
  obtain ⟨hy0, hle, hlt⟩ := ksGrid_floor q ht0
  have hMpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hL : ((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1)
      ≤ (N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ) :=
    (le_div_iff₀ hMpos).mp hle
  have hR : (N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)
      < (((ksIdx n N q t : ℕ) : ℝ) + 1) * (2 * (n : ℝ) + 1) :=
    (div_lt_iff₀ hMpos).mp hlt
  have hgap : ∀ i, ksGap n q i
      = (i : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) := fun i => rfl
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (q.val : ℝ) := by positivity
  have hMnn : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := hMpos.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hzN : (N : ℝ) * t ≤ (N : ℝ) := by
      calc (N : ℝ) * t ≤ (N : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left ht1 (by positivity)
        _ = (N : ℝ) := mul_one _
    have e1 : (0 : ℝ) ≤ 2 * (n : ℝ) * ((N : ℝ) - 1) := by
      apply mul_nonneg _ (by linarith)
      positivity
    have h1 : (N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)
        ≤ (N : ℝ) * (2 * (n : ℝ) + 1) := by
      have hkey : (N : ℝ) * (2 * (n : ℝ) + 1)
          - ((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ))
          = 2 * (n : ℝ) * ((N : ℝ) - 1) + (q.val : ℝ)
            + ((N : ℝ) - (N : ℝ) * t) := by ring
      linarith [hkey, e1, hq0, hzN]
    have hyN1 : ((N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)) / (2 * (n : ℝ) + 1)
        < ((N + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hMpos, Nat.cast_add, Nat.cast_one]
      calc (N : ℝ) * t + 2 * (n : ℝ) - (q.val : ℝ)
          ≤ (N : ℝ) * (2 * (n : ℝ) + 1) := h1
        _ < ((N : ℝ) + 1) * (2 * (n : ℝ) + 1) :=
            mul_lt_mul_of_pos_right (by linarith) hMpos
    have hltN : ksIdx n N q t < N + 1 := (Nat.floor_lt hy0).mpr hyN1
    omega
  · intro i hi
    have hi1 : i + 1 ≤ ksIdx n N q t := hi
    have hiR : ((i : ℕ) : ℝ) + 1 ≤ ((ksIdx n N q t : ℕ) : ℝ) := by
      exact_mod_cast hi1
    have hiM : ((i : ℕ) : ℝ) * (2 * (n : ℝ) + 1)
        ≤ (((ksIdx n N q t : ℕ) : ℝ) - 1) * (2 * (n : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right _ hMnn
      linarith
    rw [hgap]
    linarith [hL, hiM]
  · intro i hi
    have hi1 : ksIdx n N q t + 1 ≤ i := hi
    have hiR : ((ksIdx n N q t : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
      exact_mod_cast hi1
    have hiM : (((ksIdx n N q t : ℕ) : ℝ) + 1) * (2 * (n : ℝ) + 1)
        ≤ ((i : ℕ) : ℝ) * (2 * (n : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right _ hMnn
      linarith
    rw [hgap]
    linarith [hR, hiM, hn0]
  · rw [hgap]
    linarith [hL]
  · rw [hgap]
    linarith [hR]

/-- Grid fact (v): outside a gap, `z ≤ a k`. -/
private lemma ksGrid_not_bad_le {n N : ℕ} (hN : 1 ≤ N) (q : Fin (2 * n + 1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb : ¬ ksBad n N q t) :
    (N : ℝ) * t ≤ ksGap n q (ksIdx n N q t) := by
  by_contra hcon
  have hlt : ksGap n q (ksIdx n N q t) < (N : ℝ) * t := lt_of_not_ge hcon
  apply hb
  obtain ⟨-, _, _, -, hhi⟩ := ksGrid_mem hN q ht0 ht1
  have hgap : ksGap n q (ksIdx n N q t)
      = ((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) := rfl
  refine ⟨(q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ), ?_, ?_, ?_⟩
  · rw [Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt
    · omega
    · have hqlt := q.isLt
      exact_mod_cast hqlt
  · have hcast : ((((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ)) : ℤ)
        : ℝ) = ksGap n q (ksIdx n N q t) := by
      rw [hgap]
      push_cast
      ring
    rw [hcast]
    exact hlt
  · have hcast : ((((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ)) : ℤ)
        : ℝ) = ksGap n q (ksIdx n N q t) := by
      rw [hgap]
      push_cast
      ring
    rw [hcast]
    exact hhi

/-- Grid fact (vi): in a gap, `a k < z` and `k < N`. -/
private lemma ksGrid_bad_lt {n N : ℕ} (hN : 1 ≤ N) (q : Fin (2 * n + 1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb : ksBad n N q t) :
    ksGap n q (ksIdx n N q t) < (N : ℝ) * t ∧ ksIdx n N q t < N := by
  obtain ⟨m, hmod, hm1, hm2⟩ := hb
  obtain ⟨-, _, _, hlo, hhi⟩ := ksGrid_mem hN q ht0 ht1
  have hgap : ksGap n q (ksIdx n N q t)
      = ((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) := rfl
  have hAmod : ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ))
      % ((2 * n + 1 : ℕ) : ℤ) = (q.val : ℤ) := by
    rw [Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt
    · omega
    · have hqlt := q.isLt
      exact_mod_cast hqlt
  have hsub0 : (m - ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ)))
      % ((2 * n + 1 : ℕ) : ℤ) = 0 := by
    have heq : m % ((2 * n + 1 : ℕ) : ℤ)
        = ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ))
          % ((2 * n + 1 : ℕ) : ℤ) := by
      rw [hmod, hAmod]
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp heq
  have hdvd : ((2 * n + 1 : ℕ) : ℤ)
      ∣ (m - ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ))) :=
    Int.dvd_iff_emod_eq_zero.mpr hsub0
  have hAcast : ((((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ)) : ℤ)
      : ℝ) = ksGap n q (ksIdx n N q t) := by
    rw [hgap]
    push_cast
    ring
  have hMcast : ((((2 * n + 1 : ℕ)) : ℤ) : ℝ) = 2 * (n : ℝ) + 1 := by
    rw [Int.cast_natCast]
    norm_cast
  have hbound : |m - ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ))|
      < ((2 * n + 1 : ℕ) : ℤ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hr : |(m : ℝ) - ksGap n q (ksIdx n N q t)|
        < (((2 * n + 1 : ℕ) : ℤ) : ℝ) := by
      rw [hMcast, abs_lt]
      constructor
      · linarith [hm2, hlo]
      · linarith [hm1, hhi, hn0]
    have hr2 : |(((m - ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ)
        * (ksIdx n N q t : ℤ)) : ℤ)) : ℝ)| < ((((2 * n + 1 : ℕ) : ℤ)) : ℝ) := by
      rw [Int.cast_sub, hAcast]
      exact hr
    rw [← Int.cast_abs] at hr2
    exact_mod_cast hr2
  have hdeq : m - ((q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ))
      = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hbound
  have hmA : m
      = (q.val : ℤ) + ((2 * n + 1 : ℕ) : ℤ) * (ksIdx n N q t : ℤ) :=
    sub_eq_zero.mp hdeq
  have hlt : ksGap n q (ksIdx n N q t) < (N : ℝ) * t := by
    rw [← hAcast, ← hmA]
    exact hm1
  refine ⟨hlt, ?_⟩
  have hzN : (N : ℝ) * t ≤ (N : ℝ) := by
    calc (N : ℝ) * t ≤ (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = (N : ℝ) := mul_one _
  have hk_le : ((ksIdx n N q t : ℕ) : ℝ) ≤ ksGap n q (ksIdx n N q t) := by
    have h1 : ((ksIdx n N q t : ℕ) : ℝ)
        ≤ ((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1) :=
      le_mul_of_one_le_right (by positivity) (by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith)
    have h2 : (0 : ℝ) ≤ (q.val : ℝ) := by positivity
    rw [hgap]
    linarith
  have hltN : ((ksIdx n N q t : ℕ) : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt hk_le (lt_of_lt_of_le hlt hzN)
  exact_mod_cast hltN

/-- Grid fact (vii): representative distance bound. -/
private lemma ksGrid_rep {n N : ℕ} (hN : 1 ≤ N) (q : Fin (2 * n + 1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |t - (ksRep n N q (ksIdx n N q t) : ℝ)| ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
  obtain ⟨-, _, _, hlo, hhi⟩ := ksGrid_mem hN q ht0 ht1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hgap : ksGap n q (ksIdx n N q t)
      = ((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) := rfl
  set ℓ : ℝ := (((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ)
    - 2 * (n : ℝ)) / (N : ℝ) with hℓ
  have hNℓ : (N : ℝ) * ℓ = ksGap n q (ksIdx n N q t) - 2 * (n : ℝ) := by
    rw [hℓ, mul_div_cancel₀ _ hNne, hgap]
  have hmain : |t - ℓ| ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
    rw [le_div_iff₀ hN0]
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hN0.le
    have hmul : |t - ℓ| * (N : ℝ)
        = |(N : ℝ) * t - (ksGap n q (ksIdx n N q t) - 2 * (n : ℝ))| := by
      have heq : (t - ℓ) * (N : ℝ)
          = (N : ℝ) * t - (ksGap n q (ksIdx n N q t) - 2 * (n : ℝ)) := by
        linear_combination -hNℓ
      rw [← heq, abs_mul, abs_of_nonneg hNnn]
    rw [hmul, abs_of_nonneg (by linarith : (0 : ℝ)
      ≤ (N : ℝ) * t - (ksGap n q (ksIdx n N q t) - 2 * (n : ℝ)))]
    linarith [hhi]
  have hself : (Set.projIcc 0 1 zero_le_one t : ℝ) = t :=
    congrArg Subtype.val
      (Set.projIcc_of_mem zero_le_one (show t ∈ Set.Icc (0 : ℝ) 1 from ⟨ht0, ht1⟩))
  have hrep : ((ksRep n N q (ksIdx n N q t) : ksI) : ℝ)
      = (Set.projIcc 0 1 zero_le_one ℓ : ℝ) := rfl
  calc |t - (ksRep n N q (ksIdx n N q t) : ℝ)|
      = |(Set.projIcc 0 1 zero_le_one t : ℝ)
        - (Set.projIcc 0 1 zero_le_one ℓ : ℝ)| := by
        rw [hself, hrep]
    _ ≤ |t - ℓ| := Set.abs_projIcc_sub_projIcc zero_le_one
    _ ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := hmain

/-- Grid fact (viii): next representative distance bound in a gap. -/
private lemma ksGrid_rep_succ {n N : ℕ} (hN : 1 ≤ N) (q : Fin (2 * n + 1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hb : ksBad n N q t) :
    |t - (ksRep n N q (ksIdx n N q t + 1) : ℝ)|
      ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
  obtain ⟨hlt, -⟩ := ksGrid_bad_lt hN q ht0 ht1 hb
  obtain ⟨-, _, _, -, hhi⟩ := ksGrid_mem hN q ht0 ht1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hgap : ksGap n q (ksIdx n N q t)
      = ((ksIdx n N q t : ℕ) : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ) := rfl
  set ℓ' : ℝ := ((((ksIdx n N q t + 1 : ℕ)) : ℝ) * (2 * (n : ℝ) + 1) + (q.val : ℝ)
    - 2 * (n : ℝ)) / (N : ℝ) with hℓ'
  have hNℓ' : (N : ℝ) * ℓ' = ksGap n q (ksIdx n N q t) + 1 := by
    rw [hℓ', mul_div_cancel₀ _ hNne, hgap]
    push_cast
    ring
  have hmain : |t - ℓ'| ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
    rw [le_div_iff₀ hN0]
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hN0.le
    have hmul : |t - ℓ'| * (N : ℝ)
        = |(N : ℝ) * t - (ksGap n q (ksIdx n N q t) + 1)| := by
      have heq : (t - ℓ') * (N : ℝ)
          = (N : ℝ) * t - (ksGap n q (ksIdx n N q t) + 1) := by
        linear_combination -hNℓ'
      rw [← heq, abs_mul, abs_of_nonneg hNnn]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    rw [hmul, abs_le]
    constructor
    · linarith [hlt, hn0]
    · linarith [hhi, hn0]
  have hself : (Set.projIcc 0 1 zero_le_one t : ℝ) = t :=
    congrArg Subtype.val
      (Set.projIcc_of_mem zero_le_one (show t ∈ Set.Icc (0 : ℝ) 1 from ⟨ht0, ht1⟩))
  have hrep' : ((ksRep n N q (ksIdx n N q t + 1) : ksI) : ℝ)
      = (Set.projIcc 0 1 zero_le_one ℓ' : ℝ) := rfl
  calc |t - (ksRep n N q (ksIdx n N q t + 1) : ℝ)|
      = |(Set.projIcc 0 1 zero_le_one t : ℝ)
        - (Set.projIcc 0 1 zero_le_one ℓ' : ℝ)| := by
        rw [hself, hrep']
    _ ≤ |t - ℓ'| := Set.abs_projIcc_sub_projIcc zero_le_one
    _ ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := hmain

/-- At most one family is bad at a point. -/
private lemma ksBad_unique {n N : ℕ} {t : ℝ} {q q' : Fin (2 * n + 1)}
    (hq : ksBad n N q t) (hq' : ksBad n N q' t) : q = q' := by
  obtain ⟨m, hmod, hm1, hm2⟩ := hq
  obtain ⟨m', hmod', hm1', hm2'⟩ := hq'
  have hmeq : m = m' := by
    have h1 : (m : ℝ) < (m' : ℝ) + 1 := by linarith [hm1, hm2']
    have h2 : (m' : ℝ) < (m : ℝ) + 1 := by linarith [hm1', hm2]
    have h1' : m < m' + 1 := by exact_mod_cast h1
    have h2' : m' < m + 1 := by exact_mod_cast h2
    omega
  subst hmeq
  have hqq : (q.val : ℤ) = (q'.val : ℤ) := by
    rw [← hmod, ← hmod']
  have hqqN : q.val = q'.val := by exact_mod_cast hqq
  exact Fin.ext hqqN

open scoped Classical in
/-- At most `n` families are bad somewhere on `x`. -/
private lemma card_ksBad_le {n N : ℕ} (x : ksX n) :
    (Finset.univ.filter
      (fun q : Fin (2 * n + 1) => ∃ p, ksBad n N q ((x p : ksI) : ℝ))).card
      ≤ n := by
  have hsub : Finset.univ.filter
        (fun q : Fin (2 * n + 1) => ∃ p, ksBad n N q ((x p : ksI) : ℝ))
      ⊆ Finset.univ.biUnion (fun p : Fin n =>
        Finset.univ.filter
          (fun q : Fin (2 * n + 1) => ksBad n N q ((x p : ksI) : ℝ))) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨-, p, hp⟩ := hq
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_univ p, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hp⟩⟩
  calc (Finset.univ.filter
        (fun q : Fin (2 * n + 1) => ∃ p, ksBad n N q ((x p : ksI) : ℝ))).card
      ≤ (Finset.univ.biUnion (fun p : Fin n =>
          Finset.univ.filter
            (fun q : Fin (2 * n + 1) => ksBad n N q ((x p : ksI) : ℝ)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ _p : Fin n, 1 := by
        have h := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)))
          (t := fun p : Fin n => Finset.univ.filter
            (fun q : Fin (2 * n + 1) => ksBad n N q ((x p : ksI) : ℝ)))
        refine le_trans h ?_
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.card_le_one]
        intro q hq q' hq'
        rw [Finset.mem_filter] at hq hq'
        exact ksBad_unique hq.2 hq'.2
    _ = n := by simp

/-- Bounds for points of the unit interval. -/
private lemma ksI_bounds (t : ksI) : (0 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 := t.2

/-- 1-D step perturbation with prescribed plateau values. -/
private lemma exists_stepRamp_perturbation_1d {n N : ℕ} (hN : 1 ≤ N)
    (q : Fin (2 * n + 1)) (ψ₀ : C(ksI, ℝ)) {τ : ℝ}
    (hosc : ∀ s t : ksI, |(s : ℝ) - (t : ℝ)| ≤ (2 * (n : ℝ) + 1) / (N : ℝ) →
      |ψ₀ s - ψ₀ t| < τ)
    (c : ℕ → ℝ) (hc : ∀ k ≤ N, |c k - ψ₀ (ksRep n N q k)| < τ) :
    ∃ ψ₁ : C(ksI, ℝ), (∀ t : ksI, |ψ₁ t - ψ₀ t| < 2 * τ)
      ∧ ∀ t : ksI, ¬ ksBad n N q (t : ℝ) → ψ₁ t = c (ksIdx n N q (t : ℝ)) := by
  have hcont : Continuous
      fun t : ksI => stepRamp c (ksGap n q) N ((N : ℝ) * (t : ℝ)) := by
    apply Continuous.comp (continuous_stepRamp c (ksGap n q) N)
    exact continuous_const.mul continuous_subtype_val
  set ψ₁ : C(ksI, ℝ) :=
    ⟨fun t => stepRamp c (ksGap n q) N ((N : ℝ) * (t : ℝ)), hcont⟩ with hψ₁def
  have hψ₁t : ∀ t : ksI,
      ψ₁ t = stepRamp c (ksGap n q) N ((N : ℝ) * (t : ℝ)) := fun t => rfl
  have hgood : ∀ t : ksI, ¬ ksBad n N q (t : ℝ) →
      ψ₁ t = c (ksIdx n N q (t : ℝ)) := by
    intro t hb
    obtain ⟨ht0, ht1⟩ := ksI_bounds t
    rw [hψ₁t t]
    apply stepRamp_eq_of_between
    · exact (ksGrid_mem hN q ht0 ht1).1
    · intro i hi
      exact (ksGrid_mem hN q ht0 ht1).2.1 i hi
    · intro i hki _
      rcases eq_or_lt_of_le hki with rfl | hlt
      · exact ksGrid_not_bad_le hN q ht0 ht1 hb
      · exact (ksGrid_mem hN q ht0 ht1).2.2.1 i hlt
  refine ⟨ψ₁, ?_, hgood⟩
  intro t
  obtain ⟨ht0, ht1⟩ := ksI_bounds t
  have hkN : ksIdx n N q (t : ℝ) ≤ N := (ksGrid_mem hN q ht0 ht1).1
  have e1 : |c (ksIdx n N q (t : ℝ)) - ψ₀ t| < 2 * τ := by
    have h1 := hc _ hkN
    have hrep := ksGrid_rep hN q ht0 ht1
    have h2 := hosc (ksRep n N q (ksIdx n N q (t : ℝ))) t (by
      rw [abs_sub_comm]
      exact hrep)
    calc |c (ksIdx n N q (t : ℝ)) - ψ₀ t|
        ≤ |c (ksIdx n N q (t : ℝ)) - ψ₀ (ksRep n N q (ksIdx n N q (t : ℝ)))|
          + |ψ₀ (ksRep n N q (ksIdx n N q (t : ℝ))) - ψ₀ t| :=
          abs_sub_le _ _ _
      _ < τ + τ := add_lt_add h1 h2
      _ = 2 * τ := by ring
  by_cases hb : ksBad n N q (t : ℝ)
  · obtain ⟨hlt, hltN⟩ := ksGrid_bad_lt hN q ht0 ht1 hb
    obtain ⟨-, hlo_all, hhi_all, -, hhi⟩ := ksGrid_mem hN q ht0 ht1
    rw [hψ₁t t]
    obtain ⟨s, hs0, hs1, hseq⟩ := stepRamp_mem_segment c (ksGap n q) N
      (ksIdx n N q (t : ℝ)) ((N : ℝ) * (t : ℝ)) hltN hlo_all hlt.le hhi.le
      (fun i hi _ => hhi_all i hi)
    have e2 : |c (ksIdx n N q (t : ℝ) + 1) - ψ₀ t| < 2 * τ := by
      have h1 := hc _ hltN
      have hrep := ksGrid_rep_succ hN q ht0 ht1 hb
      have h2 := hosc (ksRep n N q (ksIdx n N q (t : ℝ) + 1)) t (by
        rw [abs_sub_comm]
        exact hrep)
      calc |c (ksIdx n N q (t : ℝ) + 1) - ψ₀ t|
          ≤ |c (ksIdx n N q (t : ℝ) + 1) - ψ₀ (ksRep n N q (ksIdx n N q (t : ℝ) + 1))|
            + |ψ₀ (ksRep n N q (ksIdx n N q (t : ℝ) + 1)) - ψ₀ t| :=
            abs_sub_le _ _ _
        _ < τ + τ := add_lt_add h1 h2
        _ = 2 * τ := by ring
    have hbound : |stepRamp c (ksGap n q) N ((N : ℝ) * (t : ℝ)) - ψ₀ t|
        ≤ max |c (ksIdx n N q (t : ℝ)) - ψ₀ t|
          |c (ksIdx n N q (t : ℝ) + 1) - ψ₀ t| :=
      stepRamp_abs_le_max c (ksIdx n N q (t : ℝ)) _ _ s hs0 hs1 hseq
    calc |stepRamp c (ksGap n q) N ((N : ℝ) * (t : ℝ)) - ψ₀ t|
        ≤ max |c (ksIdx n N q (t : ℝ)) - ψ₀ t|
          |c (ksIdx n N q (t : ℝ) + 1) - ψ₀ t| := hbound
      _ < 2 * τ := max_lt_iff.mpr ⟨e1, e2⟩
  · rw [hgood t hb]
    exact e1

/-- Separating perturbation: close `ψ'` with injective inner-sum values. -/
private lemma exists_separating_perturbation {n N : ℕ} (hN : 1 ≤ N)
    (ψ : ksPsi n) {ε : ℝ} (hε : 0 < ε)
    (hosc : ∀ q p (s t : ksI),
      |(s : ℝ) - (t : ℝ)| ≤ (2 * (n : ℝ) + 1) / (N : ℝ) →
      |ψ q p s - ψ q p t| < ε / 4) :
    ∃ ψ' : ksPsi n, ∃ v : Fin (2 * n + 1) → (Fin n → Fin (N + 1)) → ℝ,
      dist ψ' ψ < ε
        ∧ (∀ q, Function.Injective (v q))
        ∧ ∀ q (x : ksX n) (j : Fin n → Fin (N + 1)),
          (∀ p, ¬ ksBad n N q ((x p : ksI) : ℝ)
            ∧ (j p).val = ksIdx n N q ((x p : ksI) : ℝ)) →
          kolmogorovInner n ψ' q x = v q j := by
  have hE : Function.Injective (fun j : Fin n → Fin (N + 1) =>
      ∑ p, (j p).val * (N + 1) ^ (p.val : ℕ)) := by
    have hfun : (fun j : Fin n → Fin (N + 1) =>
        ∑ p, (j p).val * (N + 1) ^ (p.val : ℕ))
        = Fin.val ∘ finFunctionFinEquiv := by
      funext j
      exact (finFunctionFinEquiv_apply j).symm
    rw [hfun]
    exact Fin.val_injective.comp finFunctionFinEquiv.injective
  have hB1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  have hpow_mono : ∀ p : Fin n,
      (((N : ℝ) + 1) ^ ((p.val : ℕ) + 1)) ≤ (((N : ℝ) + 1) ^ n) :=
    fun p => pow_le_pow_right₀ hB1 p.isLt
  have hη0 : (0 : ℝ) < ε / (4 * (((N : ℝ) + 1) ^ n)) := by
    apply div_pos hε
    positivity
  obtain ⟨η, hηpos, hηlt, hinj⟩ := exists_small_injective_perturbation
    (fun q (j : Fin n → Fin (N + 1)) => ∑ p, ψ q p (ksRep n N q (j p).val))
    (fun j : Fin n → Fin (N + 1) => ∑ p, (j p).val * (N + 1) ^ (p.val : ℕ))
    hE hη0
  have hN6 : ∀ q p, ∃ ψ₁ : C(ksI, ℝ), (∀ t, |ψ₁ t - ψ q p t| < 2 * (ε / 4))
      ∧ ∀ t : ksI, ¬ ksBad n N q (t : ℝ) →
        ψ₁ t = ψ q p (ksRep n N q (ksIdx n N q (t : ℝ)))
          + η * ((ksIdx n N q (t : ℝ) : ℕ) : ℝ)
            * (((N : ℝ) + 1) ^ (p.val : ℕ)) := by
    intro q p
    refine exists_stepRamp_perturbation_1d hN q (ψ q p) (hosc q p)
      (fun k => ψ q p (ksRep n N q k)
        + η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))) ?_
    intro k hk
    have hηnn : (0 : ℝ) ≤ η := hηpos.le
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have hkB : (k : ℝ) ≤ (N : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith
    have hBpnn : (0 : ℝ) ≤ (((N : ℝ) + 1) ^ (p.val : ℕ)) := by positivity
    have hstep2 : η * (((N : ℝ) + 1) ^ n) < ε / 4 := by
      have hpos : (0 : ℝ) < 4 * (((N : ℝ) + 1) ^ n) := by positivity
      have h1 : η * (4 * (((N : ℝ) + 1) ^ n)) < ε :=
        (lt_div_iff₀ hpos).mp hηlt
      have h2 : 4 * (η * (((N : ℝ) + 1) ^ n)) < ε := by linarith [h1]
      linarith
    have hstep1 : η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))
        ≤ η * (((N : ℝ) + 1) ^ n) := by
      have hkb : (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))
          ≤ (((N : ℝ) + 1) ^ n) := by
        calc (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))
            ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ (p.val : ℕ)) :=
              mul_le_mul_of_nonneg_right hkB hBpnn
          _ = (((N : ℝ) + 1) ^ ((p.val : ℕ) + 1)) := by
              rw [pow_succ]
              ring
          _ ≤ (((N : ℝ) + 1) ^ n) := hpow_mono p
      calc η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))
          = η * ((k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))) := by ring
        _ ≤ η * (((N : ℝ) + 1) ^ n) :=
            mul_le_mul_of_nonneg_left hkb hηnn
    have heq : ψ q p (ksRep n N q k)
          + η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))
          - ψ q p (ksRep n N q k)
        = η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ)) := by ring
    rw [heq, abs_of_nonneg (by positivity : (0 : ℝ)
      ≤ η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ)))]
    calc η * (k : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))
        ≤ η * (((N : ℝ) + 1) ^ n) := hstep1
      _ < ε / 4 := hstep2
  choose ψ' hψ'close hψ'good using hN6
  have hcomp : ∀ q p, dist (ψ' q p) (ψ q p) ≤ ε / 2 := by
    intro q p
    rw [ContinuousMap.dist_le (by positivity : (0 : ℝ) ≤ ε / 2)]
    intro t
    have h := hψ'close q p t
    rw [dist_eq_norm, Real.norm_eq_abs]
    linarith [h]
  have hdist : dist ψ' ψ ≤ ε / 2 := by
    rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ ε / 2)]
    intro q
    rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ ε / 2)]
    intro p
    exact hcomp q p
  refine ⟨ψ', (fun q (j : Fin n → Fin (N + 1)) =>
    (∑ p, ψ q p (ksRep n N q (j p).val))
      + η * ((∑ p, (j p).val * (N + 1) ^ (p.val : ℕ) : ℕ) : ℝ)), ?_, ?_, ?_⟩
  · have hε2 : ε / 2 < ε := by linarith [hε]
    exact lt_of_le_of_lt hdist hε2
  · intro q
    exact hinj q
  · intro q x j hj
    have hterm : ∀ p, ψ' q p (x p)
        = ψ q p (ksRep n N q (j p).val)
          + η * ((((j p).val : ℕ)) : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ)) := by
      intro p
      obtain ⟨hnb, hjeq⟩ := hj p
      have h1 := hψ'good q p (x p) hnb
      rw [← hjeq] at h1
      exact h1
    have hLHS : kolmogorovInner n ψ' q x
        = ∑ p, (ψ q p (ksRep n N q (j p).val)
          + η * ((((j p).val : ℕ)) : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))) := by
      rw [kolmogorovInner_apply]
      apply Finset.sum_congr rfl
      intro p _
      exact hterm p
    have hRHS : (∑ p, ψ q p (ksRep n N q (j p).val))
          + η * ((∑ p, (j p).val * (N + 1) ^ (p.val : ℕ) : ℕ) : ℝ)
        = ∑ p, (ψ q p (ksRep n N q (j p).val)
          + η * ((((j p).val : ℕ)) : ℝ) * (((N : ℝ) + 1) ^ (p.val : ℕ))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      push_cast
      ring
    rw [hLHS]
    exact hRHS.symm

open scoped Classical in
/-- A separating perturbation lies in the good set. -/
private lemma mem_kolmogorovGoodSet_of_separating {n N : ℕ} (hN : 1 ≤ N)
    (f : C(ksX n, ℝ)) (hf0 : f ≠ 0)
    (hf : ∀ x y : ksX n, dist x y ≤ (2 * (n : ℝ) + 1) / (N : ℝ) →
      |f x - f y| ≤ ‖f‖ / (4 * (2 * (n : ℝ) + 1)))
    (ψ' : ksPsi n) (v : Fin (2 * n + 1) → (Fin n → Fin (N + 1)) → ℝ)
    (hinj : ∀ q, Function.Injective (v q))
    (hsep : ∀ q (x : ksX n) (j : Fin n → Fin (N + 1)),
      (∀ p, ¬ ksBad n N q ((x p : ksI) : ℝ)
        ∧ (j p).val = ksIdx n N q ((x p : ksI) : ℝ)) →
      kolmogorovInner n ψ' q x = v q j) :
    ψ' ∈ kolmogorovGoodSet n f := by
  have hMpos : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf0
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hN8 : ∀ q : Fin (2 * n + 1), ∃ gq : ℝ →ᵇ ℝ,
      ‖gq‖ ≤ ‖f‖ / ((n : ℝ) + 1)
        ∧ ∀ j : Fin n → Fin (N + 1),
          gq (v q j)
            = f (fun p => ksRep n N q (j p).val) / ((n : ℝ) + 1) := by
    intro q
    have hy : ∀ j : Fin n → Fin (N + 1),
        |f (fun p => ksRep n N q (j p).val) / ((n : ℝ) + 1)|
          ≤ ‖f‖ / ((n : ℝ) + 1) := by
      intro j
      have h1 : |f (fun p => ksRep n N q (j p).val)| ≤ ‖f‖ := by
        have h := ContinuousMap.norm_coe_le_norm f
          (fun p => ksRep n N q (j p).val)
        rwa [Real.norm_eq_abs] at h
      calc |f (fun p => ksRep n N q (j p).val) / ((n : ℝ) + 1)|
          = |f (fun p => ksRep n N q (j p).val)| / ((n : ℝ) + 1) := by
            rw [abs_div, abs_of_nonneg hnpos.le]
        _ ≤ ‖f‖ / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_right h1 hnpos.le
    obtain ⟨gq, hgq, hgy⟩ := exists_bcf_interpolate (v q) (hinj q)
      (fun j => f (fun p => ksRep n N q (j p).val) / ((n : ℝ) + 1))
      (‖f‖ / ((n : ℝ) + 1)) (by positivity) hy
    exact ⟨gq, hgq, hgy⟩
  choose g hg hgy using hN8
  refine ⟨g, hg, ?_⟩
  have hθM : (0 : ℝ) < ksTheta n * ‖f‖ := by
    change 0 < (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * ‖f‖
    positivity
  apply (ContinuousMap.norm_lt_iff _ hθM).mpr
  intro x
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  have hSx : kolmogorovSuperpose n ψ' g x
      = ∑ q, g q (kolmogorovInner n ψ' q x) := rfl
  rw [hSx]
  set G : Finset (Fin (2 * n + 1)) := Finset.univ.filter
    (fun q => ∀ p, ¬ ksBad n N q ((x p : ksI) : ℝ)) with hGdef
  have hGcard : n + 1 ≤ G.card := by
    have hdisj : Disjoint G (Finset.univ.filter
        (fun q : Fin (2 * n + 1) => ∃ p, ksBad n N q ((x p : ksI) : ℝ))) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      rw [hGdef, Finset.mem_filter] at hq1
      rw [Finset.mem_filter] at hq2
      obtain ⟨p, hp⟩ := hq2.2
      exact (hq1.2 p) hp
    have hunion : G ∪ (Finset.univ.filter
          (fun q : Fin (2 * n + 1) => ∃ p, ksBad n N q ((x p : ksI) : ℝ)))
        = Finset.univ := by
      ext q
      simp only [hGdef, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases h : ∃ p, ksBad n N q ((x p : ksI) : ℝ)
      · exact iff_of_true (Or.inr h) trivial
      · exact iff_of_true (Or.inl (fun p hb => h ⟨p, hb⟩)) trivial
    have hcard := card_ksBad_le (n := n) (N := N) x
    have hsum := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at hsum
    omega
  have hbound : ∀ q : Fin (2 * n + 1),
      |g q (kolmogorovInner n ψ' q x)| ≤ ‖f‖ / ((n : ℝ) + 1) := by
    intro q
    have h1 : ‖g q (kolmogorovInner n ψ' q x)‖ ≤ ‖g q‖ :=
      BoundedContinuousFunction.norm_coe_le_norm (g q) _
    have h2 : |g q (kolmogorovInner n ψ' q x)| ≤ ‖g q‖ := by
      rwa [Real.norm_eq_abs] at h1
    exact le_trans h2 (hg q)
  have hgood : ∀ q ∈ G, |g q (kolmogorovInner n ψ' q x) - f x / ((n : ℝ) + 1)|
      ≤ (‖f‖ / (4 * (2 * (n : ℝ) + 1))) / ((n : ℝ) + 1) := by
    intro q hq
    rw [hGdef, Finset.mem_filter] at hq
    have hmem : ∀ p : Fin n, ksIdx n N q ((x p : ksI) : ℝ) < N + 1 := by
      intro p
      have hk := (ksGrid_mem hN q (ksI_bounds (x p)).1
        (ksI_bounds (x p)).2).1
      omega
    set jq : Fin n → Fin (N + 1) := fun p =>
      ⟨ksIdx n N q ((x p : ksI) : ℝ), hmem p⟩ with hjqdef
    have hval : ∀ p, (jq p).val = ksIdx n N q ((x p : ksI) : ℝ) :=
      fun p => rfl
    have hsep_q : kolmogorovInner n ψ' q x = v q jq :=
      hsep q x jq (fun p => ⟨hq.2 p, hval p⟩)
    rw [hsep_q, hgy q jq]
    have hdist : dist x (fun p => ksRep n N q (ksIdx n N q ((x p : ksI) : ℝ)))
        ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
      rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) / (N : ℝ))]
      intro p
      have hrep := ksGrid_rep hN q (ksI_bounds (x p)).1 (ksI_bounds (x p)).2
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hrep
    have hdist' : dist x (fun p => ksRep n N q (jq p).val)
        ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
      have heq : (fun p => ksRep n N q (jq p).val)
          = (fun p => ksRep n N q (ksIdx n N q ((x p : ksI) : ℝ))) := by
        funext p
        rw [hval p]
      rw [heq]
      exact hdist
    have hfxi : |f x - f (fun p => ksRep n N q (jq p).val)|
        ≤ ‖f‖ / (4 * (2 * (n : ℝ) + 1)) := hf x _ hdist'
    calc |f (fun p => ksRep n N q (jq p).val) / ((n : ℝ) + 1)
          - f x / ((n : ℝ) + 1)|
        = |f (fun p => ksRep n N q (jq p).val) - f x| / ((n : ℝ) + 1) := by
          rw [← sub_div, abs_div, abs_of_nonneg hnpos.le]
      _ = |f x - f (fun p => ksRep n N q (jq p).val)| / ((n : ℝ) + 1) := by
          rw [abs_sub_comm]
      _ ≤ (‖f‖ / (4 * (2 * (n : ℝ) + 1))) / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_right hfxi hnpos.le
  have hFx : |f x| ≤ ‖f‖ := by
    have h := ContinuousMap.norm_coe_le_norm f x
    rwa [Real.norm_eq_abs] at h
  have hN9 := abs_sub_sum_le_of_good (Fintype.card_fin (2 * n + 1)) G hGcard
    (‖f‖) (‖f‖ / (4 * (2 * (n : ℝ) + 1))) (f x) (by positivity) hFx
    (fun q => g q (kolmogorovInner n ψ' q x)) hgood hbound
  have hfin : |f x - ∑ q, g q (kolmogorovInner n ψ' q x)|
      ≤ (n : ℝ) * ‖f‖ / ((n : ℝ) + 1)
        + (2 * (n : ℝ) + 1) * (‖f‖ / (4 * (2 * (n : ℝ) + 1)))
          / ((n : ℝ) + 1) := hN9
  have heta : (2 * (n : ℝ) + 1) * (‖f‖ / (4 * (2 * (n : ℝ) + 1)))
        / ((n : ℝ) + 1) = ‖f‖ / (4 * ((n : ℝ) + 1)) := by
    have h2n1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h4 : (4 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [heta] at hfin
  have hθ : ksTheta n = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := rfl
  rw [hθ]
  have hstrict : (n : ℝ) * ‖f‖ / ((n : ℝ) + 1) + ‖f‖ / (4 * ((n : ℝ) + 1))
      < ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) * ‖f‖ := by
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    field_simp
    nlinarith [hMpos, hn0, hn1, h2, mul_pos hMpos hn1, mul_pos hMpos h2]
  exact lt_of_le_of_lt hfin hstrict

/-- The good set is dense for `f ≠ 0`. -/
private lemma dense_kolmogorovGoodSet {n : ℕ} (f : C(ksX n, ℝ)) (hf0 : f ≠ 0) :
    Dense (kolmogorovGoodSet n f) := by
  have hMpos : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf0
  have hηpos : (0 : ℝ) < ‖f‖ / (4 * (2 * (n : ℝ) + 1)) := by positivity
  have hfunif : UniformContinuous ⇑f :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  rw [Metric.uniformContinuous_iff] at hfunif
  obtain ⟨δf, hδf0, hδf⟩ := hfunif (‖f‖ / (4 * (2 * (n : ℝ) + 1))) hηpos
  rw [Metric.dense_iff]
  intro ψ r hr
  have hΦcont : Continuous
      fun t : ksI => fun q (p : Fin n) => ψ q p t := by
    refine continuous_pi fun q => continuous_pi fun p => (ψ q p).continuous
  have hΦunif : UniformContinuous
      (fun t : ksI => fun q (p : Fin n) => ψ q p t) :=
    CompactSpace.uniformContinuous_of_continuous hΦcont
  rw [Metric.uniformContinuous_iff] at hΦunif
  obtain ⟨δψ, hδψ0, hδψ⟩ := hΦunif (r / 4) (by positivity)
  obtain ⟨N, hN, hNlt⟩ :
      ∃ N : ℕ, 1 ≤ N ∧ (2 * (n : ℝ) + 1) / (N : ℝ) < min δf δψ := by
    obtain ⟨N0, hN0⟩ := exists_nat_gt ((2 * (n : ℝ) + 1) / min δf δψ)
    have hmin0 : (0 : ℝ) < min δf δψ := lt_min hδf0 hδψ0
    refine ⟨N0 + 1, by omega, ?_⟩
    have hN0pos : (0 : ℝ) < ((N0 + 1 : ℕ) : ℝ) := by positivity
    have hcast : ((N0 : ℕ) : ℝ) < ((N0 + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have h1 : (2 * (n : ℝ) + 1) / min δf δψ < ((N0 + 1 : ℕ) : ℝ) := by
      linarith [hN0, hcast]
    have h2 := (div_lt_iff₀ hmin0).mp h1
    rw [div_lt_iff₀ hN0pos]
    linarith [h2]
  have hmin_le_f : min δf δψ ≤ δf := min_le_left _ _
  have hmin_le_ψ : min δf δψ ≤ δψ := min_le_right _ _
  have hoscN : ∀ q p (s t : ksI),
      |(s : ℝ) - (t : ℝ)| ≤ (2 * (n : ℝ) + 1) / (N : ℝ) →
      |ψ q p s - ψ q p t| < r / 4 := by
    intro q p s t hst
    have h1 : dist s t ≤ (2 * (n : ℝ) + 1) / (N : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hst
    have hdist : dist s t < δψ :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le hNlt hmin_le_ψ)
    have hΦ := hδψ hdist
    rw [dist_pi_lt_iff (by positivity : (0 : ℝ) < r / 4)] at hΦ
    have hΦq := hΦ q
    rw [dist_pi_lt_iff (by positivity : (0 : ℝ) < r / 4)] at hΦq
    have hΦqp := hΦq p
    rw [Real.dist_eq] at hΦqp
    exact hΦqp
  have hfN : ∀ x y : ksX n, dist x y ≤ (2 * (n : ℝ) + 1) / (N : ℝ) →
      |f x - f y| ≤ ‖f‖ / (4 * (2 * (n : ℝ) + 1)) := by
    intro x y hxy
    have hdist : dist x y < δf :=
      lt_of_le_of_lt hxy (lt_of_lt_of_le hNlt hmin_le_f)
    have h := hδf hdist
    rw [Real.dist_eq] at h
    exact le_of_lt h
  obtain ⟨ψ', v, hclose, hinj, hsep⟩ :=
    exists_separating_perturbation (n := n) (N := N) hN ψ hr hoscN
  refine ⟨ψ', Metric.mem_ball.mpr hclose, ?_⟩
  exact mem_kolmogorovGoodSet_of_separating hN f hf0 hfN ψ' v hinj hsep

/-- One inner family works for a whole sequence of targets. -/
private lemma exists_mem_kolmogorovGoodSet_seq {n : ℕ}
    (u : ℕ → C(ksX n, ℝ)) :
    ∃ ψ : ksPsi n, ∀ k, u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k) := by
  have hopen : ∀ k, IsOpen
      {ψ : ksPsi n | u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k)} := by
    intro k
    by_cases hk : u k = 0
    · have huniv : {ψ : ksPsi n | u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k)}
          = Set.univ := by
        ext ψ
        simp [hk]
      rw [huniv]
      exact isOpen_univ
    · have hgood : {ψ : ksPsi n | u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k)}
          = kolmogorovGoodSet n (u k) := by
        ext ψ
        simp [hk]
      rw [hgood]
      exact isOpen_kolmogorovGoodSet n (u k)
  have hdense : ∀ k, Dense
      {ψ : ksPsi n | u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k)} := by
    intro k
    by_cases hk : u k = 0
    · have huniv : {ψ : ksPsi n | u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k)}
          = Set.univ := by
        ext ψ
        simp [hk]
      rw [huniv]
      exact dense_univ
    · have hgood : {ψ : ksPsi n | u k ≠ 0 → ψ ∈ kolmogorovGoodSet n (u k)}
          = kolmogorovGoodSet n (u k) := by
        ext ψ
        simp [hk]
      rw [hgood]
      exact dense_kolmogorovGoodSet (u k) hk
  have hbaire : BaireSpace (ksPsi n) := BaireSpace.of_completelyPseudoMetrizable
  have hnonempty : Nonempty (ksPsi n) := ⟨0⟩
  have hdi := dense_iInter_of_isOpen_nat hopen hdense
  obtain ⟨ψ, hψ⟩ := Dense.nonempty hdi
  refine ⟨ψ, fun k hk => ?_⟩
  have hmem := Set.mem_iInter.mp hψ k
  exact hmem hk

/-- Uniform one-step approximation with geometric rate. -/
private lemma exists_kolmogorov_inner_approx {n : ℕ} :
    ∃ ψ : ksPsi n, ∀ f : C(ksX n, ℝ),
      ∃ g : Fin (2 * n + 1) → ℝ →ᵇ ℝ, (∀ q, ‖g q‖ ≤ 2 * ‖f‖)
        ∧ ‖f - kolmogorovSuperpose n ψ g‖ ≤ ((1 + ksTheta n) / 2) * ‖f‖ := by
  have hne : Nonempty C(ksX n, ℝ) := ⟨0⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (α := C(ksX n, ℝ))
  obtain ⟨ψ, hψ⟩ := exists_mem_kolmogorovGoodSet_seq u
  refine ⟨ψ, fun f => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0
    refine ⟨fun _ => 0, fun q => ?_, ?_⟩
    · simp
    · have hS : kolmogorovSuperpose n ψ (fun _ => 0) = 0 := by
        ext x
        rw [kolmogorovSuperpose_apply]
        simp
      rw [hS]
      simp
  · have hMpos : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf0
    have hθ0 : (0 : ℝ) < ksTheta n := by
      change 0 < (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)
      positivity
    have hθ1 : ksTheta n < 1 := by
      change (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) < 1
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 * (n : ℝ) + 2)]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    set δ : ℝ := ((1 - ksTheta n) / 4) * ‖f‖ with hδdef
    have h1θ : (0 : ℝ) < 1 - ksTheta n := by linarith [hθ1]
    have hδ : (0 : ℝ) < δ := by
      rw [hδdef]
      positivity
    obtain ⟨k, hk⟩ := hu.exists_dist_lt f hδ
    have hnorm : ‖f - u k‖ < δ := by
      rwa [dist_eq_norm] at hk
    have hnorm2 : ‖u k - f‖ < δ := by
      rwa [norm_sub_rev]
    have hle : ‖f‖ ≤ ‖u k‖ + ‖f - u k‖ := by
      have heq : f = u k + (f - u k) := by abel
      conv_lhs => rw [heq]
      exact norm_add_le (u k) (f - u k)
    have hδlt : δ < ‖f‖ := by
      rw [hδdef]
      have h1 : ((1 - ksTheta n) / 4) < 1 := by linarith [hθ0]
      calc ((1 - ksTheta n) / 4) * ‖f‖ < 1 * ‖f‖ :=
            mul_lt_mul_of_pos_right h1 hMpos
        _ = ‖f‖ := one_mul _
    have huk_pos : (0 : ℝ) < ‖u k‖ := by linarith [hle, hnorm, hδlt]
    have huk0 : u k ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at huk_pos
      exact lt_irrefl _ huk_pos
    obtain ⟨g, hgN, hLT⟩ := hψ k huk0
    have huk_le : ‖u k‖ ≤ ‖f‖ + δ := by
      have heq : u k = f + (u k - f) := by abel
      have htri : ‖u k‖ ≤ ‖f‖ + ‖u k - f‖ := by
        conv_lhs => rw [heq]
        exact norm_add_le f (u k - f)
      linarith [htri, hnorm2.le]
    have hg2 : ∀ q, ‖g q‖ ≤ 2 * ‖f‖ := by
      intro q
      have h1 := hgN q
      have h2 : ‖u k‖ / ((n : ℝ) + 1) ≤ ‖u k‖ := by
        apply div_le_self (norm_nonneg _)
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith
      linarith [h1, h2, huk_le, hδlt]
    have hfin : ‖f - kolmogorovSuperpose n ψ g‖
        ≤ ((1 + ksTheta n) / 2) * ‖f‖ := by
      have htri : ‖f - kolmogorovSuperpose n ψ g‖
          ≤ ‖f - u k‖ + ‖u k - kolmogorovSuperpose n ψ g‖ := by
        have heq : f - kolmogorovSuperpose n ψ g
            = (f - u k) + (u k - kolmogorovSuperpose n ψ g) := by abel
        rw [heq]
        exact norm_add_le _ _
      have hub : ‖u k - kolmogorovSuperpose n ψ g‖
          < ksTheta n * (‖f‖ + δ) := by
        have hθnn : (0 : ℝ) ≤ ksTheta n := le_of_lt hθ0
        calc ‖u k - kolmogorovSuperpose n ψ g‖ < ksTheta n * ‖u k‖ := hLT
          _ ≤ ksTheta n * (‖f‖ + δ) :=
              mul_le_mul_of_nonneg_left huk_le hθnn
      have hδθ : δ + ksTheta n * (‖f‖ + δ)
          ≤ ((1 + ksTheta n) / 2) * ‖f‖ := by
        have hfactor : ((1 + ksTheta n) / 2) * ‖f‖
            - ((((1 - ksTheta n) / 4) * ‖f‖)
              + ksTheta n * (‖f‖ + (((1 - ksTheta n) / 4) * ‖f‖)))
            = ‖f‖ * ((1 - ksTheta n) ^ 2 / 4) := by ring
        have hnn : (0 : ℝ) ≤ ‖f‖ * ((1 - ksTheta n) ^ 2 / 4) := by positivity
        rw [hδdef] at ⊢
        linarith [hfactor, hnn]
      linarith [htri, hnorm.le, hub.le, hδθ]
    exact ⟨g, hg2, hfin⟩

/-- Iterating the one-step approximation yields an exact outer representation. -/
private lemma exists_kolmogorov_outer {n : ℕ} :
    ∃ ψ : ksPsi n, ∀ f : C(ksX n, ℝ), ∃ φ : Fin (2 * n + 1) → C(ℝ, ℝ),
      ∀ x, f x = ∑ q, φ q (∑ p, ψ q p (x p)) := by
  obtain ⟨ψ, hψ⟩ := exists_kolmogorov_inner_approx (n := n)
  set ρ : ℝ := (1 + ksTheta n) / 2 with hρdef
  choose g hgN hgA using hψ
  have hθ0 : (0 : ℝ) < ksTheta n := by
    change 0 < (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)
    positivity
  have hθ1 : ksTheta n < 1 := by
    change (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) < 1
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * (n : ℝ) + 2)]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρdef]; linarith [hθ0]
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith [hθ1]
  refine ⟨ψ, fun f => ?_⟩
  let F : ℕ → C(ksX n, ℝ) :=
    fun k => Nat.rec (motive := fun _ => C(ksX n, ℝ)) f
      (fun _ Fk => Fk - kolmogorovSuperpose n ψ (g Fk)) k
  have hF0 : F 0 = f := rfl
  have hFs : ∀ k, F (k + 1) = F k - kolmogorovSuperpose n ψ (g (F k)) :=
    fun k => rfl
  have hFk : ∀ k, ‖F k‖ ≤ ρ ^ k * ‖f‖ := by
    intro k
    induction k with
    | zero =>
      rw [hF0]
      simp
    | succ k ih =>
      calc ‖F (k + 1)‖ = ‖F k - kolmogorovSuperpose n ψ (g (F k))‖ := by
            rw [hFs k]
        _ ≤ ρ * ‖F k‖ := hgA (F k)
        _ ≤ ρ * (ρ ^ k * ‖f‖) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * ‖f‖ := by rw [pow_succ]; ring
  have hgFk : ∀ k (q : Fin (2 * n + 1)), ‖g (F k) q‖ ≤ 2 * (ρ ^ k * ‖f‖) := by
    intro k q
    calc ‖g (F k) q‖ ≤ 2 * ‖F k‖ := hgN (F k) q
      _ ≤ 2 * (ρ ^ k * ‖f‖) := mul_le_mul_of_nonneg_left (hFk k) (by norm_num)
  have hgeo : Summable (fun k : ℕ => 2 * (ρ ^ k * ‖f‖)) :=
    Summable.mul_left 2 ((summable_geometric_of_lt_one hρ0 hρ1).mul_right ‖f‖)
  have hsumm_bcf : ∀ q : Fin (2 * n + 1), Summable (fun k : ℕ => g (F k) q) := by
    intro q
    exact Summable.of_norm_bounded hgeo (fun k => hgFk k q)
  have hsumm_pt : ∀ (q : Fin (2 * n + 1)) (y : ℝ),
      Summable (fun k : ℕ => g (F k) q y) := by
    intro q y
    apply Summable.of_norm_bounded hgeo
    intro k
    calc ‖g (F k) q y‖ ≤ ‖g (F k) q‖ :=
            BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ 2 * (ρ ^ k * ‖f‖) := hgFk k q
  have hqHas : ∀ (q : Fin (2 * n + 1)) (y : ℝ),
      HasSum (fun k : ℕ => g (F k) q y) ((∑' k : ℕ, g (F k) q) y) := by
    intro q y
    exact (BoundedContinuousFunction.evalCLM ℝ y).hasSum (hsumm_bcf q).hasSum
  have hpow0 : Filter.Tendsto (fun K : ℕ => ρ ^ K * ‖f‖) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun K : ℕ => ρ ^ K * ‖f‖) Filter.atTop
        (nhds (0 * ‖f‖)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul tendsto_const_nhds
    simpa using h
  refine ⟨fun q => (∑' k : ℕ, g (F k) q).toContinuousMap, fun x => ?_⟩
  have hfin : ∀ s : Finset (Fin (2 * n + 1)),
      HasSum (fun k : ℕ => ∑ q ∈ s, g (F k) q (kolmogorovInner n ψ q x))
        (∑ q ∈ s, (∑' k : ℕ, g (F k) q) (kolmogorovInner n ψ q x)) := by
    intro s
    refine Finset.induction ?_ ?_ s
    · simp
    · intro a s has ih
      simp only [Finset.sum_insert has]
      exact HasSum.add (hqHas a (kolmogorovInner n ψ a x)) ih
  have hsumm_fin : ∀ s : Finset (Fin (2 * n + 1)),
      Summable (fun k : ℕ => ∑ q ∈ s, g (F k) q (kolmogorovInner n ψ q x)) := by
    intro s
    refine Finset.induction ?_ ?_ s
    · simp
    · intro a s has ih
      simp only [Finset.sum_insert has]
      exact Summable.add (hsumm_pt a (kolmogorovInner n ψ a x)) ih
  have htele : ∀ K : ℕ,
      ∑ k ∈ Finset.range K, kolmogorovSuperpose n ψ (g (F k)) x
        = f x - F K x := by
    intro K
    induction K with
    | zero =>
      rw [hF0]
      simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, hFs K, ContinuousMap.sub_apply]
      ring
  have hFlim : Filter.Tendsto (fun K : ℕ => F K x) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (fun K => ?_) hpow0
    calc ‖F K x‖ ≤ ‖F K‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ρ ^ K * ‖f‖ := hFk K
  have hlim : Filter.Tendsto
      (fun K : ℕ => ∑ k ∈ Finset.range K, kolmogorovSuperpose n ψ (g (F k)) x)
      Filter.atTop (nhds (f x)) := by
    have hfun : (fun K : ℕ =>
        ∑ k ∈ Finset.range K, kolmogorovSuperpose n ψ (g (F k)) x)
        = fun K => f x - F K x := funext htele
    rw [hfun]
    have h1 : Filter.Tendsto (fun K : ℕ => f x - F K x) Filter.atTop
        (nhds (f x - 0)) :=
      tendsto_const_nhds.sub hFlim
    simpa using h1
  have hsumm_sup :
      Summable (fun k : ℕ => kolmogorovSuperpose n ψ (g (F k)) x) := by
    simpa only [kolmogorovSuperpose_apply] using hsumm_fin Finset.univ
  have heq : f x = ∑' k : ℕ, kolmogorovSuperpose n ψ (g (F k)) x :=
    tendsto_nhds_unique hlim hsumm_sup.hasSum.tendsto_sum_nat
  have hexch : (∑ q, (∑' k : ℕ, g (F k) q) (kolmogorovInner n ψ q x))
      = ∑' k : ℕ, kolmogorovSuperpose n ψ (g (F k)) x := by
    have h1 : HasSum (fun k : ℕ => ∑ q, g (F k) q (kolmogorovInner n ψ q x))
        (∑ q, (∑' k : ℕ, g (F k) q) (kolmogorovInner n ψ q x)) :=
      hfin Finset.univ
    have h2 : HasSum (fun k : ℕ => ∑ q, g (F k) q (kolmogorovInner n ψ q x))
        (∑' k : ℕ, kolmogorovSuperpose n ψ (g (F k)) x) := hsumm_sup.hasSum
    exact HasSum.unique h1 h2
  have hfinal : f x = ∑ q, (∑' k : ℕ, g (F k) q) (kolmogorovInner n ψ q x) :=
    heq.trans hexch.symm
  exact hfinal

section
namespace MathlibExt.Analysis.ContinuousMap.KolmogorovSuperpositionWanted

/-!
# Kolmogorov superposition theorem for `[0,1]^n`
-/

/--
**Kolmogorov superposition theorem.** Let $n \ge 2$. There are continuous functions
$\psi_{q,p} : [0,1] \to \mathbb{R}$ for $0 \le q \le 2n$ and $0 \le p < n$, depending only on
$n$, such that for every continuous function $f : [0,1]^n \to \mathbb{R}$ there are continuous
functions $\varphi_q : \mathbb{R} \to \mathbb{R}$ for $0 \le q \le 2n$ with
$f(x) = \sum_{q=0}^{2n} \varphi_q\left(\sum_{p=0}^{n-1} \psi_{q,p}(x_p)\right)$ for every
$x = (x_0, \dots, x_{n-1}) \in [0,1]^n$.

Proves `Wanted` entry `kolmogorov_superposition`.

Source: Kolmogorov superposition theorem, A. N. Kolmogorov, Dokl.
Akad. Nauk SSSR 114 (1957) 953–956, refined Arnold 1957; see Braun–Griebel, Acta Numer. 2009
review; Lean is n ≥ 2 exact cardinal Fin (2n+1) with inner ψ in C(Icc 0 1, ℝ) independent of f
and outer φ in C(ℝ, ℝ), compact-source specialization [0, 1]^n as Fin n → Icc.
-/
theorem kolmogorov_superposition
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ (ψ : Fin (2 * n + 1) → Fin n → C(Set.Icc (0 : ℝ) 1, ℝ)),
      ∀ (f : C(Fin n → Set.Icc (0 : ℝ) 1, ℝ)),
        ∃ (φ : Fin (2 * n + 1) → C(ℝ, ℝ)),
          ∀ (x : Fin n → Set.Icc (0 : ℝ) 1),
            f x = ∑ q : Fin (2 * n + 1), φ q (∑ p : Fin n, ψ q p (x p)) := by
  have _hn2 : 2 ≤ n := hn
  obtain ⟨ψ, hψ⟩ := exists_kolmogorov_outer (n := n)
  exact ⟨ψ, hψ⟩

end MathlibExt.Analysis.ContinuousMap.KolmogorovSuperpositionWanted
