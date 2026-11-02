/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section
namespace MetaMathlibExt

-- N1: countable subsets of ℝ are meagre.
private theorem blum_isMeagre_of_countable (S : Set ℝ) (hS : S.Countable) :
    IsMeagre S := by
  have hEq : S = ⋃ x ∈ S, ({x} : Set ℝ) := by
    ext y
    simp
  rw [hEq]
  apply isMeagre_biUnion hS
  intro x _
  apply IsNowhereDense.isMeagre
  rw [IsClosed.isNowhereDense_iff isClosed_singleton]
  exact interior_singleton x

-- Category points.
private def blumCat (A : Set ℝ) : Set ℝ :=
  {x : ℝ | ∀ U : Set ℝ, IsOpen U → x ∈ U → ¬ IsMeagre (A ∩ U)}

-- N2a: catPts is closed.
private theorem blum_isClosed_cat (A : Set ℝ) : IsClosed (blumCat A) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ IsMeagre (A ∩ U) := by
    by_contra h
    apply hx
    intro U hUo hxU hCon
    exact h ⟨U, hUo, hxU, hCon⟩
  obtain ⟨U, hUo, hxU, hUm⟩ := hx'
  refine ⟨U, ?_, hUo, hxU⟩
  intro y hy hyC
  exact hyC U hUo hy hUm

-- N2b: A minus its category points is meagre.
private theorem blum_diff_cat_isMeagre (A : Set ℝ) : IsMeagre (A \ blumCat A) := by
  set T : Set (ℚ × ℚ) := {pq | IsMeagre (A ∩ Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ))} with hT
  have hTcount : T.Countable := Set.to_countable T
  have hsub : A \ blumCat A ⊆ ⋃ pq ∈ T, (A ∩ Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ)) := by
    intro x hx
    obtain ⟨hxA, hxC⟩ : x ∈ A ∧ x ∉ blumCat A := hx
    have hx' : ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ IsMeagre (A ∩ U) := by
      by_contra h
      apply hxC
      intro U hUo hxU hCon
      exact h ⟨U, hUo, hxU, hCon⟩
    obtain ⟨U, hUo, hxU, hUm⟩ := hx'
    obtain ⟨V, hVb, hxV, hVU⟩ :=
      Real.isTopologicalBasis_Ioo_rat.exists_subset_of_mem_open hxU hUo
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hVb
    obtain ⟨p, q, -, rfl⟩ := hVb
    have hmono : A ∩ Set.Ioo (↑p : ℝ) (↑q : ℝ) ⊆ A ∩ U := by
      intro y hy
      exact ⟨hy.1, hVU hy.2⟩
    have hpqT : (p, q) ∈ T := IsMeagre.mono hmono hUm
    exact Set.mem_biUnion hpqT ⟨hxA, hxV⟩
  apply IsMeagre.mono hsub
  apply isMeagre_biUnion hTcount
  intro pq hpq
  have : pq ∈ T := hpq
  simpa [hT] using this

-- N3: A minus the interior of its category points is meagre.
private theorem blum_diff_interior_cat_isMeagre (A : Set ℝ) :
    IsMeagre (A \ interior (blumCat A)) := by
  have hC := blum_isClosed_cat A
  have hfront : IsMeagre (frontier (blumCat A)) := by
    apply IsNowhereDense.isMeagre
    rw [IsClosed.isNowhereDense_iff isClosed_frontier]
    exact interior_frontier hC
  have hsub : A \ interior (blumCat A) ⊆
      (A \ blumCat A) ∪ frontier (blumCat A) := by
    intro x hx
    obtain ⟨hxA, hxin⟩ : x ∈ A ∧ x ∉ interior (blumCat A) := hx
    by_cases hxC : x ∈ blumCat A
    · right
      have hmem : x ∈ blumCat A \ interior (blumCat A) := ⟨hxC, hxin⟩
      rwa [← hC.frontier_eq] at hmem
    · left
      exact ⟨hxA, hxC⟩
  exact IsMeagre.mono hsub (IsMeagre.union (blum_diff_cat_isMeagre A) hfront)

-- Good points: category version of continuity points.
private def blumGood (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ V : Set ℝ, IsOpen V → V.Nonempty →
    V ⊆ Metric.ball x δ → ¬ IsMeagre ({y | dist (f y) (f x) < ε} ∩ V)

-- N4: the bad points form a meagre set.
private theorem blum_isMeagre_not_good (f : ℝ → ℝ) :
    IsMeagre {x | ¬ blumGood f x} := by
  have hmeag : IsMeagre (⋃ k : ℕ, ⋃ q : ℚ,
      ({y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} \
        interior (blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))}))) :=
    isMeagre_iUnion fun k => isMeagre_iUnion fun q =>
      blum_diff_interior_cat_isMeagre _
  apply IsMeagre.mono _ hmeag
  intro x hx
  have hxG : ¬ blumGood f x := hx
  obtain ⟨ε, hεpos, hεfail⟩ : ∃ ε : ℝ, ε > 0 ∧ ∀ δ : ℝ, δ > 0 →
      ∃ V : Set ℝ, IsOpen V ∧ V.Nonempty ∧ V ⊆ Metric.ball x δ ∧
        IsMeagre ({y | dist (f y) (f x) < ε} ∩ V) := by
    by_contra h
    apply hxG
    intro ε' hε'
    by_contra hδ
    apply h
    refine ⟨ε', hε', ?_⟩
    intro δ hδ'
    by_contra hV
    apply hδ
    refine ⟨δ, hδ', ?_⟩
    intro V hVo hVne hVsub
    by_contra hCon
    exact hV ⟨V, hVo, hVne, hVsub, hCon⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hεpos
  have hKpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hfail0 : ∀ δ : ℝ, δ > 0 → ∃ V : Set ℝ, IsOpen V ∧ V.Nonempty ∧
      V ⊆ Metric.ball x δ ∧
      IsMeagre ({y | dist (f y) (f x) < 1 / ((k : ℝ) + 1)} ∩ V) := by
    intro δ hδ
    obtain ⟨V, hVo, hVne, hVsub, hVm⟩ := hεfail δ hδ
    refine ⟨V, hVo, hVne, hVsub, ?_⟩
    apply IsMeagre.mono _ hVm
    intro y hy
    obtain ⟨hy1, hy2⟩ :
      dist (f y) (f x) < 1 / ((k : ℝ) + 1) ∧ y ∈ V := hy
    refine ⟨?_, hy2⟩
    change dist (f y) (f x) < ε
    exact lt_of_lt_of_le hy1 (le_of_lt hk)
  have hrpos : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by
    apply one_div_pos.mpr
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show (f x - 1 / (2 * ((k : ℝ) + 1))) < (f x + 1 / (2 * ((k : ℝ) + 1))) by
      linarith)
  have hdist : dist (f x) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hBsub : {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} ⊆
      {y | dist (f y) (f x) < 1 / ((k : ℝ) + 1)} := by
    intro y hy
    have hy' : dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := hy
    change dist (f y) (f x) < 1 / ((k : ℝ) + 1)
    have hKne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hKpos
    have htri := dist_triangle (f y) (q : ℝ) (f x)
    have hqc : dist (q : ℝ) (f x) = dist (f x) (q : ℝ) := dist_comm _ _
    have h2 : (1 : ℝ) / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) =
        1 / ((k : ℝ) + 1) := by
      field_simp
      ring
    calc dist (f y) (f x)
        ≤ dist (f y) (q : ℝ) + dist (q : ℝ) (f x) := htri
      _ = dist (f y) (q : ℝ) + dist (f x) (q : ℝ) := by rw [hqc]
      _ < 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) :=
          add_lt_add hy' hdist
      _ = 1 / ((k : ℝ) + 1) := h2
  have hxB : x ∈ {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} := hdist
  have hxNI : x ∉ interior
      (blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))}) := by
    intro hxin
    obtain ⟨δ', hδ'pos, hδ'sub⟩ :=
      Metric.isOpen_iff.mp isOpen_interior x hxin
    have hsub2 : Metric.ball x δ' ⊆
        blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} :=
      fun y hy => interior_subset (hδ'sub hy)
    obtain ⟨V, hVo, hVne, hVsub, hVm⟩ := hfail0 δ' hδ'pos
    obtain ⟨z, hzV⟩ := hVne
    have hzC : z ∈
        blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} :=
      hsub2 (hVsub hzV)
    have hzNC : ¬ IsMeagre
        ({y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} ∩ V) :=
      hzC V hVo hzV
    apply hzNC
    apply IsMeagre.mono _ hVm
    intro y hy
    obtain ⟨hy1, hy2⟩ :
      y ∈ {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} ∧ y ∈ V := hy
    exact ⟨hBsub hy1, hy2⟩
  have hmem : x ∈ {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} \
      interior (blumCat
        {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))}) := ⟨hxB, hxNI⟩
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨q, hmem⟩⟩

-- Dyadic open intervals and dyadic rationals.
private def blumDyI (m : ℕ) (a : ℤ) : Set ℝ :=
  Set.Ioo ((a : ℝ) / 2 ^ m) (((a : ℝ) + 1) / 2 ^ m)

private def blumDyadic : Set ℝ :=
  {x : ℝ | ∃ m : ℕ, ∃ a : ℤ, x = (a : ℝ) / 2 ^ m}

-- N5e: dyadics are countable.
private theorem blum_dyadic_countable : blumDyadic.Countable := by
  have hEq : blumDyadic =
      Set.range (fun p : ℕ × ℤ => ((p.2 : ℝ) / 2 ^ p.1)) := by
    ext x
    constructor
    · intro h
      have h' : ∃ m : ℕ, ∃ a : ℤ, x = (a : ℝ) / 2 ^ m := h
      obtain ⟨m, a, rfl⟩ := h'
      exact ⟨(m, a), rfl⟩
    · intro h
      obtain ⟨⟨m, a⟩, rfl⟩ := h
      exact ⟨m, a, rfl⟩
  rw [hEq]
  exact Set.countable_range _

-- N5c: non-dyadic points lie in their floor dyadic interval.
private theorem blum_mem_dyI_floor (m : ℕ) {x : ℝ} (hx : x ∉ blumDyadic) :
    x ∈ blumDyI m ⌊x * 2 ^ m⌋ := by
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hfle : (⌊x * 2 ^ m⌋ : ℝ) ≤ x * 2 ^ m := Int.floor_le _
  have hflt : x * 2 ^ m < (⌊x * 2 ^ m⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hlt : (⌊x * 2 ^ m⌋ : ℝ) < x * 2 ^ m := by
    by_contra h
    have hle : x * 2 ^ m ≤ (⌊x * 2 ^ m⌋ : ℝ) := le_of_not_gt h
    have heq : x * 2 ^ m = (⌊x * 2 ^ m⌋ : ℝ) := le_antisymm hle hfle
    have heq2 : x = ((⌊x * 2 ^ m⌋ : ℝ)) / 2 ^ m := by
      rw [eq_div_iff (ne_of_gt h2pos)]
      exact heq
    apply hx
    change ∃ mm : ℕ, ∃ aa : ℤ, x = (aa : ℝ) / 2 ^ mm
    exact ⟨m, ⌊x * 2 ^ m⌋, heq2⟩
  rw [blumDyI]
  rw [Set.mem_Ioo]
  constructor
  · rw [div_lt_iff₀ h2pos]
    linarith [hlt]
  · rw [lt_div_iff₀ h2pos]
    linarith [hflt]

-- N5d: a dyadic interval sits in a small ball around any of its points.
private theorem blum_dyI_subset_ball (m : ℕ) (a : ℤ) {x : ℝ}
    (hx : x ∈ blumDyI m a) : blumDyI m a ⊆ Metric.ball x (1 / 2 ^ m) := by
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hlen : (((a : ℝ) + 1) / 2 ^ m) - ((a : ℝ) / 2 ^ m) = 1 / 2 ^ m := by
    field_simp
    ring
  have hx' : (a : ℝ) / 2 ^ m < x ∧ x < ((a : ℝ) + 1) / 2 ^ m := by
    simpa [blumDyI] using hx
  intro y hy
  have hy' : (a : ℝ) / 2 ^ m < y ∧ y < ((a : ℝ) + 1) / 2 ^ m := by
    simpa [blumDyI] using hy
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2, hlen]

private theorem blumDyI_mem_iff (m : ℕ) (a : ℤ) (x : ℝ) :
    x ∈ blumDyI m a ↔ (a : ℝ) < x * 2 ^ m ∧ x * 2 ^ m < (a : ℝ) + 1 := by
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  rw [blumDyI, Set.mem_Ioo, div_lt_iff₀ h2pos, lt_div_iff₀ h2pos]

private theorem blum_dyI_laminar {m m' : ℕ} {a a' : ℤ} (hle : m ≤ m')
    (hne : (blumDyI m' a' ∩ blumDyI m a).Nonempty) :
    blumDyI m' a' ⊆ blumDyI m a := by
  obtain ⟨z, hz1, hz2⟩ := hne
  have hz1' := (blumDyI_mem_iff m' a' z).mp hz1
  have hz2' := (blumDyI_mem_iff m a z).mp hz2
  set j := m' - m with hj
  have hm' : m' = m + j := (Nat.add_sub_cancel' hle).symm
  have hPpos : (0 : ℤ) < 2 ^ j := pow_pos (by norm_num) _
  have hPne : (2 : ℤ) ^ j ≠ 0 := ne_of_gt hPpos
  set b := a' / 2 ^ j with hb
  have h1 : b * 2 ^ j ≤ a' := Int.ediv_mul_le _ hPne
  have h2 : a' < (b + 1) * 2 ^ j := Int.lt_ediv_add_one_mul_self _ hPpos
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have c1 : (b : ℝ) * 2 ^ j ≤ (a' : ℝ) := by
    have h : ((b * 2 ^ j : ℤ) : ℝ) ≤ ((a' : ℤ) : ℝ) := Int.cast_le.mpr h1
    push_cast at h
    exact h
  have c2 : (a' : ℝ) < ((b : ℝ) + 1) * 2 ^ j := by
    have h : ((a' : ℤ) : ℝ) < ((((b + 1) * 2 ^ j : ℤ)) : ℝ) :=
      Int.cast_lt.mpr h2
    push_cast at h
    exact h
  have h3 : a' + 1 ≤ (b + 1) * 2 ^ j := by omega
  have c3 : (a' : ℝ) + 1 ≤ ((b : ℝ) + 1) * 2 ^ j := by
    have h : (((a' + 1 : ℤ)) : ℝ) ≤ ((((b + 1) * 2 ^ j : ℤ)) : ℝ) :=
      Int.cast_le.mpr h3
    push_cast at h
    exact h
  have hpow : (2 : ℝ) ^ m' = 2 ^ m * 2 ^ j := by rw [hm', pow_add]
  have sub1 : blumDyI m' a' ⊆ blumDyI m b := by
    intro y hy
    have hy' := (blumDyI_mem_iff m' a' y).mp hy
    rw [hpow] at hy'
    rw [blumDyI_mem_iff]
    constructor
    · have e3 : y * (2 ^ m * 2 ^ j) = (y * 2 ^ m) * 2 ^ j := by ring
      have hlt : (b : ℝ) * 2 ^ j < (y * 2 ^ m) * 2 ^ j := by
        rw [← e3]
        exact lt_of_le_of_lt c1 hy'.1
      exact lt_of_mul_lt_mul_right hlt (le_of_lt h2j)
    · have e3 : y * (2 ^ m * 2 ^ j) = (y * 2 ^ m) * 2 ^ j := by ring
      have hlt : (y * 2 ^ m) * 2 ^ j < ((b : ℝ) + 1) * 2 ^ j := by
        rw [← e3]
        exact lt_of_lt_of_le hy'.2 c3
      exact lt_of_mul_lt_mul_right hlt (le_of_lt h2j)
  have hzb := (blumDyI_mem_iff m b z).mp (sub1 hz1)
  have hba1 : b ≤ a := by
    have h : (b : ℝ) < (a : ℝ) + 1 := lt_trans hzb.1 hz2'.2
    have h' : b < a + 1 := by exact_mod_cast h
    omega
  have hba2 : a ≤ b := by
    have h : (a : ℝ) < (b : ℝ) + 1 := lt_trans hz2'.1 hzb.2
    have h' : a < b + 1 := by exact_mod_cast h
    omega
  have hba : b = a := le_antisymm hba1 hba2
  rw [hba] at sub1
  exact sub1

-- N5b: a dyadic interval cannot contain one of strictly smaller level.
private theorem blum_dyI_not_subset_of_lt {m m' : ℕ} {a a' : ℤ} (hlt : m < m') :
    ¬ blumDyI m a ⊆ blumDyI m' a' := by
  intro hsub
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2m' : (0 : ℝ) < 2 ^ m' := by positivity
  have hlen : (((a : ℝ) + 1) / 2 ^ m) - ((a : ℝ) / 2 ^ m) = 1 / 2 ^ m := by
    field_simp
    ring
  have hlen' : (((a' : ℝ) + 1) / 2 ^ m') - ((a' : ℝ) / 2 ^ m') = 1 / 2 ^ m' := by
    field_simp
    ring
  set l : ℝ := (a : ℝ) / 2 ^ m with hl
  set r : ℝ := ((a : ℝ) + 1) / 2 ^ m with hr
  have hlr : l < r := by
    rw [hl, hr]
    have : (a : ℝ) / 2 ^ m < ((a : ℝ) + 1) / 2 ^ m := by
      apply div_lt_div_of_pos_right _ h2m
      linarith
    exact this
  set p : ℝ := l + (r - l) / 4 with hp
  set q : ℝ := l + 3 * (r - l) / 4 with hq
  have hplr : l < p ∧ p < r := by constructor <;> (rw [hp]; linarith)
  have hqlr : l < q ∧ q < r := by constructor <;> (rw [hq]; linarith)
  have hmem_p : p ∈ blumDyI m a := by
    rw [blumDyI]
    exact Set.mem_Ioo.mpr ⟨by rw [← hl]; exact hplr.1, by rw [← hr]; exact hplr.2⟩
  have hmem_q : q ∈ blumDyI m a := by
    rw [blumDyI]
    exact Set.mem_Ioo.mpr ⟨by rw [← hl]; exact hqlr.1, by rw [← hr]; exact hqlr.2⟩
  have hp' := (blumDyI_mem_iff m' a' p).mp (hsub hmem_p)
  have hq' := (blumDyI_mem_iff m' a' q).mp (hsub hmem_q)
  have hdist : (r - l) / 2 < 1 / 2 ^ m' := by
    have e : q - p = (r - l) / 2 := by rw [hp, hq]; ring
    have h1 : q * 2 ^ m' < (a' : ℝ) + 1 := hq'.2
    have h2 : (a' : ℝ) < p * 2 ^ m' := hp'.1
    have h3 : (q - p) * 2 ^ m' < 1 := by linarith [h1, h2]
    have h4 : (q - p) < 1 / 2 ^ m' := by
      rw [lt_div_iff₀ h2m']
      linarith [h3]
    rw [e] at h4
    exact h4
  have h2mne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h2m
  have hlen2 : (r - l) / 2 = 1 / 2 ^ (m + 1) := by
    rw [hlen, pow_succ]
    field_simp
  rw [hlen2] at hdist
  have hpow : (2 : ℝ) ^ m' < (2 : ℝ) ^ (m + 1) := by
    have h := (one_div_lt_one_div (by positivity : (0:ℝ) < 2 ^ (m+1))
      h2m').mp hdist
    exact h
  have hlt2 : m' < m + 1 :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

-- N5f: every open neighborhood contains arbitrarily fine nonempty dyadic intervals.
private theorem blum_dyI_small_mem_open {U : Set ℝ} (hUo : IsOpen U) {y : ℝ}
    (hy : y ∈ U) (M : ℕ) : ∃ m : ℕ, M ≤ m ∧ ∃ a : ℤ,
      blumDyI m a ⊆ U ∧ (blumDyI m a).Nonempty := by
  obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hUo y hy
  have htend : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ((1 : ℝ) / 2) ^ n < r / 2 :=
    htend.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < r / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  set m := max N M with hm
  have hmM : M ≤ m := le_max_right _ _
  have hpow : ((1 : ℝ) / 2) ^ m < r / 2 := hN m (le_max_left _ _)
  have h12 : ((1 : ℝ) / 2) ^ m = 1 / (2 : ℝ) ^ m := by rw [div_pow, one_pow]
  rw [h12] at hpow
  have hballpos : (0 : ℝ) < 1 / 2 ^ m := by positivity
  have hdense := Set.Countable.dense_compl ℝ blum_dyadic_countable
  have hballne : (Metric.ball y (1 / 2 ^ m)).Nonempty :=
    (Metric.nonempty_ball (x := y)).mpr hballpos
  have hmeet := (dense_iff_inter_open.mp hdense) (Metric.ball y (1 / 2 ^ m))
    Metric.isOpen_ball hballne
  obtain ⟨z, hzball, hznd⟩ := hmeet
  have hzball' : dist z y < 1 / 2 ^ m := Metric.mem_ball.mp hzball
  have hznd' : z ∉ blumDyadic := hznd
  refine ⟨m, hmM, ⌊z * 2 ^ m⌋, ?_, ⟨z, blum_mem_dyI_floor m hznd'⟩⟩
  have hza := blum_mem_dyI_floor (m := m) hznd'
  intro w hw
  apply hrsub
  have hwz : w ∈ Metric.ball z (1 / 2 ^ m) :=
    blum_dyI_subset_ball m _ hza hw
  rw [Metric.mem_ball] at hwz ⊢
  have htri : dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
  have hcomm : dist z y = dist y z := dist_comm _ _
  linarith [htri, hwz, hzball', hpow]

-- Labels are `(level, dyadic index, band center, band radius)`.
-- State is `(chosen points, labels)`.
private def blumInv (f : ℝ → ℝ) (s : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ)) :
    Prop :=
  (∀ d ∈ s.1, blumGood f d ∧ d ∉ blumDyadic) ∧
  (∀ ℓ ∈ s.2, ∀ d ∈ s.1, d ∈ blumDyI ℓ.1 ℓ.2.1 →
    dist (f d) ℓ.2.2.1 < ℓ.2.2.2) ∧
  (∀ ℓ ∈ s.2, ∀ ℓ' ∈ s.2, blumDyI ℓ.1 ℓ.2.1 ⊆ blumDyI ℓ'.1 ℓ'.2.1 →
    Metric.ball ℓ.2.2.1 ℓ.2.2.2 ⊆ Metric.ball ℓ'.2.2.1 ℓ'.2.2.2) ∧
  (∀ ℓ ∈ s.2, ∀ V : Set ℝ, IsOpen V → V.Nonempty → V ⊆ blumDyI ℓ.1 ℓ.2.1 →
    ¬ IsMeagre ((f ⁻¹' Metric.ball ℓ.2.2.1 ℓ.2.2.2) ∩ V))

-- N6: the empty state satisfies the invariant.
private theorem blum_inv_empty (f : ℝ → ℝ) : blumInv f (∅, ∅) := by
  unfold blumInv
  simp

-- Removing a meagre set from a non-meagre set leaves a nonempty set.
private theorem blum_nonempty_diff_meagre {s B : Set ℝ} (hmeag : IsMeagre B)
    (hnot : ¬ IsMeagre s) : (s \ B).Nonempty := by
  by_contra h
  apply hnot
  have hempty : s \ B = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hsub : s ⊆ (s \ B) ∪ B := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inr hxB
    · exact Or.inl ⟨hx, hxB⟩
  rw [hempty] at hsub
  exact IsMeagre.mono hsub (IsMeagre.union IsMeagre.empty hmeag)

-- Arbitrarily fine dyadic levels.
private theorem blum_exists_fine_level (M' : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ m : ℕ, M' ≤ m ∧ 1 / (2 : ℝ) ^ m < r₀ := by
  have htend : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ((1 : ℝ) / 2) ^ n < r₀ :=
    htend.eventually (Iio_mem_nhds hr₀)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N M', le_max_right _ _, ?_⟩
  have hle : ((1 : ℝ) / 2) ^ (max N M') ≤ ((1 : ℝ) / 2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have h12 : ((1 : ℝ) / 2) ^ (max N M') = 1 / (2 : ℝ) ^ (max N M') := by
    rw [div_pow, one_pow]
  rw [← h12]
  exact lt_of_le_of_lt hle (hN _ (le_refl _))

-- N7: add a new point inside a nonempty open set.
private theorem blum_add_point (f : ℝ → ℝ) {P : Finset ℝ}
    {L : Finset (ℕ × ℤ × ℝ × ℝ)} (hInv : blumInv f (P, L))
    {U : Set ℝ} (hUo : IsOpen U) (hUne : U.Nonempty) :
    ∃ y : ℝ, y ∈ U ∧ y ∉ (↑P : Set ℝ) ∧ blumInv f (insert y P, L) := by
  classical
  obtain ⟨V1, V2, V3, V4⟩ := hInv
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨m, hmM, a, hsub, hne⟩ :=
    blum_dyI_small_mem_open hUo hy₀ (L.sup (fun ℓ => ℓ.1) + 1)
  have hlevel : ∀ ℓ : ℕ × ℤ × ℝ × ℝ, ℓ ∈ L → ℓ.1 < m := by
    intro ℓ hℓ
    have hle : ℓ.1 ≤ L.sup (fun ℓ => ℓ.1) := Finset.le_sup hℓ
    omega
  have hVo : IsOpen (blumDyI m a) := by
    rw [blumDyI]
    exact isOpen_Ioo
  set Λ := L.filter
    (fun ℓ => (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty) with hΛ
  have hBmeag : IsMeagre
      ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) :=
    IsMeagre.union (IsMeagre.union (blum_isMeagre_not_good f)
      (blum_isMeagre_of_countable _ blum_dyadic_countable))
      (blum_isMeagre_of_countable _ (Finset.finite_toSet P).countable)
  have hVnot : ¬ IsMeagre (blumDyI m a) := not_isMeagre_of_isOpen hVo hne
  have hV1new : ∀ y : ℝ, y ∉
      ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) →
      (blumGood f y ∧ y ∉ blumDyadic) ∧ y ∉ (↑P : Set ℝ) := by
    intro y hyB
    have hyG : blumGood f y := by
      by_contra hG
      exact hyB (Or.inl (Or.inl hG))
    have hyD : y ∉ blumDyadic := by
      intro hD
      exact hyB (Or.inl (Or.inr hD))
    have hyP : y ∉ (↑P : Set ℝ) := by
      intro hP
      exact hyB (Or.inr hP)
    exact ⟨⟨hyG, hyD⟩, hyP⟩
  by_cases hΛempty : Λ = ∅
  · obtain ⟨y, hy⟩ := blum_nonempty_diff_meagre hBmeag hVnot
    obtain ⟨hyV, hyB⟩ : y ∈ blumDyI m a ∧ y ∉
        ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) := hy
    obtain ⟨hyG, hyP⟩ := hV1new y hyB
    refine ⟨y, hsub hyV, hyP, ?_, ?_, V3, V4⟩
    · intro d hd
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · exact hyG
      · exact V1 d hdP
    · intro ℓ hℓ d hd hdy
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · exfalso
        have hmeet : (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty :=
          ⟨d, hyV, hdy⟩
        have hmem : ℓ ∈ Λ := Finset.mem_filter.mpr ⟨hℓ, hmeet⟩
        rw [hΛempty] at hmem
        exact Finset.notMem_empty ℓ hmem
      · exact V2 ℓ hℓ d hdP hdy
  · obtain ⟨ℓs, hℓs_mem, hℓs_max⟩ :=
      Finset.exists_max_image Λ (fun ℓ => ℓ.1)
        (Finset.nonempty_iff_ne_empty.mpr hΛempty)
    have hmax : ∀ x' : ℕ × ℤ × ℝ × ℝ, x' ∈ Λ → x'.1 ≤ ℓs.1 :=
      hℓs_max
    have hℓsL : ℓs ∈ L := (Finset.mem_filter.mp hℓs_mem).1
    have hVsub : ∀ ℓ : ℕ × ℤ × ℝ × ℝ, ℓ ∈ Λ →
        blumDyI m a ⊆ blumDyI ℓ.1 ℓ.2.1 := by
      intro ℓ hℓ
      have hℓL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
      have hmeet : (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty :=
        (Finset.mem_filter.mp hℓ).2
      exact blum_dyI_laminar (le_of_lt (hlevel ℓ hℓL)) hmeet
    have hband : ∀ ℓ : ℕ × ℤ × ℝ × ℝ, ℓ ∈ Λ →
        Metric.ball ℓs.2.2.1 ℓs.2.2.2 ⊆ Metric.ball ℓ.2.2.1 ℓ.2.2.2 := by
      intro ℓ hℓ
      have hℓL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
      have h1 : blumDyI m a ⊆ blumDyI ℓs.1 ℓs.2.1 := hVsub ℓs hℓs_mem
      have h2 : blumDyI m a ⊆ blumDyI ℓ.1 ℓ.2.1 := hVsub ℓ hℓ
      have hlev : ℓ.1 ≤ ℓs.1 := hmax ℓ hℓ
      have hne2 : (blumDyI ℓs.1 ℓs.2.1 ∩
          blumDyI ℓ.1 ℓ.2.1).Nonempty := by
        obtain ⟨z, hzm⟩ := hne
        exact ⟨z, h1 hzm, h2 hzm⟩
      exact V3 ℓs hℓsL ℓ hℓL (blum_dyI_laminar hlev hne2)
    have hkey : ¬ IsMeagre ((f ⁻¹' Metric.ball ℓs.2.2.1 ℓs.2.2.2) ∩
        blumDyI m a) :=
      V4 ℓs hℓsL _ hVo hne (hVsub ℓs hℓs_mem)
    obtain ⟨y, hy⟩ := blum_nonempty_diff_meagre hBmeag hkey
    obtain ⟨hyV, hyB⟩ : y ∈ (f ⁻¹' Metric.ball ℓs.2.2.1 ℓs.2.2.2) ∩
        blumDyI m a ∧ y ∉
        ({x | ¬ blumGood f x} ∪ blumDyadic ∪ (↑P : Set ℝ)) := hy
    obtain ⟨hyf, hydy⟩ :
      y ∈ f ⁻¹' Metric.ball ℓs.2.2.1 ℓs.2.2.2 ∧ y ∈ blumDyI m a := hyV
    obtain ⟨hyG, hyP⟩ := hV1new y hyB
    refine ⟨y, hsub hydy, hyP, ?_, ?_, V3, V4⟩
    · intro d hd
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · exact hyG
      · exact V1 d hdP
    · intro ℓ hℓ d hd hdy
      have hd' : d = y ∨ d ∈ P := Finset.mem_insert.mp hd
      rcases hd' with rfl | hdP
      · have hmeet : (blumDyI m a ∩ blumDyI ℓ.1 ℓ.2.1).Nonempty :=
          ⟨d, hydy, hdy⟩
        have hmem : ℓ ∈ Λ := Finset.mem_filter.mpr ⟨hℓ, hmeet⟩
        have hfy : f d ∈ Metric.ball ℓs.2.2.1 ℓs.2.2.2 := hyf
        exact Metric.mem_ball.mp ((hband ℓ hmem) hfy)
      · exact V2 ℓ hℓ d hdP hdy

-- N8: add a fine label around an existing point.
private theorem blum_add_label (f : ℝ → ℝ) {P : Finset ℝ}
    {L : Finset (ℕ × ℤ × ℝ × ℝ)} (hInv : blumInv f (P, L))
    {d : ℝ} (hdP : d ∈ P) (k : ℕ) :
    ∃ ℓ : ℕ × ℤ × ℝ × ℝ, d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((k : ℝ) + 1) ∧
      blumInv f (P, insert ℓ L) := by
  classical
  obtain ⟨V1, V2, V3, V4⟩ := hInv
  obtain ⟨hdGood, hdDy⟩ := V1 d hdP
  have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hKinv : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  set S := L.filter (fun ℓ => d ∈ blumDyI ℓ.1 ℓ.2.1) with hS
  obtain ⟨ε, hεpos, hεK, hεsub⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / ((k : ℝ) + 1) ∧
      ∀ ℓ ∈ S, Metric.ball (f d) ε ⊆ Metric.ball ℓ.2.2.1 ℓ.2.2.2 := by
    by_cases hSe : S = ∅
    · refine ⟨1 / ((k : ℝ) + 1), hKinv, le_rfl, ?_⟩
      intro ℓ hℓ
      rw [hSe] at hℓ
      exact absurd hℓ (Finset.notMem_empty ℓ)
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      set T := S.image (fun ℓ => ℓ.2.2.2 - dist (f d) ℓ.2.2.1) with hT
      have hTne : T.Nonempty := hSne.image _
      have hmem2 : ∀ ℓ ∈ S, dist (f d) ℓ.2.2.1 < ℓ.2.2.2 := by
        intro ℓ hℓ
        have hL : ℓ ∈ L := (Finset.mem_filter.mp hℓ).1
        have hdy : d ∈ blumDyI ℓ.1 ℓ.2.1 := (Finset.mem_filter.mp hℓ).2
        exact V2 ℓ hL d hdP hdy
      have hTpos : ∀ t ∈ T, 0 < t := by
        intro t ht
        obtain ⟨ℓ, hℓS, hfa⟩ := Finset.mem_image.mp ht
        have hfa' : ℓ.2.2.2 - dist (f d) ℓ.2.2.1 = t := hfa
        rw [← hfa']
        linarith [hmem2 ℓ hℓS]
      have hminpos : 0 < T.min' hTne := hTpos _ (Finset.min'_mem _ hTne)
      refine ⟨min (1 / ((k : ℝ) + 1)) (T.min' hTne),
        lt_min hKinv hminpos, min_le_left _ _, ?_⟩
      intro ℓ hℓ
      have hle : min (1 / ((k : ℝ) + 1)) (T.min' hTne) ≤
          ℓ.2.2.2 - dist (f d) ℓ.2.2.1 :=
        le_trans (min_le_right _ _)
          (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩))
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      have htri : dist y ℓ.2.2.1 ≤ dist y (f d) + dist (f d) ℓ.2.2.1 :=
        dist_triangle _ _ _
      linarith
  obtain ⟨ρ, hρ, hGoodρ⟩ := hdGood ε hεpos
  obtain ⟨g, hgpos, hgρ, hgisol⟩ : ∃ g : ℝ, 0 < g ∧ g ≤ ρ ∧
      ∀ d' ∈ P, d' ≠ d → g ≤ dist d d' := by
    set E := P.erase d with hE
    by_cases hEe : E = ∅
    · refine ⟨ρ, hρ, le_rfl, ?_⟩
      intro d' hd' hne
      have hmem : d' ∈ E := Finset.mem_erase.mpr ⟨hne, hd'⟩
      rw [hEe] at hmem
      exact absurd hmem (Finset.notMem_empty d')
    · have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEe
      set Dists := E.image (fun d' => dist d d') with hD
      have hDne : Dists.Nonempty := hEne.image _
      have hDpos : ∀ t ∈ Dists, 0 < t := by
        intro t ht
        obtain ⟨d', hd'E, hfa⟩ := Finset.mem_image.mp ht
        have hne : d' ≠ d := (Finset.mem_erase.mp hd'E).1
        have hfa' : dist d d' = t := hfa
        rw [← hfa']
        exact dist_pos.mpr (Ne.symm hne)
      have hminpos : 0 < Dists.min' hDne := hDpos _ (Finset.min'_mem _ hDne)
      refine ⟨min ρ (Dists.min' hDne), lt_min hρ hminpos, min_le_left _ _, ?_⟩
      intro d' hd' hne
      have hmem : d' ∈ E := Finset.mem_erase.mpr ⟨hne, hd'⟩
      exact le_trans (min_le_right _ _)
        (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨d', hmem, rfl⟩))
  obtain ⟨m, hmM, hmlt⟩ :=
    blum_exists_fine_level (L.sup (fun ℓ => ℓ.1) + 1) hgpos
  have hlevel : ∀ ℓ ∈ L, ℓ.1 < m := by
    intro ℓ hℓ
    have hle : ℓ.1 ≤ L.sup (fun ℓ => ℓ.1) := Finset.le_sup hℓ
    omega
  have hdmem : d ∈ blumDyI m ⌊d * 2 ^ m⌋ := blum_mem_dyI_floor m hdDy
  have hball : blumDyI m ⌊d * 2 ^ m⌋ ⊆ Metric.ball d (1 / 2 ^ m) :=
    blum_dyI_subset_ball m _ hdmem
  have hisol : ∀ d' ∈ P, d' ∈ blumDyI m ⌊d * 2 ^ m⌋ → d' = d := by
    intro d' hd'P hd'I
    by_contra hne
    have h1 : dist d' d < 1 / 2 ^ m := Metric.mem_ball.mp (hball hd'I)
    have h2 : g ≤ dist d d' := hgisol d' hd'P hne
    rw [dist_comm d d'] at h2
    linarith
  refine ⟨(m, ⌊d * 2 ^ m⌋, f d, ε), hdmem, hεK, ?_, ?_, ?_, ?_⟩
  · exact V1
  · intro q hq d' hd'P hd'I
    rcases Finset.mem_insert.mp hq with rfl | hqL
    · have hdd : d' = d := hisol d' hd'P hd'I
      rw [hdd]
      change dist (f d) (f d) < ε
      rw [dist_self]
      exact hεpos
    · exact V2 q hqL d' hd'P hd'I
  · intro q hq q' hq' hsub
    rcases Finset.mem_insert.mp hq with rfl | hqL
    · rcases Finset.mem_insert.mp hq' with rfl | hq'L
      · exact le_rfl
      · exact hεsub q' (Finset.mem_filter.mpr ⟨hq'L, hsub hdmem⟩)
    · rcases Finset.mem_insert.mp hq' with rfl | hq'L
      · exact absurd hsub (blum_dyI_not_subset_of_lt (hlevel q hqL))
      · exact V3 q hqL q' hq'L hsub
  · intro q hq V hVo hVne hVsub
    rcases Finset.mem_insert.mp hq with rfl | hqL
    · have hle : (1 : ℝ) / 2 ^ m ≤ ρ := le_trans (le_of_lt hmlt) hgρ
      have hVsub' : V ⊆ Metric.ball d ρ :=
        hVsub.trans (hball.trans (Metric.ball_subset_ball hle))
      have hkey := hGoodρ V hVo hVne hVsub'
      change ¬ IsMeagre ((f ⁻¹' Metric.ball (f d) ε) ∩ V)
      have heq : (f ⁻¹' Metric.ball (f d) ε) = {y | dist (f y) (f d) < ε} := by
        ext y
        simp [Metric.mem_ball]
      rw [heq]
      exact hkey
    · exact V4 q hqL V hVo hVne hVsub

-- N9: one full stage: add a point in U (if open nonempty) and fine labels everywhere.
private theorem blum_step (f : ℝ → ℝ) {P : Finset ℝ} {L : Finset (ℕ × ℤ × ℝ × ℝ)}
    (hInv : blumInv f (P, L)) (U : Set ℝ) (k : ℕ) :
    ∃ P' : Finset ℝ, ∃ L' : Finset (ℕ × ℤ × ℝ × ℝ), P ⊆ P' ∧ L ⊆ L' ∧
      blumInv f (P', L') ∧ (U.Nonempty → IsOpen U → (↑P' ∩ U).Nonempty) ∧
      ∀ d ∈ P, ∃ ℓ ∈ L', d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((k : ℝ) + 1) := by
  classical
  obtain ⟨P1, hPsub, hInv1, hUmeet⟩ :
      ∃ P1 : Finset ℝ, P ⊆ P1 ∧ blumInv f (P1, L) ∧
        (U.Nonempty → IsOpen U → (↑P1 ∩ U).Nonempty) := by
    by_cases hU : U.Nonempty ∧ IsOpen U
    · obtain ⟨hUne, hUo⟩ := hU
      obtain ⟨y, hyU, _, hInv1⟩ := blum_add_point f hInv hUo hUne
      refine ⟨insert y P, Finset.subset_insert y P, hInv1, ?_⟩
      intro _ _
      exact ⟨y, Finset.mem_coe.mpr (Finset.mem_insert_self y P), hyU⟩
    · refine ⟨P, (fun x hx => hx), hInv, ?_⟩
      intro hUne hUo
      exact absurd ⟨hUne, hUo⟩ hU
  have key : ∀ S : Finset ℝ, S ⊆ P1 →
      ∀ L₀ : Finset (ℕ × ℤ × ℝ × ℝ), L ⊆ L₀ → blumInv f (P1, L₀) →
      ∃ L', L₀ ⊆ L' ∧ blumInv f (P1, L') ∧
        ∀ d ∈ S, ∃ ℓ ∈ L', d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((k : ℝ) + 1) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _ L₀ hLL₀ hInv₀
      exact ⟨L₀, (fun x hx => hx), hInv₀,
        fun d hd => absurd hd (Finset.notMem_empty d)⟩
    · intro a S' haS' IH hsub L₀ hLL₀ hInv₀
      have haP1 : a ∈ P1 := hsub (Finset.mem_insert_self a S')
      have hS'P1 : S' ⊆ P1 := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      obtain ⟨L₁, hL₀₁, hInv₁, hlab₁⟩ := IH hS'P1 L₀ hLL₀ hInv₀
      obtain ⟨ℓn, hmem_n, hr_n, hInv₂⟩ := blum_add_label f hInv₁ haP1 k
      refine ⟨insert ℓn L₁, fun x hx => Finset.mem_insert_of_mem (hL₀₁ hx),
        hInv₂, ?_⟩
      intro d hd
      rcases Finset.mem_insert.mp hd with hda | hdS'
      · refine ⟨ℓn, Finset.mem_insert_self ℓn L₁, ?_, hr_n⟩
        rw [hda]
        exact hmem_n
      · obtain ⟨ℓ, hℓ, hdy, hr⟩ := hlab₁ d hdS'
        exact ⟨ℓ, Finset.mem_insert_of_mem hℓ, hdy, hr⟩
  obtain ⟨L', hLL', hInv', hlab'⟩ :=
    key P1 (fun x hx => hx) L (fun x hx => hx) hInv1
  refine ⟨P1, L', hPsub, hLL', hInv', hUmeet, ?_⟩
  intro d hd
  obtain ⟨ℓ, hℓ, hdy, hr⟩ := hlab' d (hPsub hd)
  exact ⟨ℓ, hℓ, hdy, hr⟩

-- N10: the stage sequence.
private theorem blum_seq (f : ℝ → ℝ) :
    ∃ σ : ℕ → ℚ × ℚ, Function.Surjective σ ∧
    ∃ s : ℕ → Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ),
      s 0 = (∅, ∅) ∧ (∀ n, blumInv f (s n)) ∧
      (∀ n n' : ℕ, n ≤ n' → (s n).1 ⊆ (s n').1) ∧
      (∀ n n' : ℕ, n ≤ n' → (s n).2 ⊆ (s n').2) ∧
      (∀ n, (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
        (↑(s (n+1)).1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty) ∧
      (∀ n, ∀ d ∈ (s n).1, ∃ ℓ ∈ (s (n+1)).2,
        d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (ℚ × ℚ)
  have hstep : ∀ st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ), blumInv f st →
      ∀ n : ℕ, ∃ st' : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ),
        st.1 ⊆ st'.1 ∧ st.2 ⊆ st'.2 ∧ blumInv f st' ∧
        ((Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
          (↑st'.1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty) ∧
        ∀ d ∈ st.1, ∃ ℓ ∈ st'.2,
          d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1) := by
    intro st hst n
    obtain ⟨P', L', hPP', hLL', hInv', hmeet, hlab⟩ :=
      blum_step f hst (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)) n
    exact ⟨(P', L'), hPP', hLL', hInv', fun hne => hmeet hne isOpen_Ioo,
      fun d hd => hlab d hd⟩
  have hstep' : ∀ st : {st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ) // blumInv f st},
      ∀ n : ℕ, ∃ st' : {st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ) // blumInv f st},
        st.val.1 ⊆ st'.val.1 ∧ st.val.2 ⊆ st'.val.2 ∧
        ((Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
          (↑st'.val.1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty) ∧
        ∀ d ∈ st.val.1, ∃ ℓ ∈ st'.val.2,
          d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1) := by
    intro st n
    obtain ⟨⟨P', L'⟩, hPP', hLL', hInv', hmeet, hlab⟩ :=
      hstep st.val st.property n
    exact ⟨⟨(P', L'), hInv'⟩, hPP', hLL', hmeet, fun d hd => hlab d hd⟩
  choose nxt hnxt using hstep'
  obtain ⟨s, hs0, hsS⟩ : ∃ s : ℕ →
      {st : Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ) // blumInv f st},
      s 0 = ⟨(∅, ∅), blum_inv_empty f⟩ ∧ ∀ n, s (n + 1) = nxt (s n) n :=
    ⟨fun n => Nat.rec (motive := fun _ => _) ⟨(∅, ∅), blum_inv_empty f⟩
      (fun n st => nxt st n) n, rfl, fun n => rfl⟩
  have hmonoP : ∀ n n' : ℕ, n ≤ n' → (s n).val.1 ⊆ (s n').val.1 := by
    intro n n'
    induction n' with
    | zero =>
      intro h
      have hn0 : n = 0 := Nat.le_zero.mp h
      rw [hn0]
    | succ k IH =>
      intro h
      by_cases hkn : n ≤ k
      · intro x hx
        have h1 : x ∈ (s k).val.1 := IH hkn hx
        have h2 := (hnxt (s k) k).1
        rw [← hsS k] at h2
        exact h2 h1
      · have hnk : n = k + 1 := by omega
        rw [hnk]
  have hmonoL : ∀ n n' : ℕ, n ≤ n' → (s n).val.2 ⊆ (s n').val.2 := by
    intro n n'
    induction n' with
    | zero =>
      intro h
      have hn0 : n = 0 := Nat.le_zero.mp h
      rw [hn0]
    | succ k IH =>
      intro h
      by_cases hkn : n ≤ k
      · intro x hx
        have h1 : x ∈ (s k).val.2 := IH hkn hx
        have h2 := (hnxt (s k) k).2.1
        rw [← hsS k] at h2
        exact h2 h1
      · have hnk : n = k + 1 := by omega
        rw [hnk]
  refine ⟨σ, hσ, fun n => (s n).val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (s 0).val = (∅, ∅)
    rw [hs0]
  · intro n
    exact (s n).property
  · intro n n' hnn'
    exact hmonoP n n' hnn'
  · intro n n' hnn'
    exact hmonoL n n' hnn'
  · intro n hne
    change (↑(s (n+1)).val.1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty
    rw [hsS n]
    exact (hnxt (s n) n).2.2.1 hne
  · intro n d hd
    change ∃ ℓ ∈ (s (n+1)).val.2, d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1)
    obtain ⟨ℓ, hℓ, hdy, hr⟩ := (hnxt (s n) n).2.2.2 d hd
    rw [← hsS n] at hℓ
    exact ⟨ℓ, hℓ, hdy, hr⟩

-- N11: density and continuity from the stage sequence.
private theorem blum_dense_cont (f : ℝ → ℝ) (σ : ℕ → ℚ × ℚ)
    (hσ : Function.Surjective σ)
    (s : ℕ → Finset ℝ × Finset (ℕ × ℤ × ℝ × ℝ))
    (hsInv : ∀ n, blumInv f (s n))
    (hmonoP : ∀ n n' : ℕ, n ≤ n' → (s n).1 ⊆ (s n').1)
    (hmonoL : ∀ n n' : ℕ, n ≤ n' → (s n).2 ⊆ (s n').2)
    (hmeet : ∀ n, (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty →
      (↑(s (n+1)).1 ∩ Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty)
    (hlab : ∀ n, ∀ d ∈ (s n).1, ∃ ℓ ∈ (s (n+1)).2,
      d ∈ blumDyI ℓ.1 ℓ.2.1 ∧ ℓ.2.2.2 ≤ 1 / ((n : ℝ) + 1)) :
    ∃ D : Set ℝ, Dense D ∧ ContinuousOn f D := by
  classical
  set D : Set ℝ := ⋃ n, ↑(s n).1 with hD
  have hDmem : ∀ n, ∀ d : ℝ, d ∈ (s n).1 → d ∈ D := by
    intro n d hd
    rw [hD]
    exact Set.mem_iUnion.mpr ⟨n, Finset.mem_coe.mpr hd⟩
  refine ⟨D, ?_, ?_⟩
  · rw [dense_iff_inter_open]
    intro W hWo hWne
    obtain ⟨y, hyW⟩ := hWne
    obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hWo y hyW
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show y - r / 2 < y by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (y : ℝ) < y + r / 2 by linarith)
    have hIooW : Set.Ioo ((p : ℚ) : ℝ) ((q : ℚ) : ℝ) ⊆ W := by
      intro z hz
      apply hrsub
      have hz' : ((p : ℚ) : ℝ) < z ∧ z < ((q : ℚ) : ℝ) := hz
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz'.1, hz'.2, hp1, hp2, hq1, hq2, hrpos]
    have hIne : (Set.Ioo ((p : ℚ) : ℝ) ((q : ℚ) : ℝ)).Nonempty :=
      ⟨y, hp2, hq1⟩
    obtain ⟨n, hn⟩ := hσ (p, q)
    have hp_eq : ((σ n).1 : ℝ) = ((p : ℚ) : ℝ) := by rw [hn]
    have hq_eq : ((σ n).2 : ℝ) = ((q : ℚ) : ℝ) := by rw [hn]
    have hne : (Set.Ioo ((σ n).1 : ℝ) ((σ n).2 : ℝ)).Nonempty := by
      rw [hp_eq, hq_eq]
      exact hIne
    obtain ⟨z, hzmem, hzIoo⟩ := hmeet n hne
    rw [hp_eq, hq_eq] at hzIoo
    exact ⟨z, hIooW hzIoo, hDmem (n + 1) z hzmem⟩
  · rw [Metric.continuousOn_iff]
    intro d hdD ε hεpos
    have hdD' : d ∈ ⋃ m, ↑(s m).1 := by rw [← hD]; exact hdD
    obtain ⟨n₀, hn₀'⟩ := Set.mem_iUnion.mp hdD'
    have hn₀ : d ∈ (s n₀).1 := Finset.mem_coe.mp hn₀'
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 2 by linarith)
    set n := max k n₀ with hn
    have hn0 : n₀ ≤ n := le_max_right _ _
    have hnk : k ≤ n := le_max_left _ _
    have hdP : d ∈ (s n).1 := hmonoP n₀ n hn0 hn₀
    obtain ⟨ℓ, hℓL, hdy, hr⟩ := hlab n d hdP
    have h2 : 2 * (1 / ((n : ℝ) + 1)) < ε := by
      have hkk : ((k : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
        exact_mod_cast Nat.succ_le_succ hnk
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hkk
      linarith [hk]
    have hopen : IsOpen (blumDyI ℓ.1 ℓ.2.1) := by
      rw [blumDyI]
      exact isOpen_Ioo
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hopen d hdy
    refine ⟨δ, hδpos, ?_⟩
    intro y hyD hydist
    have hyD'' : y ∈ ⋃ m, ↑(s m).1 := by rw [← hD]; exact hyD
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hyD''
    have hyP : y ∈ (s N).1 := Finset.mem_coe.mp hN
    set N' := max N (n + 1) with hN'
    have hNN' : N ≤ N' := le_max_left _ _
    have hnN' : n + 1 ≤ N' := le_max_right _ _
    have hyP' : y ∈ (s N').1 := hmonoP N N' hNN' hyP
    have hdP' : d ∈ (s N').1 := hmonoP n N' (le_trans (Nat.le_succ n) hnN') hdP
    have hℓL' : ℓ ∈ (s N').2 := hmonoL (n + 1) N' hnN' hℓL
    obtain ⟨oV1, oV2, oV3, oV4⟩ := hsInv N'
    have hymem : y ∈ blumDyI ℓ.1 ℓ.2.1 :=
      hδsub (Metric.mem_ball.mpr hydist)
    have hfy : dist (f y) ℓ.2.2.1 < ℓ.2.2.2 := oV2 ℓ hℓL' y hyP' hymem
    have hfd : dist (f d) ℓ.2.2.1 < ℓ.2.2.2 := oV2 ℓ hℓL' d hdP' hdy
    have htri : dist (f y) (f d) ≤ dist (f y) ℓ.2.2.1 + dist (f d) ℓ.2.2.1 := by
      have h := dist_triangle (f y) ℓ.2.2.1 (f d)
      rwa [dist_comm ℓ.2.2.1 (f d)] at h
    linarith [htri, hfy, hfd, hr, h2]

/-- **Blumberg's theorem.** For every function $f : \mathbb{R} \to \mathbb{R}$ there is a dense
set $D \subseteq \mathbb{R}$ such that the restriction of $f$ to $D$ is continuous.

Proves `Wanted` entry `blumberg_theorem`.

Source: https://en.wikipedia.org/wiki/Blumberg_theorem, statement blumberg-s1.
-/
theorem blumberg_theorem : ∀ f : ℝ → ℝ, ∃ D : Set ℝ, Dense D ∧ ContinuousOn f D := by
  intro f
  obtain ⟨σ, hσ, s, hs0, hsInv, hmonoP, hmonoL, hmeet, hlab⟩ := blum_seq f
  exact blum_dense_cont f σ hσ s hsInv hmonoP hmonoL hmeet hlab

end MetaMathlibExt
end
