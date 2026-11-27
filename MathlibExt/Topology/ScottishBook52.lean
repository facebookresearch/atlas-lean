/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.ContinuousMap.Basic

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Borel complexity of everywhere differentiable functions

In the compact-open topology on continuous real functions on the open unit interval,
the everywhere differentiable functions form a non-Borel set.

We code trees by labellings of finite sequences of natural numbers. Each active vertex
carries a smooth bump and scaled copies of its children's functions on disjoint intervals.
The widths of the child intervals decay quadratically in their distance from zero.
The resulting function is everywhere differentiable exactly when there is no infinite
active branch. A diagonal argument in Baire space gives the non-Borel lower bound.
-/

@[expose] public section

namespace MathlibExt.Topology.ScottishBook52Wanted

/-- **Functions differentiable at every point of $(0, 1)$.** A continuous function
$f \colon (0, 1) \to \mathbb{R}$ has a derivative at every point if for every $x \in (0, 1)$ the
function $\tilde f \colon \mathbb{R} \to \mathbb{R}$ equal to $f$ on $(0, 1)$ and to $0$ outside
$(0, 1)$ is differentiable at $x$. Since $\tilde f$ agrees with $f$ near every point of $(0, 1)$,
this depends only on $f$: it says that $f$ is differentiable at every point of $(0, 1)$. -/
def HasDerivativeAtEveryPoint (f : C(↥(Set.Ioo (0 : ℝ) 1), ℝ)) : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
    DifferentiableAt ℝ (fun y => if h : y ∈ Set.Ioo (0 : ℝ) 1 then f ⟨y, h⟩ else 0) x

noncomputable section

open Set Filter _root_.Topology MeasureTheory

private abbrev I := ↥(Ioo (0 : ℝ) 1)

private lemma differentiable_restriction (g : ℝ → ℝ) (hg : Continuous g) :
    HasDerivativeAtEveryPoint ⟨fun x : I ↦ g x, hg.comp continuous_subtype_val⟩ ↔
    ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ g x := by
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  apply Filter.EventuallyEq.differentiableAt_iff
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  simp [hy]

private abbrev Seq := ℕ → ℕ

private def prefixList (a : Seq) (n : ℕ) := List.ofFn (fun i : Fin n ↦ a i)

private def flag (p x y : Seq) (n : ℕ) : Prop :=
  p (Encodable.encode (prefixList x n, prefixList y n)) ≠ 0

-- A code lies in the diagonal set when its own section has no infinite branch.
private def diagonal : Set Seq := {p | ¬ ∃ y : Seq, ∀ n, flag p p y n}

-- This code records precisely the finite prefixes attained on the graph of F.
private def graphCode (F : Seq → Seq) (i : ℕ) : ℕ := by
  classical
  exact if ∃ z n, Encodable.encode (prefixList (F z) n, prefixList z n) = i then 1 else 0

private lemma flag_graphCode (F : Seq → Seq) (x y : Seq) (n : ℕ) :
    flag (graphCode F) x y n ↔
      ∃ z, prefixList (F z) n = prefixList x n ∧ prefixList z n = prefixList y n := by
  classical
  simp only [flag, graphCode, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
    Encodable.encode_inj, Prod.mk.injEq]
  constructor
  · rintro ⟨z, m, h₁, h₂⟩
    have hm := congrArg List.length h₂
    simp only [prefixList, List.length_ofFn] at hm
    subst m
    exact ⟨z, h₁, h₂⟩
  · rintro ⟨z, h₁, h₂⟩
    exact ⟨z, n, h₁, h₂⟩

private lemma tendsto_of_prefixList {u : ℕ → Seq} {x : Seq}
    (hu : ∀ n, prefixList (u n) n = prefixList x n) :
    Tendsto u atTop (𝓝 x) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_gt_atTop i] with n hn
  exact congrFun (List.ofFn_inj.mp (hu n)) ⟨i, hn⟩

private lemma branch_graphCode {F : Seq → Seq} (hF : Continuous F) (x : Seq) :
    (∃ y : Seq, ∀ n, flag (graphCode F) x y n) ↔ x ∈ range F := by
  constructor
  · rintro ⟨y, hy⟩
    choose z hz using fun n ↦ (flag_graphCode F x y n).1 (hy n)
    have hzy : Tendsto z atTop (𝓝 y) := tendsto_of_prefixList fun n ↦ (hz n).2
    exact ⟨y, tendsto_nhds_unique (hF.continuousAt.tendsto.comp hzy)
      (tendsto_of_prefixList fun n ↦ (hz n).1)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun n ↦ (flag_graphCode F (F y) y n).2 ⟨y, rfl, rfl⟩⟩

private theorem diagonal_not_borel : ¬ MeasurableSet diagonal := by
  intro h
  obtain ⟨β, _, _, F, hF, hr⟩ := analyticSet_iff_exists_polishSpace_range.1 h.analyticSet
  have hz : (fun _ ↦ 0) ∈ diagonal := by
    rintro ⟨y, hy⟩
    exact hy 0 rfl
  obtain ⟨z, _⟩ := hr.symm ▸ hz
  let : Nonempty β := ⟨z⟩
  obtain ⟨g, hg, honto⟩ := PolishSpace.exists_nat_nat_continuous_surjective β
  -- At its own code the graph would have a branch exactly when it has none.
  have hc := branch_graphCode (hF.comp hg) (graphCode (F ∘ g))
  rw [honto.range_comp, hr] at hc
  exact iff_not_self hc

private abbrev TreeCode := List ℕ → Bool

-- At each vertex, the k-th child occupies [a, a + a²].
private def offset (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ (k + 1)

private def width (k : ℕ) : ℝ := offset k ^ 2

private def interval (k : ℕ) := Icc (offset k) (offset k + width k)

private def window (k : ℕ) := Ioo (offset k / 2) (2 * offset k)

private lemma offset_pos (k : ℕ) : 0 < offset k := by unfold offset; positivity

private lemma offset_le (k : ℕ) : offset k ≤ 1 / 4 := by
  simpa [offset, pow_succ] using
    mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) (n := k))
      (by norm_num : (0 : ℝ) ≤ 1 / 4)

private lemma width_pos (k : ℕ) : 0 < width k := sq_pos_of_pos (offset_pos k)

private lemma width_le (k : ℕ) : width k ≤ offset k := by
  rw [width, pow_two]
  exact mul_le_of_le_one_right (offset_pos k).le (by linarith [offset_le k])

private lemma interval_sub (k : ℕ) : interval k ⊆ window k := by
  intro x ⟨hx, hx'⟩
  constructor
  · linarith [offset_pos k]
  · have h := mul_lt_mul_of_pos_right (show offset k < 1 by linarith [offset_le k]) (offset_pos k)
    dsimp [width] at hx'
    nlinarith

private lemma window_unique {i j : ℕ} {x : ℝ} (hi : x ∈ window i) (hj : x ∈ window j) : i = j := by
  have hsep (m n : ℕ) (hmn : m < n) : 2 * offset n ≤ offset m / 2 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
      (show m + 1 + 1 ≤ n + 1 by omega)
    dsimp [offset]
    rw [pow_succ (n := m + 1)] at h
    linarith
  rcases lt_trichotomy i j with h | h | h
  · linarith [hi.1, hj.2, hsep i j h]
  · exact h
  · linarith [hj.1, hi.2, hsep j i h]

private def scaled (k : ℕ) (x : ℝ) := (x - offset k) / width k

private lemma scaled_mem {k : ℕ} {x : ℝ} :
    scaled k x ∈ Icc (0 : ℝ) 1 ↔ x ∈ interval k := by
  simp only [scaled, interval, mem_Icc, le_div_iff₀ (width_pos k), div_le_iff₀ (width_pos k)]
  constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith

private def bump : ContDiffBump (3 / 4 : ℝ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

private lemma bump_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 1 ≤ x) : bump x = 0 := by
  apply bump.zero_of_le_dist
  change 1 / 8 ≤ |x - 3 / 4|
  rcases hx with h | h
  · linarith [neg_le_abs (x - 3 / 4)]
  · linarith [le_abs_self (x - 3 / 4)]

-- Layer n contains the bumps at depth n below s. An inactive vertex kills its entire subtree.
private def layer (T : TreeCode) : ℕ → List ℕ → ℝ → ℝ
  | 0, s, x => if T s then bump x else 0
  | n + 1, s, x => if T s then ∑' k, width k * layer T n (s ++ [k]) (scaled k x) else 0

private lemma layer_off (T : TreeCode) (n : ℕ) (s : List ℕ) {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    layer T n s x = 0 := by
  induction n generalizing s x with
  | zero =>
    have hb : bump x = 0 := bump_zero (by simp only [mem_Icc, not_and_or, not_le] at hx; grind)
    simp [layer, hb]
  | succ n ih =>
    suffices h : ∀ k, layer T n (s ++ [k]) (scaled k x) = 0 by simp [layer, h]
    intro k
    apply ih
    rw [scaled_mem]
    intro hk
    exact hx ⟨by linarith [hk.1, offset_pos k], by linarith [hk.2, width_le k, offset_le k]⟩

private lemma layer_child (T : TreeCode) (n : ℕ) (s : List ℕ) {x : ℝ} {k : ℕ}
    (hx : x ∈ window k) (hT : T s = true) :
    layer T (n + 1) s x = width k * layer T n (s ++ [k]) (scaled k x) := by
  simp only [layer, hT, ite_true]
  apply tsum_eq_single k
  intro j hj
  rw [layer_off, mul_zero]
  exact fun h ↦ hj (window_unique (interval_sub _ (scaled_mem.1 h)) hx)

private lemma layer_gap (T : TreeCode) (n : ℕ) (s : List ℕ) {x : ℝ}
    (hx : ∀ k, x ∉ interval k) : layer T (n + 1) s x = 0 := by
  have hz (k : ℕ) := layer_off T n (s ++ [k]) (fun h ↦ hx k (scaled_mem.mp h))
  simp [layer, hz]

private lemma layer_bound (T : TreeCode) (n : ℕ) (s : List ℕ) (x : ℝ) :
    layer T n s x ∈ Icc (0 : ℝ) ((1 / 2)^n) := by
  induction n generalizing s x with
  | zero =>
    cases h : T s <;> simp [layer, h, bump.nonneg, bump.le_one]
  | succ n ih =>
    rcases em (∃ k, x ∈ interval k) with ⟨k, hk⟩ | h
    · cases hT : T s with
      | false => simp [layer, hT]
      | true =>
        rw [layer_child _ _ _ (interval_sub _ hk) hT]
        obtain ⟨h₁, h₂⟩ := ih (s ++ [k]) (scaled k x)
        refine ⟨mul_nonneg (width_pos k).le h₁, ?_⟩
        rw [pow_succ']
        exact mul_le_mul (by linarith [width_le k, offset_le k]) h₂ h₁ (by norm_num)
    · rw [layer_gap T n s (not_exists.mp h)]
      exact ⟨le_rfl, by positivity⟩

private def treeFun (T : TreeCode) (s : List ℕ) (x : ℝ) := ∑' n, layer T n s x

private lemma layer_summable (T : TreeCode) (s : List ℕ) (x : ℝ) :
    Summable (fun n ↦ layer T n s x) :=
  Summable.of_nonneg_of_le (fun n ↦ (layer_bound T n s x).1)
    (fun n ↦ (layer_bound T n s x).2) summable_geometric_two

private lemma treeFun_bound (T : TreeCode) (s : List ℕ) (x : ℝ) :
    treeFun T s x ∈ Icc (0 : ℝ) 2 :=
  ⟨tsum_nonneg (fun n ↦ (layer_bound T n s x).1),
    (Summable.tsum_le_tsum (fun n ↦ (layer_bound T n s x).2) (layer_summable T s x)
      summable_geometric_two).trans_eq tsum_geometric_two⟩

private lemma treeFun_gap (T : TreeCode) (s : List ℕ) {x : ℝ} (hx : ∀ k, x ∉ interval k) :
    treeFun T s x = if T s then bump x else 0 := by
  rw [treeFun, (layer_summable T s x).tsum_eq_zero_add]
  simp_rw [layer_gap T _ s hx]
  simp [layer]

private lemma treeFun_inactive (T : TreeCode) (s : List ℕ) (hT : T s = false) :
    treeFun T s = 0 := by
  funext x
  have h (n) : layer T n s x = 0 := by cases n <;> simp [layer, hT]
  simp [treeFun, h]

private lemma treeFun_child (T : TreeCode) (s : List ℕ) {x : ℝ} {k : ℕ} (hx : x ∈ window k)
    (hT : T s = true) : treeFun T s x = width k * treeFun T (s ++ [k]) (scaled k x) := by
  rw [treeFun, (layer_summable T s x).tsum_eq_zero_add]
  have hb := bump_zero (x := x) (Or.inl (by linarith [hx.2, offset_le k]))
  simp_rw [layer_child T _ s hx hT]
  simp only [layer, hT, ite_true, hb, zero_add, treeFun, tsum_mul_left]

private lemma offset_summable : Summable offset :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))

private lemma continuous_gate (s : List ℕ) {f : TreeCode × ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun z : TreeCode × ℝ ↦ if z.1 s then f z else 0) := by
  have h : Continuous (fun b : Bool ↦ if b then (1 : ℝ) else 0) := continuous_of_discreteTopology
  convert (h.comp ((continuous_apply s).comp continuous_fst)).mul hf using 1
  ext z
  cases hz : z.1 s <;> simp [hz]

private lemma continuous_layer (n : ℕ) (s : List ℕ) :
    Continuous (fun z : TreeCode × ℝ ↦ layer z.1 n s z.2) := by
  induction n generalizing s with
  | zero => exact continuous_gate _ (bump.continuous.comp continuous_snd)
  | succ n ih =>
    apply continuous_gate
    apply continuous_tsum (u := offset)
    · intro k
      apply continuous_const.mul
      have hscale : Continuous (fun z : TreeCode × ℝ ↦ scaled k z.2) := by
        unfold scaled
        fun_prop
      exact (ih (s ++ [k])).comp (continuous_fst.prodMk hscale)
    · exact offset_summable
    · intro k z
      obtain ⟨h₁, h₂⟩ := layer_bound z.1 n (s ++ [k]) (scaled k z.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (width_pos k).le h₁)]
      exact (mul_le_of_le_one_right (width_pos k).le
        (h₂.trans (pow_le_one₀ (by norm_num) (by norm_num)))).trans (width_le k)

private lemma continuous_treeFun (s : List ℕ) :
    Continuous (fun z : TreeCode × ℝ ↦ treeFun z.1 s z.2) := by
  apply continuous_tsum (fun n ↦ continuous_layer n s) summable_geometric_two
  intro n z
  obtain ⟨h₁, h₂⟩ := layer_bound z.1 n s z.2
  simpa [Real.norm_eq_abs, abs_of_nonneg h₁] using h₂

-- The child intervals can accumulate only at zero.
private lemma eventually_gap {x : ℝ} (h₀ : x ≠ 0) (hx : ∀ k, x ∉ interval k) :
    ∀ᶠ y in 𝓝 x, ∀ k, y ∉ interval k := by
  rcases lt_or_gt_of_ne h₀ with hneg | hpos
  · filter_upwards [gt_mem_nhds hneg] with y hy k hk
    linarith [hk.1, offset_pos k]
  have ht := offset_summable.tendsto_atTop_zero.eventually
    (gt_mem_nhds (show 0 < x / 4 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht
  have hf : ∀ᶠ y in 𝓝 x, ∀ k ∈ Finset.range N, y ∉ interval k :=
    (eventually_all_finset _).2 fun k _ ↦ isClosed_Icc.isOpen_compl.mem_nhds (hx k)
  filter_upwards [hf, lt_mem_nhds (show x / 2 < x by linarith)] with y hy hy' k hk
  by_cases h : k < N
  · exact hy k (Finset.mem_range.mpr h) hk
  have hsmall : offset k < x / 4 := hN k (by omega)
  linarith [hk.2, width_le k]

-- Every child copy has height at most twice its width, hence is O(x²) at the origin.
private lemma treeFun_origin (T : TreeCode) (s : List ℕ) :
    HasDerivAt (treeFun T s) 0 0 := by
  have h₀ : treeFun T s 0 = 0 := by
    rw [treeFun_gap _ _ (fun k h ↦ (offset_pos k).not_ge h.1), bump_zero (Or.inl (by norm_num))]
    simp
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  simp only [h₀, sub_zero, smul_zero, Real.norm_eq_abs]
  intro c hc
  filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num),
    gt_mem_nhds (show 0 < c / 2 by linarith)] with x hx hcx
  rw [abs_of_nonneg (treeFun_bound T s x).1]
  rcases em (∃ k, x ∈ interval k) with ⟨k, hk⟩ | h
  · cases hT : T s with
    | false => simp [treeFun_inactive T s hT, mul_nonneg hc.le (abs_nonneg x)]
    | true =>
      rw [treeFun_child _ _ (interval_sub _ hk) hT, abs_of_pos ((offset_pos k).trans_le hk.1)]
      have h := mul_le_mul_of_nonneg_left (treeFun_bound T (s ++ [k]) (scaled k x)).2
        (width_pos k).le
      have hx' : offset k ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (offset_pos k).le hk.1 2
      dsimp [width] at h
      unfold width
      nlinarith [mul_nonneg (show 0 ≤ c - 2 * x by linarith) ((offset_pos k).le.trans hk.1)]
  · rw [treeFun_gap _ _ (not_exists.mp h), bump_zero (Or.inl hx.le)]
    simpa using mul_nonneg hc.le (abs_nonneg x)

private lemma differentiable_of_children (T : TreeCode) (s : List ℕ)
    (h : ∀ k, Differentiable ℝ (treeFun T (s ++ [k]))) : Differentiable ℝ (treeFun T s) := by
  cases hT : T s with
  | false => rw [treeFun_inactive _ _ hT]; exact differentiable_const _
  | true =>
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact (treeFun_origin T s).differentiableAt
    by_cases hc : ∃ k, x ∈ interval k
    · obtain ⟨k, hk⟩ := hc
      have he : treeFun T s =ᶠ[𝓝 x] fun y ↦ width k * treeFun T (s ++ [k]) (scaled k y) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds (interval_sub _ hk)) fun _ hy ↦
          treeFun_child _ _ hy hT
      exact he.differentiableAt_iff.mpr (differentiableAt_const _ |>.mul
        ((h k _).comp x (by unfold scaled; fun_prop)))
    · have he : treeFun T s =ᶠ[𝓝 x] bump := (eventually_gap hx (not_exists.mp hc)).mono
          fun _ hy ↦ by simp [treeFun_gap _ _ hy, hT]
      exact he.differentiableAt_iff.mpr (bump.contDiffAt.differentiableAt (n := 1) (by decide))

private lemma prefixList_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixList a (n + 1) = prefixList a n ++ [a n] := by
  rw [prefixList, List.ofFn_succ', List.concat_eq_append]
  rfl

-- Failure of differentiability passes to some child, giving an infinite active branch.
private lemma branch_of_not_differentiable {T : TreeCode} (h : ¬Differentiable ℝ (treeFun T [])) :
    ∃ y : ℕ → ℕ, ∀ n, T (prefixList y n) = true := by
  classical
  let Bad := fun s ↦ ¬Differentiable ℝ (treeFun T s)
  have step (s) (hs : Bad s) : ∃ k, Bad (s ++ [k]) := by
    by_contra! H
    exact hs (differentiable_of_children _ _ (by simpa [Bad] using H))
  let next (s) := if hs : Bad s then (step s hs).choose else 0
  let walk : ℕ → List ℕ := Nat.rec [] (fun _ s ↦ s ++ [next s])
  have bad (n) : Bad (walk n) := by
    induction n with
    | zero => exact h
    | succ n ih =>
      change Bad (walk n ++ [next (walk n)])
      simpa [next, ih] using (step (walk n) ih).choose_spec
  let y (n) := next (walk n)
  have path (n) : prefixList y n = walk n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [prefixList_succ, ih]
  refine ⟨y, fun n ↦ ?_⟩
  rw [path]
  cases hT : T (walk n)
  · exact (bad n (by rw [treeFun_inactive T _ hT]; exact differentiable_const _)).elim
  · rfl

private lemma treeFun_peak {T : TreeCode} {s : List ℕ} (hs : T s = true) :
    treeFun T s (3 / 4) = 1 := by
  have hg (k) : (3 / 4 : ℝ) ∉ interval k := fun hk ↦ by linarith [hk.2, width_le k, offset_le k]
  simp only [treeFun_gap _ _ hg, hs, ite_true]
  exact bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)

-- The intervals along a branch are nested affine copies of the unit interval.
private lemma bad_point_of_branch {T : TreeCode} {y : ℕ → ℕ} (hy : ∀ n, T (prefixList y n) = true) :
    ∃ x ∈ Ioo (0 : ℝ) 1, ¬DifferentiableAt ℝ (treeFun T []) x := by
  -- At depth n the affine copy of the unit interval has left endpoint l n and width w n.
  let w : ℕ → ℝ := Nat.rec 1 (fun n t ↦ t * width (y n))
  let l : ℕ → ℝ := Nat.rec 0 (fun n t ↦ t + w n * offset (y n))
  have ws (n) : w (n + 1) = w n * width (y n) := rfl
  have ls (n) : l (n + 1) = l n + w n * offset (y n) := rfl
  have wp (n) : 0 < w n := by
    induction n with
    | zero => exact zero_lt_one
    | succ n ih => exact mul_pos ih (width_pos _)
  have wbound (n) : w n ≤ (1 / 2 : ℝ)^n := by
    induction n with
    | zero => simp [w]
    | succ n ih =>
      rw [ws, pow_succ]
      exact mul_le_mul ih (by linarith [width_le (y n), offset_le (y n)])
        (width_pos _).le (by positivity)
  have wlim : Tendsto w atTop (𝓝 0) := squeeze_zero (fun n ↦ (wp n).le) wbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  let J n := Icc (l n) (l n + w n)
  have nested (n) : J (n + 1) ⊆ J n := by
    intro z ⟨hz, hz'⟩
    rw [ls] at hz hz'
    rw [ws] at hz'
    have hc : offset (y n) + width (y n) ≤ 1 := by linarith [offset_le (y n), width_le (y n)]
    constructor
    · linarith [mul_pos (wp n) (offset_pos (y n))]
    · nlinarith [mul_le_mul_of_nonneg_left hc (wp n).le]
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed J nested
    (fun n ↦ nonempty_Icc.2 (by linarith [wp n])) isCompact_Icc (fun _ ↦ isClosed_Icc)
  have hxJ (n) : x ∈ J n := mem_iInter.mp hx n
  have hxI : x ∈ Ioo (0 : ℝ) 1 := by
    have ⟨h₁, h₂⟩ := hxJ 1
    change 0 + 1 * offset (y 0) ≤ x at h₁
    change x ≤ 0 + 1 * offset (y 0) + 1 * width (y 0) at h₂
    constructor <;> linarith [offset_pos (y 0), offset_le (y 0), width_le (y 0)]
  have copy (n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      treeFun T [] (l n + w n * t) = w n * treeFun T (prefixList y n) t := by
    induction n generalizing t with
    | zero => simp [l, w, prefixList]
    | succ n ih =>
      let k := y n
      let u := offset k + width k * t
      have hu : u ∈ interval k := ⟨by dsimp [u]; nlinarith [mul_nonneg (width_pos k).le ht.1],
        by dsimp [u]; nlinarith [mul_le_mul_of_nonneg_left ht.2 (width_pos k).le]⟩
      have hu' : u ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith [hu.1, offset_pos k], by linarith [hu.2, width_le k, offset_le k]⟩
      have hscale : scaled k u = t := by
        dsimp [scaled, u]
        field_simp [(width_pos k).ne']
        ring
      rw [show l (n + 1) + w (n + 1) * t = l n + w n * u by rw [ls, ws]; dsimp [u, k]; ring,
        ih u hu', treeFun_child _ _ (interval_sub _ hu) (hy n), hscale, ws, prefixList_succ]
      ring
  have upper (n) : treeFun T [] x ≤ w n * 2 := by
    let t := (x - l n) / w n
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.2 (hxJ n).1) (wp n).le
      · exact (div_le_iff₀ (wp n)).2 (by linarith [(hxJ n).2])
    have H := copy n t ht
    rw [show l n + w n * t = x by dsimp [t]; field_simp [(wp n).ne']; ring] at H
    exact H.le.trans (mul_le_mul_of_nonneg_left (treeFun_bound _ _ _).2 (wp n).le)
  have hzero : treeFun T [] x = 0 := le_antisymm
    (by simpa using ge_of_tendsto (wlim.mul_const 2) (Eventually.of_forall upper))
    (treeFun_bound _ _ _).1
  let peak n := l n + w n * (3 / 4)
  have dist_le (n) : |peak n - x| ≤ w n := by
    rw [abs_le]
    dsimp [peak]
    constructor <;> linarith [(hxJ n).1, (hxJ n).2, wp n]
  have hlim : Tendsto peak atTop (𝓝 x) := tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun n ↦ dist_nonneg) dist_le wlim)
  refine ⟨x, hxI, fun hd ↦ ?_⟩
  -- The limit point is a minimum. A derivative there would vanish, but each nearby
  -- peak has height equal to the width of its interval.
  have hm : IsLocalMin (treeFun T []) x :=
    Eventually.of_forall fun z ↦ hzero.trans_le (treeFun_bound _ _ z).1
  have hder := hd.hasDerivAt
  rw [hm.deriv_eq_zero, hasDerivAt_iff_isLittleO] at hder
  have he := hlim.eventually (hder.bound (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨n, hn⟩ := he.exists
  have hp : treeFun T [] (peak n) = w n := by
    change treeFun T [] (l n + w n * (3 / 4)) = w n
    rw [copy n (3 / 4) (by constructor <;> norm_num), treeFun_peak (hy n),
      mul_one]
  simp only [hzero, sub_zero, smul_zero, hp, Real.norm_eq_abs, abs_of_pos (wp n)] at hn
  linarith [dist_le n, wp n]

private def marked (p : Seq) (s : List ℕ) : Bool :=
  decide (p (Encodable.encode (prefixList p s.length, s)) ≠ 0)

private lemma marked_prefix (p y : Seq) (n : ℕ) :
    marked p (prefixList y n) = true ↔ flag p p y n := by
  simp [marked, flag, prefixList]

private lemma measurable_marked : Measurable marked := by
  apply Measurable.of_eval
  intro s
  let idx (p : Seq) := Encodable.encode (prefixList p s.length, s)
  have hidx : Measurable idx := by
    let key (v : Fin s.length → ℕ) := Encodable.encode (List.ofFn v, s)
    exact (measurable_of_countable key).comp (.of_eval fun i ↦ measurable_pi_apply (i : ℕ))
  have hval : Measurable (fun p : Seq ↦ p (idx p)) := by
    have heval : Measurable (fun z : Seq × ℕ ↦ z.1 z.2) :=
      measurable_from_prod_countable_left fun i ↦ measurable_pi_apply i
    exact heval.comp (measurable_id.prodMk hidx)
  exact (measurable_of_countable (fun i : ℕ ↦ decide (i ≠ 0))).comp hval

private def reduction : C(TreeCode, C(I, ℝ)) :=
  ContinuousMap.curry ⟨fun z ↦ treeFun z.1 [] z.2.val,
    (continuous_treeFun []).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩

private lemma reduction_preimage :
    (fun p ↦ reduction (marked p)) ⁻¹' {f : C(I, ℝ) | HasDerivativeAtEveryPoint f} = diagonal := by
  ext p
  have hc : Continuous (treeFun (marked p) []) :=
    (continuous_treeFun []).comp (continuous_const.prodMk continuous_id)
  refine (differentiable_restriction _ hc).trans ?_
  constructor
  · intro hd ⟨y, hy⟩
    obtain ⟨x, hx, hbad⟩ := bad_point_of_branch (fun n ↦ (marked_prefix p y n).2 (hy n))
    exact hbad (hd x hx)
  · intro h
    have hd : Differentiable ℝ (treeFun (marked p) []) := by
      by_contra hn
      obtain ⟨y, hy⟩ := branch_of_not_differentiable hn
      exact h ⟨y, fun n ↦ (marked_prefix p y n).1 (hy n)⟩
    exact fun x _ ↦ hd x

/--
**Everywhere differentiable functions do not form a Borel set.** In the space $C((0, 1))$ of
continuous real functions on the open interval $(0, 1)$, with the compact-open topology (uniform
convergence on compact subsets), the set of functions that have a derivative at every point of
$(0, 1)$ is not a Borel set.

This is Banach's Problem 52 of the Scottish Book. The typescript also records that this class is
not an $F_\sigma$ set, that it is coanalytic, and that the problem was solved by Mazurkiewicz.

Source: S. Banach, Problem 52 of the Scottish Book; solved by Mazurkiewicz,
as recorded in typescript Ad 52; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem everywhere_differentiable_class_not_borel :
    ¬ MeasurableSet { f : C(↥(Set.Ioo (0 : ℝ) 1), ℝ) | HasDerivativeAtEveryPoint f } := by
  intro h
  apply diagonal_not_borel
  rw [← reduction_preimage]
  exact h.preimage (reduction.continuous.measurable.comp measurable_marked)

end

end MathlibExt.Topology.ScottishBook52Wanted
