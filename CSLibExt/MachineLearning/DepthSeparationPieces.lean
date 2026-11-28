/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.Backpropagation
public import Mathlib.Algebra.Notation
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Piece-count bounds for univariate ReLU networks

Upper bounds on the number of affine pieces of univariate functions computed
by feedforward ReLU networks, following the lecture-notes account of piece
combination rules and the per-node induction (M. Telgarsky, deep learning
theory lecture notes, Section 5.2).

The combination rules formalized are those the per-node induction needs; the
general composition rule for arbitrary outer functions is not included, only
its ReLU instance.
-/

@[expose] public section

namespace Cslib.MachineLearning.DepthSeparationPieces

open Cslib.MachineLearning.Backpropagation

/-- Bounded piece-count predicate: `PiecesLE n f` holds when `f` satisfies the
collinearity equation on each interval avoiding some breakpoint set `s` with at
most `n` intervals (`s.card + 1` intervals). This captures continuous
piecewise-affine functions: `f` is affine on each closed interval between
consecutive breakpoints, with values agreeing at shared endpoints. This is the
bounded form of the lecture-notes affine-pieces definition for continuous `f`,
so `PiecesLE n f` implies the source piece count of `f` is at most `n`; no
minimality of the breakpoint set is claimed. -/
def PiecesLE (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, s.card + 1 ≤ n ∧ ∀ (x y z : ℝ), x ≤ y → y ≤ z →
    (∀ p ∈ s, ¬(x < p ∧ p < z)) →
    (f y - f x) * (z - x) = (f z - f x) * (y - x)

/-- The input vector with every coordinate equal to `x`. -/
def inputVec (d : ℕ → ℕ) (x : ℝ) : EuclideanSpace ℝ (Fin (d 0)) :=
  WithLp.toLp 2 fun _ => x

/-- Every coordinate of `inputVec d x` equals `x`. -/
theorem inputVec_apply (d : ℕ → ℕ) (x : ℝ) (j : Fin (d 0)) :
    inputVec d x j = x := rfl

/-- A ReLU network: every layer applies `posPart` coordinatewise after an
affine map with the given weights and biases. -/
def IsReluNet (d : ℕ → ℕ) (Nnet : Net d) : Prop :=
  ∀ (k : ℕ), ∃ (W : Fin (d (k + 1)) → Fin (d k) → ℝ)
    (b : Fin (d (k + 1)) → ℝ),
    ∀ (x : EuclideanSpace ℝ (Fin (d k))) (j : Fin (d (k + 1))),
      Nnet.layer k x j = ((∑ i, W j i * x i) + b j)⁺

/-- A ReLU network up to layer `n`: layers `0, ..., n - 1` apply `posPart`
coordinatewise after an affine map. These are exactly the layers that
`forward n` traverses. -/
def IsReluNetUpTo (d : ℕ → ℕ) (Nnet : Net d) (n : ℕ) : Prop :=
  ∀ k < n, ∃ (W : Fin (d (k + 1)) → Fin (d k) → ℝ)
    (b : Fin (d (k + 1)) → ℝ),
    ∀ (x : EuclideanSpace ℝ (Fin (d k))) (j : Fin (d (k + 1))),
      Nnet.layer k x j = ((∑ i, W j i * x i) + b j)⁺

/-- A full ReLU network is a ReLU network up to any bound. -/
theorem IsReluNet.isReluNetUpTo (d : ℕ → ℕ) (Nnet : Net d) (n : ℕ)
    (h : IsReluNet d Nnet) : IsReluNetUpTo d Nnet n :=
  fun k _ => h k

/-- No function has zero pieces: any breakpoint set gives at least one. -/
theorem piecesLE_zero_none (f : ℝ → ℝ) : ¬ PiecesLE 0 f := by
  rintro ⟨s, hsn, _⟩
  omega

/-- A constant function has one piece. -/
theorem piecesLE_const (c : ℝ) : PiecesLE 1 (fun _ => c) := by
  refine ⟨∅, by simp, ?_⟩
  intro x y z _ _ _
  change (c - c) * (z - x) = (c - c) * (y - x)
  ring

/-- The identity has one piece. -/
theorem piecesLE_id : PiecesLE 1 id := by
  refine ⟨∅, by simp, ?_⟩
  intro x y z _ _ _
  change (y - x) * (z - x) = (z - x) * (y - x)
  ring

/-- An affine function has one piece. -/
theorem piecesLE_affine (a b : ℝ) : PiecesLE 1 (fun x => a * x + b) := by
  refine ⟨∅, by simp, ?_⟩
  intro x y z _ _ _
  change ((a * y + b) - (a * x + b)) * (z - x) =
    ((a * z + b) - (a * x + b)) * (y - x)
  ring

/-- The ReLU has two pieces, with breakpoint set `{0}`. -/
theorem piecesLE_relu : PiecesLE 2 (fun x => x⁺) := by
  refine ⟨{0}, by norm_num [Finset.card_singleton], ?_⟩
  intro x y z hxy hyz hmem
  have h0 : ¬(x < 0 ∧ 0 < z) := hmem 0 (Finset.mem_singleton_self 0)
  have hdisj : 0 ≤ x ∨ z ≤ 0 := by
    by_contra h
    rw [not_or] at h
    exact h0 ⟨not_le.mp h.1, not_le.mp h.2⟩
  change (y⁺ - x⁺) * (z - x) = (z⁺ - x⁺) * (y - x)
  rcases hdisj with hx | hz
  · rw [posPart_eq_self.mpr hx, posPart_eq_self.mpr (le_trans hx hxy),
      posPart_eq_self.mpr (le_trans (le_trans hx hxy) hyz)]
    ring
  · rw [posPart_eq_zero.mpr (le_trans hxy (le_trans hyz hz)),
      posPart_eq_zero.mpr (le_trans hyz hz), posPart_eq_zero.mpr hz]
    ring

/-- Sum of two functions: piece bounds add (breakpoint union argument). -/
theorem piecesLE_add (n m : ℕ) (f g : ℝ → ℝ) :
    PiecesLE n f → PiecesLE m g → PiecesLE (n + m) (f + g) := by
  rintro ⟨s, hsn, hs⟩ ⟨t, htm, ht⟩
  refine ⟨s ∪ t, ?_, ?_⟩
  · have hle := Finset.card_union_le s t
    omega
  · intro x y z hxy hyz hmem
    have h1 := hs x y z hxy hyz
      (fun p hp => hmem p (Finset.mem_union_left t hp))
    have h2 := ht x y z hxy hyz
      (fun p hp => hmem p (Finset.mem_union_right s hp))
    simp only [Pi.add_apply] at h1 h2 ⊢
    linear_combination h1 + h2

/-- Scaling keeps the same piece bound. -/
theorem piecesLE_smul (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    PiecesLE n f → PiecesLE n (c • f) := by
  rintro ⟨s, hsn, hs⟩
  refine ⟨s, hsn, ?_⟩
  intro x y z hxy hyz hmem
  have h1 := hs x y z hxy hyz hmem
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * h1

/-- A constant shift keeps the same piece bound. -/
theorem piecesLE_add_const (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    PiecesLE n f → PiecesLE n (fun x => f x + c) := by
  rintro ⟨s, hsn, hs⟩
  refine ⟨s, hsn, ?_⟩
  intro x y z hxy hyz hmem
  have h1 := hs x y z hxy hyz hmem
  change ((f y + c) - (f x + c)) * (z - x) = ((f z + c) - (f x + c)) * (y - x)
  linear_combination h1

/-- Sum over a nonempty index set: bounds add. The nonemptiness hypothesis
is needed since the empty sum would claim bound zero. -/
theorem piecesLE_sum_nonempty (ι : Type*) (s : Finset ι)
    (n : ι → ℕ) (f : ι → ℝ → ℝ) (hne : s.Nonempty)
    (h : ∀ i ∈ s, PiecesLE (n i) (f i)) :
    PiecesLE (∑ i ∈ s, n i) (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert hne h
  induction s using Finset.induction with
  | empty =>
    intro hne _
    exact absurd hne (by simp)
  | insert a t hat ih =>
    intro hne h
    by_cases hs : t.Nonempty
    · have hmem : ∀ i ∈ t, PiecesLE (n i) (f i) :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ih' := ih hs hmem
      have ha := h a (Finset.mem_insert_self a t)
      have hsum : (fun x : ℝ => ∑ i ∈ insert a t, f i x)
          = f a + (fun x => ∑ i ∈ t, f i x) := by
        funext x
        rw [Finset.sum_insert hat]
        rfl
      have hnsum : ∑ i ∈ insert a t, n i = n a + ∑ i ∈ t, n i :=
        Finset.sum_insert hat
      rw [hnsum, hsum]
      exact piecesLE_add _ _ _ _ ha ih'
    · have hs0 : t = ∅ :=
        Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => hs ⟨i, hi⟩)
      subst hs0
      simp only [Finset.insert_empty, Finset.sum_singleton]
      exact h a (Finset.mem_insert_self a ∅)

/-- Affine combination rule for a positive number of terms. -/
theorem piecesLE_sum_of_pos (k : ℕ) (n : Fin k → ℕ) (g : Fin k → ℝ → ℝ)
    (a : Fin k → ℝ) (b : ℝ) (h : ∀ i, PiecesLE (n i) (g i)) (hk : 0 < k) :
    PiecesLE (∑ i, n i) (fun x => (∑ i, a i * g i x) + b) := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      PiecesLE (n i) (fun x => a i * g i x) := by
    intro i _
    have hi := piecesLE_smul _ (a i) _ (h i)
    have heq : (fun x : ℝ => a i * g i x) = a i • g i := by
      funext x
      exact (smul_eq_mul _ _).symm
    rw [heq]
    exact hi
  have hS := piecesLE_sum_nonempty (Fin k) Finset.univ n
    (fun i x => a i * g i x) hne hsm
  have hC := piecesLE_add_const _ b _ hS
  exact hC

/-- The affine combination rule is false for zero terms: it would claim
`PiecesLE 0` of a constant function. -/
theorem piecesLE_sum_empty_false :
    ¬ ∀ (n : Fin 0 → ℕ) (g : Fin 0 → ℝ → ℝ) (a : Fin 0 → ℝ) (b : ℝ),
      (∀ i, PiecesLE (n i) (g i)) →
      PiecesLE (∑ i, n i) (fun x => (∑ i, a i * g i x) + b) := by
  have hsum : ∀ (n : Fin 0 → ℕ), (∑ i, n i) = 0 :=
    fun n => Finset.sum_of_isEmpty Finset.univ
  intro h
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) 0
    (fun i => i.elim0)
  rw [hsum] at h0
  exact piecesLE_zero_none _ h0

/-- Monotonicity of the piece bound: a larger bound still works. -/
theorem piecesLE_mono (n m : ℕ) (f : ℝ → ℝ) (hle : n ≤ m)
    (h : PiecesLE n f) : PiecesLE m f := by
  obtain ⟨s, hsn, hs⟩ := h
  exact ⟨s, le_trans hsn hle, hs⟩

/-- Affine combination rule: the bound of an affine combination is at most
the sum of the bounds, and at least one. The maximum with `1` covers the
zero-term case (see above); the positive case is proved separately. -/
theorem piecesLE_sum (k : ℕ) (n : Fin k → ℕ) (g : Fin k → ℝ → ℝ)
    (a : Fin k → ℝ) (b : ℝ) (h : ∀ i, PiecesLE (n i) (g i)) :
    PiecesLE (max (∑ i, n i) 1) (fun x => (∑ i, a i * g i x) + b) := by
  by_cases hk : k = 0
  · subst hk
    have h0 : (∑ i : Fin 0, n i) = 0 := Finset.sum_of_isEmpty Finset.univ
    have hmax : max (∑ i : Fin 0, n i) 1 = 1 := by omega
    have hfun : (fun x : ℝ => (∑ i, a i * g i x) + b) = fun _ => b := by
      funext x
      show (∑ i, a i * g i x) + b = b
      have he : (∑ i, a i * g i x) = 0 := Finset.sum_of_isEmpty Finset.univ
      rw [he, zero_add]
    rw [hmax, hfun]
    exact piecesLE_const b
  · have hk' : 0 < k := by omega
    exact piecesLE_mono _ _ _ (Nat.le_max_left _ _)
      (piecesLE_sum_of_pos _ n g a b h hk')

open Classical in
private def pieceMem (s : Finset ℝ) (k : ℕ) (x : ℝ) : Prop :=
  (s.filter (· < x)).card ≤ k ∧ k ≤ (s.filter (· ≤ x)).card

open Classical in
private theorem pieceMem_interval (s : Finset ℝ) (k : ℕ) (x z w : ℝ)
    (hx : pieceMem s k x) (hz : pieceMem s k z)
    (hxw : x ≤ w) (hwz : w ≤ z) : pieceMem s k w := by
  obtain ⟨_, hbx⟩ := hx
  obtain ⟨haz, _⟩ := hz
  have hsub1 : s.filter (· < w) ⊆ s.filter (· < z) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, lt_of_lt_of_le hq.2 hwz⟩
  have hsub2 : s.filter (· ≤ x) ⊆ s.filter (· ≤ w) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, le_trans hq.2 hxw⟩
  exact ⟨le_trans (Finset.card_le_card hsub1) haz,
    le_trans hbx (Finset.card_le_card hsub2)⟩

open Classical in
private theorem no_interior_of_pieceMem (s : Finset ℝ) (k : ℕ) (x z : ℝ)
    (hx : pieceMem s k x) (hz : pieceMem s k z)
    (p : ℝ) (hp : p ∈ s) : ¬(x < p ∧ p < z) := by
  rintro ⟨hpx, hpz⟩
  obtain ⟨_, hbx⟩ := hx
  obtain ⟨haz, _⟩ := hz
  have hsub : s.filter (· ≤ x) ⊆ s.filter (· < z) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, lt_of_le_of_lt hq.2 (lt_trans hpx hpz)⟩
  have hpne : s.filter (· ≤ x) ≠ s.filter (· < z) := by
    intro heq
    have hmem : p ∈ s.filter (· ≤ x) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨hp, hpz⟩
    rw [Finset.mem_filter] at hmem
    exact absurd hmem.2 (not_le.mpr hpx)
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hpne⟩)
  omega

open Classical in
private theorem aff_of_pieceMem (s : Finset ℝ) (h : ℝ → ℝ) (k : ℕ) (x z : ℝ)
    (hcol : ∀ a b c : ℝ, a ≤ b → b ≤ c →
      (∀ p ∈ s, ¬(a < p ∧ p < c)) →
      (h b - h a) * (c - a) = (h c - h a) * (b - a))
    (hx : pieceMem s k x) (hz : pieceMem s k z) (hxz : x < z) :
    ∃ m c : ℝ, ∀ w : ℝ, pieceMem s k w → h w = m * w + c := by
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxz)
  set m : ℝ := (h z - h x) / (z - x) with hm
  set c : ℝ := h x - m * x with hc
  have hmzx : m * (z - x) = h z - h x := by
    rw [hm, div_mul_cancel₀ _ hzx]
  have hx0 : h x = m * x + c := by rw [hc]; ring
  have hz0 : h z = m * z + c := by
    have htmp : m * z + c = h x + m * (z - x) := by rw [hc]; ring
    rw [htmp, hmzx]
    ring
  refine ⟨m, c, fun w hw => ?_⟩
  have hne : x - z ≠ 0 := sub_ne_zero.mpr (ne_of_lt hxz)
  rcases le_total w x with hwx | hxw
  · have hno := fun p hp => no_interior_of_pieceMem s k w z hw hz p hp
    have heq := hcol w x z hwx (le_of_lt hxz) hno
    rw [hx0, hz0] at heq
    have hkey : (h w - (m * w + c)) * (x - z) = 0 := by
      linear_combination heq
    have h0 := (mul_eq_zero.mp hkey).resolve_right hne
    exact sub_eq_zero.mp h0
  · rcases le_total w z with hwz | hzw
    · have hno := fun p hp => no_interior_of_pieceMem s k x z hx hz p hp
      have heq := hcol x w z hxw hwz hno
      rw [hx0, hz0] at heq
      have hkey : (h w - (m * w + c)) * (z - x) = 0 := by
        linear_combination heq
      have h0 := (mul_eq_zero.mp hkey).resolve_right hzx
      exact sub_eq_zero.mp h0
    · have hno := fun p hp => no_interior_of_pieceMem s k x w hx hw p hp
      have heq := hcol x z w (le_of_lt hxz) hzw hno
      rw [hx0, hz0] at heq
      have hkey : (h w - (m * w + c)) * (z - x) = 0 := by
        linear_combination -heq
      have h0 := (mul_eq_zero.mp hkey).resolve_right hzx
      exact sub_eq_zero.mp h0

open Classical in
private noncomputable def reluRoot (s : Finset ℝ) (h : ℝ → ℝ) (k : ℕ) : ℝ :=
  if hex : ∃ r : ℝ, pieceMem s k r ∧ h r = 0 then Classical.choose hex else 0

open Classical in
private theorem reluRoot_mixed_contra (s : Finset ℝ) (h : ℝ → ℝ) (k : ℕ)
    (x z m c : ℝ) (hmc : ∀ w : ℝ, pieceMem s k w → h w = m * w + c)
    (hxmem : pieceMem s k x) (hzmem : pieceMem s k z)
    (hxx : h x = m * x + c)
    (hmzx : m * (z - x) = h z - h x) (hm0 : m ≠ 0)
    (hxm : h x / m < 0) (hzm : 0 < h z / m)
    (hR : reluRoot s h k ∈ s ∪ Finset.image (reluRoot s h)
      (Finset.range (s.card + 1)))
    (hmem : ∀ p ∈ s ∪ Finset.image (reluRoot s h) (Finset.range (s.card + 1)),
      ¬(x < p ∧ p < z)) : False := by
  set r : ℝ := x - h x / m with hr
  have hcancel : m * (h x / m) = h x := by
    rw [mul_comm m (h x / m), div_mul_cancel₀ _ hm0]
  have heqr : r - x = -(h x / m) := by rw [hr]; ring
  have heqz : z - r = h z / m := by
    rw [hr, eq_div_iff_mul_eq hm0]
    linear_combination hmzx + hcancel
  have hrx : x < r := by
    rw [← sub_pos, heqr]
    exact neg_pos.mpr hxm
  have hrz : r < z := by
    rw [← sub_pos, heqz]
    exact hzm
  have hrmem : pieceMem s k r :=
    pieceMem_interval s k x z r hxmem hzmem (le_of_lt hrx) (le_of_lt hrz)
  have hr0 : h r = 0 := by
    have hrr := hmc r hrmem
    rw [hrr, hr]
    linear_combination -hxx - hcancel
  by_cases hex : ∃ r_ : ℝ, pieceMem s k r_ ∧ h r_ = 0
  · have hfk : reluRoot s h k = Classical.choose hex := dite_eq_left hex
    have hch := Classical.choose_spec hex
    have hqaff := hmc _ hch.1
    have e1 : m * Classical.choose hex + c = 0 := by
      rw [← hqaff]; exact hch.2
    have e2 : m * r + c = 0 := by
      rw [← hmc r hrmem]; exact hr0
    have hdiff : m * (Classical.choose hex - r) = 0 := by
      linear_combination e1 - e2
    have hchoose : Classical.choose hex = r :=
      sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hm0)
    have hrt : r ∈ s ∪ Finset.image (reluRoot s h)
        (Finset.range (s.card + 1)) := by
      rw [← hchoose, ← hfk]; exact hR
    exact absurd ⟨hrx, hrz⟩ (hmem r hrt)
  · exact (hex ⟨r, hrmem, hr0⟩).elim

/-- ReLU after a bounded-piece function: at most one new breakpoint per
affine piece (the unique root of a nonconstant affine piece). -/
theorem piecesLE_relu_comp (n : ℕ) (h : ℝ → ℝ) :
    PiecesLE n h → PiecesLE (2 * n) (fun x => (h x)⁺) := by
  classical
  rintro ⟨s, hsn, hs⟩
  refine ⟨s ∪ Finset.image (reluRoot s h) (Finset.range (s.card + 1)), ?_, ?_⟩
  · have hR : (Finset.image (reluRoot s h)
        (Finset.range (s.card + 1))).card ≤
        (Finset.range (s.card + 1)).card := Finset.card_image_le
    rw [Finset.card_range] at hR
    have hun := Finset.card_union_le s
      (Finset.image (reluRoot s h) (Finset.range (s.card + 1)))
    omega
  · intro x y z hxy hyz hmem
    change ((h y)⁺ - (h x)⁺) * (z - x) = ((h z)⁺ - (h x)⁺) * (y - x)
    have hsave : ∀ p ∈ s, ¬(x < p ∧ p < z) := fun p hp =>
      hmem p (Finset.mem_union_left _ hp)
    have heq := hs x y z hxy hyz hsave
    set k : ℕ := (s.filter (· < z)).card with hk
    have hsubAxz : s.filter (· < x) ⊆ s.filter (· < z) := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, lt_of_lt_of_le hq.2 (le_trans hxy hyz)⟩
    have hsubBxz : s.filter (· ≤ x) ⊆ s.filter (· ≤ z) := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, le_trans hq.2 (le_trans hxy hyz)⟩
    have hsubAzBx : s.filter (· < z) ⊆ s.filter (· ≤ x) := by
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      obtain ⟨hqs, hqz⟩ := hq
      refine ⟨hqs, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hsave q hqs ⟨hcon, hqz⟩
    have hxmem : pieceMem s k x :=
      ⟨by rw [hk]; exact Finset.card_le_card hsubAxz,
        by rw [hk]; exact Finset.card_le_card hsubAzBx⟩
    have hzmem : pieceMem s k z := ⟨by rw [hk],
      by rw [hk]; exact le_trans (Finset.card_le_card hsubAzBx) (Finset.card_le_card hsubBxz)⟩
    have hkle : k ≤ s.card := by
      rw [hk]
      exact Finset.card_le_card (Finset.filter_subset _ s)
    rcases eq_or_lt_of_le (le_trans hxy hyz) with hEq | hLt
    · have hyz' : y ≤ x := by
        have h2 := hyz
        rw [← hEq] at h2
        exact h2
      have hyx : y = x := le_antisymm hyz' hxy
      subst hEq
      subst hyx
      rfl
    · have hzxpos : 0 < z - x := sub_pos.mpr hLt
      obtain ⟨m, c, hmc⟩ := aff_of_pieceMem s h k x z hs hxmem hzmem hLt
      have hxx : h x = m * x + c := hmc x hxmem
      have hzz : h z = m * z + c := hmc z hzmem
      have hRmem : reluRoot s h k ∈ Finset.image (reluRoot s h)
          (Finset.range (s.card + 1)) :=
        Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      have hRsub : reluRoot s h k ∈ s ∪ Finset.image (reluRoot s h)
          (Finset.range (s.card + 1)) :=
        Finset.mem_union_right _ hRmem
      by_cases hnn : 0 ≤ h x ∧ 0 ≤ h z
      · obtain ⟨hx0, hz0⟩ := hnn
        have hmul : h y * (z - x) = (z - y) * h x + (y - x) * h z := by
          linear_combination heq
        have hnn2 : 0 ≤ h y * (z - x) := by
          rw [hmul]
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr hyz) hx0)
            (mul_nonneg (sub_nonneg.mpr hxy) hz0)
        have hy0 : 0 ≤ h y := nonneg_of_mul_nonneg_left hnn2 hzxpos
        rw [posPart_eq_self.mpr hx0, posPart_eq_self.mpr hy0,
          posPart_eq_self.mpr hz0]
        exact heq
      · by_cases hnp : h x ≤ 0 ∧ h z ≤ 0
        · obtain ⟨hx0, hz0⟩ := hnp
          have hmul : h y * (z - x) = (z - y) * h x + (y - x) * h z := by
            linear_combination heq
          have hnn2 : h y * (z - x) ≤ 0 := by
            rw [hmul]
            exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hyz) hx0)
              (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hz0)
          have hy0 : h y ≤ 0 := nonpos_of_mul_nonpos_left hnn2 hzxpos
          rw [posPart_eq_zero.mpr hx0, posPart_eq_zero.mpr hy0,
            posPart_eq_zero.mpr hz0]
          ring
        · push Not at hnn hnp
          have hnn' : h x < 0 ∨ h z < 0 := by
            by_cases h1 : 0 ≤ h x
            · exact Or.inr (hnn h1)
            · exact Or.inl (lt_of_not_ge h1)
          have hnp' : 0 < h x ∨ 0 < h z := by
            by_cases h1 : h x ≤ 0
            · exact Or.inr (hnp h1)
            · exact Or.inl (lt_of_not_ge h1)
          rcases hnn' with hnx | hnz <;> rcases hnp' with hpx | hpz
          · exact absurd (lt_trans hnx hpx) (lt_irrefl _)
          · have hm0 : m ≠ 0 := by
              intro hm
              have heqxz : h x = h z := by rw [hxx, hzz, hm]; ring
              rw [heqxz] at hnx
              exact absurd (lt_trans hpz hnx) (lt_irrefl _)
            have hmzx : m * (z - x) = h z - h x := by
              linear_combination hxx - hzz
            have hmpos : 0 < m := pos_of_mul_pos_left
              (by rw [hmzx]; exact sub_pos.mpr (lt_trans hnx hpz))
              (le_of_lt hzxpos)
            have hxm : h x / m < 0 := div_neg_of_neg_of_pos hnx hmpos
            have hzm : 0 < h z / m := div_pos hpz hmpos
            exact (reluRoot_mixed_contra s h k x z m c hmc hxmem hzmem
              hxx hmzx hm0 hxm hzm hRsub hmem).elim
          · have hm0 : m ≠ 0 := by
              intro hm
              have heqxz : h x = h z := by rw [hxx, hzz, hm]; ring
              rw [heqxz] at hpx
              exact absurd (lt_trans hpx hnz) (lt_irrefl _)
            have hmzx : m * (z - x) = h z - h x := by
              linear_combination hxx - hzz
            have hmneg : m < 0 := Left.neg_of_mul_neg_left
              (by rw [hmzx]; exact sub_neg.mpr (lt_trans hnz hpx))
              (le_of_lt hzxpos)
            have hxm : h x / m < 0 := div_neg_of_pos_of_neg hpx hmneg
            have hzm : 0 < h z / m := div_pos_of_neg_of_neg hnz hmneg
            exact (reluRoot_mixed_contra s h k x z m c hmc hxmem hzmem
              hxx hmzx hm0 hxm hzm hRsub hmem).elim
          · exact absurd (lt_trans hpz hnz) (lt_irrefl _)

/-- Per-node bound for positive widths: the output of node `j` after `i`
layers has at most `2 ^ i` times the product of widths over layers `1` to
`i - 1` pieces. Only the traversed layers are constrained, so widths after
layer `i` may be zero (finite-network encodings); positivity of the traversed
widths is still necessary (a zero traversed width collapses the product bound). -/
theorem node_piecesLE (d : ℕ → ℕ) (Nnet : Net d) (i : ℕ)
    (hN : IsReluNetUpTo d Nnet i) (hd0 : d 0 = 1) (hpos : ∀ j < i, 0 < d j)
    (j : Fin (d i)) :
    PiecesLE ((2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k)
      (fun x => (Nnet.forward i (inputVec d x)) j) := by
  revert j hpos hN
  induction i with
  | zero =>
    intro _ _ j
    have hIcc : Finset.Icc (1:ℕ) (0 - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    have hfun : (fun x => (Nnet.forward 0 (inputVec d x)) j) = id := by
      funext x
      simp only [Net.forward]
      exact inputVec_apply d x j
    rw [hIcc, Finset.prod_empty, pow_zero, mul_one, hfun]
    exact piecesLE_id
  | succ i ih =>
    intro hN hpos j
    obtain ⟨W, b, hWb⟩ := hN i (by omega)
    have h1 : ∀ x : ℝ, Nnet.forward (i + 1) (inputVec d x)
        = Nnet.layer i (Nnet.forward i (inputVec d x)) := by
      intro x
      simp only [Net.forward]
    have hfw : ∀ x : ℝ, (Nnet.forward (i + 1) (inputVec d x)) j
        = ((∑ k, W j k * (Nnet.forward i (inputVec d x)) k) + b j)⁺ := by
      intro x
      rw [h1 x]
      exact hWb _ j
    have hfun : (fun x => (Nnet.forward (i + 1) (inputVec d x)) j)
        = fun x => ((∑ k, W j k * (Nnet.forward i (inputVec d x)) k) + b j)⁺ := by
      funext x
      exact hfw x
    have hB1 : (1:ℕ) ≤ (2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k :=
      one_le_mul (Nat.one_le_pow i 2 (by norm_num))
        (Finset.one_le_prod (fun k hk => hpos k (by
          have h2 := Finset.mem_Icc.mp hk
          omega)))
    have hS1 : (1:ℕ) ≤ (d i) * ((2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k) :=
      one_le_mul (hpos i (by omega)) hB1
    have hsumconst :
        (∑ _k : Fin (d i), (2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k)
          = (d i) * ((2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]
    have hN' : IsReluNetUpTo d Nnet i := fun k hk => hN k (by omega)
    have hpos' : ∀ j < i, 0 < d j := fun j hj => hpos j (by omega)
    have hsum : PiecesLE
        (max (∑ _k : Fin (d i), (2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k) 1)
        (fun x => (∑ k, W j k * (Nnet.forward i (inputVec d x)) k) + b j) :=
      piecesLE_sum _ _ _ _ _ (fun k => ih hN' hpos' k)
    rw [hsumconst] at hsum
    have hmax : max ((d i) * ((2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k)) 1
        = (d i) * ((2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k) :=
      max_eq_left hS1
    rw [hmax] at hsum
    have hrelu := piecesLE_relu_comp _ _ hsum
    have hprod : ∏ k ∈ Finset.Icc 1 ((i + 1) - 1), d k
        = (∏ k ∈ Finset.Icc 1 (i - 1), d k) * d i := by
      have hsub : (i + 1 : ℕ) - 1 = i := by omega
      rw [hsub]
      by_cases hi : i = 0
      · subst hi
        have he1 : Finset.Icc (1:ℕ) 0 = ∅ := Finset.Icc_eq_empty (by omega)
        rw [he1, Finset.prod_empty, hd0, mul_one]
      · have h2 :=
          Finset.prod_Icc_succ_top (show 1 ≤ (i - 1) + 1 from by omega) d
        rw [show (i - 1) + 1 = i from by omega] at h2
        exact h2
    have hbound : 2 * ((d i) * ((2 ^ i) * ∏ k ∈ Finset.Icc 1 (i - 1), d k))
        ≤ (2 ^ (i + 1)) * ∏ k ∈ Finset.Icc 1 ((i + 1) - 1), d k := by
      rw [hprod, pow_succ]
      apply le_of_eq
      ring
    have hmono := piecesLE_mono _ _ _ hbound hrelu
    rw [hfun]
    exact hmono

/-- Arithmetic-geometric mean corollary: a product is bounded by the
`L`-th power of the mean, for `L` positive terms. -/
private theorem prod_le_mean_pow (ι : Type*) (s : Finset ι) (w : ι → ℝ) (L : ℕ)
    (hcard : s.card = L) (hL : 0 < L) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∏ i ∈ s, w i ≤ ((∑ i ∈ s, w i) / (L : ℝ)) ^ L := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hL)
  have hsum : ∑ i ∈ s, (fun _ => ((L : ℝ))⁻¹) i = 1 := by
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ hL0
  have hAM := Real.geom_mean_le_arith_mean_weighted s (fun _ => ((L : ℝ))⁻¹) w
    (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg L)) hsum hw
  have hterm : ∀ i ∈ s, (w i ^ ((L : ℝ))⁻¹) ^ L = w i := by
    intro i hi
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hw i hi), inv_mul_cancel₀ hL0,
      Real.rpow_one]
  have hA : (∏ i ∈ s, w i ^ ((L : ℝ))⁻¹) ^ L = ∏ i ∈ s, w i := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl hterm
  have hB : (∑ i ∈ s, ((L : ℝ))⁻¹ * w i) = (∑ i ∈ s, w i) / (L : ℝ) := by
    rw [← Finset.mul_sum, div_eq_inv_mul]
  have hnonneg : 0 ≤ ∏ i ∈ s, w i ^ ((L : ℝ))⁻¹ :=
    Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hw i hi) _)
  rw [← hA, ← hB]
  exact pow_le_pow_left₀ hnonneg hAM L

/-- Whole-network bound for positive widths, via the per-node bound and
the arithmetic-geometric mean inequality on the width product. Only the
traversed layers are constrained, so widths after layer `L` may be zero
(finite-network encodings); positivity of the traversed widths is still
necessary. -/
theorem net_piecesLE (d : ℕ → ℕ) (Nnet : Net d) (L : ℕ)
    (hN : IsReluNetUpTo d Nnet L) (hd0 : d 0 = 1) (hdL : d L = 1) (hL : 0 < L)
    (hpos : ∀ j < L, 0 < d j) :
    ∃ n : ℕ, PiecesLE n (fun x => (Nnet.forward L (inputVec d x)) ⟨0, by omega⟩) ∧
      (n : ℝ) ≤ (2 * ((∑ i ∈ Finset.Icc 1 L, d i) : ℝ) / (L : ℝ)) ^ L := by
  have hprod : ∏ k ∈ Finset.Icc 1 (L - 1), d k = ∏ k ∈ Finset.Icc 1 L, d k := by
    have h2 := Finset.prod_Icc_succ_top (show 1 ≤ (L - 1) + 1 from by omega) d
    rw [show (L - 1) + 1 = L from by omega] at h2
    rw [hdL, mul_one] at h2
    exact h2.symm
  have hcard : (Finset.Icc 1 L).card = L := by
    rw [Nat.card_Icc]
    omega
  have hAM : ∏ k ∈ Finset.Icc 1 L, ((d k : ℕ) : ℝ)
      ≤ ((∑ k ∈ Finset.Icc 1 L, ((d k : ℕ) : ℝ)) / (L : ℝ)) ^ L :=
    prod_le_mean_pow _ _ _ _ hcard hL (fun k _ => Nat.cast_nonneg _)
  refine ⟨(2 ^ L) * ∏ k ∈ Finset.Icc 1 (L - 1), d k,
    node_piecesLE d Nnet L hN hd0 hpos ⟨0, by omega⟩, ?_⟩
  rw [hprod]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, Nat.cast_ofNat]
  have hfact : ((2 * ∑ i ∈ Finset.Icc 1 L, ((d i : ℕ) : ℝ)) / (L : ℝ)) ^ L
      = 2 ^ L * (((∑ i ∈ Finset.Icc 1 L, ((d i : ℕ) : ℝ)) / (L : ℝ)) ^ L) := by
    rw [div_pow, mul_pow]
    ring
  rw [hfact]
  exact mul_le_mul_of_nonneg_left hAM (pow_nonneg (by norm_num) L)

end Cslib.MachineLearning.DepthSeparationPieces
