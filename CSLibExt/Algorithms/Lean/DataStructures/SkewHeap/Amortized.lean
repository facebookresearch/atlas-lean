/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Amortized_Complexity/Skew_Heap_Analysis.thy` (Archive of Formal Proofs, entry `Amortized Complexity`, https://isa-afp.org/entries/Amortized_Complexity.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow

`thys/Amortized_Complexity/Priority_Queue_ops_merge.thy` (Archive of Formal Proofs, entry `Amortized Complexity`, https://isa-afp.org/entries/Amortized_Complexity.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Framework
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Skew-heap amortized analysis

The potential `Phi` (number of right-heavy nodes), the spine counts
`rh` / `lrh` / `rlh`, the exponential spine bounds `Gexp` / `Dexp`,
equation (22.1) (`Glog` / `Dlog`), the time functions `T_merge` /
`T_insert` / `T_delMin` (Appendix B.10), Lemma 22.1 (`amor_le`),
the logarithmic amortized bounds `a_merge` / `a_insert` /
`a_delMin`, the potential-method link to the framework
(`amortizedCost_*`, `potential_method_telescoping`, Ch. 19 §19.1),
the framework instantiation for skew heaps (`skewAmortized`), and
Exercise 22.1 (exactly `k` insertions producing a tree of height
exactly `k`, so the worst-case height is linear in the number of
insertions). `T_insert` / `T_delMin` are `Nat`-valued (Isabelle's
are `int`-valued coerced `T_merge`); the values are identical.
`size1Nat` is defined recursively (Isabelle's `size1`) with
`size1_size` as `size1Nat_eq_size_add_one`.

Source: the AFP entry `Amortized Complexity` (Tobias Nipkow,
2014; BSD), `thys/Amortized_Complexity/Skew_Heap_Analysis.thy`
(https://isa-afp.org/entries/Amortized_Complexity.html), for the
potential, the spine bounds, Lemma 22.1 and the amortized bounds;
the operation type is `Priority_Queue_ops_merge.thy` in the same
entry. Book: Ch. 22 section 22.2 (pp. 253-256), Appendix B.10
(p. 353) for the time functions, and Exercise 22.1 (p. 253). The
definitions and proofs are re-established in Lean; Isabelle-derived
names are kept for traceability.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace SkewHeap

open Cslib.Algorithms.Lean.Amortized


variable {α : Type u}


/- ## §22.2: potential, `rh`, `lrh`, `rlh` -/

/-- `rh l r`: 1 if the left subtree is smaller than the right, else 0. -/
def rh (l r : Tree α) : ℕ := if size l < size r then 1 else 0

theorem rh_cases (l r : Tree α) : rh l r = 1 ∨ rh l r = 0 := by unfold rh; split <;> simp

theorem rh_eq_one_iff (l r : Tree α) : rh l r = 1 ↔ size l < size r := by
  unfold rh; split <;> simp_all

theorem rh_eq_zero_iff (l r : Tree α) : rh l r = 0 ↔ ¬ size l < size r := by
  unfold rh; split <;> simp_all

theorem rh_le_one (l r : Tree α) : rh l r ≤ 1 := by unfold rh; split <;> omega

/-- `rh1` (Isabelle's name for the same statement). -/
theorem rh1 (l r : Tree α) : rh l r ≤ 1 := rh_le_one l r

/-- `lrh t` (Γ): number of right-heavy nodes on the left spine. -/
def lrh : Tree α → ℕ
  | .leaf => 0
  | .node l _ r => rh l r + lrh l

@[simp] theorem lrh_leaf : lrh (Tree.leaf : Tree α) = 0 := rfl
theorem lrh_node (l : Tree α) (a : α) (r : Tree α) : lrh (.node l a r) = rh l r + lrh l := rfl

/-- `rlh t` (Δ): number of not-right-heavy nodes on the right spine. -/
def rlh : Tree α → ℕ
  | .leaf => 0
  | .node l _ r => (1 - rh l r) + rlh r

@[simp] theorem rlh_leaf : rlh (Tree.leaf : Tree α) = 0 := rfl
theorem rlh_node (l : Tree α) (a : α) (r : Tree α) :
    rlh (.node l a r) = (1 - rh l r) + rlh r := rfl

/-- `Gexp`: `2 ^ lrh t ≤ size t + 1`. -/
theorem Gexp (t : Tree α) : (2 : ℕ) ^ lrh t ≤ size t + 1 := by
  induction t with
  | leaf => simp
  | node l a r ihl _ =>
    rw [lrh_node, size_node]
    rcases rh_cases l r with h | h
    · rw [h, pow_add, pow_one]
      have hlt : size l < size r := (rh_eq_one_iff l r).mp h
      have hih : (2 : ℕ) ^ lrh l ≤ size l + 1 := ihl
      calc 2 * (2 : ℕ) ^ lrh l ≤ 2 * (size l + 1) := Nat.mul_le_mul_left 2 hih
        _ ≤ size l + size r + 2 := by omega
    · rw [h]; simp; omega

/-- `Dexp`: `2 ^ rlh t ≤ size t + 1`. -/
theorem Dexp (t : Tree α) : (2 : ℕ) ^ rlh t ≤ size t + 1 := by
  induction t with
  | leaf => simp
  | node l a r _ ihr =>
    rw [rlh_node, size_node]
    rcases rh_cases l r with h | h
    · rw [h]; simp; omega
    · have hge : ¬ size l < size r := (rh_eq_zero_iff l r).mp h
      have heq : (1 - 0 + rlh r) = 1 + rlh r := by simp
      rw [h, heq, pow_add, pow_one]
      calc 2 * (2 : ℕ) ^ rlh r ≤ 2 * (size r + 1) := Nat.mul_le_mul_left 2 ihr
        _ ≤ size l + size r + 2 := by omega

/-- Isabelle's nat-valued `size1`: `size1 Leaf = 1`,
`size1 (Node l _ r) = size1 l + size1 r` (book Ch. 4 `|t|₁`).
Defined by the same recursion as in Isabelle, not as `size t + 1`. -/
def size1Nat : Tree α → ℕ
  | .leaf => 1
  | .node l _ r => size1Nat l + size1Nat r

@[simp] theorem size1Nat_leaf : size1Nat (Tree.leaf : Tree α) = 1 := rfl

theorem size1Nat_node (l : Tree α) (a : α) (r : Tree α) :
    size1Nat (.node l a r) = size1Nat l + size1Nat r := rfl

/-- `size1_size` (Isabelle): `size1 t = size t + 1`. -/
theorem size1Nat_eq_size_add_one (t : Tree α) : size1Nat t = size t + 1 := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    rw [size1Nat_node, size_node, ihl, ihr]; omega

theorem size1Nat_merge [LinearOrder α] (t1 t2 : Tree α) :
    size1Nat (merge t1 t2) = size1Nat t1 + size1Nat t2 - 1 := by
  rw [size1Nat_eq_size_add_one, size1Nat_eq_size_add_one,
    size1Nat_eq_size_add_one, size_merge]; omega

/-- `|t|₁ = |t| + 1`, as a real number (book `|t|₁`, Isabelle `size1 t`).
Isabelle's `size1` is nat-valued and is cast to `ℝ` at the logarithm;
`size1` here is that cast (`size1_cast`). -/
def size1 (t : Tree α) : ℝ := (size1Nat t : ℝ)

theorem size1_cast (t : Tree α) : size1 t = ((size1Nat t : ℕ) : ℝ) := rfl

theorem size1_eq (t : Tree α) : size1 t = (size t : ℝ) + 1 := by
  simp only [size1, size1Nat_eq_size_add_one, Nat.cast_add, Nat.cast_one]

/-- The logarithm argument in `a_merge`, in Isabelle's nat-cast form. -/
theorem size1_add_cast (t1 t2 : Tree α) :
    size1 t1 + size1 t2 = ((size1Nat t1 + size1Nat t2 : ℕ) : ℝ) := by
  simp only [size1, Nat.cast_add]

theorem size1_pos (t : Tree α) : 0 < size1 t := by rw [size1_eq]; positivity

/-- `Glog`: `lrh t ≤ log₂ |t|₁` — equation (22.1), first half. -/
theorem Glog (t : Tree α) : (lrh t : ℝ) ≤ Real.logb 2 (size1 t) := by
  have h := Gexp (α := α) t
  have hcast : (2 : ℝ) ^ lrh t ≤ size1 t := by
    rw [size1_eq]
    have h' : ((2 ^ lrh t : ℕ) : ℝ) ≤ ((size t + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; exact h'
  have hlog : Real.logb 2 ((2 : ℝ) ^ lrh t) = (lrh t : ℝ) := by
    rw [Real.logb_pow]; simp
  rw [← hlog]
  exact (Real.logb_le_logb (by norm_num) (by positivity) (size1_pos t)).mpr hcast

/-- `Dlog`: `rlh t ≤ log₂ |t|₁` — equation (22.1), second half. -/
theorem Dlog (t : Tree α) : (rlh t : ℝ) ≤ Real.logb 2 (size1 t) := by
  have h := Dexp (α := α) t
  have hcast : (2 : ℝ) ^ rlh t ≤ size1 t := by
    rw [size1_eq]
    have h' : ((2 ^ rlh t : ℕ) : ℝ) ≤ ((size t + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; exact h'
  have hlog : Real.logb 2 ((2 : ℝ) ^ rlh t) = (rlh t : ℝ) := by
    rw [Real.logb_pow]; simp
  rw [← hlog]
  exact (Real.logb_le_logb (by norm_num) (by positivity) (size1_pos t)).mpr hcast

/-- `plus_log_le_2log_plus`, in Isabelle's full generality:
`log_b x + log_b y ≤ 2 log_b (x + y)` for `b > 1`, `x, y > 0`. -/
theorem plus_log_le_2log_plus {b x y : ℝ} (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) :
    Real.logb b x + Real.logb b y ≤ 2 * Real.logb b (x + y) := by
  have h1 : Real.logb b x ≤ Real.logb b (x + y) := by
    apply (Real.logb_le_logb hb hx (by linarith)).mpr; linarith
  have h2 : Real.logb b y ≤ Real.logb b (x + y) := by
    apply (Real.logb_le_logb hb hy (by linarith)).mpr; linarith
  linarith

variable {α : Type u} [LinearOrder α]

/- ## Time function and potential -/

/-- `T_merge`: the recursive-equation count of `merge` (Appendix B.10).
It counts one per recursive equation of `merge` — one per call,
including the leaf cases — following the same recursive branches as
`merge` itself. It is a count of recursive equations, not wall-clock
runtime, and not the cost of reusing a persistent state. -/
def T_merge : Tree α → Tree α → ℕ
  | .leaf, _ => 1
  | _, .leaf => 1
  | .node l1 a1 r1, .node l2 a2 r2 =>
      (if a1 ≤ a2 then T_merge (.node l2 a2 r2) r1 else T_merge (.node l1 a1 r1) r2) + 1
termination_by t1 t2 => size t1 + size t2
decreasing_by (all_goals simp only [size_node]; omega)

theorem T_merge_leaf_left (t : Tree α) : T_merge .leaf t = 1 := by simp [T_merge]

theorem T_merge_leaf_right (t : Tree α) : T_merge t .leaf = 1 := by
  cases t with
  | leaf => simp [T_merge]
  | node l a r => simp [T_merge]

theorem T_merge_nneg (t1 t2 : Tree α) : 0 ≤ T_merge t1 t2 := Nat.zero_le _

/-- The `time_fun` equation for `merge` in the node–node case
(Appendix B.10). -/
theorem T_merge_node_node (l1 _a1 r1 l2 _a2 r2 : Tree α) (v1 v2 : α) :
    T_merge (.node l1 v1 r1) (.node l2 v2 r2) =
      (if v1 ≤ v2 then T_merge (.node l2 v2 r2) r1
       else T_merge (.node l1 v1 r1) r2) + 1 := by
  simp [T_merge]

/-- `Φ`: the potential, the number of right-heavy nodes. -/
def Phi : Tree α → ℤ
  | .leaf => 0
  | .node l _ r => Phi l + Phi r + (rh l r : ℤ)

omit [LinearOrder α] in
@[simp] theorem Phi_leaf : Phi (Tree.leaf : Tree α) = 0 := rfl
omit [LinearOrder α] in
theorem Phi_node (l : Tree α) (a : α) (r : Tree α) :
    Phi (.node l a r) = Phi l + Phi r + (rh l r : ℤ) := rfl

omit [LinearOrder α] in
/-- `Φ_nneg`: the potential is nonnegative. -/
theorem Phi_nneg (t : Tree α) : 0 ≤ Phi t := by
  induction t with
  | leaf => simp
  | node l a r ihl _ => rw [Phi_node]; positivity

/-- Non-vacuity: the potential is not always `0`. -/
theorem exists_phi_pos : ∃ t : Tree ℕ, Phi t ≠ 0 := by
  refine ⟨.node .leaf 0 (.node .leaf 0 .leaf), ?_⟩
  simp [Phi, rh, size]

omit [LinearOrder α] in
theorem lrh_node_int (l : Tree α) (a : α) (r : Tree α) :
    (lrh (.node l a r) : ℤ) = (rh l r : ℤ) + (lrh l : ℤ) := by
  rw [lrh_node]; push_cast; ring

omit [LinearOrder α] in
theorem rlh_node_int (l : Tree α) (a : α) (r : Tree α) :
    (rlh (.node l a r) : ℤ) = (1 - (rh l r : ℤ)) + (rlh r : ℤ) := by
  rw [rlh_node]
  have h : ((1 - rh l r + rlh r : ℕ) : ℤ) = ((1 - rh l r : ℕ) : ℤ) + (rlh r : ℤ) := by
    push_cast; ring
  rw [h]
  have h2 : ((1 - rh l r : ℕ) : ℤ) = 1 - (rh l r : ℤ) := by
    rw [Nat.cast_sub (rh_le_one l r)]; simp
  rw [h2]

/-- Lemma 22.1 (`amor_le`): the amortized complexity of `merge`,
in terms of `lrh` and `rlh`. -/
theorem amor_le (t1 t2 : Tree α) :
    (T_merge t1 t2 : ℤ) + Phi (merge t1 t2) - Phi t1 - Phi t2 ≤
      (lrh (merge t1 t2) : ℤ) + (rlh t1 : ℤ) + (rlh t2 : ℤ) + 1 := by
  induction t1, t2 using merge.induct with
  | case1 t =>
    rw [merge_leaf_left]
    have hT : T_merge (Tree.leaf : Tree α) t = 1 := T_merge_leaf_left t
    rw [hT]; simp [rlh_leaf]; omega
  | case2 t ht =>
    rw [merge_leaf_right]
    have hT : T_merge t (Tree.leaf : Tree α) = 1 := T_merge_leaf_right t
    rw [hT]; simp [rlh_leaf]; omega
  | case3 l1 a1 r1 l2 a2 r2 h ih =>
    have e_merge : merge (.node l1 a1 r1) (.node l2 a2 r2) =
        .node (merge (.node l2 a2 r2) r1) a1 l1 := by simp [merge, h]
    have e_T : T_merge (.node l1 a1 r1) (.node l2 a2 r2) =
        T_merge (.node l2 a2 r2) r1 + 1 := by simp [T_merge, h]
    have hPhiMerge : Phi (merge (.node l1 a1 r1) (.node l2 a2 r2)) =
        Phi (merge (.node l2 a2 r2) r1) + Phi l1 +
          (rh (merge (.node l2 a2 r2) r1) l1 : ℤ) := by rw [e_merge, Phi_node]
    have hPhi1 : Phi (.node l1 a1 r1) = Phi l1 + Phi r1 + (rh l1 r1 : ℤ) :=
      Phi_node l1 a1 r1
    have hLrh : (lrh (merge (.node l1 a1 r1) (.node l2 a2 r2)) : ℤ) =
        (rh (merge (.node l2 a2 r2) r1) l1 : ℤ) +
          (lrh (merge (.node l2 a2 r2) r1) : ℤ) := by rw [e_merge, lrh_node_int]
    have hRlh1 : (rlh (.node l1 a1 r1) : ℤ) = (1 - (rh l1 r1 : ℤ)) + (rlh r1 : ℤ) :=
      rlh_node_int l1 a1 r1
    rw [hPhiMerge, hPhi1, hLrh, hRlh1, e_T]
    push_cast
    have hrh1 : (rh l1 r1 : ℤ) ≤ 1 := by exact_mod_cast rh_le_one l1 r1
    have hrhm : (rh (merge (.node l2 a2 r2) r1) l1 : ℤ) ≤ 1 := by
      exact_mod_cast rh_le_one _ _
    omega
  | case4 l1 a1 r1 l2 a2 r2 h ih =>
    have e_merge : merge (.node l1 a1 r1) (.node l2 a2 r2) =
        .node (merge (.node l1 a1 r1) r2) a2 l2 := by simp [merge, h]
    have e_T : T_merge (.node l1 a1 r1) (.node l2 a2 r2) =
        T_merge (.node l1 a1 r1) r2 + 1 := by simp [T_merge, h]
    have hPhiMerge : Phi (merge (.node l1 a1 r1) (.node l2 a2 r2)) =
        Phi (merge (.node l1 a1 r1) r2) + Phi l2 +
          (rh (merge (.node l1 a1 r1) r2) l2 : ℤ) := by rw [e_merge, Phi_node]
    have hPhi2 : Phi (.node l2 a2 r2) = Phi l2 + Phi r2 + (rh l2 r2 : ℤ) :=
      Phi_node l2 a2 r2
    have hLrh : (lrh (merge (.node l1 a1 r1) (.node l2 a2 r2)) : ℤ) =
        (rh (merge (.node l1 a1 r1) r2) l2 : ℤ) +
          (lrh (merge (.node l1 a1 r1) r2) : ℤ) := by rw [e_merge, lrh_node_int]
    have hRlh2 : (rlh (.node l2 a2 r2) : ℤ) = (1 - (rh l2 r2 : ℤ)) + (rlh r2 : ℤ) :=
      rlh_node_int l2 a2 r2
    rw [hPhiMerge, hPhi2, hLrh, hRlh2, e_T]
    push_cast
    have hrh2 : (rh l2 r2 : ℤ) ≤ 1 := by exact_mod_cast rh_le_one l2 r2
    have hrhm : (rh (merge (.node l1 a1 r1) r2) l2 : ℤ) ≤ 1 := by
      exact_mod_cast rh_le_one _ _
    omega

/-- `amor_le_long`: Isabelle states Lemma 22.1 twice, once with the
detailed proof (`amor_le_long`) and once as `amor_le`. The two
statements are identical; the proof above is the detailed one, so
`amor_le_long` is that same proof. -/
theorem amor_le_long (t1 t2 : Tree α) :
    (T_merge t1 t2 : ℤ) + Phi (merge t1 t2) - Phi t1 - Phi t2 ≤
      (lrh (merge t1 t2) : ℤ) + (rlh t1 : ℤ) + (rlh t2 : ℤ) + 1 :=
  amor_le t1 t2

/-- The real-valued version of Lemma 22.1. -/
theorem amor_le_real (t1 t2 : Tree α) :
    (T_merge t1 t2 : ℝ) + (Phi (merge t1 t2) : ℝ) - (Phi t1 : ℝ) - (Phi t2 : ℝ) ≤
      (lrh (merge t1 t2) : ℝ) + (rlh t1 : ℝ) + (rlh t2 : ℝ) + 1 := by
  have h := amor_le t1 t2
  exact_mod_cast h

/-- The logarithmic amortized bound for `merge` (`a_merge`). The
bound sums the logarithmic spine bounds for the two inputs and the
output (`amor_le_real`); it assumes no worst-case logarithmic height.
`T_merge` is the recursive-equation count, as above.
Isabelle writes the logarithm as `log 2 ((size1 t1 + size1 t2 : ℕ) : ℝ)`;
`size1_add_cast` below states that this equals the real sum
`size1 t1 + size1 t2` used here. -/
theorem a_merge (t1 t2 : Tree α) :
    (T_merge t1 t2 : ℝ) + (Phi (merge t1 t2) : ℝ) - (Phi t1 : ℝ) - (Phi t2 : ℝ) ≤
      3 * Real.logb 2 (size1 t1 + size1 t2) + 1 := by
  have h1 := amor_le_real t1 t2
  have hG : (lrh (merge t1 t2) : ℝ) ≤ Real.logb 2 (size1 (merge t1 t2)) := Glog _
  have hD1 : (rlh t1 : ℝ) ≤ Real.logb 2 (size1 t1) := Dlog _
  have hD2 : (rlh t2 : ℝ) ≤ Real.logb 2 (size1 t2) := Dlog _
  have hsize : size1 (merge t1 t2) = size1 t1 + size1 t2 - 1 := by
    rw [size1_eq, size1_eq, size1_eq, size_merge]; push_cast; ring
  have hpos1 : 0 < size1 (merge t1 t2) := size1_pos _
  have hpos2 : 0 < size1 t1 + size1 t2 := by
    have h1' := size1_pos t1; have h2' := size1_pos t2; linarith
  have hlog1 : Real.logb 2 (size1 (merge t1 t2)) ≤ Real.logb 2 (size1 t1 + size1 t2) := by
    apply (Real.logb_le_logb (by norm_num) hpos1 hpos2).mpr
    rw [hsize]; linarith [size1_pos t1, size1_pos t2]
  have hplus : Real.logb 2 (size1 t1) + Real.logb 2 (size1 t2) ≤
      2 * Real.logb 2 (size1 t1 + size1 t2) :=
    plus_log_le_2log_plus (by norm_num) (size1_pos t1) (size1_pos t2)
  linarith

/-- `T_insert`: the recursive-equation count of `insert`, as the
`T_merge` count of merging a singleton tree (as in the analysis
file). -/
def T_insert (a : α) (t : Tree α) : ℕ := T_merge (.node .leaf a .leaf) t

/-- `T_delMin`: the recursive-equation count of `delMin` — `0` on
`Leaf`, else the `T_merge` count of merging the two children (as in
the analysis file). -/
def T_delMin : Tree α → ℕ
  | .leaf => 0
  | .node l _ r => T_merge l r

/-- The amortized bound for `insert` (`a_insert`). -/
theorem a_insert (a : α) (t : Tree α) :
    (T_insert a t : ℝ) + (Phi (insert a t) : ℝ) - (Phi t : ℝ) ≤
      3 * Real.logb 2 (size1 t + 2) + 1 := by
  have h := a_merge (.node .leaf a .leaf : Tree α) t
  have hPhi : Phi (.node .leaf a .leaf : Tree α) = 0 := by
    simp [Phi_node, Phi_leaf, rh]
  have hsize1 : size1 (.node .leaf a .leaf : Tree α) = 2 := by
    have hs : size (.node .leaf a .leaf : Tree α) = 1 := by simp [size_node, size_leaf]
    rw [size1_eq, hs]; norm_num
  have hins : insert a t = merge (.node .leaf a .leaf) t := rfl
  have hT : T_insert a t = T_merge (.node .leaf a .leaf) t := rfl
  rw [hPhi, hsize1] at h
  have h2 : (2 : ℝ) + size1 t = size1 t + 2 := by ring
  rw [h2] at h
  simp only [Int.cast_zero, sub_zero] at h
  rw [hins, hT]
  linarith

/-- The amortized bound for `delMin` (`a_delMin`). -/
theorem a_delMin (t : Tree α) :
    (T_delMin t : ℝ) + (Phi (delMin t) : ℝ) - (Phi t : ℝ) ≤
      3 * Real.logb 2 (size1 t + 2) + 1 := by
  cases t with
  | leaf =>
    have hgoal : (T_delMin (Tree.leaf : Tree α) : ℝ) +
        (Phi (delMin (Tree.leaf : Tree α)) : ℝ) - (Phi (Tree.leaf : Tree α) : ℝ) = 0 := by
      simp [T_delMin, delMin, Phi_leaf]
    have hsize : size1 (Tree.leaf : Tree α) = 1 := by rw [size1_eq]; simp [size_leaf]
    rw [hgoal, hsize]
    have hlog : 0 ≤ Real.logb 2 ((1 : ℝ) + 2) :=
      Real.logb_nonneg (by norm_num) (by norm_num)
    linarith
  | node l a r =>
    have h := a_merge l r
    have hT : T_delMin (.node l a r) = T_merge l r := rfl
    have hD : delMin (.node l a r) = merge l r := rfl
    have hsize : size1 (.node l a r) = size1 l + size1 r := by
      simp only [size1, size1Nat_node, Nat.cast_add]
    have hPhi : Phi (.node l a r) = Phi l + Phi r + (rh l r : ℤ) := Phi_node l a r
    rw [hT, hD, hPhi, hsize]
    have hpos : 0 < size1 l + size1 r := by
      have h1' := size1_pos l; have h2' := size1_pos r; linarith
    have hlog : Real.logb 2 (size1 l + size1 r) ≤
        Real.logb 2 ((size1 l + size1 r) + 2) := by
      apply (Real.logb_le_logb (by norm_num) hpos (by linarith)).mpr; linarith
    have hrh : (0 : ℝ) ≤ ((rh l r : ℤ) : ℝ) := by
      exact_mod_cast Nat.zero_le (rh l r)
    push_cast
    linarith

/-- `a_del_min` (Isabelle's spelling; same statement as `a_delMin`). -/
theorem a_del_min (t : Tree α) :
    (T_delMin t : ℝ) + (Phi (delMin t) : ℝ) - (Phi t : ℝ) ≤
      3 * Real.logb 2 (size1 t + 2) + 1 :=
  a_delMin t

/- ## Exercise 22.1 -/

/-- If `a` is ≤ every element of `t`, inserting `a` grows the height by exactly one. -/
theorem height_insert_min {a : α} {t : Tree α}
    (h : ∀ x ∈ toSet t, a ≤ x) : height (insert a t) = height t + 1 := by
  cases t with
  | leaf =>
    have e : insert a (Tree.leaf : Tree α) = .node .leaf a .leaf := by
      simp [insert, merge_leaf_right]
    rw [e]; simp
  | node l b r =>
    have hab : a ≤ b := h b (by simp [toSet_node])
    have e : insert a (.node l b r) = .node (.node l b r) a .leaf := by
      simp [insert, merge, hab, merge_leaf_right]
    rw [e]
    simp [height_node, height_leaf]

/-- `rangeTree m k`: the tree obtained by inserting `m, m+1, …, m+k-1`
from the rightmost end (so each insertion is a new minimum). -/
def rangeTree : ℕ → ℕ → Tree ℕ
  | _, 0 => .leaf
  | m, k + 1 => insert m (rangeTree (m + 1) k)

theorem toSet_rangeTree_ge (m k : ℕ) (x : ℕ) (hx : x ∈ toSet (rangeTree m k)) :
    m ≤ x := by
  induction k generalizing m with
  | zero => simp [rangeTree] at hx
  | succ k ih =>
    have e : rangeTree m (k + 1) = insert m (rangeTree (m + 1) k) := rfl
    rw [e, toSet_insert] at hx
    rcases hx with hx | hx
    · simp at hx; omega
    · have := ih (m + 1) hx; omega

theorem height_rangeTree (m k : ℕ) : height (rangeTree m k) = k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    have e : rangeTree m (k + 1) = insert m (rangeTree (m + 1) k) := rfl
    rw [e, height_insert_min (t := rangeTree (m + 1) k) (a := m)]
    · rw [ih (m + 1)]
    · intro x hx
      have := toSet_rangeTree_ge (m + 1) k x hx; omega

theorem foldr_insert_range' (m k : ℕ) :
    List.foldr (fun a t => insert a t) .leaf (List.range' m k) = rangeTree m k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    have e : List.range' m (k + 1) = m :: List.range' (m + 1) k := rfl
    rw [e]
    simp only [List.foldr_cons]
    rw [ih (m + 1)]
    rfl

/-- Exercise 22.1, in `foldr` form: exactly `k` insertions (the list
is written in increasing order, but `foldr` inserts its rightmost
element first) produce a tree of height exactly `k`. -/
theorem exercise_22_1_foldr (k : ℕ) :
    ∃ ns : List ℕ,
      ns.length = k ∧
        height (List.foldr (fun a t => insert a t) .leaf ns) = k := by
  refine ⟨List.range' 0 k, ?_, ?_⟩
  · simp
  · rw [foldr_insert_range', height_rangeTree]

/-- Exercise 22.1, in the book's "insertion one by one" form: exactly
`k` insertions, in temporal order, folded left, so the list is
decreasing: `k-1, k-2, …, 0`, each a new minimum, and the resulting
tree has height exactly `k`. -/
theorem exercise_22_1 (k : ℕ) :
    ∃ ns : List ℕ,
      ns.length = k ∧
        height (List.foldl (fun t a => insert a t) .leaf ns) = k := by
  obtain ⟨ns, hlen, hns⟩ := exercise_22_1_foldr k
  exact ⟨ns.reverse, by rw [List.length_reverse, hlen],
    by rw [List.foldl_reverse, hns]⟩

/- ## Instantiation of the framework for skew heaps -/

/-- The operation type (`'a op` in `Priority_Queue_ops_merge.thy`). -/
inductive PQOp (α : Type u) where
  | empty : PQOp α
  | insert : α → PQOp α
  | delMin : PQOp α
  | merge : PQOp α

/-- `arity`: `Empty` 0, `Insert`/`Del_min` 1, `Merge` 2. -/
def pqArity : PQOp α → ℕ
  | .empty => 0
  | .insert _ => 1
  | .delMin => 1
  | .merge => 2

/-- `exec` for skew heaps. Isabelle's `fun` equations cover only the
arity-matching cases (`Empty` with `[]`, `Insert`/`Del_min` with one
element, `Merge` with two); Lean requires a total function, so the
remaining cases return `.leaf`. No lemma uses those cases: the
framework only calls `exec` on `wf` histories, whose argument lists
have exactly the arity length, and `U_bound` closes mismatched-length
cases by the arity hypothesis, not by the fallback value. -/
def skewExec : PQOp α → List (Tree α) → Tree α
  | .empty, _ => .leaf
  | .insert a, [t] => insert a t
  | .delMin, [t] => delMin t
  | .merge, [t1, t2] => merge t1 t2
  | _, _ => .leaf

/-- `cost` for skew heaps. Same totalisation remark as for `skewExec`:
Isabelle's equations cover only arity-matching lists; the fallback
is `0`, and it is never used on a `wf` history. `Del_min` cost is
written as `T_delMin t + 1`, which equals Isabelle's case split
(`Leaf ↦ 1`, `Node ↦ T_merge + 1`). -/
def skewCost : PQOp α → List (Tree α) → ℕ
  | .empty, _ => 1
  | .insert a, [t] => T_merge (.node .leaf a .leaf) t + 1
  | .delMin, [t] => T_delMin t + 1
  | .merge, [t1, t2] => T_merge t1 t2
  | _, _ => 0

/-- `U` for skew heaps: the amortized bounds. Same totalisation remark
as for `skewExec`: the fallback is `0`, never used on a `wf` history. -/
noncomputable def skewU : PQOp α → List (Tree α) → ℝ
  | .empty, _ => 1
  | .insert _, [t] => 3 * Real.logb 2 (size1 t + 2) + 2
  | .delMin, [t] => 3 * Real.logb 2 (size1 t + 2) + 2
  | .merge, [t1, t2] => 3 * Real.logb 2 (size1 t1 + size1 t2) + 1
  | _, _ => 0

theorem skewExec_empty : skewExec (PQOp.empty : PQOp α) [] = .leaf := by simp [skewExec]

theorem skewExec_insert (a : α) (t : Tree α) :
    skewExec (.insert a) [t] = insert a t := by simp [skewExec]

theorem skewExec_delMin (t : Tree α) : skewExec .delMin [t] = delMin t := by simp [skewExec]

theorem skewExec_merge (t1 t2 : Tree α) :
    skewExec .merge [t1, t2] = merge t1 t2 := by simp [skewExec]

theorem skewCost_empty : skewCost (PQOp.empty : PQOp α) [] = 1 := by simp [skewCost]

theorem skewCost_insert (a : α) (t : Tree α) :
    skewCost (.insert a) [t] = T_merge (.node .leaf a .leaf) t + 1 := by simp [skewCost]

theorem skewCost_delMin_leaf :
    skewCost (PQOp.delMin : PQOp α) [Tree.leaf] = 1 := by
  simp [skewCost, T_delMin]

theorem skewCost_delMin_node (l : Tree α) (a : α) (r : Tree α) :
    skewCost .delMin [.node l a r] = T_delMin (.node l a r) + 1 := by
  simp [skewCost]

theorem skewCost_merge (t1 t2 : Tree α) :
    skewCost .merge [t1, t2] = T_merge t1 t2 := by simp [skewCost]

omit [LinearOrder α] in
theorem skewU_empty : skewU (PQOp.empty : PQOp α) [] = 1 := by simp [skewU]

omit [LinearOrder α] in
theorem skewU_insert (a : α) (t : Tree α) :
    skewU (.insert a) [t] = 3 * Real.logb 2 (size1 t + 2) + 2 := by simp [skewU]

omit [LinearOrder α] in
theorem skewU_delMin (t : Tree α) :
    skewU .delMin [t] = 3 * Real.logb 2 (size1 t + 2) + 2 := by simp [skewU]

omit [LinearOrder α] in
theorem skewU_merge (t1 t2 : Tree α) :
    skewU .merge [t1, t2] = 3 * Real.logb 2 (size1 t1 + size1 t2) + 1 := by simp [skewU]

/-- The amortized-framework instance for skew heaps: the
`interpretation Amortized` at the end of `Skew_Heap_Analysis.thy`. -/
noncomputable def skewAmortized : AmortizedData (PQOp α) (Tree α) where
  arity := pqArity
  exec := skewExec
  inv := fun _ => True
  cost := skewCost
  Phi := fun t => (Phi t : ℝ)
  U := skewU
  inv_exec := by intro f ss _ _; trivial
  ppos := by
    intro s _
    have h := Phi_nneg s
    exact_mod_cast h
  U_bound := by
    intro f ss _ hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [skewExec_empty, skewCost_empty, skewU_empty]
        simp [Phi_leaf]
      | cons s ss => simp [pqArity] at hlen
    | insert a =>
      cases ss with
      | nil => simp [pqArity] at hlen
      | cons t ss =>
        cases ss with
        | nil =>
          rw [skewExec_insert, skewCost_insert, skewU_insert]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have h := a_insert a t
          have hT : T_insert a t = T_merge (.node .leaf a .leaf) t := rfl
          have hins : insert a t = merge (.node .leaf a .leaf) t := rfl
          rw [hT] at h
          have hcost : ((T_merge (.node .leaf a .leaf) t + 1 : ℕ) : ℝ) =
              (T_merge (.node .leaf a .leaf) t : ℝ) + 1 := by push_cast; ring
          rw [hcost]
          linarith
        | cons _ _ => simp [pqArity] at hlen
    | delMin =>
      cases ss with
      | nil => simp [pqArity] at hlen
      | cons t ss =>
        cases ss with
        | nil =>
          rw [skewExec_delMin, skewU_delMin]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          cases t with
          | leaf =>
            rw [skewCost_delMin_leaf]
            simp [Phi_leaf, delMin, size1, size1Nat]
            have hlog : 0 ≤ Real.logb 2 ((1 : ℝ) + 2) :=
              Real.logb_nonneg (by norm_num) (by norm_num)
            linarith
          | node l a r =>
            rw [skewCost_delMin_node]
            have h := a_delMin (.node l a r)
            have hcost : ((T_delMin (.node l a r) + 1 : ℕ) : ℝ) =
                (T_delMin (.node l a r) : ℝ) + 1 := by push_cast; ring
            rw [hcost]
            linarith
        | cons _ _ => simp [pqArity] at hlen
    | merge =>
      cases ss with
      | nil => simp [pqArity] at hlen
      | cons t1 ss =>
        cases ss with
        | nil => simp [pqArity] at hlen
        | cons t2 ss =>
          cases ss with
          | nil =>
            rw [skewExec_merge, skewCost_merge, skewU_merge]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
            have h := a_merge t1 t2
            linarith
          | cons _ _ => simp [pqArity] at hlen

/-- Total cost of a skew-heap operation history is bounded by the
total `U` bound — the framework's `t_sum_le_U_sum`, specialised. -/
theorem skew_t_sum_le_U_sum {ot : RoseTree (PQOp α)} (hw : wf skewAmortized ot) :
    cost_sum skewAmortized ot ≤ U_sum skewAmortized ot :=
  t_sum_le_U_sum skewAmortized hw

/- ## The potential method (book Ch. 19, §19.1) -/

/-- Ch. 19, equation (19.1): the amortized running time of a
one-argument operation is `A_f s = T_f s + Φ (f s) - Φ s`. For a
two-argument operation (e.g. `merge`), the analogue given in Ch. 19
is `A_g s₁ s₂ = T_g s₁ s₂ + Φ (g s₁ s₂) - (Φ s₁ + Φ s₂)`.
The framework's `acost` is exactly this definition, with `cost`
in place of `T` (the framework's `cost` for skew heaps is `T_merge`
for `merge`, and `T_insert + 1` / `T_delMin + 1` for insert /
delMin — the `+1` is Isabelle's framework `cost`, see the comment on
`skewCost`; `a_insert` / `a_delMin` are stated with `T_insert` /
`T_delMin` as in the analysis file). The three lemmas below state
`acost` for the skew operations in the form (19.1). -/
theorem amortizedCost_merge (t1 t2 : Tree α) :
    acost skewAmortized (.merge : PQOp α) [t1, t2] =
      (T_merge t1 t2 : ℝ) + (Phi (merge t1 t2) : ℝ) -
        ((Phi t1 : ℝ) + (Phi t2 : ℝ)) := by
  show ((skewCost (.merge : PQOp α) [t1, t2] : ℕ) : ℝ) +
      (Phi (skewExec (.merge : PQOp α) [t1, t2]) : ℝ) -
        ((Phi t1 : ℝ) + ((Phi t2 : ℝ) + 0)) = _
  rw [skewCost_merge, skewExec_merge]
  ring

theorem amortizedCost_insert (a : α) (t : Tree α) :
    acost skewAmortized (.insert a) [t] =
      ((T_insert a t : ℝ) + 1) + (Phi (insert a t) : ℝ) - (Phi t : ℝ) := by
  show ((skewCost (.insert a) [t] : ℕ) : ℝ) +
      (Phi (skewExec (.insert a) [t]) : ℝ) - ((Phi t : ℝ) + 0) = _
  rw [skewCost_insert, skewExec_insert]
  have hT : T_insert a t = T_merge (.node .leaf a .leaf) t := rfl
  rw [hT]
  push_cast
  ring

theorem amortizedCost_delMin (t : Tree α) :
    acost skewAmortized (.delMin : PQOp α) [t] =
      ((T_delMin t : ℝ) + 1) + (Phi (delMin t) : ℝ) - (Phi t : ℝ) := by
  cases t with
  | leaf =>
    show ((skewCost (.delMin : PQOp α) [Tree.leaf] : ℕ) : ℝ) +
        (Phi (skewExec (.delMin : PQOp α) [Tree.leaf]) : ℝ) -
          ((Phi (Tree.leaf : Tree α) : ℝ) + 0) = _
    rw [skewCost_delMin_leaf, skewExec_delMin]
    simp [delMin, Phi_leaf, T_delMin]
  | node l a r =>
    show ((skewCost (.delMin : PQOp α) [.node l a r] : ℕ) : ℝ) +
        (Phi (skewExec (.delMin : PQOp α) [.node l a r]) : ℝ) -
          ((Phi (.node l a r) : ℝ) + 0) = _
    rw [skewCost_delMin_node, skewExec_delMin, delMin_node]
    push_cast
    ring

/-- Ch. 19's telescoping sum: for a sequence of operations
`s₀, …, sₙ` with `s_{i+1} = f s_i`,
`∑ A_f s_i = ∑ T_f s_i + Φ sₙ - Φ s₀`. In the framework this is
`t_sum_a_sum`, for operation *histories* (rose trees) rather than
just sequences; the initial potential `Φ s₀` is `Φ Leaf = 0`,
because a well-formed history's leaves are `Empty` operations whose
state is `Leaf`. -/
theorem potential_method_telescoping {ot : RoseTree (PQOp α)}
    (hw : wf skewAmortized ot) :
    cost_sum skewAmortized ot =
      acost_sum skewAmortized ot - (Phi (state skewAmortized ot) : ℝ) :=
  t_sum_a_sum skewAmortized hw

/-- Ch. 19's conclusion for a history: because `Φ ≥ 0`, the total
actual cost is at most the total amortized cost. -/
theorem potential_method_le {ot : RoseTree (PQOp α)}
    (hw : wf skewAmortized ot) :
    cost_sum skewAmortized ot ≤ acost_sum skewAmortized ot :=
  t_sum_le_a_sum skewAmortized hw


end SkewHeap

end Cslib.Algorithms.Lean
