/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.TokenRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounded convergence of Dijkstra's token ring

For `n + 1` machines and `n + 2` colors, every execution reaches a constant configuration
within `2 * (n + 1) ^ 2` steps. In particular, it reaches the consecutive-color legal form of
J. Aspnes, *Notes on Theory of Distributed Systems*, Chapter 32, §32.2. This legal form is
closed under steps and implies exactly one privileged machine. No fairness is assumed: every
step must be an actual `Step`.

As in Aspnes's argument, a color missing initially can only occupy an initial segment of the
linear order starting at machine `0`, until the ring becomes constant. The potential charges a
disagreeing edge by its distance from the end, and charges each remaining increment of machine
`0` before the missing color by the number of machines. Each copy removes a disagreement and
can create one only at the next, cheaper edge. An increment can add at most the first edge's
charge, and it cannot wrap the modular distance before the ring has become constant.

The states with exactly one privilege allow two arbitrary distinct colors, not necessarily
consecutive ones. The consecutive-color condition is kept separate from `Legit`.
-/

namespace Cslib.Distributed.TokenRing

private lemma cast_eq_iff_of_le {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    (i : ZMod (n + 1)) = (j : ZMod (n + 1)) ↔ i = j := by
  constructor
  · intro h
    simpa only [ZMod.val_natCast_of_lt (Nat.lt_succ_of_le hi),
      ZMod.val_natCast_of_lt (Nat.lt_succ_of_le hj)] using congrArg ZMod.val h
  · rintro rfl
    rfl

private lemma cast_last (n : ℕ) : (n : ZMod (n + 1)) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  exact (Nat.cast_succ n).symm.trans (ZMod.natCast_self (n + 1))

private lemma val_last (n : ℕ) : (-1 : ZMod (n + 1)).val = n := by
  rw [← cast_last, ZMod.val_natCast_of_lt (Nat.lt_succ_self n)]

private lemma cast_succ_ne_zero {n k : ℕ} (hk : k < n) :
    ((k + 1 : ℕ) : ZMod (n + 1)) ≠ 0 := by
  intro h
  have := (cast_eq_iff_of_le (n := n) (i := k + 1) (j := 0) (by omega) (by omega)).mp h
  omega

private lemma privileged_succ {n : ℕ} {x : ZMod (n + 1) → ZMod (n + 2)} {k : ℕ}
    (hk : k < n) : privileged x (k + 1 : ℕ) ↔ x (k + 1 : ℕ) ≠ x k := by
  rw [privileged, ite_eq_right (cast_succ_ne_zero hk), Nat.cast_succ, add_sub_cancel_right]

private lemma chain_eq {α : Type*} {f : ℕ → α} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → f (k + 1) = f k) : f b = f a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    exact (h b hab (Nat.lt_succ_self b)).trans (ih fun k ha hk => h k ha (by omega))

/-- The consecutive-color legal form for a ring on `n + 1` machines with `n + 2` colors.
For some cut `j`, machines `0` through `j` have the color of machine `0`, and the remaining
machines have that color minus one modulo `n + 2`. The second block can be empty. -/
@[expose] public def PiecewiseLegal {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2)) : Prop :=
  ∃ j : ℕ, j ≤ n ∧ ∀ i, x i = if i.val ≤ j then x 0 else x 0 - 1

private lemma piecewiseLegal_of_constant {n : ℕ} {x : ZMod (n + 1) → ZMod (n + 2)}
    (h : ∀ i, x i = x 0) : PiecewiseLegal x :=
  ⟨n, le_rfl, fun i => by simpa only [ite_eq_left (Nat.le_of_lt_succ (ZMod.val_lt i))] using h i⟩

/-- On a ring of `n + 1` machines indexed `0` through `n` with `n + 2` colors, a configuration
has exactly one privileged machine if and only if there is a cut `j` with `0 ≤ j ≤ n` such
that machines `0` through `j` have the first machine's color and machines after `j` have the
last machine's color. -/
public theorem legit_iff_two_blocks {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2)) :
    Legit x ↔ ∃ j : ℕ, j ≤ n ∧ ∀ i, x i = if i.val ≤ j then x 0 else x (-1) := by
  classical
  constructor
  · rintro ⟨p, hp, huniq⟩
    have heq (k : ℕ) (hk : k < n) (hne : (↑(k + 1) : ZMod (n + 1)) ≠ p) :
        x (k + 1 : ℕ) = x k := by
      by_contra hd
      exact hne (huniq _ ((privileged_succ hk).mpr hd))
    by_cases hp0 : p = 0
    · subst p
      refine ⟨n, le_rfl, fun i => ?_⟩
      rw [ite_eq_left (Nat.le_of_lt_succ (ZMod.val_lt i)), ← ZMod.natCast_zmod_val i]
      exact chain_eq (f := fun k => x k) (Nat.zero_le i.val)
        (fun k _ hk => heq k (by have := ZMod.val_lt i; omega) (cast_succ_ne_zero (by
          have := ZMod.val_lt i
          omega)))
    · have hpval : p.val ≠ 0 := by simpa using hp0
      have hpn := ZMod.val_lt p
      refine ⟨p.val - 1, by omega, fun i => ?_⟩
      have hin := ZMod.val_lt i
      have ne_p (k : ℕ) (hk : k < n) (hne : k + 1 ≠ p.val) :
          (↑(k + 1) : ZMod (n + 1)) ≠ p := by
        rw [← ZMod.natCast_zmod_val p]
        exact fun h => hne ((cast_eq_iff_of_le (by omega) (by omega)).mp h)
      split_ifs with hi
      · rw [← ZMod.natCast_zmod_val i]
        exact chain_eq (f := fun k => x k) (Nat.zero_le i.val)
          (fun k _ hk => heq k (by omega) (ne_p k (by omega) (by omega)))
      · rw [← ZMod.natCast_zmod_val i, ← cast_last]
        exact (chain_eq (f := fun k => x k) (Nat.le_of_lt_succ hin)
          (fun k ha hk => heq k hk (ne_p k hk (by omega)))).symm
  · rintro ⟨j, hj, hform⟩
    obtain ⟨p, hp⟩ := exists_privileged x
    have nonzero (i : ZMod (n + 1)) (hi : i ≠ 0) (h : privileged x i) :
        i.val = j + 1 ∧ x 0 ≠ x (-1) := by
      have hi0 : i.val ≠ 0 := by simpa using hi
      have hin := ZMod.val_lt i
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hkn : k < n := by omega
      have hi' : i = (↑(k + 1) : ZMod (n + 1)) := by rw [← ZMod.natCast_zmod_val i, hk]
      have hdiff := (privileged_succ hkn).mp (hi' ▸ h)
      have hkval := ZMod.val_natCast_of_lt (n := n + 1) (a := k) (by omega)
      rw [← hi', hform i, hform (k : ZMod (n + 1)), hkval] at hdiff
      by_cases hleft : i.val ≤ j
      · exact (hdiff (by rw [ite_eq_left hleft, ite_eq_left (show k ≤ j by omega)])).elim
      · by_cases hright : k ≤ j
        · rw [ite_eq_right hleft, ite_eq_left hright] at hdiff
          exact ⟨by omega, Ne.symm hdiff⟩
        · exact (hdiff (by rw [ite_eq_right hleft, ite_eq_right hright])).elim
    refine ⟨p, hp, fun i hi => ?_⟩
    by_cases hp0 : p = 0
    · subst p
      by_contra hi0
      exact (nonzero i hi0 hi).2 (by simpa [privileged] using hp)
    · have hp' := nonzero p hp0 hp
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact hp'.2 (by simpa [privileged] using hi)
      have hval := (nonzero i hi0 hi).1.trans hp'.1.symm
      simpa only [ZMod.natCast_zmod_val] using congrArg (fun k : ℕ => (k : ZMod (n + 1))) hval

/-- On a ring of `n + 1` machines with `n + 2` colors, a configuration is in the consecutive-color
legal form if and only if exactly one machine is privileged and the last machine's color equals
either the first machine's color or that color minus one modulo `n + 2`.
Unique privilege alone does not impose this disjunction. -/
public theorem piecewiseLegal_iff {n : ℕ} {x : ZMod (n + 1) → ZMod (n + 2)} :
    PiecewiseLegal x ↔ Legit x ∧ (x (-1) = x 0 ∨ x (-1) = x 0 - 1) := by
  constructor
  · rintro ⟨j, hj, hform⟩
    have hlast := hform (-1)
    rw [val_last] at hlast
    by_cases he : n ≤ j
    · refine ⟨(legit_iff_two_blocks x).mpr ⟨j, hj, ?_⟩, Or.inl (by simpa [he] using hlast)⟩
      intro i
      have hi : i.val ≤ j := (Nat.le_of_lt_succ (ZMod.val_lt i)).trans he
      simpa only [ite_eq_left hi] using hform i
    · rw [ite_eq_right he] at hlast
      exact ⟨(legit_iff_two_blocks x).mpr ⟨j, hj, by simpa only [hlast] using hform⟩, Or.inr hlast⟩
  · rintro ⟨hlegit, hlast | hlast⟩
    · obtain ⟨j, _, hform⟩ := (legit_iff_two_blocks x).mp hlegit
      exact piecewiseLegal_of_constant fun i => by simpa [hlast] using hform i
    · obtain ⟨j, hj, hform⟩ := (legit_iff_two_blocks x).mp hlegit
      exact ⟨j, hj, by simpa only [hlast] using hform⟩

/-- On a ring of `n + 1` machines with `n + 2` colors, every actual central-daemon step from
the consecutive-color legal form leads to another configuration of that form. -/
public theorem piecewiseLegal_closed {n : ℕ} {x y : ZMod (n + 1) → ZMod (n + 2)}
    (hx : PiecewiseLegal x) (h : Step x y) : PiecewiseLegal y := by
  have hy := legit_closed (piecewiseLegal_iff.mp hx).1 h
  apply piecewiseLegal_iff.mpr
  refine ⟨hy, ?_⟩
  obtain ⟨i, hp, rfl⟩ := h
  by_cases hi : i = 0
  · subst i
    -- In the singleton ring the two endpoints are the same machine.
    by_cases hlast : (-1 : ZMod (n + 1)) = 0
    · exact Or.inl (congrArg _ hlast)
    · rw [privileged, ite_eq_left rfl] at hp
      right
      rw [moveVal, ite_eq_left rfl, Function.update_self, Function.update_of_ne hlast,
        add_sub_cancel_right, hp]
  · -- Copying preserves the two allowed colors and does not change the first machine.
    obtain ⟨j, _, hj⟩ := hx
    have hcolor (k : ZMod (n + 1)) : x k = x 0 ∨ x k = x 0 - 1 := by
      rw [hj k]
      split_ifs <;> simp
    rw [moveVal, ite_eq_right hi, Function.update_of_ne (Ne.symm hi)]
    by_cases hlast : (-1 : ZMod (n + 1)) = i
    · rw [hlast, Function.update_self]
      exact hcolor (i - 1)
    · rw [Function.update_of_ne hlast]
      exact hcolor (-1)

-- Edge `k` runs from `k` to `k + 1`. The wraparound term `k = n` has weight zero.
private def edge {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2)) (k : ℕ) : ℕ :=
  if x (k + 1 : ℕ) = x k then 0 else n - k

private def disagreement {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2)) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), edge x k

private lemma edge_le {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2)) (k : ℕ) :
    edge x k ≤ n - k := by
  unfold edge
  split_ifs <;> omega

private lemma disagreement_le {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2)) :
    disagreement x ≤ (n + 1) * n := by
  calc
    disagreement x ≤ ∑ _k ∈ Finset.range (n + 1), n :=
      Finset.sum_le_sum fun k _ => (edge_le x k).trans (Nat.sub_le ..)
    _ = (n + 1) * n := by simp

private lemma disagreement_update_zero_le {n : ℕ} (x : ZMod (n + 1) → ZMod (n + 2))
    (a : ZMod (n + 2)) : disagreement (Function.update x 0 a) ≤ disagreement x + n := by
  classical
  have h : ∀ k ∈ Finset.range (n + 1),
      edge (Function.update x 0 a) k ≤ edge x k + (if k = 0 then n else 0) := by
    intro k hk
    have hkn : k ≤ n := by simpa using hk
    by_cases he : k = n
    · subst k
      simp [edge]
    by_cases h0 : k = 0
    · subst k
      simpa using (edge_le (Function.update x 0 a) 0).trans (Nat.le_add_left n (edge x 0))
    have hk0 : (k : ZMod (n + 1)) ≠ 0 :=
      fun hh => h0 ((cast_eq_iff_of_le (j := 0) hkn (Nat.zero_le n)).mp hh)
    unfold edge
    rw [Function.update_of_ne hk0,
      Function.update_of_ne (cast_succ_ne_zero (show k < n by omega)), ite_eq_right h0, add_zero]
  simpa [disagreement, Finset.sum_add_distrib] using Finset.sum_le_sum h

private lemma disagreement_update_copy_lt {n k : ℕ} {x : ZMod (n + 1) → ZMod (n + 2)}
    (hk : k < n) (hd : x (k + 1 : ℕ) ≠ x k) :
    disagreement (Function.update x (k + 1 : ℕ) (x k)) < disagreement x := by
  classical
  let y := Function.update x (k + 1 : ℕ) (x k)
  have hy (j : ℕ) (hj : j ≤ n) (hne : j ≠ k + 1) : y j = x j :=
    Function.update_of_ne (fun h => hne ((cast_eq_iff_of_le hj (by omega)).mp h)) _ _
  have h : ∀ j ∈ Finset.range (n + 1),
      edge y j + (if j = k then n - k else 0) ≤
        edge x j + (if j = k + 1 then n - (k + 1) else 0) := by
    intro j hj
    have hjn : j ≤ n := by simpa using hj
    by_cases he : j = n
    · subst j
      simp [edge, ne_of_gt hk]
    by_cases hjk : j = k
    · subst j
      have hz : edge y k = 0 := by
        unfold edge
        rw [show y (k + 1 : ℕ) = x k from Function.update_self .., hy k (by omega) (by omega),
          ite_eq_left rfl]
      have hx : edge x k = n - k := by rw [edge, ite_eq_right hd]
      simp [hz, hx]
    by_cases hjs : j = k + 1
    · subst j
      exact (by simpa using (edge_le y (k + 1)).trans (Nat.le_add_left _ (edge x (k + 1))))
    have heq : edge y j = edge x j := by
      unfold edge
      rw [hy (j + 1) (by omega) (by omega), hy j hjn hjs]
    simp [heq, hjk, hjs]
  have hk' : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hks : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hs := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    ite_eq_left hk', ite_eq_left hks] at hs
  change disagreement y + (n - k) ≤ disagreement x + (n - (k + 1)) at hs
  change disagreement y < disagreement x
  omega

-- A color occupies an initial segment exactly when membership propagates backwards along
-- every non-wraparound edge. This formulation includes both the empty and the full segment.
private def MarkerPrefix {n : ℕ} (c : ZMod (n + 2)) (x : ZMod (n + 1) → ZMod (n + 2)) : Prop :=
  ∀ k : ℕ, k < n → x (k + 1 : ℕ) = c → x k = c

private lemma MarkerPrefix.constant_of_last {n : ℕ} {c : ZMod (n + 2)}
    {x : ZMod (n + 1) → ZMod (n + 2)} (h : MarkerPrefix c x) (hlast : x (-1) = c) :
    ∀ i, x i = c := by
  have aux (d : ℕ) (hd : d ≤ n) : x (n - d : ℕ) = c := by
    induction d with
    | zero => simpa only [Nat.sub_zero, cast_last] using hlast
    | succ d ih =>
      exact h (n - (d + 1)) (by omega) (by
        rw [show n - (d + 1) + 1 = n - d by omega]
        exact ih (by omega))
  intro i
  have hi := ZMod.val_lt i
  have he := aux (n - i.val) (by omega)
  rwa [show n - (n - i.val) = i.val by omega, ZMod.natCast_zmod_val] at he

private lemma MarkerPrefix.update_copy {n j : ℕ} {c : ZMod (n + 2)}
    {x : ZMod (n + 1) → ZMod (n + 2)} (h : MarkerPrefix c x) (hj : j < n) :
    MarkerPrefix c (Function.update x (j + 1 : ℕ) (x j)) := by
  let y := Function.update x (j + 1 : ℕ) (x j)
  have hy (i : ℕ) (hi : i ≤ n) (hne : i ≠ j + 1) : y i = x i :=
    Function.update_of_ne (fun he => hne ((cast_eq_iff_of_le hi (by omega)).mp he)) _ _
  intro k hk hc
  change y (k + 1 : ℕ) = c at hc
  change y k = c
  by_cases he : k = j
  · subst k
    rw [show y (j + 1 : ℕ) = x j from Function.update_self ..] at hc
    rwa [hy j (by omega) (by omega)]
  rw [hy (k + 1) (by omega) (by omega)] at hc
  have hkc := h k hk hc
  by_cases hkj : k = j + 1
  · subst k
    rw [show y (j + 1 : ℕ) = x j from Function.update_self ..]
    exact h j hj hkc
  · rwa [hy k (by omega) hkj]

private lemma MarkerPrefix.update_zero {n : ℕ} {c : ZMod (n + 2)}
    {x : ZMod (n + 1) → ZMod (n + 2)} (h : MarkerPrefix c x) (hx : x 0 ≠ c)
    (a : ZMod (n + 2)) : MarkerPrefix c (Function.update x 0 a) := by
  intro k hk hc
  rw [Function.update_of_ne (cast_succ_ne_zero hk)] at hc
  have hkc := h k hk hc
  by_cases h0 : k = 0
  · subst k
    exact (hx hkc).elim
  · have hk0 : (k : ZMod (n + 1)) ≠ 0 :=
      fun he => h0 ((cast_eq_iff_of_le (j := 0) (by omega) (by omega)).mp he)
    rwa [Function.update_of_ne hk0]

private def potential {n : ℕ} (c : ZMod (n + 2)) (x : ZMod (n + 1) → ZMod (n + 2)) : ℕ :=
  disagreement x + (n + 1) * (c - x 0).val

private lemma val_sub_add_one {n : ℕ} {c a : ZMod (n + 2)} (hne : a ≠ c) :
    (c - (a + 1)).val + 1 = (c - a).val := by
  have hpos : (c - a).val ≠ 0 := by simpa [sub_eq_zero] using Ne.symm hne
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hlt := ZMod.val_lt (c - a)
  have hcast : c - (a + 1) = (d : ZMod (n + 2)) := by
    calc
      c - (a + 1) = (c - a) - 1 := (sub_sub ..).symm
      _ = d := by rw [← ZMod.natCast_zmod_val (c - a), hd, Nat.cast_succ, add_sub_cancel_right]
  rw [hcast, ZMod.val_natCast_of_lt (by omega), hd]

private lemma potential_step {n : ℕ} {c : ZMod (n + 2)} {x y : ZMod (n + 1) → ZMod (n + 2)}
    (h : MarkerPrefix c x) (hx : ¬ ∀ i, x i = x 0) (hs : Step x y) :
    MarkerPrefix c y ∧ potential c y < potential c x := by
  obtain ⟨i, hp, rfl⟩ := hs
  by_cases hi : i = 0
  · subst i
    have hne : x 0 ≠ c := by
      intro he
      have hl : x (-1) = c := (show x 0 = x (-1) by simpa [privileged] using hp).symm.trans he
      exact hx fun j => (h.constant_of_last hl j).trans he.symm
    rw [moveVal, ite_eq_left rfl]
    refine ⟨h.update_zero hne _, ?_⟩
    have hu := disagreement_update_zero_le x (x 0 + 1)
    have hg := congrArg ((n + 1) * ·) (val_sub_add_one hne)
    simp only [Nat.mul_add, Nat.mul_one] at hg
    unfold potential
    rw [Function.update_self]
    omega
  · have hval : i.val ≠ 0 := by simpa using hi
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hval
    have hin := ZMod.val_lt i
    have hkn : k < n := by omega
    have hi' : i = (↑(k + 1) : ZMod (n + 1)) := by rw [← ZMod.natCast_zmod_val i, hk]
    have hd := (privileged_succ hkn).mp (hi' ▸ hp)
    rw [moveVal, ite_eq_right hi, hi']
    have hpred : (↑(k + 1) : ZMod (n + 1)) - 1 = ↑k := by
      rw [Nat.cast_succ, add_sub_cancel_right]
    rw [hpred]
    refine ⟨h.update_copy hkn, ?_⟩
    unfold potential
    rw [Function.update_of_ne (Ne.symm (cast_succ_ne_zero hkn))]
    exact Nat.add_lt_add_right (disagreement_update_copy_lt hkn hd) _

private lemma exists_constant_of_steps {n : ℕ}
    (run : ℕ → ZMod (n + 1) → ZMod (n + 2))
    (hstep : ∀ t < 2 * (n + 1) ^ 2, Step (run t) (run (t + 1))) :
    ∃ t ≤ 2 * (n + 1) ^ 2, ∀ i, run t i = run t 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ∀ i, run 0 i ≠ c := by
    by_contra! h
    have hcard := Fintype.card_le_of_surjective (run 0) h
    simp only [ZMod.card] at hcard
    omega
  by_contra hnone
  have hnonconst (t : ℕ) (ht : t ≤ 2 * (n + 1) ^ 2) : ¬ ∀ i, run t i = run t 0 :=
    fun h => hnone ⟨t, ht, h⟩
  have hbound (t : ℕ) (ht : t ≤ 2 * (n + 1) ^ 2) :
      MarkerPrefix c (run t) ∧ potential c (run t) + t ≤ potential c (run 0) := by
    induction t with
    | zero => exact ⟨fun k _ h => (hc _ h).elim, by simp⟩
    | succ t ih =>
      obtain ⟨hp, hb⟩ := ih (by omega)
      obtain ⟨hp', hlt⟩ := potential_step hp (hnonconst t (by omega)) (hstep t (by omega))
      exact ⟨hp', by omega⟩
  have hsmall : potential c (run 0) < 2 * (n + 1) ^ 2 := by
    have hg : (c - run 0 0).val ≤ n + 1 := Nat.le_of_lt_succ (ZMod.val_lt _)
    calc
      potential c (run 0) ≤ (n + 1) * n + (n + 1) * (n + 1) :=
        Nat.add_le_add (disagreement_le _) (Nat.mul_le_mul_left _ hg)
      _ < (n + 1) * (n + 1) + (n + 1) * (n + 1) :=
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) (by omega)) _
      _ = 2 * (n + 1) ^ 2 := by rw [pow_two, two_mul]
  have hfinal := (hbound _ le_rfl).2
  omega

/-- Dijkstra's token ring on `n + 1` machines with state space `ZMod (n + 2)` enters the
consecutive-color legal form within `2 * (n + 1) ^ 2` central-daemon steps. The proof finds a
constant configuration in this prefix. The sequence is unconstrained after the prefix; in
particular, no fairness assumption is needed. -/
public theorem exists_piecewiseLegal_of_steps {n : ℕ}
    (run : ℕ → ZMod (n + 1) → ZMod (n + 2))
    (hstep : ∀ t < 2 * (n + 1) ^ 2, Step (run t) (run (t + 1))) :
    ∃ t ≤ 2 * (n + 1) ^ 2, PiecewiseLegal (run t) := by
  obtain ⟨t, ht, hconst⟩ := exists_constant_of_steps run hstep
  exact ⟨t, ht, piecewiseLegal_of_constant hconst⟩

/-- Dijkstra's central-daemon token ring on `n + 1` machines with `n + 2` colors stabilizes in
the consecutive-color legal form: every prefix of `2 * (n + 1) ^ 2` actual steps visits that form
by the end of the prefix, and every actual step from a configuration of that form preserves it.
No fairness assumption is needed. -/
public theorem self_stabilizes_piecewiseLegal (n : ℕ) :
    (∀ run : ℕ → ZMod (n + 1) → ZMod (n + 2),
      (∀ t < 2 * (n + 1) ^ 2, Step (run t) (run (t + 1))) →
        ∃ t ≤ 2 * (n + 1) ^ 2, PiecewiseLegal (run t)) ∧
    (∀ {x y : ZMod (n + 1) → ZMod (n + 2)}, PiecewiseLegal x → Step x y → PiecewiseLegal y) :=
  ⟨exists_piecewiseLegal_of_steps, piecewiseLegal_closed⟩

/-- For any natural number `n`, let `run` be a sequence of configurations of Dijkstra's
central-daemon token ring on `n + 1` machines with `n + 2` colors. If the transition from
`run t` to `run (t + 1)` is an actual step for every `t < 2 * (n + 1) ^ 2`, then
`run (2 * (n + 1) ^ 2)` has exactly one privileged machine. -/
public theorem legit_at_quadratic_bound {n : ℕ}
    (run : ℕ → ZMod (n + 1) → ZMod (n + 2))
    (hstep : ∀ t < 2 * (n + 1) ^ 2, Step (run t) (run (t + 1))) :
    Legit (run (2 * (n + 1) ^ 2)) := by
  obtain ⟨t, ht, hlegal⟩ := exists_piecewiseLegal_of_steps run hstep
  have hlegit : Legit (run t) := (piecewiseLegal_iff.mp hlegal).1
  have propagate (u : ℕ) (htu : t ≤ u) (hu : u ≤ 2 * (n + 1) ^ 2) : Legit (run u) := by
    induction u, htu using Nat.le_induction with
    | base => exact hlegit
    | succ u htu ih => exact legit_closed (ih (by omega)) (hstep u (by omega))
  exact propagate _ ht le_rfl

end Cslib.Distributed.TokenRing
