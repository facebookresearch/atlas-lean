/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

/-!
# Endpoint counts of peakless-tieless parking functions

Reversal exchanges the two strict endpoint inequalities. Deleting the first entry
of a word with equal endpoints gives a word with first entry strictly below the last;
the inverse prepends another copy of the last entry.

## References

* Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
  Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
  Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, pp. 1–34,
  Remark 39 and Lemma 40.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- `w` has no ties. -/
local notation "NoTies" w:max => ∀ i j, j.val = i.val + 1 → w i ≠ w j

set_option quotPrecheck false in
/-- `w` has no peaks. -/
local notation "NoPeaks" w:max =>
  ∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (w i < w j ∧ w k < w j)

set_option quotPrecheck false in
/-- The peakless-tieless parking functions `PTPF_n`. -/
local notation "ptpfSet" n:max =>
  Finset.filter (fun f : Fin n → Fin n => IsParkingFunction n f ∧ (NoTies f) ∧ NoPeaks f)
    Finset.univ

set_option quotPrecheck false in
/-- The words in `PTPF_m` whose first and last entries satisfy `r`. -/
local notation "ptpfWithEnds" m:max r:max =>
  (ptpfSet m).filter (fun f => ∃ i j : Fin m, i.val = 0 ∧ j.val + 1 = m ∧ r (f i) (f j))

set_option quotPrecheck false in
/-- Number of `α ∈ PTPF_m` whose first and last entries satisfy `r`. -/
local notation "ptpfEnds" m:max r:max => (ptpfWithEnds m r).card

namespace PeaklessTielessEnds

variable {n : ℕ}

private lemma mem_ends {f : Fin (n + 1) → Fin (n + 1)} {r : Fin (n + 1) → Fin (n + 1) → Prop}
    [DecidableRel r] :
    f ∈ ptpfWithEnds (n + 1) r ↔
      (IsParkingFunction (n + 1) f ∧ (NoTies f) ∧ NoPeaks f) ∧ r (f 0) (f (Fin.last n)) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨0, Fin.last n, rfl, rfl, h⟩⟩
  rintro ⟨i, j, hi, hj, h⟩
  rwa [show i = 0 from Fin.ext hi, show j = Fin.last n from Fin.ext (by simp; omega)] at h

private lemma reverse_shape {m : ℕ} {f : Fin m → Fin m} (ht : NoTies f) (hp : NoPeaks f) :
    (NoTies (f ∘ Fin.rev)) ∧ NoPeaks (f ∘ Fin.rev) := by
  constructor
  · intro i j hij
    exact (ht j.rev i.rev (by simp only [Fin.val_rev]; omega)).symm
  · intro i j k hij hjk h
    exact hp k.rev j.rev i.rev (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega) ⟨h.2, h.1⟩

private lemma card_reverse :
    ptpfEnds (n + 1) (fun a b : Fin (n + 1) => b < a) =
      ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b) := by
  apply Finset.card_equiv (Fin.revPerm.arrowCongr (Equiv.refl (Fin (n + 1))))
  intro f
  change f ∈ ptpfWithEnds (n + 1) (fun a b => b < a) ↔
    (f ∘ Fin.rev) ∈ ptpfWithEnds (n + 1) (fun a b => a < b)
  simp only [mem_ends (r := fun a b => b < a), mem_ends (r := fun a b => a < b)]
  have hpark : IsParkingFunction (n + 1) f ↔ IsParkingFunction (n + 1) (f ∘ Fin.rev) := by
    simp only [isParkingFunction_iff_card_filter_le]
    have hcount (k : Fin (n + 1)) : (Finset.univ.filter (fun i => (f ∘ Fin.rev) i ≤ k)).card =
        (Finset.univ.filter (fun i => f i ≤ k)).card :=
      Finset.card_equiv Fin.revPerm (fun _ => by simp)
    simp only [hcount]
  simp only [Function.comp_apply, Fin.rev_zero, Fin.rev_last] at ⊢
  refine and_congr (and_congr hpark ?_) Iff.rfl
  constructor
  · exact fun ⟨ht, hp⟩ => reverse_shape ht hp
  · rintro ⟨ht, hp⟩
    simpa only [Function.comp_apply, Fin.rev_rev] using reverse_shape ht hp

-- A global maximum in the interior would either be a peak or tie one of its neighbors.
private lemma le_max_ends {f : Fin (n + 1) → Fin (n + 1)} (ht : NoTies f) (hp : NoPeaks f)
    (i : Fin (n + 1)) : f i ≤ max (f 0) (f (Fin.last n)) := by
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ f ⟨0, Finset.mem_univ _⟩
  refine (hmax i (Finset.mem_univ _)).trans ?_
  by_cases h0 : p = 0
  · rw [h0]
    exact le_max_left _ _
  by_cases hn : p = Fin.last n
  · rw [hn]
    exact le_max_right _ _
  have hp0 : p.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hpn : p.val ≠ n := fun h => hn (Fin.ext h)
  let l : Fin (n + 1) := ⟨p.val - 1, by omega⟩
  let r : Fin (n + 1) := ⟨p.val + 1, by omega⟩
  have hl : p.val = l.val + 1 := by dsimp [l]; omega
  exact (hp l p r hl rfl ⟨(hmax l (Finset.mem_univ _)).lt_of_ne (ht l p hl),
    (hmax r (Finset.mem_univ _)).lt_of_ne (ht p r rfl).symm⟩).elim

-- Prepending a maximum affects only thresholds at which all the old entries qualify.
private lemma parking_cons_castSucc_iff (f : Fin n → Fin n) (a : Fin n) (ha : ∀ i, f i ≤ a) :
    IsParkingFunction (n + 1) (Fin.cons a.castSucc fun i => (f i).castSucc) ↔
      IsParkingFunction n f := by
  let g : Fin (n + 1) → Fin (n + 1) := Fin.cons a.castSucc fun i => (f i).castSucc
  change IsParkingFunction (n + 1) g ↔ IsParkingFunction n f
  simp only [isParkingFunction_iff_card_filter_le]
  have hcount (k : Fin n) :
      (Finset.univ.filter (fun i => g i ≤ k.castSucc)).card =
        (Finset.univ.filter (fun i => f i ≤ k)).card + (if a ≤ k then 1 else 0) := by
    rw [Fin.card_filter_univ_succ']
    simp [g, Nat.add_comm]
  constructor
  · intro h k
    by_cases hk : a ≤ k
    · have hall (i : Fin n) : f i ≤ k := (ha i).trans hk
      simpa [hall] using Nat.succ_le_of_lt k.isLt
    · simpa only [hcount, ite_eq_right hk, Nat.add_zero, Fin.val_castSucc] using h k.castSucc
  · intro h k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [Fin.le_last]
    · rw [hcount]
      exact (h j).trans (Nat.le_add_right _ _)

private abbrev prependLast (f : Fin (n + 1) → Fin (n + 1)) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cons (f (Fin.last n)).castSucc fun i => (f i).castSucc

private lemma prependLast_mem {f : Fin (n + 1) → Fin (n + 1)}
    (hf : f ∈ ptpfWithEnds(n + 1)(fun a b => a < b)) :
    prependLast f ∈ ptpfWithEnds (n + 2) (fun a b => a = b) := by
  obtain ⟨⟨hpark, ht, hp⟩, hends⟩ := mem_ends.mp hf
  have hmax (i : Fin (n + 1)) : f i ≤ f (Fin.last n) := by
    simpa only [max_eq_right hends.le] using le_max_ends ht hp i
  have hstep : prependLast f (0 : Fin (n + 1)).succ < prependLast f 0 := by
    simpa [prependLast] using hends
  refine mem_ends.mpr ⟨⟨(parking_cons_castSucc_iff f _ hmax).mpr hpark, ?_, ?_⟩, ?_⟩
  · intro i j hij
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (show j ≠ 0 by
      intro h; subst j; simp at hij)
    refine Fin.cases ?_ (fun i => ?_) i hij
    · intro hj
      have hj0 : j = 0 := Fin.ext (by simpa using hj)
      subst j
      exact hstep.ne'
    · intro hij
      exact fun h => ht i j (by simpa using hij) (Fin.castSucc_injective _ h)
  · intro i j k hij hjk h
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (show j ≠ 0 by
      intro he; subst j; simp at hij)
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero (show k ≠ 0 by
      intro he; subst k; simp at hjk)
    refine Fin.cases ?_ (fun i => ?_) i hij h
    · intro hj h
      have hj0 : j = 0 := Fin.ext (by simpa using hj)
      subst j
      exact hstep.not_gt h.1
    · intro hij h
      exact hp i j k (by simpa using hij) (by simpa using hjk)
        (by simpa [prependLast] using h)
  · simp [prependLast, ← Fin.succ_last]

private lemma exists_prependLast {g : Fin (n + 2) → Fin (n + 2)}
    (hg : g ∈ ptpfWithEnds(n + 2)(fun a b => a = b)) :
    ∃ f ∈ ptpfWithEnds (n + 1) (fun a b => a < b), prependLast f = g := by
  obtain ⟨⟨hpark, ht, hp⟩, hends⟩ := mem_ends.mp hg
  have hmax (i : Fin (n + 2)) : g i ≤ g 0 := by
    simpa only [← hends, max_self] using le_max_ends ht hp i
  -- The largest preference available at length `n + 2` cannot occur twice.
  have hbound : g 0 < Fin.last (n + 1) := by
    refine lt_of_le_of_ne (Fin.le_last _) fun he => ?_
    have hc : 1 < (Finset.univ.filter (fun i => Fin.last (n + 1) ≤ g i)).card := by
      exact Finset.one_lt_card.mpr ⟨0, by simp [he], Fin.last (n + 1), by simp [← hends, he],
        by simp [Fin.ext_iff]⟩
    have h := hpark (Fin.last (n + 1))
    change (Finset.univ.filter (fun i => Fin.last (n + 1) ≤ g i)).card ≤ n + 2 - (n + 1) at h
    omega
  let f (i : Fin (n + 1)) : Fin (n + 1) :=
    ⟨(g i.succ).val, (hmax i.succ).trans_lt hbound⟩
  have heq : prependLast f = g := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change g (Fin.last n).succ = g 0
      simpa only [Fin.succ_last] using hends.symm
    · rfl
  refine ⟨f, mem_ends.mpr ⟨⟨?_, ?_, ?_⟩, ?_⟩, heq⟩
  · apply (parking_cons_castSucc_iff f (f (Fin.last n)) ?_).mp
    · rwa [← heq] at hpark
    · intro i
      change g i.succ ≤ g (Fin.last n).succ
      rw [Fin.succ_last, ← hends]
      exact hmax i.succ
  · intro i j hij he
    exact ht i.succ j.succ (by simp [hij]) (Fin.ext (congrArg (fun k : Fin (n + 1) => k.val) he))
  · intro i j k hij hjk h
    exact hp i.succ j.succ k.succ (by simp [hij]) (by simp [hjk]) h
  · change g (0 : Fin (n + 1)).succ < g (Fin.last n).succ
    rw [Fin.succ_last, ← hends]
    exact (hmax _).lt_of_ne (ht 0 (0 : Fin (n + 1)).succ rfl).symm

private lemma card_prependLast :
    ptpfEnds (n + 2) (fun a b : Fin (n + 2) => a = b) =
      ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b) := by
  symm
  refine Finset.card_bij (fun f _ => prependLast f) (fun _ => prependLast_mem) ?_ ?_
  · intro f _ g _ h
    funext i
    exact Fin.castSucc_injective _ (congrFun h i.succ)
  · intro g hg
    obtain ⟨f, hf, h⟩ := exists_prependLast hg
    exact ⟨f, hf, h⟩

end PeaklessTielessEnds

open PeaklessTielessEnds in
/-- **First and last entries of peakless-tieless parking functions.** A parking function
$(a_1, \dots, a_m)$ is peakless-tieless if $a_i \ne a_{i+1}$ for all $1 \le i \le m - 1$ and there
is no $i$ with $a_{i-1} < a_i > a_{i+1}$. Let $G_m$, $E_m$ and $L_m$ be the sets of
peakless-tieless parking functions of length $m$ with $a_1 > a_m$, $a_1 = a_m$ and $a_1 < a_m$,
respectively. Then $|E_{n+1}| = |L_n|$ for every $n \ge 1$, and $|G_{n+1}| = |L_{n+1}|$ for every
$n \ge 0$.

Source: Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton,
Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking
Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 40
(`jis-2024-24.8.6-lem-40`). -/
public theorem peakless_tieless_ends_card (n : ℕ) :
    (1 ≤ n → ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a = b) =
      ptpfEnds n (fun a b : Fin n => a < b)) ∧
    ptpfEnds (n + 1) (fun a b : Fin (n + 1) => b < a) =
      ptpfEnds (n + 1) (fun a b : Fin (n + 1) => a < b) := by
  refine ⟨?_, card_reverse⟩
  cases n with
  | zero => simp
  | succ n => exact fun _ => card_prependLast

end MetaMathlibExt
