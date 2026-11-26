/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.Combinatorics.Enumerative.LuckyCars
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Fin
import MathlibExt.Combinatorics.Enumerative.LuckyParkingFunctions

/-!
# Lucky cars in weakly increasing parking functions

The first `k` cars occupy exactly the first `k` spots. A lucky car is therefore a fixed point
of the preference map, and splitting immediately before that fixed point gives the two
Catalan factors.

## References

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer Sequences 29 (2026),
  Article 26.1.1, pp. 1–18, Section 4.1 and Lemma 18.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt

private theorem isParkingFunction_iff_le_id_of_monotone {n : ℕ} {f : Fin n → Fin n}
    (hf : Monotone f) : IsParkingFunction n f ↔ ∀ k, f k ≤ k := by
  rw [isParkingFunction_iff_card_filter_le]
  constructor
  · intro h k
    by_contra hk
    -- If the preference at `k` is too large, only the `k` earlier cars can prefer at most `k`.
    have hsub : Finset.univ.filter (fun j => f j ≤ k) ⊆ Finset.Iio k := by
      intro j hj
      exact Finset.mem_Iio.mpr (lt_of_not_ge fun hkj =>
        hk ((hf hkj).trans (Finset.mem_filter.mp hj).2))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    exact (Nat.not_succ_le_self k.val) ((h k).trans hc)
  · intro h k
    rw [← Fin.card_Iic k]
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h j).trans (Finset.mem_Iic.mp hj)⟩

private theorem nextFreeSpot_eq_of_occupied_prefix {n : ℕ} {occ : Finset (Fin n)}
    {a s : Fin n} (ha : a ≤ s) (hocc : ∀ t, t ∈ occ ↔ t < s) :
    nextFreeSpot occ a = s := by
  let free := Finset.univ.filter (fun t : Fin n => a ≤ t ∧ t ∉ occ)
  have hs : s ∈ free := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, fun h =>
    (lt_irrefl s) ((hocc s).mp h)⟩
  have hfree : free.Nonempty := ⟨s, hs⟩
  change (if h : free.Nonempty then free.min' h else a) = s
  rw [dite_eq_left hfree]
  refine le_antisymm (Finset.min'_le _ _ hs) (le_of_not_gt fun hlt => ?_)
  exact (Finset.mem_filter.mp (Finset.min'_mem free hfree)).2.2 ((hocc _).mpr hlt)

private theorem parkSpotsFrom_ofFn_eq {n m k : ℕ} (hkm : k + m ≤ n)
    (g : Fin m → Fin n) (hg : ∀ i, (g i).val ≤ k + i.val)
    (occ : Finset (Fin n)) (hocc : ∀ s, s ∈ occ ↔ s.val < k) :
    parkSpotsFrom (List.ofFn g) occ =
      List.ofFn (fun i : Fin m => (⟨k + i.val, by omega⟩ : Fin n)) := by
  induction m generalizing k occ with
  | zero => simp [parkSpotsFrom]
  | succ m ih =>
    let s : Fin n := ⟨k, by omega⟩
    have hs : nextFreeSpot occ (g 0) = s :=
      nextFreeSpot_eq_of_occupied_prefix (by simpa [s, Fin.le_def] using hg 0) hocc
    rw [List.ofFn_succ, List.ofFn_succ, parkSpotsFrom, hs]
    refine congrArg (s :: ·) ?_
    have hg' (i : Fin m) : (g i.succ).val ≤ k + 1 + i.val := by
      simpa only [Fin.val_succ, Nat.add_assoc, Nat.one_add] using hg i.succ
    have hocc' (t : Fin n) : t ∈ insert s occ ↔ t.val < k + 1 := by
      rw [Finset.mem_insert, hocc t, Fin.ext_iff]
      change t.val = k ∨ t.val < k ↔ t.val < k + 1
      omega
    simpa only [Fin.val_succ, Nat.add_assoc, Nat.one_add] using
      ih (k := k + 1) (by omega) (fun i => g i.succ) hg' (insert s occ) hocc'

private theorem parkSpots_eq_self_of_le {n : ℕ} {f : Fin n → Fin n}
    (hf : ∀ i, f i ≤ i) (i : Fin n) : parkSpots f i = i := by
  have h : parkSpotsFrom (List.ofFn f) ∅ = List.ofFn (fun k : Fin n => k) := by
    simpa [Fin.eta] using parkSpotsFrom_ofFn_eq (k := 0) (Nat.zero_add n).le f
      (fun k => by simpa using Fin.le_def.mp (hf k)) ∅ (by simp)
  rw [parkSpots, h]
  rw [← List.getElem_eq_getD (h := by simp) i, List.getElem_ofFn]

/-- **Increasing lucky-car counts (Lemma 18).** Number the cars and spots $0, \dots, n-1$, let
$q^{\mathrm{inc}}_n(i, j)$ be the number of weakly increasing parking functions of length $n$ in
which car $i$ prefers spot $j$ and is lucky, and let $C_m$ be the $m$-th Catalan number. For all
$i, j \in \{0, \dots, n-1\}$, $q^{\mathrm{inc}}_n(i, j) = C_i \, C_{n-i}$ if $i = j$, and
$q^{\mathrm{inc}}_n(i, j) = 0$ otherwise.

In the one-based indexing of the source the diagonal value reads $C_{i-1} C_{n-i+1}$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Lemma 18. -/
theorem qInc_eq (n : ℕ) (i j : Fin n) :
    qInc n i j =
      if i = j then catalan i.val * catalan (n - i.val)
      else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, qInc]
    refine (Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)).trans
      (card_monotone_le_id_eq_self n i)
    constructor
    · rintro ⟨hp, hm, hi, _⟩
      exact ⟨hm, (isParkingFunction_iff_le_id_of_monotone hm).mp hp, hi⟩
    · rintro ⟨hm, hb, hi⟩
      exact ⟨(isParkingFunction_iff_le_id_of_monotone hm).mpr hb, hm, hi,
        (parkSpots_eq_self_of_le hb i).trans hi.symm⟩
  · rw [ite_eq_right hij, qInc]
    have : IsEmpty { f : Fin n → Fin n //
        IsParkingFunction n f ∧ Monotone f ∧ f i = j ∧ IsLuckyCar f i } := by
      refine ⟨fun ⟨f, hp, hm, hfi, hl⟩ => hij ?_⟩
      have hb := (isParkingFunction_iff_le_id_of_monotone hm).mp hp
      exact (parkSpots_eq_self_of_le hb i).symm.trans (hl.trans hfi)
    exact Nat.card_of_isEmpty

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
