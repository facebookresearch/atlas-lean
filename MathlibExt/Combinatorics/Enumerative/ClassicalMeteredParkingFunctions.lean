/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
import MathlibExt.Combinatorics.Enumerative.PollakPartialParkingFunctions

/-!
# Classical parking functions under metered parking

Every partial parking function succeeds for every meter length.
-/

namespace MetaMathlibExt

namespace IsPartialParkingFunction

open PollakPartialParking

-- The classical first free spot is available to the metered car. If that car parks
-- earlier, its spot was already occupied in the classical process.
private theorem metered_step {n a : ℕ} {occ : Finset (Fin n)} {x : Fin n}
    (hx : linFirstFree n occ a = some x) (active : List ℕ)
    (hactive : ∀ s ∈ active, ∃ y ∈ occ, (y : ℕ) = s) :
    ∃ z ∈ insert x occ,
      (List.range' a (n - a)).find? (fun s => decide (s ∉ active)) = some (z : ℕ) := by
  let free := Finset.univ.filter fun y : Fin n => a ≤ y.val ∧ y ∉ occ
  unfold linFirstFree at hx
  split at hx
  · rename_i hfree
    have hmin : free.min' hfree = x := Option.some.inj hx
    have hxmem : x ∈ free := hmin ▸ free.min'_mem hfree
    obtain ⟨hax, hxocc⟩ := (Finset.mem_filter.mp hxmem).2
    have hxavail : x.val ∉ active := by
      intro h
      obtain ⟨y, hy, heq⟩ := hactive _ h
      exact hxocc (Fin.ext heq ▸ hy)
    cases hfind : (List.range' a (n - a)).find? (fun s => decide (s ∉ active)) with
    | none =>
      have h := List.find?_range'_eq_none.mp hfind x.val hax (by omega)
      simp [hxavail] at h
    | some s =>
      obtain ⟨_, hrange, hbefore⟩ := List.find?_range'_eq_some.mp hfind
      obtain ⟨has, hsn⟩ := List.mem_range'_1.mp hrange
      have hsx : s ≤ x.val := by
        by_contra! h
        simpa [hxavail] using hbefore x.val hax h
      let z : Fin n := ⟨s, by omega⟩
      refine ⟨z, ?_, rfl⟩
      by_cases hz : z ∈ occ
      · exact Finset.mem_insert_of_mem hz
      · have hzfree : z ∈ free := Finset.mem_filter.mpr ⟨Finset.mem_univ _, has, hz⟩
        have hxs : x ≤ z := hmin ▸ free.min'_le z hzfree
        exact Finset.mem_insert.mpr (Or.inl (le_antisymm hsx hxs))
  · contradiction

-- Every spot in the metered history belongs to the classical occupied set for the same prefix.
private theorem metered_prefix {m n : ℕ} (f : Fin m → Fin n) (t k : ℕ) (hk : k ≤ m)
    {occ : {u : Finset (Fin n) // u.card ≤ k}} (hocc : linOccAux m n f k = some occ) :
    ∀ o ∈ meteredOutcome t n ((List.ofFn fun i => (f i : ℕ)).take k),
      ∃ y ∈ occ.val, o = some (y : ℕ) := by
  induction k with
  | zero => simp [meteredOutcome]
  | succ k ih =>
    have hkm : k < m := by omega
    rw [linOccAux] at hocc
    split at hocc
    · contradiction
    next prev hprev =>
      rw [dite_eq_left hkm] at hocc
      split at hocc
      next x hx =>
        cases hocc
        let out := meteredOutcome t n ((List.ofFn fun i => (f i : ℕ)).take k)
        have hist := ih hkm.le hprev
        let active := (out.drop (out.length - t)).filterMap id
        have hactive (s : ℕ) (hs : s ∈ active) : ∃ y ∈ prev.val, (y : ℕ) = s := by
          obtain ⟨o, ho, rfl⟩ := List.mem_filterMap.mp hs
          obtain ⟨y, hy, heq⟩ := hist (some s) (List.drop_subset _ _ ho)
          exact ⟨y, hy, by simpa using heq.symm⟩
        obtain ⟨z, hz, hnext⟩ := metered_step hx active hactive
        rw [List.take_succ_eq_append_getElem (by simpa using hkm)]
        simp only [List.getElem_ofFn, meteredOutcome, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        change ∀ o ∈ out ++ [(List.range' _ _).find? (fun s => decide (s ∉ active))],
          ∃ y ∈ insert x prev.val, o = some (y : ℕ)
        rw [hnext]
        intro o ho
        rcases List.mem_append.mp ho with h | h
        · obtain ⟨y, hy, heq⟩ := hist o h
          exact ⟨y, Finset.mem_insert_of_mem hy, heq⟩
        · exact ⟨z, hz, List.mem_singleton.mp h⟩
      next => contradiction

end IsPartialParkingFunction

/-- **Classical parking functions are metered parking functions.** Let $m \le n$. Every partial
parking function $f$ with $m$ cars and $n$ spots is a $t$-metered parking function for every
$t \in \mathbb{N}$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 4 (`integers-2025-A73-prop-4`). -/
public theorem IsPartialParkingFunction.isMeteredParkingFunction {m n : ℕ} (hmn : m ≤ n)
    {f : Fin m → Fin n} (hf : IsPartialParkingFunction m n f) (t : ℕ) :
    IsMeteredParkingFunction t f := by
  obtain ⟨occ, hocc⟩ := Option.isSome_iff_exists.mp <|
    (PollakPartialParking.linSuccess_iff_isPartialParkingFunction m n f hmn).2 hf
  have hist := IsPartialParkingFunction.metered_prefix f t m le_rfl hocc
  simp only [List.take_of_length_le (show (List.ofFn fun i => (f i : ℕ)).length ≤ m by simp)]
    at hist
  intro o ho
  obtain ⟨_, _, rfl⟩ := hist o ho
  exact Option.some_ne_none _

end MetaMathlibExt
