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
# Metered parking with a long meter

When the meter remembers all earlier arrivals, metered parking succeeds exactly for
classical partial parking functions (`isMeteredParkingFunction_iff_of_le`).
-/

namespace MetaMathlibExt

open PollakPartialParking

namespace isMeteredParkingFunction_iff_of_le

-- Searching the spots in increasing order finds the minimum of the free spots.
private theorem find?_eq_linFirstFree {n : ℕ} (a : Fin n) {occupied : List ℕ}
    {occ : Finset (Fin n)} (hocc : ∀ s : Fin n, s ∈ occ ↔ s.val ∈ occupied) :
    (List.range' a (n - a)).find? (fun s => decide (s ∉ occupied)) =
      (linFirstFree n occ a).map Fin.val := by
  let free := Finset.univ.filter (fun s : Fin n => a.val ≤ s.val ∧ s ∉ occ)
  have mem_free (s : Fin n) : s ∈ free ↔ a.val ≤ s.val ∧ s.val ∉ occupied := by
    simp [free, hocc]
  unfold linFirstFree
  split_ifs with h
  · let x := free.min' h
    have hx := (mem_free x).mp (free.min'_mem h)
    change _ = some x.val
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hx.2, x.val - a.val, by simp; omega, by simp; omega, ?_⟩
    intro j hj
    simp only [List.getElem_range', Nat.one_mul, Bool.not_eq_true', decide_eq_false_iff_not,
      not_not]
    by_contra hfree
    let s : Fin n := ⟨a.val + j, by omega⟩
    have hle : x ≤ s := free.min'_le s ((mem_free s).mpr ⟨by dsimp [s]; omega, hfree⟩)
    change x.val ≤ a.val + j at hle
    omega
  · apply List.find?_eq_none.mpr
    intro s hs
    have hmem := List.mem_range'_1.mp hs
    let spot : Fin n := ⟨s, by omega⟩
    simpa using fun hn => h ⟨spot, (mem_free spot).mpr ⟨hmem.1, hn⟩⟩

-- Linear probing stops at the first failure. The metered history retains that failure,
-- or, if all cars have parked, records exactly the occupied spots.
private def Agrees {k n : ℕ} (out : List (Option ℕ)) :
    Option {occ : Finset (Fin n) // occ.card ≤ k} → Prop
  | none => none ∈ out
  | some occ => none ∉ out ∧ ∀ s : Fin n, s ∈ occ.val ↔ s.val ∈ out.filterMap id

private theorem prefix_agrees {m n t : ℕ} (ht : m - 1 ≤ t) (f : Fin m → Fin n)
    (k : ℕ) (hk : k ≤ m) :
    let prefs := List.ofFn fun i => (f i : ℕ)
    let out := meteredOutcome t n (prefs.take k)
    out.length = k ∧ Agrees out (linOccAux m n f k) := by
  intro prefs
  dsimp only
  induction k with
  | zero => simp [meteredOutcome, linOccAux, Agrees]
  | succ k ih =>
    have hkm : k < m := by omega
    let out := meteredOutcome t n (prefs.take k)
    let a := f ⟨k, hkm⟩
    obtain ⟨hlen, hagree⟩ : out.length = k ∧ Agrees out (linOccAux m n f k) := ih hkm.le
    have hdrop : out.length - t = 0 := by omega
    let next := (List.range' a (n - a)).find? (fun s => decide (s ∉ out.filterMap id))
    have hstep : meteredOutcome t n (prefs.take (k + 1)) = out ++ [next] := by
      rw [List.take_succ_eq_append_getElem (by simpa [prefs] using hkm)]
      simp only [prefs, List.getElem_ofFn, meteredOutcome, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      change out ++ [(List.range' a (n - a)).find? (fun s =>
        decide (s ∉ (out.drop (out.length - t)).filterMap id))] = _
      rw [hdrop, List.drop_zero]
    rw [hstep]
    refine ⟨by simp [hlen], ?_⟩
    cases hprev : linOccAux m n f k with
    | none =>
      rw [hprev] at hagree
      simpa only [linOccAux, hprev, Agrees] using List.mem_append_left [next] hagree
    | some occ =>
      rw [hprev] at hagree
      obtain ⟨hsuccess, hocc⟩ := hagree
      rw [show next = (linFirstFree n occ.val a).map Fin.val from find?_eq_linFirstFree a hocc]
      cases hspot : linFirstFree n occ.val (f ⟨k, hkm⟩) with
      | none => simp [linOccAux, hprev, hkm, hspot, Agrees]
      | some x =>
        simp [linOccAux, hprev, hkm, hspot, Agrees, hsuccess, hocc, List.filterMap_append,
          Fin.val_inj, or_comm]

end isMeteredParkingFunction_iff_of_le

/-- **Metered parking functions with a long meter are classical.** Let $m \le n$ and
$t \ge m - 1$. A map $f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$ is a $t$-metered parking
function if and only if it is a partial parking function with $m$ cars and $n$ spots.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 3 (`integers-2025-A73-prop-3`). -/
public theorem isMeteredParkingFunction_iff_of_le {m n t : ℕ} (ht : m - 1 ≤ t)
    (hmn : m ≤ n) (f : Fin m → Fin n) :
    IsMeteredParkingFunction t f ↔ IsPartialParkingFunction m n f := by
  rw [← linSuccess_iff_isPartialParkingFunction m n f hmn]
  have h := (isMeteredParkingFunction_iff_of_le.prefix_agrees ht f m le_rfl).2
  simp only [List.take_of_length_le (by simp : (List.ofFn fun i => (f i : ℕ)).length ≤ m)] at h
  unfold IsMeteredParkingFunction LinSuccess
  cases hs : linOccAux m n f m with
  | none =>
    rw [hs] at h
    exact ⟨fun hall => (hall none h rfl).elim, by simp⟩
  | some occ =>
    rw [hs] at h
    exact ⟨fun _ => rfl, fun _ o ho heq => h.1 (heq ▸ ho)⟩

end MetaMathlibExt
