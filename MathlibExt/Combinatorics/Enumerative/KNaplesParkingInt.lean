/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.List.Nodup

/-!
# Integer Naples parking

Increasing the backward search by one spot keeps all cars in $[0,n]$ whenever
the original run on the integer line fills $[1,n]$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The $k$-Naples rule on $\mathbb{Z}$.** When the spots in a finite list $O$ of integers are
occupied, a car preferring $a \in \mathbb{Z}$ parks in $a$ if $a$ is free; otherwise in the first
free spot among $a - 1, \dots, a - k$, checked in decreasing order with no lower bound; otherwise
in the first free spot among $a + 1, \dots, a + |O| + 1$, checked in increasing order (one of
them is free, so this is the first free spot after $a$).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2 (parking on `ℤ`). -/
public def naplesSpotInt (k : ℕ) (occ : List ℤ) (a : ℤ) : ℤ :=
  if a ∉ occ then a else
    match ((List.range k).map fun j => a - ((j + 1 : ℕ) : ℤ)).find?
        (fun s => decide (s ∉ occ)) with
    | some s => s
    | none => (((List.range (occ.length + 1)).map fun j => a + ((j + 1 : ℕ) : ℤ)).find?
        (fun s => decide (s ∉ occ))).getD a

/-- **Naples parking on $\mathbb{Z}$.** Starting from a list of occupied spots in $\mathbb{Z}$,
cars with integer preferences $a_1, \dots, a_m$ arrive in order, and each takes the spot given by
the $k$-Naples rule on $\mathbb{Z}$ for the spots occupied when it arrives. The result is the
final list of occupied spots: the spots of the cars, most recent first, followed by the initially
occupied spots.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 2 (parking on `ℤ`). -/
public def naplesParkInt (k : ℕ) : List ℤ → List ℤ → List ℤ
  | occ, [] => occ
  | occ, a :: as => naplesParkInt k (naplesSpotInt k occ a :: occ) as

end

namespace naplesParkInt_succ_mem_Icc

private theorem firstFree_index {f : ℕ → ℤ} {m : ℕ} {occ : List ℤ} {s : ℤ}
    (h : ((List.range m).map f).find? (fun t => decide (t ∉ occ)) = some s) :
    s ∉ occ ∧ ∃ i, f i = s ∧ i < m ∧ ∀ j < i, f j ∈ occ := by
  simpa using List.find?_eq_some_iff_getElem.mp h

private theorem all_occupied {f : ℕ → ℤ} {m : ℕ} {occ : List ℤ}
    (h : ((List.range m).map f).find? (fun t => decide (t ∉ occ)) = none) :
    ∀ j < m, f j ∈ occ := by
  simpa using List.find?_eq_none.mp h

/-- Bounds supplied by a free spot in either search direction. -/
private structure SpotSpec (k : ℕ) (occ : List ℤ) (a s : ℤ) : Prop where
  free : s ∉ occ
  lower : a - k ≤ s
  back : ∀ t ∉ occ, a - k ≤ t → t ≤ a → t ≤ s ∧ s ≤ a
  forward : ∀ t ∉ occ, a < t → s ≤ t

private theorem spot_spec (k : ℕ) (occ : List ℤ) (a : ℤ) :
    SpotSpec k occ a (naplesSpotInt k occ a) := by
  by_cases ha : a ∉ occ
  · rw [naplesSpotInt, ite_eq_left ha]
    exact ⟨ha, by omega, fun _ _ _ ht => ⟨ht, le_rfl⟩, fun _ _ ht => ht.le⟩
  let back (j : ℕ) := a - ((j + 1 : ℕ) : ℤ)
  let fwd (j : ℕ) := a + ((j + 1 : ℕ) : ℤ)
  unfold naplesSpotInt
  rw [ite_eq_right ha]
  replace ha : a ∈ occ := not_not.mp ha
  change SpotSpec k occ a (match ((List.range k).map back).find? _ with
    | some s => s
    | none => (((List.range (occ.length + 1)).map fwd).find? _).getD a)
  split
  next s h =>
    obtain ⟨hs, i, rfl, hi, hprev⟩ := firstFree_index h
    refine ⟨hs, by dsimp [back]; omega, ?_, by dsimp [back]; intros; omega⟩
    intro t ht hlo hhi
    refine ⟨?_, by dsimp [back]; omega⟩
    by_contra! hlt
    have hta : t ≠ a := by rintro rfl; exact ht ha
    let j := (a - t - 1).toNat
    have heq : back j = t := by dsimp [back, j]; omega
    exact ht (heq ▸ hprev j (by dsimp [back, j] at *; omega))
  next h =>
    have hb := all_occupied h
    have back_full (t : ℤ) (ht : a - k ≤ t) (ht' : t ≤ a) : t ∈ occ := by
      by_cases heq : t = a
      · simpa [heq] using ha
      let j := (a - t - 1).toNat
      have hj : j < k := by dsimp [j]; omega
      have heq' : back j = t := by dsimp [back, j]; omega
      exact heq' ▸ hb j hj
    cases hf : ((List.range (occ.length + 1)).map fwd).find? (fun t => decide (t ∉ occ)) with
    | none =>
      have hsub : (List.range (occ.length + 1)).map fwd ⊆ occ := by
        intro t ht
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
        exact all_occupied hf j (List.mem_range.mp hj)
      have hnodup := (List.nodup_range (n := occ.length + 1)).map
        (f := fwd) (fun x y hxy => by dsimp [fwd] at hxy; omega)
      have := hnodup.length_le_of_subset hsub
      simp only [List.length_map, List.length_range] at this
      omega
    | some s =>
      obtain ⟨hs, i, rfl, hi, hprev⟩ := firstFree_index hf
      refine ⟨hs, by dsimp [fwd]; omega, fun t ht hl hu => (ht (back_full t hl hu)).elim, ?_⟩
      intro t ht hgt
      by_contra! hlt
      let j := (t - a - 1).toNat
      have heq : fwd j = t := by dsimp [fwd, j]; omega
      exact ht (heq ▸ hprev j (by dsimp [fwd, j] at *; omega))

/-- Between two free spots of the original run, the longer-backtracking run has a
free spot in the interval with the right endpoint excluded. -/
private def FreeBetween (old new : List ℤ) : Prop :=
  ∀ l ∉ old, ∀ r ∉ old, l < r → ∃ t ∉ new, l ≤ t ∧ t < r

private theorem freeBetween_cons {old new : List ℤ} {a : ℤ} {k : ℕ}
    (h : FreeBetween old new) :
    FreeBetween (naplesSpotInt k old a :: old) (naplesSpotInt (k + 1) new a :: new) := by
  let p := naplesSpotInt k old a
  let q := naplesSpotInt (k + 1) new a
  have hp : SpotSpec k old a p := spot_spec ..
  have hq : SpotSpec (k + 1) new a q := spot_spec ..
  intro l hl r hr hlr
  change l ∉ p :: old at hl
  change r ∉ p :: old at hr
  simp only [List.mem_cons, not_or] at hl hr
  suffices ∃ t ∉ new, l ≤ t ∧ t < r ∧ t ≠ q by
    obtain ⟨t, ht, hlt, htr, hne⟩ := this
    exact ⟨t, List.not_mem_cons_of_ne_of_not_mem hne ht, hlt, htr⟩
  by_cases hpl : p < l
  · -- A free spot between p and l stops the new car before l.
    obtain ⟨w, hw, hpw, hwl⟩ := h p hp.free l hl.2 hpl
    have hmin := hp.lower
    have ha : a < l := by
      by_contra! hla
      have := (hp.back l hl.2 (by omega) hla).1
      omega
    have hql : q < l := by
      by_cases hwa : w ≤ a
      · have := (hq.back w hw (by omega) hwa).2
        omega
      · have := hq.forward w hw (by omega)
        omega
    obtain ⟨t, ht, hlt, htr⟩ := h l hl.2 r hr.2 hlr
    exact ⟨t, ht, hlt, htr, by omega⟩
  by_cases hrp : r < p
  · -- Either r is beyond backward reach, or a free spot in [r,p) stops the car.
    have hrq : r ≤ q := by
      by_cases hreach : r ≤ a - (k + 1 : ℕ)
      · exact hreach.trans hq.lower
      have hra : r ≤ a := by
        by_contra! har
        have := hp.forward r hr.2 har
        omega
      have hpa := (hp.back r hr.2 (by omega) hra).2
      obtain ⟨w, hw, hrw, hwp⟩ := h r hr.2 p hp.free hrp
      exact hrw.trans (hq.back w hw (by omega) (by omega)).1
    obtain ⟨t, ht, hlt, htr⟩ := h l hl.2 r hr.2 hlr
    exact ⟨t, ht, hlt, htr, by omega⟩
  -- When l < p < r, the new car can occupy at most one of two distinct free spots.
  obtain ⟨u, hu, hlu, hup⟩ := h l hl.2 p hp.free (by omega)
  obtain ⟨v, hv, hpv, hvr⟩ := h p hp.free r hr.2 (by omega)
  by_cases huq : u = q
  · exact ⟨v, hv, by omega, hvr, by omega⟩
  · exact ⟨u, hu, hlu, by omega, huq⟩

private theorem freeBetween_park (k : ℕ) (prefs : List ℤ) {old new : List ℤ}
    (h : FreeBetween old new) :
    FreeBetween (naplesParkInt k old prefs) (naplesParkInt (k + 1) new prefs) := by
  induction prefs generalizing old new with
  | nil => exact h
  | cons a prefs ih => exact ih (freeBetween_cons h)

end naplesParkInt_succ_mem_Icc

-- The interval comparison does not need the length and preference hypotheses in the statement.
set_option linter.unusedVariables false in
open naplesParkInt_succ_mem_Icc in
/-- **One more backward step keeps the cars in $\{0, \dots, n\}$.** Let $(a_1, \dots, a_n)$ be
integers with $1 \le a_j \le n$ for every $j$. If, under the $k$-Naples rule on $\mathbb{Z}$, the
cars with these preferences, arriving in order with no spot occupied, occupy exactly the spots
$1, \dots, n$, then under the $(k + 1)$-Naples rule on $\mathbb{Z}$ every car parks in a spot $s$
with $0 \le s \le n$.

Every $k \ge 0$ is admitted (the source's proof treats any $k \ge 0$).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Lemma 1. -/
public theorem naplesParkInt_succ_mem_Icc {k n : ℕ} {α : List ℤ} (hlen : α.length = n)
    (hα : ∀ a ∈ α, 1 ≤ a ∧ a ≤ n)
    (hpark : ∀ s : ℤ, s ∈ naplesParkInt k [] α ↔ 1 ≤ s ∧ s ≤ n) :
    ∀ s ∈ naplesParkInt (k + 1) [] α, 0 ≤ s ∧ s ≤ n := by
  have hempty : FreeBetween [] [] := fun l _ _ _ hlr => ⟨l, by simp, le_rfl, hlr⟩
  have h := freeBetween_park k α hempty
  intro s hs
  by_contra! hout
  have hfree (t : ℤ) (ht : t = s ∨ t = s + 1) : t ∉ naplesParkInt k [] α := by
    intro hmem
    have := (hpark t).mp hmem
    omega
  obtain ⟨t, ht, hlo, hhi⟩ :=
    h s (hfree s (Or.inl rfl)) (s + 1) (hfree _ (Or.inr rfl)) (by omega)
  have hts : t = s := by omega
  exact ht (hts ▸ hs)

end MetaMathlibExt
