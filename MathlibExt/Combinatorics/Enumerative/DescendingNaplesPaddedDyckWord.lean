/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import MathlibExt.Combinatorics.Enumerative.DescendingNaplesDyckPath
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Descending Naples parking functions and padded Dyck words

Adding `k` Up steps and `k` Down steps raises a bounded walk to a Dyck word.
The extra Down step in the required suffix is the last step of the original walk.
With zero padding, the correspondence sends weakly decreasing ordinary parking functions of
length `n` that contain preference `j : Fin n` to Dyck words with an Up step in column `j`.

## References

* J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny, and A. R. Vindas Meléndez,
  *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
  Article A44, pp. 1–18, Proposition 3 (using Proposition 2).
* A. Christensen, P. E. Harris, Z. Jones, M. Loving, A. Ramos Rodríguez, J. Rennie,
  and G. Rojas Kirby, *A Generalization of Parking Functions Allowing Backward Movement*,
  Electronic Journal of Combinatorics 27(1) (2020), Article P1.33, pp. 1–20, Theorem 1.3
  (the bounded-path correspondence cited in Proposition 2).
* Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer Sequences 29 (2026),
  Article 26.1.1, pp. 1–18, Section 4, for the ordinary parking correspondence.
-/

namespace MetaMathlibExt

open DyckStep

private def stepEquiv : Bool ≃ DyckStep where
  toFun b := if b then U else D
  invFun s := s == U
  left_inv b := by cases b <;> rfl
  right_inv s := by cases s <;> rfl

private def steps {m : ℕ} (p : Fin m → Bool) : List DyckStep :=
  List.ofFn fun i => stepEquiv (p i)

@[simp] private theorem length_steps {m : ℕ} (p : Fin m → Bool) : (steps p).length = m :=
  List.length_ofFn

/-- **Height of a sequence of Dyck steps.** For a finite sequence $l$ of Up steps $U$ and Down
steps $D$ and a natural number $j$, the height of $l$ after $j$ steps is the integer obtained as
the number of $U$ minus the number of $D$ among the first $j$ steps of $l$ (among all of $l$
when $j$ exceeds its length).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 3. -/
@[expose] public def dyckStepHeight (l : List DyckStep) (j : ℕ) : ℤ :=
  ((l.take j).count DyckStep.U : ℤ) - ((l.take j).count DyckStep.D : ℤ)

local notation:max "height[" l "]" => dyckStepHeight l (List.length l)

/-- The final height of a word is its Up count minus its Down count, as integers. -/
public theorem dyckStepHeight_full_eq (l : List DyckStep) :
    dyckStepHeight l l.length = (l.count U : ℤ) - (l.count D : ℤ) := by
  simp [dyckStepHeight]

/-- The empty word has zero height at every index. -/
public theorem dyckStepHeight_nil (j : ℕ) : dyckStepHeight [] j = 0 := by
  simp [dyckStepHeight]

/-- Prepending an Up step increases the final height by one. -/
public theorem dyckStepHeight_full_cons_U (l : List DyckStep) :
    dyckStepHeight (U :: l) (U :: l).length = dyckStepHeight l l.length + 1 := by
  rw [dyckStepHeight_full_eq, dyckStepHeight_full_eq]
  simp
  omega

/-- The final height of a concatenation is the sum of the two final heights. -/
@[simp] public theorem dyckStepHeight_full_append (l r : List DyckStep) :
    dyckStepHeight (l ++ r) (l ++ r).length =
      dyckStepHeight l l.length + dyckStepHeight r r.length := by
  simp only [dyckStepHeight_full_eq, List.count_append, Int.natCast_add]
  omega

private theorem dyckStepHeight_steps {m : ℕ} (p : Fin m → Bool) (j : ℕ) :
    height[(steps p).take j] = latticeHeight p j := by
  induction m generalizing j with
  | zero => simp [steps, dyckStepHeight_nil, latticeHeight]
  | succ m ih =>
    cases j with
    | zero => simp [dyckStepHeight_nil, latticeHeight]
    | succ j =>
      simp only [steps, List.ofFn_succ, List.take_succ_cons]
      change height[[stepEquiv (p 0)] ++ (steps fun i => p i.succ).take j] = _
      rw [dyckStepHeight_full_append, ih]
      simp only [latticeHeight, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
        Nat.zero_lt_succ, ite_true, Nat.succ_lt_succ_iff]
      cases p 0 <;> simp [dyckStepHeight, stepEquiv]

private theorem getLast?_steps {m : ℕ} (p : Fin m → Bool) (i : Fin m) (hi : i.val + 1 = m) :
    (steps p).getLast? = some (stepEquiv (p i)) := by
  rw [List.getLast?_eq_getElem?, length_steps, show m - 1 = i.val by omega]
  simp [steps, i.isLt]

private def pad (k : ℕ) (l : List DyckStep) : List DyckStep :=
  List.replicate k U ++ (l ++ List.replicate k D)

@[simp] private theorem length_pad (k : ℕ) (l : List DyckStep) :
    (pad k l).length = k + (l.length + k) := by simp [pad]

@[simp] private theorem dyckStepHeight_pad (k : ℕ) (l : List DyckStep) :
    height[pad k l] = height[l] := by
  simp only [dyckStepHeight_full_eq]
  simp [pad, List.count_replicate]
  omega

/-- A prefix height is the contribution of each of the three blocks. -/
private theorem dyckStepHeight_take_pad (k : ℕ) (l : List DyckStep) (j : ℕ) :
    height[(pad k l).take j] =
      (min j k : ℕ) + height[l.take (j - k)] - (min (j - k - l.length) k : ℕ) := by
  simp only [dyckStepHeight_full_eq]
  simp [pad, List.take_append, List.count_replicate]
  omega

private def toPaddedWord {n k : ℕ} {p : Fin (2 * n) → Bool} (hp : IsKDyckPath n k p) :
    {w : DyckWord // w.semilength = n + k} := by
  have hbal : height[steps p] = 0 := by
    have htake : (steps p).take (2 * n) = steps p := List.take_of_length_le (by simp)
    simpa only [htake] using (dyckStepHeight_steps p (2 * n)).trans hp.1
  have hprefix (j : ℕ) : 0 ≤ height[(pad k (steps p)).take j] := by
    rw [dyckStepHeight_take_pad, length_steps]
    by_cases hj : j ≤ k
    · simp [Nat.sub_eq_zero_of_le hj, dyckStepHeight_nil]
    by_cases hj' : j - k ≤ 2 * n
    · rw [dyckStepHeight_steps]
      have := hp.2.1 (j - k) hj'
      omega
    · rw [List.take_of_length_le (by rw [length_steps]; omega), hbal]
      omega
  let w : DyckWord := ⟨pad k (steps p), by
    have h := (dyckStepHeight_pad k (steps p)).trans hbal
    rw [dyckStepHeight_full_eq] at h
    omega, fun j => by
    have h := hprefix j
    rw [dyckStepHeight_full_eq] at h
    omega⟩
  refine ⟨w, ?_⟩
  have h := w.two_mul_semilength_eq_length
  change 2 * w.semilength = (pad k (steps p)).length at h
  rw [length_pad, length_steps] at h
  omega

private theorem padded_suffix {n k : ℕ} (hn : 1 ≤ n) {p : Fin (2 * n) → Bool}
    (hp : IsKDyckPath n k p) : List.replicate (k + 1) D <:+ pad k (steps p) := by
  let i : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hi : i.val + 1 = 2 * n := by dsimp [i]; omega
  have h := getLast?_steps p i hi
  rw [hp.2.2 i hi] at h
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp (show (steps p).getLast? = some D from h)
  rw [pad, hl, List.append_assoc, ← List.append_assoc (List.replicate k U) l,
    List.singleton_append, ← List.replicate_succ]
  exact List.suffix_append ..

/-- Strip `k` steps from each end, retaining one Down step from the final run. -/
private theorem exists_middle {n k : ℕ} (hn : 1 ≤ n)
    (w : {w : DyckWord // w.semilength = n + k})
    (hpre : List.replicate k U <+: w.1.toList) (hsuf : List.replicate (k + 1) D <:+ w.1.toList) :
    ∃ l : List DyckStep, l.length = 2 * n ∧ l.getLast? = some D ∧ w.1.toList = pad k l := by
  obtain ⟨front, hfront⟩ := hsuf
  have hlen := w.1.two_mul_semilength_eq_length
  rw [w.2, ← hfront, List.length_append, List.length_replicate] at hlen
  have hk : k ≤ front.length := by omega
  have htake := List.prefix_iff_eq_take.mp hpre
  rw [List.length_replicate, ← hfront, List.take_append_of_le_length hk] at htake
  refine ⟨front.drop k ++ [D], by simp; omega, List.getLast?_concat, ?_⟩
  calc
    w.1.toList = front ++ List.replicate (k + 1) D := hfront.symm
    _ = pad k (front.drop k ++ [D]) := by
      rw [pad, List.append_assoc (front.drop k), List.singleton_append, ← List.replicate_succ,
        ← List.append_assoc, htake, List.take_append_drop]

private theorem exists_walk {n k : ℕ} (w : DyckWord) {l : List DyckStep}
    (h : w.toList = pad k l) (hlen : l.length = 2 * n) (hlast : l.getLast? = some D) :
    ∃ p : Fin (2 * n) → Bool, IsKDyckPath n k p ∧ steps p = l := by
  let p : Fin (2 * n) → Bool := fun i =>
    have hi : i.val < l.length := by rw [hlen]; exact i.isLt
    stepEquiv.symm l[i.val]
  have hsteps : steps p = l := by
    apply List.ext_getElem
    · rw [length_steps, hlen]
    · intro i hi _
      simp [steps, p, List.getElem_ofFn]
  refine ⟨p, ⟨?_, ?_, ?_⟩, hsteps⟩
  · rw [← dyckStepHeight_steps, hsteps, List.take_of_length_le hlen.le,
      ← dyckStepHeight_pad k l, ← h]
    simp [dyckStepHeight_full_eq, w.count_U_eq_count_D]
  · intro j hj
    have hnonneg : 0 ≤ height[w.toList.take (k + j)] := by
      rw [dyckStepHeight_full_eq]
      have := w.count_D_le_count_U (k + j)
      omega
    rw [h, dyckStepHeight_take_pad, hlen, Nat.add_sub_cancel_left, ← hsteps,
      dyckStepHeight_steps] at hnonneg
    omega
  · intro i hi
    have hstep := getLast?_steps p i hi
    rw [hsteps, hlast, Option.some.injEq] at hstep
    exact stepEquiv.injective hstep.symm

open Classical in
/-- **Descending $k$-Naples parking functions and Dyck paths.** For all natural numbers $n \ge 1$
and $k \ge 1$, the number of weakly decreasing $k$-Naples parking functions of length $n$ equals
the number of Dyck paths of semilength $n + k$ (that is, with $2(n + k)$ steps) whose first $k$
steps are Up and whose last $k + 1$ steps are Down.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 3. -/
public theorem descendingNaplesCount_eq_card_dyckPath {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) :
    descendingNaplesCount n k = (Finset.univ.filter
      fun p : {p : DyckWord // p.semilength = n + k} =>
        List.replicate k DyckStep.U <+: p.1.toList ∧
          List.replicate (k + 1) DyckStep.D <:+ p.1.toList).card := by
  rw [descendingNaplesCount_eq_card_kDyckPath hn hk, ← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  refine Equiv.ofBijective (fun p => ?_) ⟨?_, ?_⟩
  · have hp := (Finset.mem_filter.mp p.2).2
    exact ⟨toPaddedWord hp, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, List.prefix_append .., padded_suffix hn hp⟩⟩
  · intro p q he
    have heq := congrArg (fun w => w.1.1.toList) he
    change pad k (steps p.1) = pad k (steps q.1) at heq
    have hs := List.append_cancel_right (List.append_cancel_left heq)
    have hs' := List.ofFn_injective hs
    exact Subtype.ext (funext fun i => stepEquiv.injective (congrFun hs' i))
  · intro w
    obtain ⟨hpre, hsuf⟩ := (Finset.mem_filter.mp w.2).2
    obtain ⟨l, hlen, hl, hpad⟩ := exists_middle hn w.1 hpre hsuf
    obtain ⟨p, hp, he⟩ := exists_walk w.1.1 hpad hlen hl
    refine ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply DyckWord.ext
    change pad k (steps p) = w.1.1.toList
    rw [he, hpad]

private lemma classical_toPaddedWord_list {n : ℕ} {p : Fin (2 * n) → Bool}
    (hp : IsKDyckPath n 0 p) : (toPaddedWord hp).1.toList = steps p := by
  simp [toPaddedWord, pad]

private noncomputable def classicalPathEquivDyck {n : ℕ} (hn : 1 ≤ n) :
    {p : Fin (2 * n) → Bool // IsKDyckPath n 0 p} ≃ {p : DyckWord // p.semilength = n} := by
  refine Equiv.ofBijective (fun p => toPaddedWord p.2) ⟨?_, ?_⟩
  · intro p q h
    have hl := congrArg (fun w : {p : DyckWord // p.semilength = n} => w.1.toList) h
    rw [classical_toPaddedWord_list, classical_toPaddedWord_list] at hl
    have hw := List.ofFn_injective hl
    exact Subtype.ext (funext fun i => stepEquiv.injective (congrFun hw i))
  · rintro ⟨p, hp⟩
    have hlen := p.two_mul_semilength_eq_length
    rw [hp] at hlen
    have hne : p.toList ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hlast : p.toList.getLast? = some D := by
      rw [List.getLast?_eq_some_getLast hne, p.getLast_eq_D]
    obtain ⟨w, hw, hsteps⟩ := exists_walk (k := 0) p (by simp [pad]) hlen.symm hlast
    exact ⟨⟨w, hw⟩, Subtype.ext (DyckWord.ext ((classical_toPaddedWord_list hw).trans hsteps))⟩

private lemma twice_count_D_before {n : ℕ} (p : Fin (2 * n) → Bool) (t : Fin (2 * n)) :
    (t.val : ℤ) - latticeHeight p t.val = 2 * (((steps p).take t.val).count D : ℤ) := by
  rw [← dyckStepHeight_steps]
  let l := (steps p).take t.val
  have hlen : l.length = t.val := by simp [l]
  have hc : l.length = l.count D + l.count U := by
    have hcompl : (fun s : DyckStep => decide ((s == D) ≠ true)) = (· == U) := by
      funext s
      cases s <;> rfl
    simpa only [List.count, hcompl] using l.length_eq_countP_add_countP (· == D)
  change (t.val : ℤ) - height[l] = 2 * (l.count D : ℤ)
  rw [dyckStepHeight_full_eq]
  omega

private lemma steps_column_iff {n : ℕ} (p : Fin (2 * n) → Bool) (j : ℕ) :
    (∃ a t, steps p = a ++ U :: t ∧ a.count D = j) ↔
      ∃ t : Fin (2 * n), p t = true ∧ (t.val : ℤ) - latticeHeight p t.val = 2 * (j : ℤ) := by
  constructor
  · rintro ⟨a, t, he, hj⟩
    have hlen : a.length < 2 * n := by
      have := congrArg List.length he
      simp only [length_steps, List.length_append, List.length_cons] at this
      omega
    let k : Fin (2 * n) := ⟨a.length, hlen⟩
    have hget : (steps p)[a.length]'(by simpa using hlen) = U := by
      simp [he, List.getElem_append_right]
    have hk : p k = true := by simpa [steps, stepEquiv, k, apply_dite, apply_ite] using hget
    refine ⟨k, hk, ?_⟩
    rw [twice_count_D_before, he]
    simp [k, hj]
  · rintro ⟨t, hu, hd⟩
    let l := steps p
    have hlt : t.val < l.length := by simp [l]
    have hu' : l[t.val] = U := by simp [l, steps, stepEquiv, hu]
    refine ⟨l.take t.val, l.drop (t.val + 1), ?_, ?_⟩
    · calc
        l = l.take t.val ++ l.drop t.val := (List.take_append_drop ..).symm
        _ = _ := by rw [List.drop_eq_getElem_cons hlt, hu']
    · rw [twice_count_D_before] at hd
      change 2 * ((l.take t.val).count D : ℤ) = 2 * (j : ℤ) at hd
      omega

/-- **Dyck words of decreasing parking functions with a prescribed preference.** For every
`j : Fin n`, weakly decreasing parking functions of length `n` that contain preference `j`
are in bijection with Dyck words of semilength `n` having an Up step preceded by exactly `j.val`
Down steps.

Source: Steve Butler et al., *Lucky Cars and Lucky Spots in Parking Functions*,
Journal of Integer Sequences 29 (2026), Article 26.1.1, Section 4. -/
public noncomputable def decreasingParkingPreferenceEquivDyckWord {n : ℕ} (j : Fin n) :
    {f : {f : Fin n → Fin n // IsParkingFunction n f ∧ Antitone f} // ∃ i, f.1 i = j} ≃
      {w : {w : DyckWord // w.semilength = n} //
        ∃ a t, w.1.toList = a ++ U :: t ∧ a.count D = j.val} := by
  refine (decreasingParkingPreferenceEquivPath j).trans
    ((classicalPathEquivDyck (Nat.one_le_of_lt j.isLt)).subtypeEquiv ?_)
  intro p
  change _ ↔ ∃ a t, (toPaddedWord p.2).1.toList = a ++ U :: t ∧ a.count D = j.val
  rw [classical_toPaddedWord_list]
  exact (steps_column_iff p.1 j.val).symm

end MetaMathlibExt
