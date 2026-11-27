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

## References

* J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny, and A. R. Vindas Meléndez,
  *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
  Article A44, pp. 1–18, Proposition 3 (using Proposition 2).
* A. Christensen, P. E. Harris, Z. Jones, M. Loving, A. Ramos Rodríguez, J. Rennie,
  and G. Rojas Kirby, *A Generalization of Parking Functions Allowing Backward Movement*,
  Electronic Journal of Combinatorics 27(1) (2020), Article P1.33, pp. 1–20, Theorem 1.3
  (the bounded-path correspondence cited in Proposition 2).
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

private def stepHeight (l : List DyckStep) : ℤ := (l.count U : ℤ) - (l.count D : ℤ)

@[simp] private theorem stepHeight_append (l r : List DyckStep) :
    stepHeight (l ++ r) = stepHeight l + stepHeight r := by
  simp only [stepHeight, List.count_append, Int.natCast_add]
  omega

private theorem stepHeight_steps {m : ℕ} (p : Fin m → Bool) (j : ℕ) :
    stepHeight ((steps p).take j) = latticeHeight p j := by
  induction m generalizing j with
  | zero => simp [steps, stepHeight, latticeHeight]
  | succ m ih =>
    cases j with
    | zero => simp [stepHeight, latticeHeight]
    | succ j =>
      simp only [steps, List.ofFn_succ, List.take_succ_cons]
      change stepHeight ([stepEquiv (p 0)] ++ (steps fun i => p i.succ).take j) = _
      rw [stepHeight_append, ih]
      simp only [latticeHeight, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
        Nat.zero_lt_succ, ite_true, Nat.succ_lt_succ_iff]
      cases p 0 <;> simp [stepHeight, stepEquiv]

private theorem getLast?_steps {m : ℕ} (p : Fin m → Bool) (i : Fin m) (hi : i.val + 1 = m) :
    (steps p).getLast? = some (stepEquiv (p i)) := by
  rw [List.getLast?_eq_getElem?, length_steps, show m - 1 = i.val by omega]
  simp [steps, i.isLt]

private def pad (k : ℕ) (l : List DyckStep) : List DyckStep :=
  List.replicate k U ++ (l ++ List.replicate k D)

@[simp] private theorem length_pad (k : ℕ) (l : List DyckStep) :
    (pad k l).length = k + (l.length + k) := by simp [pad]

@[simp] private theorem stepHeight_pad (k : ℕ) (l : List DyckStep) :
    stepHeight (pad k l) = stepHeight l := by
  simp [pad, stepHeight, List.count_replicate]
  omega

/-- A prefix height is the contribution of each of the three blocks. -/
private theorem stepHeight_take_pad (k : ℕ) (l : List DyckStep) (j : ℕ) :
    stepHeight ((pad k l).take j) =
      (min j k : ℕ) + stepHeight (l.take (j - k)) - (min (j - k - l.length) k : ℕ) := by
  simp [pad, List.take_append, stepHeight, List.count_replicate]
  omega

private def toPaddedWord {n k : ℕ} {p : Fin (2 * n) → Bool} (hp : IsKDyckPath n k p) :
    {w : DyckWord // w.semilength = n + k} := by
  have hbal : stepHeight (steps p) = 0 := by
    have htake : (steps p).take (2 * n) = steps p := List.take_of_length_le (by simp)
    simpa only [htake] using (stepHeight_steps p (2 * n)).trans hp.1
  have hprefix (j : ℕ) : 0 ≤ stepHeight ((pad k (steps p)).take j) := by
    rw [stepHeight_take_pad, length_steps]
    by_cases hj : j ≤ k
    · simp [Nat.sub_eq_zero_of_le hj, stepHeight]
    by_cases hj' : j - k ≤ 2 * n
    · rw [stepHeight_steps]
      have := hp.2.1 (j - k) hj'
      omega
    · rw [List.take_of_length_le (by rw [length_steps]; omega), hbal]
      omega
  let w : DyckWord := ⟨pad k (steps p), by
    have h := (stepHeight_pad k (steps p)).trans hbal
    unfold stepHeight at h
    omega, fun j => by
    have h := hprefix j
    unfold stepHeight at h
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
  · rw [← stepHeight_steps, hsteps, List.take_of_length_le hlen.le, ← stepHeight_pad k l, ← h]
    simp [stepHeight, w.count_U_eq_count_D]
  · intro j hj
    have hnonneg : 0 ≤ stepHeight (w.toList.take (k + j)) := by
      unfold stepHeight
      have := w.count_D_le_count_U (k + j)
      omega
    rw [h, stepHeight_take_pad, hlen, Nat.add_sub_cancel_left, ← hsteps,
      stepHeight_steps] at hnonneg
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

end MetaMathlibExt
