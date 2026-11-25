/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/Data/Fin/Tuple/Basic.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert

/-!
# Insertions and appends in tuples

The positions `k.castSucc` and `k.succ` of `Fin (m + 1)` are adjacent: each one skips the other
to land on `k` (`Fin.succAbove_castSucc_self`, `Fin.succAbove_succ_self`). This file reads off
the entry of an insertion at one of them in the other position, and compares updating the two
insertions there. It also shows how `Fin.snoc` interacts with reindexing along a map extended to
send the last position to the last position. The image of an initial segment under `Fin.cons`
is obtained by inserting the first entry into the corresponding image for the tail.
A tuple of length three is determined by its three entries. A tuple in a sum type that starts on
the left, ends on the right and never steps from right to left steps from left to right exactly
once.

## Main results

* `Fin.insertNth_castSucc_apply_succ` and `Fin.insertNth_succ_apply_castSucc`: after inserting at
  one of two adjacent positions, the other position holds the `k`-th entry of the tuple.
* `Fin.update_insertNth_castSucc`: inserting at `k.castSucc` and updating `k.succ` is inserting at
  `k.succ` and updating `k.castSucc`.
* `Fin.snoc_comp_snoc_castSucc_comp`: reindexing along `g` and then appending agrees with
  appending and then reindexing along the extension of `g` that fixes the last position.
* `Fin.tail_contractNth_succ`, `Fin.init_contractNth_castSucc`: contracting two adjacent entries
  away from the first (last) one commutes with dropping the first (last) entry.
* `Fin.snoc_comp_swap_castSucc`: exchanging two entries other than the last one commutes with
  appending.
* `Fin.tail_snoc`: dropping the first entry commutes with appending a last one.
* `Fin.snoc_tail_comp_rev`: appending the first entry to the reversed tail reverses the tuple.
* `Fin.forall_snoc_eq_iff_snoc_eq`: appending one entry to each of two tuples gives the same
  equality pattern exactly when the old patterns agree and the new entries repeat the same
  positions.
* `Fin.update_append_castAdd`, `Fin.update_append_natAdd`: updating an entry of `Fin.append u v`
  updates the corresponding entry of `u` or of `v`.
* `Fin.append_comp_swap_castAdd`, `Fin.append_comp_swap_natAdd`: exchanging two entries of
  `Fin.append u v` exchanges the corresponding entries of `u` or of `v`.
* `Fin.contractNth_zero_cons`, `Fin.contractNth_succ_cons`: contracting entries of a tuple
  `Fin.cons x a`.
* `Fin.contractNth_castSucc_castSucc_snoc`, `Fin.contractNth_castSucc_last_snoc`: contracting
  entries of a tuple `Fin.snoc a x`.
* `Fin.init_contractNth_castSucc_last`: contracting the last two entries and dropping the last
  one drops the last two entries.
* `Fin.contractNth_last`: contracting at the last position drops the last entry.
* `Fin.contractNth_castSucc_castSucc_apply_last` and `Fin.contractNth_castSucc_last_apply_last`:
  the last entry of a contraction.
* `Fin.contractNth_castSucc_eq_update_removeNth_succ`: contracting the entries `j` and `j + 1`
  is deleting entry `j + 1` and then overwriting entry `j` by the contraction.
* `Fin.update_removeNth_succ_eq_removeNth_castSucc`: deleting entry `j + 1` and then overwriting
  entry `j` by the deleted entry is deleting entry `j`.
* `Fin.contractNth_castSucc_const`: contracting two adjacent entries of a constant tuple.
* `Fin.insertNth_apply_zero_of_ne_zero`, `Fin.insertNth_apply_last_of_ne_last`: inserting away
  from the first (last) position keeps the first (last) entry.
* `Fin.contractNth_castSucc_insertNth_succ_castSucc`: contracting the two steps of a path that
  meet at an inserted vertex.
* `Fin.removeNth_succ_cons`: deleting an entry of `Fin.cons x a` other than the first deletes
  the corresponding entry of `a`.
* `Fin.insertNth_one_ne_zero`: inserting the entry `1` gives a nonzero tuple.
* `Fin.injective_apply_zero_one_two`: a tuple of length three is determined by its entries.
* `Fin.injective_comp_succAbove_of_eq` and `Fin.range_comp_succAbove_of_eq`: if `b p = b q`,
  deleting the entry at `p` or at `q` gives an injective tuple in the same cases, and does not
  change the set of entries.
* `Fin.existsUnique_isLeft_castSucc_and_isRight_succ`: a tuple in `α ⊕ β` from the left summand to
  the right one that never steps back steps from left to right exactly once.
-/

public section

namespace Fin

variable {m : ℕ} {α : Sort*}

/-- After inserting at `k.castSucc`, the next position `k.succ` holds the `k`-th entry. -/
@[simp]
theorem insertNth_castSucc_apply_succ (k : Fin m) (u : α) (y : Fin m → α) :
    (k.castSucc.insertNth u y : Fin (m + 1) → α) k.succ = y k := by
  rw [← succAbove_castSucc_self, insertNth_apply_succAbove]

/-- After inserting at `k.succ`, the previous position `k.castSucc` holds the `k`-th entry. -/
@[simp]
theorem insertNth_succ_apply_castSucc (k : Fin m) (v : α) (y : Fin m → α) :
    (k.succ.insertNth v y : Fin (m + 1) → α) k.castSucc = y k := by
  rw [← succAbove_succ_self, insertNth_apply_succAbove]

/-- Two insertions at adjacent positions agree away from those positions. -/
theorem update_insertNth_castSucc (k : Fin m) (y : Fin m → α) (u v : α) :
    Function.update (k.castSucc.insertNth u y : Fin (m + 1) → α) k.succ v =
      Function.update (k.succ.insertNth v y : Fin (m + 1) → α) k.castSucc u := by
  have hk : k.castSucc ≠ k.succ := castSucc_lt_succ.ne
  ext l
  rcases lt_trichotomy l k.castSucc with h | rfl | h
  · rw [Function.update_of_ne (h.trans castSucc_lt_succ).ne, Function.update_of_ne h.ne,
      insertNth_apply_below h, insertNth_apply_below (h.trans castSucc_lt_succ)]
    simp
  · simp [hk]
  rcases eq_or_lt_of_le (castSucc_lt_iff_succ_le.1 h) with h' | h'
  · subst h'; simp [hk.symm]
  · rw [Function.update_of_ne h'.ne', Function.update_of_ne h.ne', insertNth_apply_above h,
      insertNth_apply_above h']
    simp

/-- Appending `z` to `c` and reindexing along the extension of `g` that sends the last position
to the last position is the same as appending `z` to `c ∘ g`. -/
theorem snoc_comp_snoc_castSucc_comp {n : ℕ} (c : Fin n → α) (z : α) (g : Fin m → Fin n) :
    snoc c z ∘ snoc (castSucc ∘ g) (last n) = snoc (c ∘ g) z := by
  funext i
  exact lastCases (by simp) (fun j => by simp) i

/-- Exchanging the entries `j` and `k` of `Fin.snoc c z` is appending `z` to `c` with the entries
`j` and `k` exchanged. -/
theorem snoc_comp_swap_castSucc {n : ℕ} (c : Fin n → α) (z : α) (j k : Fin n) :
    snoc c z ∘ Equiv.swap j.castSucc k.castSucc = snoc (c ∘ Equiv.swap j k) z := by
  funext i
  refine lastCases ?_ (fun i ↦ ?_) i
  · simp [Equiv.swap_apply_of_ne_of_ne, (castSucc_lt_last j).ne.symm, (castSucc_lt_last k).ne.symm]
  · rw [Function.comp_apply, ← (castSucc_injective n).map_swap j k i]
    simp

/-- Dropping the first entry of `Fin.snoc a x` is appending `x` to the tail of `a`. -/
theorem tail_snoc {n : ℕ} (a : Fin (n + 1) → α) (x : α) :
    tail (snoc a x : Fin (n + 2) → α) = snoc (tail a) x := by
  conv_lhs => rw [← cons_self_tail a, ← cons_snoc_eq_snoc_cons, tail_cons]

/-- Appending the first entry of `a` to its reversed tail is reversing `a`. -/
theorem snoc_tail_comp_rev {α : Type*} {n : ℕ} (a : Fin (n + 1) → α) :
    snoc (tail a ∘ rev) (a 0) = a ∘ rev := by
  rw [← cons_comp_rev, cons_self_tail]

/-- Appending one entry to each of two tuples gives the same equality pattern exactly when the
old patterns agree and the new entries repeat the same positions. -/
theorem forall_snoc_eq_iff_snoc_eq {β : Sort*} {n : ℕ} {a : Fin n → α} {b : Fin n → β} {x : α}
    {y : β} :
    (∀ i j, (snoc a x : Fin (n + 1) → α) i = (snoc a x : Fin (n + 1) → α) j ↔
      (snoc b y : Fin (n + 1) → β) i = (snoc b y : Fin (n + 1) → β) j) ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i, a i = x ↔ b i = y := by
  simp only [Fin.forall_fin_succ', snoc_castSucc, snoc_last, eq_comm (a := x), eq_comm (a := y),
    iff_self, and_true]
  exact ⟨fun h => ⟨fun i => (h.1 i).1, fun i => (h.1 i).2⟩,
    fun h => ⟨fun i => ⟨h.1 i, h.2 i⟩, h.2⟩⟩

/-- Updating `Fin.append u v` at a position of `u` is appending the updated `u` to `v`. -/
@[simp]
theorem update_append_castAdd {n : ℕ} (u : Fin m → α) (v : Fin n → α) (i : Fin m) (a : α) :
    Function.update (append u v) (castAdd n i) a = append (Function.update u i a) v :=
  funext fun j ↦ addCases (fun j ↦ by simp [Function.update_apply])
    (fun j ↦ by
      rw [Function.update_of_ne fun h ↦ by simp [Fin.ext_iff] at h; omega]
      simp) j

/-- Updating `Fin.append u v` at a position of `v` is appending `u` to the updated `v`. -/
@[simp]
theorem update_append_natAdd {n : ℕ} (u : Fin m → α) (v : Fin n → α) (i : Fin n) (a : α) :
    Function.update (append u v) (natAdd m i) a = append u (Function.update v i a) :=
  funext fun j ↦ addCases (fun j ↦ by
      rw [Function.update_of_ne fun h ↦ by simp [Fin.ext_iff] at h; omega]
      simp)
    (fun j ↦ by simp [Function.update_apply]) j

/-- Exchanging two entries of `Fin.append u v` at positions of `u` is appending `v` to `u` with
those entries exchanged. -/
theorem append_comp_swap_castAdd {n : ℕ} (u : Fin m → α) (v : Fin n → α) (j k : Fin m) :
    append u v ∘ Equiv.swap (castAdd n j) (castAdd n k) = append (u ∘ Equiv.swap j k) v :=
  funext fun i ↦ addCases
    (fun i ↦ by rw [Function.comp_apply, ← (castAdd_injective m n).map_swap j k i]; simp)
    (fun i ↦ by
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (fun h ↦ by simp [Fin.ext_iff] at h; omega) (fun h ↦ by simp [Fin.ext_iff] at h; omega)]
      simp) i

/-- Exchanging two entries of `Fin.append u v` at positions of `v` is prepending `u` to `v` with
those entries exchanged. -/
theorem append_comp_swap_natAdd {n : ℕ} (u : Fin m → α) (v : Fin n → α) (j k : Fin n) :
    append u v ∘ Equiv.swap (natAdd m j) (natAdd m k) = append u (v ∘ Equiv.swap j k) :=
  funext fun i ↦ addCases
    (fun i ↦ by
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (fun h ↦ by simp [Fin.ext_iff] at h; omega) (fun h ↦ by simp [Fin.ext_iff] at h; omega)]
      simp)
    (fun i ↦ by rw [Function.comp_apply, ← (natAdd_injective n m).map_swap j k i]; simp) i

section ContractNth

variable {n : ℕ} (op : α → α → α)

/-- Contracting two adjacent entries after the first commutes with dropping the first entry. -/
theorem tail_contractNth_succ (j : Fin (n + 1)) (a : Fin (n + 2) → α) :
    tail (contractNth j.succ op a) = contractNth j op (tail a) := by
  funext k
  simp only [tail, contractNth, val_succ, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff,
    succ_castSucc]

/-- Contracting two adjacent entries before the last commutes with dropping the last entry. -/
theorem init_contractNth_castSucc (j : Fin (n + 1)) (a : Fin (n + 2) → α) :
    init (contractNth j.castSucc op a) = contractNth j op (init a) := by
  funext k
  simp only [init, contractNth, val_castSucc, succ_castSucc]

/-- Contracting the first two entries of `Fin.cons x a` combines `x` with the first entry of `a`
under `op`. -/
theorem contractNth_zero_cons (x : α) (a : Fin (n + 1) → α) :
    contractNth 0 op (cons x a) = cons (op x (a 0)) (tail a) := by
  funext k
  cases k using Fin.cases with
  | zero => rfl
  | succ k => rfl

/-- Contracting two entries of `Fin.cons x a` other than the first contracts `a`. -/
theorem contractNth_succ_cons (j : Fin (n + 1)) (x : α) (a : Fin (n + 1) → α) :
    contractNth j.succ op (cons x a) = cons x (contractNth j op a) := by
  rw [← cons_self_tail (contractNth j.succ op (cons x a)), tail_contractNth_succ, tail_cons,
    contractNth_apply_of_lt _ _ _ _ (Nat.succ_pos _), castSucc_zero, cons_zero]

/-- Contracting the last two entries and dropping the last one drops the last two entries. -/
theorem init_contractNth_castSucc_last (a : Fin (n + 2) → α) :
    init (contractNth (last n).castSucc op a) = init (init a) := by
  funext k
  simp only [init, contractNth, val_castSucc, val_last, k.is_lt, ↓reduceIte]

/-- Contracting at the last position, which has no successor, drops the last entry. -/
@[simp]
theorem contractNth_last (a : Fin (n + 1) → α) : contractNth (last n) op a = init a := by
  funext k
  rw [contractNth_apply_of_lt _ _ _ _ (by simp), init]

/-- A contraction not involving the last entry keeps the last entry. -/
@[simp]
theorem contractNth_castSucc_castSucc_apply_last (j : Fin n) (a : Fin (n + 2) → α) :
    contractNth j.castSucc.castSucc op a (last n) = a (last (n + 1)) := by
  rw [contractNth_apply_of_gt _ _ _ _ (by simp [j.isLt]), succ_last]

/-- Contracting the last two entries makes their product the last entry. -/
@[simp]
theorem contractNth_castSucc_last_apply_last (a : Fin (n + 2) → α) :
    contractNth (last n).castSucc op a (last n) = op (a (last n).castSucc) (a (last (n + 1))) := by
  rw [contractNth_apply_of_eq _ _ _ _ (by simp), succ_last]

/-- Contracting two entries of `Fin.snoc a x` other than the last contracts `a`. -/
theorem contractNth_castSucc_castSucc_snoc (j : Fin n) (a : Fin (n + 1) → α) (x : α) :
    contractNth j.castSucc.castSucc op (snoc a x) = snoc (contractNth j.castSucc op a) x := by
  rw [← snoc_init_self (contractNth j.castSucc.castSucc op (snoc a x)),
    init_contractNth_castSucc, init_snoc, contractNth_castSucc_castSucc_apply_last, snoc_last]

/-- Contracting the last two entries of `Fin.snoc a x` combines the last entry of `a` with `x`
under `op`. -/
theorem contractNth_castSucc_last_snoc (a : Fin (n + 1) → α) (x : α) :
    contractNth (last n).castSucc op (snoc a x) = snoc (init a) (op (a (last n)) x) := by
  rw [← snoc_init_self (contractNth (last n).castSucc op (snoc a x)),
    init_contractNth_castSucc_last, init_snoc, contractNth_castSucc_last_apply_last,
    snoc_castSucc, snoc_last]

/-- Contracting the entries `j` and `j + 1` is deleting entry `j + 1` and then overwriting
entry `j` by the contraction. -/
theorem contractNth_castSucc_eq_update_removeNth_succ (j : Fin (n + 1)) (a : Fin (n + 2) → α) :
    contractNth j.castSucc op a =
      Function.update (removeNth j.succ a) j (op (a j.castSucc) (a j.succ)) := by
  funext k
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · rw [Function.update_of_ne hkj.ne, contractNth_apply_of_lt _ _ _ _ hkj, removeNth_apply,
      succAbove_of_castSucc_lt _ _ (by simpa using hkj.le)]
  · rw [Function.update_self, contractNth_apply_of_eq _ _ _ _ rfl]
  · rw [Function.update_of_ne hkj.ne', contractNth_apply_of_gt _ _ _ _ hkj, removeNth_apply,
      succAbove_of_lt_succ _ _ (by simpa using hkj)]

/-- Contracting two adjacent entries of a constant tuple overwrites one entry of the shorter
constant tuple by the contraction. -/
theorem contractNth_castSucc_const (j : Fin n) (x : α) :
    contractNth j.castSucc op (fun _ => x) = Function.update (fun _ => x) j (op x x) := by
  funext k
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · rw [Function.update_of_ne hkj.ne, contractNth_apply_of_lt _ _ _ _ hkj]
  · rw [Function.update_self, contractNth_apply_of_eq _ _ _ _ rfl]
  · rw [Function.update_of_ne hkj.ne', contractNth_apply_of_gt _ _ _ _ hkj]

end ContractNth

/-- Deleting entry `j + 1` and then overwriting entry `j` by the deleted entry is deleting
entry `j`. -/
theorem update_removeNth_succ_eq_removeNth_castSucc {n : ℕ} (j : Fin (n + 1))
    (a : Fin (n + 2) → α) :
    Function.update (removeNth j.succ a) j (a j.succ) = removeNth j.castSucc a := by
  funext k
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · rw [Function.update_of_ne hkj.ne, removeNth_apply, removeNth_apply,
      succAbove_of_castSucc_lt _ _ (by simpa using hkj.le),
      succAbove_of_castSucc_lt _ _ (by simpa using hkj)]
  · rw [Function.update_self, removeNth_apply, succAbove_castSucc_self]
  · rw [Function.update_of_ne hkj.ne', removeNth_apply, removeNth_apply,
      succAbove_of_lt_succ _ _ (by simpa using hkj),
      succAbove_of_le_castSucc _ _ (by simpa using hkj.le)]

/-- Inserting at a position other than the first keeps the first entry. -/
@[simp]
theorem insertNth_apply_zero_of_ne_zero {β : Type*} {n : ℕ} {p : Fin (n + 2)} (hp : p ≠ 0)
    (v : β) (x : Fin (n + 1) → β) : insertNth (α := fun _ => β) p v x 0 = x 0 := by
  rw [← succAbove_ne_zero_zero hp, insertNth_apply_succAbove]

/-- Inserting at a position other than the last keeps the last entry. -/
@[simp]
theorem insertNth_apply_last_of_ne_last {β : Type*} {n : ℕ} {p : Fin (n + 2)}
    (hp : p ≠ last (n + 1)) (v : β) (x : Fin (n + 1) → β) :
    insertNth (α := fun _ => β) p v x (last (n + 1)) = x (last n) := by
  rw [← succAbove_ne_last_last hp, insertNth_apply_succAbove]

/-- **Contracting along a path with an inserted vertex.** Let `f k` be a function of the two
endpoints of the `k`-th step of a path. Along the path obtained from `x` by inserting `v` after
`xₗ`, contracting the steps `l` and `l + 1` gives the entries `f ((l + 1).succAbove k)` read
along `x`, except in position `l`, which holds `op (f l xₗ v) (f (l + 1) v xₗ₊₁)`. -/
theorem contractNth_castSucc_insertNth_succ_castSucc {β γ : Sort*} {n : ℕ} (op : γ → γ → γ)
    (l : Fin n) (f : Fin (n + 1) → β → β → γ) (x : Fin (n + 1) → β) (v : β) :
    contractNth l.castSucc op (fun k => f k
        (insertNth (α := fun _ => β) l.succ.castSucc v x k.castSucc)
        (insertNth (α := fun _ => β) l.succ.castSucc v x k.succ)) =
      Function.update (fun k => f (l.succ.succAbove k) (x k.castSucc) (x k.succ)) l
        (op (f l.castSucc (x l.castSucc) v) (f l.succ v (x l.succ))) := by
  funext k
  rcases lt_trichotomy k l with h | rfl | h
  · rw [contractNth_apply_of_lt _ _ _ _ h, Function.update_of_ne h.ne,
      succAbove_of_castSucc_lt _ _ (by simpa using h.le)]
    have h₁ : k.castSucc.castSucc < l.succ.castSucc := lt_def.mpr (by simp; omega)
    have h₂ : k.succ.castSucc < l.succ.castSucc := lt_def.mpr (by simp; omega)
    rw [← succAbove_of_castSucc_lt _ _ h₁, succ_castSucc k, ← succAbove_of_castSucc_lt _ _ h₂,
      insertNth_apply_succAbove, insertNth_apply_succAbove]
  · rw [contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self]
    have h₁ : k.castSucc.castSucc < k.succ.castSucc := lt_def.mpr (by simp)
    rw [← succAbove_of_castSucc_lt _ _ h₁, succ_castSucc k,
      ← succAbove_of_le_castSucc k.succ.castSucc k.succ le_rfl, insertNth_apply_same,
      insertNth_apply_succAbove, insertNth_apply_succAbove]
  · rw [contractNth_apply_of_gt _ _ _ _ h, Function.update_of_ne h.ne',
      succAbove_of_le_castSucc _ _ (by simpa using h)]
    have h₁ : l.succ.castSucc ≤ k.castSucc.castSucc := le_def.mpr (by simp; omega)
    have h₂ : l.succ.castSucc ≤ k.succ.castSucc := le_def.mpr (by simp; omega)
    rw [← succ_castSucc k, ← succAbove_of_le_castSucc _ _ h₁, ← succAbove_of_le_castSucc _ _ h₂,
      insertNth_apply_succAbove, insertNth_apply_succAbove]

/-- Deleting an entry of `Fin.cons x a` other than the first deletes the corresponding entry
of `a`. -/
theorem removeNth_succ_cons {n : ℕ} (j : Fin (n + 1)) (x : α) (a : Fin (n + 1) → α) :
    removeNth j.succ (cons x a : Fin (n + 2) → α) = cons x (removeNth j a) := by
  funext k
  cases k using Fin.cases <;> simp [removeNth_apply]

/-- The image of the first `n + 1` entries of a prepended tuple consists of its first entry
and the image of the first `n` entries of its tail. -/
@[simp]
theorem image_cons_le_eq_insert {α : Type*} {n : ℕ} (x : α) (p : Fin m → α) :
    Fin.cons x p '' {index | (index : ℕ) ≤ n} =
      insert x (p '' {index | (index : ℕ) < n}) := by
  ext element
  simp [Set.mem_image, Fin.exists_fin_succ, eq_comm, Nat.add_one_le_iff]

/-- Inserting the entry `1` into a tuple gives a tuple that does not vanish. -/
theorem insertNth_one_ne_zero {α : Type*} [Zero α] [One α] [NeZero (1 : α)] {n : ℕ}
    (i : Fin (n + 1)) (z : Fin n → α) : insertNth (α := fun _ ↦ α) i 1 z ≠ 0 :=
  fun h ↦ one_ne_zero (α := α) (by simpa using congr_fun h i)

/-- A tuple of length three is determined by its three entries. -/
theorem injective_apply_zero_one_two {α : Type*} :
    Function.Injective fun x : Fin 3 → α ↦ (x 0, x 1, x 2) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  funext m
  match m with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | 2 => exact h.2.2


/-- If deleting the entry at `q` leaves an injective tuple, two positions other than `q` holding
the same entry are equal. -/
theorem eq_of_injective_comp_succAbove {n : ℕ} {b : Fin (n + 1) → α} {q : Fin (n + 1)}
    (hq : Function.Injective (b ∘ q.succAbove)) {i j : Fin (n + 1)} (hi : i ≠ q) (hj : j ≠ q)
    (h : b i = b j) : i = j := by
  obtain ⟨i, rfl⟩ := exists_succAbove_eq hi
  obtain ⟨j, rfl⟩ := exists_succAbove_eq hj
  exact congrArg _ (hq h)

/-- If `b p = b q`, deleting the entry at `p` leaves an injective tuple exactly when
deleting the entry at `q` does. -/
theorem injective_comp_succAbove_of_eq {n : ℕ} {b : Fin (n + 1) → α} {p q : Fin (n + 1)}
    (h : b p = b q) (hp : Function.Injective (b ∘ p.succAbove)) :
    Function.Injective (b ∘ q.succAbove) := by
  obtain rfl | hpq := eq_or_ne p q
  · exact hp
  intro x y hxy
  have key (z : Fin (n + 1)) :
      (if z = p then q else z) ≠ p ∧ b (if z = p then q else z) = b z := by
    split_ifs with hzp
    · exact ⟨hpq.symm, hzp ▸ h.symm⟩
    · exact ⟨hzp, rfl⟩
  have hx := key (q.succAbove x)
  have hy := key (q.succAbove y)
  have := eq_of_injective_comp_succAbove hp hx.1 hy.1 (hx.2.trans (hxy.trans hy.2.symm))
  refine succAbove_right_injective (p := q) ?_
  split_ifs at this with h₁ h₂ h₂
  · exact h₁.trans h₂.symm
  · exact absurd this.symm (succAbove_ne q y)
  · exact absurd this (succAbove_ne q x)
  · exact this

/-- If `b p = b q` for `p ≠ q`, deleting the entry at `p` does not change the set of entries. -/
theorem range_comp_succAbove_of_eq {α : Type*} {n : ℕ} {b : Fin (n + 1) → α}
    {p q : Fin (n + 1)} (hpq : p ≠ q) (h : b p = b q) :
    Set.range (b ∘ p.succAbove) = Set.range b := by
  refine (Set.range_comp_subset_range _ _).antisymm ?_
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = p
  · obtain ⟨z, hz⟩ := exists_succAbove_eq hpq.symm
    exact ⟨z, by simp [hz, hi, h]⟩
  · obtain ⟨z, hz⟩ := exists_succAbove_eq hi
    exact ⟨z, by simp [hz]⟩

/-- A tuple in `α ⊕ β` that starts in `α`, ends in `β` and never steps from `β` back to `α` steps
from `α` to `β` at exactly one position. -/
theorem existsUnique_isLeft_castSucc_and_isRight_succ {α β : Type*} {n : ℕ}
    (x : Fin (n + 1) → α ⊕ β) (h0 : (x 0).isLeft) (hlast : (x (last n)).isRight)
    (hstep : ∀ l : Fin n, (x l.castSucc).isRight → (x l.succ).isRight) :
    ∃! l : Fin n, (x l.castSucc).isLeft ∧ (x l.succ).isRight := by
  -- The level `0` on `α` and `1` on `β` is monotone along the tuple.
  set v : Fin (n + 1) → ℕ := fun k => if (x k).isLeft then 0 else 1 with hv
  have hmono : Monotone v := monotone_iff_le_succ.mpr fun l => by
    by_cases h : (x l.castSucc).isLeft
    · simp [hv, h]
    · have := hstep l (by simpa using h)
      simp [hv, h, Sum.not_isLeft.mpr this]
  have hcross (l : Fin n) : (x l.castSucc).isLeft → (x l.succ).isRight →
      v l.castSucc = 0 ∧ v l.succ = 1 := fun h₁ h₂ => by
    simp [hv, h₁, Sum.not_isLeft.mpr h₂]
  obtain ⟨l₀, h₁, h₂⟩ : ∃ l₀ : Fin n, (x l₀.castSucc).isLeft ∧ (x l₀.succ).isRight := by
    by_contra! hne
    have hleft (k : Fin (n + 1)) : (x k).isLeft := by
      induction k using Fin.induction with
      | zero => exact h0
      | succ k ih => simpa using hne k ih
    exact absurd (hleft (last n)) (Sum.not_isLeft.mpr hlast)
  refine ⟨l₀, ⟨h₁, h₂⟩, fun l ⟨hl₁, hl₂⟩ => ?_⟩
  obtain ⟨hv₁, hv₂⟩ := hcross l hl₁ hl₂
  obtain ⟨hv₀₁, hv₀₂⟩ := hcross l₀ h₁ h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono (castSucc_lt_iff_succ_le.mp (castSucc_lt_castSucc_iff.mpr h))
    omega
  · have := hmono (castSucc_lt_iff_succ_le.mp (castSucc_lt_castSucc_iff.mpr h))
    omega

end Fin
