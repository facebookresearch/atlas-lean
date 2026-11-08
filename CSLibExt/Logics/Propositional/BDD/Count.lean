/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting satisfying assignments of a BDD
-/
module

public import CSLibExt.Logics.Propositional.BDD.Basic

/-!
# Counting satisfying assignments of a BDD

Bryant's satisfy-count: the number of assignments to the variables `0, …, m - 1`
that make an ordered diagram true, computed in one pass over the tree. A node
testing `v` reached with `n` as the next unaccounted variable contributes a
factor `2 ^ (v - n)` for the skipped variables `n, …, v - 1`; a leaf `true`
reached at `n` contributes `2 ^ (m - n)`.

The specification `countModels xs f σ` enumerates the assignments directly: it
tries both values of every variable of `xs` in turn, starting from `σ`, and counts
those on which `f` is true.

## Main definitions

- `BDD.VarsLT m t` : every variable tested in `t` is below `m`.
- `BDD.satCountFrom m n t`, `BDD.satCount m t` : the one-pass count.
- `BDD.countModels xs f σ` : the specification by enumeration.

## Main results

- `BDD.satCount_eq_countModels` : for `t` ordered and with variables below `m`,
  `satCount m t = countModels (List.range m) (eval · t) σ` for every `σ`.

## References

- R. E. Bryant, *Graph-based algorithms for Boolean function manipulation*,
  IEEE Trans. Computers C-35(8), 1986, 677-691 (§4.6, satisfy-count).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Logic.PL.BDD

/-- Every variable tested in the diagram is below `m`. -/
def VarsLT (m : Nat) : BDD → Prop
  | leaf _ => True
  | node v lo hi => v < m ∧ VarsLT m lo ∧ VarsLT m hi

/-- The number of assignments to the variables `n, …, m - 1` that make `t` true, for `t`
ordered from `n` with variables below `m`. -/
def satCountFrom (m : Nat) : Nat → BDD → Nat
  | n, leaf b => if b then 2 ^ (m - n) else 0
  | n, node v lo hi => 2 ^ (v - n) * (satCountFrom m (v + 1) lo + satCountFrom m (v + 1) hi)

/-- The number of assignments to the variables `0, …, m - 1` that make `t` true. -/
def satCount (m : Nat) (t : BDD) : Nat := satCountFrom m 0 t

/-- The number of ways to assign the variables of `xs`, starting from `σ`, that make `f`
true: both values of each variable are tried in turn. -/
def countModels : List Nat → ((Nat → Bool) → Bool) → (Nat → Bool) → Nat
  | [], f, σ => if f σ then 1 else 0
  | x :: xs, f, σ =>
    countModels xs f (Function.update σ x false) + countModels xs f (Function.update σ x true)

/-- `countModels xs f σ` only looks at `f` on assignments that agree with `σ` off `xs`. -/
theorem countModels_congr {xs : List Nat} {f g : (Nat → Bool) → Bool} {σ : Nat → Bool}
    (h : ∀ τ : Nat → Bool, (∀ x, x ∉ xs → τ x = σ x) → f τ = g τ) :
    countModels xs f σ = countModels xs g σ := by
  induction xs generalizing σ with
  | nil => simp [countModels, h σ fun _ _ ↦ rfl]
  | cons y ys ih =>
    have key : ∀ b, countModels ys f (Function.update σ y b) =
        countModels ys g (Function.update σ y b) := fun b ↦ ih fun τ hτ ↦ h τ fun x hx ↦ by
      have hxy : x ≠ y := fun e ↦ hx (e ▸ List.mem_cons_self ..)
      rw [hτ x fun hx' ↦ hx (List.mem_cons_of_mem _ hx'), Function.update_of_ne hxy]
    simp only [countModels, key]

/-- Enumerating the variables `n, …, m - 1` counts what `satCountFrom` computes. -/
theorem satCountFrom_eq_countModels (m : Nat) :
    ∀ (k n : Nat), m - n = k → ∀ {t : BDD}, OrderedFrom n t → VarsLT m t →
      ∀ σ : Nat → Bool,
        satCountFrom m n t = countModels (List.range' n (m - n)) (fun τ ↦ t.eval τ) σ := by
  intro k
  induction k with
  | zero =>
    intro n hk t ht hm σ
    rw [hk]
    cases t with
    | leaf b => cases b <;> simp [satCountFrom, countModels, hk]
    | node v lo hi => exact absurd (ht.1.trans_lt hm.1) (by omega)
  | succ k ih =>
    intro n hk t ht hm σ
    have hrange : List.range' n (m - n) = n :: List.range' (n + 1) (m - (n + 1)) := by
      rw [hk, show m - (n + 1) = k by omega, List.range'_succ]
    have hn : n ∉ List.range' (n + 1) (m - (n + 1)) := by simp [List.mem_range'_1]
    rw [hrange, countModels]
    cases t with
    | leaf b =>
      rw [← ih (n + 1) (by omega) (t := leaf b) trivial trivial,
        ← ih (n + 1) (by omega) (t := leaf b) trivial trivial]
      cases b
      · simp [satCountFrom]
      · simp only [satCountFrom, ite_true, show m - n = (m - (n + 1)) + 1 by omega, Nat.pow_succ,
          Nat.mul_two]
    | node v lo hi =>
      obtain ⟨hv, hlo, hhi⟩ := ht
      obtain ⟨hvm, hmlo, hmhi⟩ := hm
      rcases Nat.eq_or_lt_of_le hv with hnv | hlt
      · -- the node tests `n` itself: each value of `n` selects one child
        subst hnv
        have hsel : ∀ b, countModels (List.range' (n + 1) (m - (n + 1)))
            (fun τ ↦ (node n lo hi).eval τ) (Function.update σ n b) =
            countModels (List.range' (n + 1) (m - (n + 1)))
              (fun τ ↦ (if b then hi else lo).eval τ) (Function.update σ n b) :=
          fun b ↦ countModels_congr fun τ hτ ↦ by
            have : τ n = b := by rw [hτ n hn, Function.update_self]
            cases b <;> simp [this]
        rw [hsel false, hsel true]
        simp only [Bool.false_eq_true, ite_false, ite_true]
        rw [← ih (n + 1) (by omega) hlo hmlo, ← ih (n + 1) (by omega) hhi hmhi]
        simp [satCountFrom]
      · -- the node tests a later variable: `n` is free, and doubles the count
        have ht' : OrderedFrom (n + 1) (node v lo hi) := ⟨by omega, hlo, hhi⟩
        rw [← ih (n + 1) (by omega) ht' ⟨hvm, hmlo, hmhi⟩,
          ← ih (n + 1) (by omega) ht' ⟨hvm, hmlo, hmhi⟩]
        simp only [satCountFrom, show v - n = (v - (n + 1)) + 1 by omega, Nat.pow_succ]
        rw [Nat.mul_right_comm, Nat.mul_two]

/-- **Satisfy-count**: for a diagram ordered from `0` whose variables are below `m`,
`satCount m t` is the number of assignments to `0, …, m - 1` that make it true. -/
theorem satCount_eq_countModels {m : Nat} {t : BDD} (ht : OrderedFrom 0 t) (hm : VarsLT m t)
    (σ : Nat → Bool) :
    satCount m t = countModels (List.range m) (fun τ ↦ t.eval τ) σ := by
  rw [satCount, satCountFrom_eq_countModels m _ 0 rfl ht hm σ, List.range_eq_range']
  simp

end Cslib.Logic.PL.BDD
