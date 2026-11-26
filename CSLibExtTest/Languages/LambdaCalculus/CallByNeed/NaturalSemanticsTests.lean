/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CallByNeed.NaturalSemantics

/-!
# Tests for the call-by-need natural semantics

Names are natural numbers. Each test of sharing, of Launchbury's examples and of mutual
recursion gives one evaluation from the empty heap and then uses `Eval.unique_up_to_renaming` to
show that every evaluation has the same value and the same number of additions.

* Sharing: `let u = 3 + 2 in u + u` performs 2 additions, and its final heap binds one new name
  to `5`, while `(3 + 2) + (3 + 2)` performs 3, so the shared `3 + 2` is computed once.
* Launchbury's examples: `let u = 3 + 2, v = u + 1 in v + v` gives `12` with 3 additions and a
  final heap binding `6` and `5`; the program applying `f = λx. (let v = u + 1 in v + x)` to `2`
  and `3` gives `17` with 6 additions, and with `v` floated out of `f` it gives `17` with 5.
* A mutually recursive `let` of three bindings, two of which refer to each other, evaluates to
  an abstraction without additions.
* Negative controls: the black hole `let x = x in x`, an unbound variable, a numeral applied to a
  variable and an abstraction added to a numeral have no evaluation.
* Capture boundary: in a heap binding `p` to `7` and `q` to `2`, the closed configuration
  `((λx. λp. x) p) q`, whose inner binder is also bound in the heap, evaluates to `2` on every
  evaluation, because naive substitution captures the argument `p`; with the inner binder renamed
  to a fresh name it evaluates to `7`.
-/

namespace Cslib.Languages.LambdaCalculus.CallByNeedTests

open Cslib.Languages.LambdaCalculus.CallByNeed

/-! ### Sharing -/

/-- `let u = 3 + 2 in u + u`, with `u` named `0`. -/
def share : Expr ℕ :=
  .letrec (.cons 0 (.add (.num 3) (.num 2)) .nil) (.add (.var 0) (.var 0))

/-- One evaluation of `share`: the new name `1` is bound to `3 + 2`, which is evaluated once
and updated to `5`. -/
theorem share_eval : Eval ∅ [] share [(1, .num 5)] (.num 10) 2 := by
  have h : Eval ∅ [] share _ _ _ :=
    .letrec [1] (by decide) (by decide) (by decide) (by decide)
      (.add (.var rfl (.add .num .num)) (.var rfl .num))
  exact h

/-- Every evaluation of `share` returns `10`, performs exactly 2 additions, and ends with a
single binding, of a new name to `5`. -/
theorem share_unique (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) (h : Eval ∅ [] share Δ w n) :
    w = .num 10 ∧ n = 2 ∧ ∃ p, Δ = [(p, .num 5)] := by
  obtain ⟨hn, π, -, hΔ, hw⟩ := share_eval.unique_up_to_renaming h (by unfold Closed; decide)
  exact ⟨hw, hn.symm, π 1, hΔ⟩

/-- `(3 + 2) + (3 + 2)`, the same computation without sharing. -/
def unshared : Expr ℕ :=
  .add (.add (.num 3) (.num 2)) (.add (.num 3) (.num 2))

/-- One evaluation of `unshared`. -/
theorem unshared_eval : Eval ∅ [] unshared [] (.num 10) 3 := by
  have h : Eval ∅ [] unshared _ _ _ := .add (.add .num .num) (.add .num .num)
  exact h

/-- Every evaluation of `unshared` returns `10` and performs 3 additions. -/
theorem unshared_unique (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) (h : Eval ∅ [] unshared Δ w n) :
    w = .num 10 ∧ n = 3 := by
  obtain ⟨hn, π, -, -, hw⟩ := unshared_eval.unique_up_to_renaming h (by unfold Closed; decide)
  exact ⟨hw, hn.symm⟩

/-! ### Launchbury's examples -/

/-- `let u = 3 + 2, v = u + 1 in v + v`, with `u` and `v` named `0` and `1`. -/
def lb4 : Expr ℕ :=
  .letrec (.cons 0 (.add (.num 3) (.num 2)) (.cons 1 (.add (.var 0) (.num 1)) .nil))
    (.add (.var 1) (.var 1))

/-- One evaluation of `lb4`, with `u` and `v` allocated as `2` and `3`. -/
theorem lb4_eval : Eval ∅ [] lb4 [(3, .num 6), (2, .num 5)] (.num 12) 3 := by
  have h : Eval ∅ [] lb4 _ _ _ :=
    .letrec [2, 3] (by decide) (by decide) (by decide) (by decide)
      (.add (.var rfl (.add (.var rfl (.add .num .num)) .num)) (.var rfl .num))
  exact h

/-- Every evaluation of `lb4` returns `12`, performs 3 additions, and ends with two bindings,
to `6` and to `5`. -/
theorem lb4_unique (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) (h : Eval ∅ [] lb4 Δ w n) :
    w = .num 12 ∧ n = 3 ∧ List.map Prod.snd Δ = [.num 6, .num 5] := by
  obtain ⟨hn, π, -, hΔ, hw⟩ := lb4_eval.unique_up_to_renaming h (by unfold Closed; decide)
  subst hΔ
  exact ⟨hw, hn.symm, rfl⟩

/-- `let u = 3 + 2, f = λx. (let v = u + 1 in v + x), a = 2, b = 3 in f a + f b`, with `u`,
`f`, `x`, `v`, `a` and `b` named `0` to `5`: `v` is recomputed at each call of `f`. -/
def fInside : Expr ℕ :=
  .letrec
    (.cons 0 (.add (.num 3) (.num 2))
      (.cons 1 (.lam 2 (.letrec (.cons 3 (.add (.var 0) (.num 1)) .nil) (.add (.var 3) (.var 2))))
        (.cons 4 (.num 2) (.cons 5 (.num 3) .nil))))
    (.add (.app (.var 1) 4) (.app (.var 1) 5))

/-- One evaluation of `fInside`. -/
theorem fInside_eval : ∃ Δ, Eval ∅ [] fInside Δ (.num 17) 6 := by
  have h : Eval ∅ [] fInside _ _ _ :=
    .letrec [6, 7, 8, 9] (by decide) (by decide) (by decide) (by decide)
      (.add
        (.app (.var rfl .lam)
          (.letrec [10] (by decide) (by decide) (by decide) (by decide)
            (.add (.var rfl (.add (.var rfl (.add .num .num)) .num)) (.var rfl .num))))
        (.app (.var rfl .lam)
          (.letrec [11] (by decide) (by decide) (by decide) (by decide)
            (.add (.var rfl (.add (.var rfl .num) .num)) (.var rfl .num)))))
  exact ⟨_, h⟩

/-- Every evaluation of `fInside` returns `17` and performs 6 additions. -/
theorem fInside_unique (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) (h : Eval ∅ [] fInside Δ w n) :
    w = .num 17 ∧ n = 6 := by
  obtain ⟨Δ₀, h₀⟩ := fInside_eval
  obtain ⟨hn, π, -, -, hw⟩ := h₀.unique_up_to_renaming h (by unfold Closed; decide)
  exact ⟨hw, hn.symm⟩

/-- `let u = 3 + 2, v = u + 1, f = λx. v + x, a = 2, b = 3 in f a + f b`, with `u`, `v`, `f`,
`x`, `a` and `b` named `0` to `5`: `v` is floated out of `f` and computed once. -/
def fOutside : Expr ℕ :=
  .letrec
    (.cons 0 (.add (.num 3) (.num 2))
      (.cons 1 (.add (.var 0) (.num 1))
        (.cons 2 (.lam 3 (.add (.var 1) (.var 3)))
          (.cons 4 (.num 2) (.cons 5 (.num 3) .nil)))))
    (.add (.app (.var 2) 4) (.app (.var 2) 5))

/-- One evaluation of `fOutside`. -/
theorem fOutside_eval : ∃ Δ, Eval ∅ [] fOutside Δ (.num 17) 5 := by
  have h : Eval ∅ [] fOutside _ _ _ :=
    .letrec [6, 7, 8, 9, 10] (by decide) (by decide) (by decide) (by decide)
      (.add
        (.app (.var rfl .lam)
          (.add (.var rfl (.add (.var rfl (.add .num .num)) .num)) (.var rfl .num)))
        (.app (.var rfl .lam) (.add (.var rfl .num) (.var rfl .num))))
  exact ⟨_, h⟩

/-- Every evaluation of `fOutside` returns `17` and performs 5 additions. -/
theorem fOutside_unique (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) (h : Eval ∅ [] fOutside Δ w n) :
    w = .num 17 ∧ n = 5 := by
  obtain ⟨Δ₀, h₀⟩ := fOutside_eval
  obtain ⟨hn, π, -, -, hw⟩ := h₀.unique_up_to_renaming h (by unfold Closed; decide)
  exact ⟨hw, hn.symm⟩

/-! ### Mutual recursion -/

/-- `let f = λx. g, g = λy. f, k = 0 in (f k) k`, with `f`, `x`, `g`, `y` and `k` named `0`
to `4`: `f` and `g` refer to each other. -/
def mutualRec : Expr ℕ :=
  .letrec (.cons 0 (.lam 1 (.var 2)) (.cons 2 (.lam 3 (.var 0)) (.cons 4 (.num 0) .nil)))
    (.app (.app (.var 0) 4) 4)

/-- One evaluation of `mutualRec`, with `f`, `g` and `k` allocated as `5`, `6` and `7`: `f k`
looks up `g`, and applying its value to `k` looks up `f` again. -/
theorem mutualRec_eval :
    Eval ∅ [] mutualRec [(5, .lam 1 (.var 6)), (6, .lam 3 (.var 5)), (7, .num 0)]
      (.lam 1 (.var 6)) 0 := by
  have h : Eval ∅ [] mutualRec _ _ _ :=
    .letrec [5, 6, 7] (by decide) (by decide) (by decide) (by decide)
      (.app (.app (.var rfl .lam) (.var rfl .lam)) (.var rfl .lam))
  exact h

/-- Every evaluation of `mutualRec` returns an abstraction whose body is a variable, performs
no addition, and ends with three bindings. -/
theorem mutualRec_unique (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) (h : Eval ∅ [] mutualRec Δ w n) :
    n = 0 ∧ (∃ x q, w = .lam x (.var q)) ∧ Δ.length = 3 := by
  obtain ⟨hn, π, -, hΔ, hw⟩ := mutualRec_eval.unique_up_to_renaming h (by unfold Closed; decide)
  subst hΔ
  exact ⟨hn.symm, ⟨π 1, π 6, hw⟩, rfl⟩

/-! ### Negative controls -/

/-- The black hole `let x = x in x`, with `x` named `0`, has no evaluation: evaluating the new
name removes its binding, and the name is then unbound. -/
theorem blackhole_stuck (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) :
    ¬ Eval ∅ [] (.letrec (.cons 0 (.var 0) .nil) (.var 0)) Δ w n := by
  intro h
  cases h with
  | letrec ps _ _ hlen _ h =>
    match ps, hlen with
    | [p], _ =>
      cases h with
      | var hl h =>
        simp [Binds.alloc, Binds.exprs, Binds.vars, Expr.subst, Heap.lookup] at hl
        subst hl
        cases h with
        | var hl _ => simp [Binds.alloc, Binds.exprs, Binds.vars, Expr.subst, Heap.lookup,
            Heap.erase] at hl

/-- An unbound variable has no evaluation. -/
theorem unbound_stuck (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) : ¬ Eval ∅ [] (.var 0) Δ w n := by
  intro h
  cases h with
  | var hl _ => simp [Heap.lookup] at hl

/-- A numeral applied to a variable has no evaluation. -/
theorem numApp_stuck (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) : ¬ Eval ∅ [] (.app (.num 1) 0) Δ w n := by
  intro h
  cases h with
  | app h _ => cases h

/-- An abstraction added to a numeral has no evaluation. -/
theorem lamAdd_stuck (Δ : Heap ℕ) (w : Expr ℕ) (n : ℕ) :
    ¬ Eval ∅ [] (.add (.lam 0 (.var 0)) (.num 1)) Δ w n := by
  intro h
  cases h with
  | add h _ => cases h

/-! ### Capture boundary -/

/-- Capture outside the good configurations of the source semantics. In the heap binding `p` to
`7` and `q` to `2`, with `x`, `p` and `q` named `0`, `1` and `2`, the configuration
`((λx. λp. x) p) q` is closed, but its inner binder `p` is also bound in the heap. Naive
substitution captures the argument `p` under `λp`, so every evaluation returns `2`, the value of
`q`; with the inner binder renamed to the fresh name `3`, the program returns `7`, the value of
`p`. -/
theorem capture_boundary :
    Eval ∅ [(1, .num 7), (2, .num 2)] (.app (.app (.lam 0 (.lam 1 (.var 0))) 1) 2)
        [(2, .num 2), (1, .num 7)] (.num 2) 0 ∧
      (∀ Δ w n, Eval ∅ [(1, .num 7), (2, .num 2)]
        (.app (.app (.lam 0 (.lam 1 (.var 0))) 1) 2) Δ w n → w = .num 2) ∧
      Eval ∅ [(1, .num 7), (2, .num 2)] (.app (.app (.lam 0 (.lam 3 (.var 0))) 1) 2)
        [(1, .num 7), (2, .num 2)] (.num 7) 0 := by
  have h₁ : Eval ∅ [(1, .num 7), (2, .num 2)] (.app (.app (.lam 0 (.lam 1 (.var 0))) 1) 2)
      [(2, .num 2), (1, .num 7)] (.num 2) 0 := by
    have h : Eval ∅ [(1, .num 7), (2, .num 2)] (.app (.app (.lam 0 (.lam 1 (.var 0))) 1) 2)
        _ _ _ := .app (.app .lam .lam) (.var rfl .num)
    exact h
  refine ⟨h₁, fun Δ w n h => ?_, ?_⟩
  · obtain ⟨-, π, -, -, hw⟩ := h₁.unique_up_to_renaming h (by unfold Closed; decide)
    exact hw
  · have h : Eval ∅ [(1, .num 7), (2, .num 2)] (.app (.app (.lam 0 (.lam 3 (.var 0))) 1) 2)
        _ _ _ := .app (.app .lam .lam) (.var rfl .num)
    exact h

end Cslib.Languages.LambdaCalculus.CallByNeedTests
