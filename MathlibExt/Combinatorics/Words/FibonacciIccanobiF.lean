/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.Iterate
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
import Mathlib.Data.Nat.Init

/-!
# Fibonacci and iccanobiF iterates of a

With `a` encoded by `true`, the Fibonacci morphism `F` and the backward morphism `B` satisfy
`F(w)a = aB(w)`. Applying `B` to either conjugacy identity and cancelling the final `a` gives
the identity for the next iterate.
-/

namespace MetaMathlibExt

namespace fibonacci_iccanobiF_conjugate_a

private def backwardMorph (w : List Bool) : List Bool :=
  w.flatMap fun x => if x then [false, true] else [true]

private theorem backwardMorph_append (u v : List Bool) :
    backwardMorph (u ++ v) = backwardMorph u ++ backwardMorph v :=
  List.flatMap_append

private theorem fibMorph_append_a (w : List Bool) :
    (fibMorph w).map (!·) ++ [true] = [true] ++ backwardMorph (w.map (!·)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x
    · exact congrArg ([true, false] ++ ·) ih
    · exact congrArg (true :: ·) ih

private theorem step {u v : List Bool} (hu : backwardMorph u = v ++ [true])
    (hv : backwardMorph v = u ++ [true]) {k : ℕ}
    (h : u ++ (fibWord k).map (!·) = backwardMorph^[k] [true] ++ v) :
    v ++ (fibWord (k + 1)).map (!·) = backwardMorph^[k + 1] [true] ++ u := by
  apply List.append_cancel_right (bs := [true])
  simpa only [fibWord, List.append_assoc, fibMorph_append_a, Function.iterate_succ_apply',
    backwardMorph_append, hu, hv] using congrArg backwardMorph h

end fibonacci_iccanobiF_conjugate_a

open fibonacci_iccanobiF_conjugate_a in
/-- **Fibonacci and iccanobiF iterates of a.** Let $\varrho_F$ be the Fibonacci substitution
$a \mapsto ab$, $b \mapsto a$ and let $\varrho_F'$ be the iccanobiF substitution $a \mapsto ba$,
$b \mapsto a$, acting on finite words over the letters $a$ and $b$; thus $\varrho_F^m(a)$ is the
finite Fibonacci word $f_m$ with each $0$ written as $a$ and each $1$ as $b$. Then for every
$n \ge 1$, $ab\,\varrho_F^{2n}(a) = (\varrho_F')^{2n}(a)\,ba$ and
$ba\,\varrho_F^{2n-1}(a) = (\varrho_F')^{2n-1}(a)\,ab$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 51
(`jis-2025-25.1.5-prop-51`). -/
public theorem fibonacci_iccanobiF_conjugate_a (n : ℕ) (hn : 1 ≤ n) :
    [true, false] ++ (fibWord (2 * n)).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 *
        n] [true] ++ [false, true] ∧
      [false, true] ++ (fibWord (2 * n - 1)).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 * n -
            1] [true] ++ [true, false] := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ n hn ih =>
    have odd := step (u := [true, false]) (v := [false, true]) rfl rfl ih.1
    have even := step rfl rfl odd
    exact ⟨even, odd⟩

end MetaMathlibExt
