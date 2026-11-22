/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.Clocked
public import CSLibExt.Computability.Complexity.Host
public import Mathlib.Tactic.Linarith

/-!
# The clocked universal function is polynomial-time

The clocked universal machine of `Cslib.Turing.Universal.Clocked`, run in the reduction host of
`Cslib.Complexity.Host`, computes the clocked evaluator `Code.evalSteps` on encoded inputs: from
the bits `encIn c x T` (the clock `T` in unary, the input symbols of `x`, and the code `c`) it
writes `encOut (c.evalSteps x T)` within `O(n ^ 2)` steps, `n = |encIn c x T|`. The machine
spends `O(|codeCells c|)` steps per simulated step, so the quadratic bound is
`O((T + 1) · |codeCells c|)` plus the cost of reading the input and writing the output.

The host's `reduction` asks for a component that is correct on every bit list. This file uses the
same host machine but only on the encodings `encIn c x T` (`Host.rprog_run_at`, the host run for a
single input), which is what `TM2ComputableInPolyTime` with the encoding `encIn` requires.

All numbers in `encIn` and `encOut` are in unary: the clock `T`, and also the states, symbols and
actions in the code's cells. So the bound is polynomial in the unary size of the code (the length
of `codeCells c`), not in the size of its binary `Primcodable` encoding; for a fixed code the
running time is linear in `T + |x|`, which is what the time hierarchy theorem needs.

## Main results

- `univComp`: the clocked universal machine as a host component.
- `univTime_le`: its step bound is at most `18 (n + 1) ^ 2`.
- `nonempty_univPolyTime`: `TM2ComputableInPolyTime` for `fun (c, x, T) ↦ c.evalSteps x T`,
  with the input encoding `encIn` and the output encoding `encOut`.

## References

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 1.4 and
  Theorem 3.1 (the time hierarchy theorem, which uses a clocked universal machine).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.Universal.Clocked

open _root_.Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
  Cslib.Complexity.Host

/-- The clocked universal machine as a host component. -/
abbrev univComp : Comp where
  K := K
  Γ := Γ
  finΓ := fun _ ↦ inferInstanceAs (Fintype Bool)
  L := Lab
  prog := prog
  ks := [.Q, .N, .A, .H, .L, .R, .C, .B, .T, .U, .V, .Ck, .X, .P, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- The cells of a list have the sum of the numbers plus one marker per number. -/
private theorem length_cells (l : List ℕ) : (cells l).length = l.sum + l.length := by
  induction l with
  | nil => simp [cells]
  | cons a l ih =>
    simp only [cells, List.flatMap_cons, List.length_append, cell, List.length_replicate,
      List.sum_cons, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- Reading the input symbols costs at most `n + 3` per symbol. -/
private theorem sum_map_add_three (l : List ℕ) :
    (l.map (· + 3)).sum = l.sum + 3 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **The step bound is quadratic** in the length of the input bits. -/
theorem univTime_le (c : Code) (x : List Bool) (T : ℕ) :
    univTime c x T ≤ 18 * ((encIn c x T).length + 1) ^ 2 := by
  set n := (encIn c x T).length
  have hn : n = T + 1 + ((input x).sum + (input x).length) + 1 + (codeCells c).length := by
    simp only [n, encIn, List.length_append, List.length_cons, List.length_reverse, cell,
      List.length_replicate, List.length_nil, length_cells]
    omega
  have hsum : (input x).length ≤ (input x).sum := by
    have : ∀ l : List Bool, (l.map bitSym).length ≤ (l.map bitSym).sum := by
      intro l
      induction l with
      | nil => simp
      | cons b l ih => cases b <;> simp [bitSym] at ih ⊢ <;> omega
    exact this x
  have hlen : (input x).length = x.length := List.length_map _
  have hhead : (input x).headI ≤ 2 := by
    cases x with
    | nil => simp [input]
    | cons b x => cases b <;> simp [input, bitSym]
  have h1 : (T + 1) * (14 * (codeCells c).length + 19) ≤ n * (14 * n + 19) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (x.length + T + 1) * ((codeCells c).length + 3) ≤ n * (n + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hclock : clockTime c T = (T + 1) * (14 * (codeCells c).length + 19) := by
    simp only [clockTime, loopStepTime]
    ring
  simp only [univTime, parseTime, hclock, sum_map_add_three, length_cells]
  nlinarith

/-- The polynomial step bound of the component. -/
noncomputable def univPoly : Polynomial ℕ := Polynomial.C 18 * (Polynomial.X + 1) ^ 2

/-- **The clocked universal function is polynomial-time computable.** A `FinTM2` reads
`encIn c x T` and writes `encOut (c.evalSteps x T)`, in time quadratic in the length of the
input: the component takes at most `univPoly n = 18 (n + 1) ^ 2` steps, and the reduction host
keeps the degree. -/
theorem nonempty_univPolyTime :
    Nonempty (TM2ComputableInPolyTime (fun a : Code × List Bool × ℕ ↦ encIn a.1 a.2.1 a.2.2)
      encOut (fun a ↦ a.1.evalSteps a.2.1 a.2.2)) :=
  ⟨{ tm := rtm univComp .X .O id .pc0 .done
     inputAlphabet := Equiv.refl Bool
     outputAlphabet := Equiv.refl Bool
     time := rtime univComp .X .O id .pc0 .done univPoly
     outputsFun := fun a ↦ by
      have hx : List.map (Equiv.refl Bool).invFun (encIn a.1 a.2.1 a.2.2) =
          encIn a.1 a.2.1 a.2.2 := List.map_id _
      have h := rprog_run_at (c := univComp) (cX := .X) (cO := .O) (gX := id) (start := .pc0)
        (done := .done) (Equiv.refl Bool) (encOut (a.1.evalSteps a.2.1 a.2.2)) univPoly rfl
        (List.map (Equiv.refl Bool).invFun (encIn a.1 a.2.1 a.2.2)) (by
          obtain ⟨v, S', hr, hO⟩ := univ_run a.1 a.2.1 a.2.2
          have hb := univTime_le a.1 a.2.1 a.2.2
          refine ⟨v, S', ?_, by simpa using hO⟩
          rw [hx, List.map_id]
          exact hr.mono (by simpa [univPoly, Polynomial.eval_mul, Polynomial.eval_pow] using hb))
      unfold RunLe at h
      refine ⟨⟨Classical.choose h, ?_⟩, ?_⟩
      · rw [initList_eq, Option.map_some, haltList_eq]
        exact (Classical.choose_spec h).2
      · exact (Classical.choose_spec h).1.trans (le_of_eq (by simp)) }⟩

end Cslib.Turing.Universal.Clocked
