/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.AnnotatedArrival

/-!
# Exact arrival times under uniform gate delays

`Circuit.outputArrivals_le_add_mul_outputDepths` bounds the arrival time of every designated
output of a circuit by `a0 + D * depth` when every delay lies in `[0, D]` and every input
arrives by `a0 ≥ 0`. This file shows that the bound is attained under uniform delays: if every
gate has delay `D ≥ 0`, every input arrives at `a0 ≥ 0`, and no gate of the circuit is a
constant, then every designated output arrives exactly at `a0 + D * depth`
(`Circuit.outputArrivals_uniform_of_noConstantGates`). The premise is needed: a constant gate
arrives at its delay alone while `Line.depth` gives it depth `1`, so a circuit that uses one can
arrive before the bound when `0 < a0`.

`Program.NoConstantGates` asks only that the gates the program uses read at least one wire; the
signature may also offer constants. `Circuit.outputArrivals_uniform` is the special case of a
signature whose operations all take an argument. `Circuit.exists_outputDepths_eq_depth` shows
that a circuit with at least one output attains its depth at some output, so under the same
premises the latest output arrives exactly at `a0 + D * Circuit.depth`.
-/

@[expose] public section

namespace Cslib.Circuits

universe v

/-- Every gate of the program reads at least one wire: no gate of `p` is a
constant. Only the operations the program uses matter; the signature may
also offer constants. -/
def Program.NoConstantGates {σ : Signature.{v}} {m : ℕ} :
    {g : ℕ} → Program σ m g → Prop
  | _, .empty => True
  | _, .gate p line => Program.NoConstantGates p ∧ 0 < σ.Arity line.op

/-- A signature without constants admits no constant gate. -/
theorem Program.noConstantGates_of_arity_pos {σ : Signature.{v}} {m : ℕ}
    (hσ : ∀ op, 0 < σ.Arity op) : ∀ {g : ℕ} (p : Program σ m g), p.NoConstantGates
  | _, .empty => trivial
  | _, .gate p line => ⟨Program.noConstantGates_of_arity_pos hσ p, hσ line.op⟩

/-- The fold-max from `0` of the values `a0 + D * f k` over a nonempty index
type is `a0` plus `D` times the fold-max of `f`. -/
private theorem foldl_max_add_mul : ∀ {n : ℕ} (f : Fin n → ℕ) (a0 D : ℝ),
    0 ≤ a0 → 0 ≤ D → 0 < n →
    Fin.foldl n (fun t k => max t (a0 + D * (f k : ℝ))) 0
      = a0 + D * ((Fin.foldl n (fun d k => max d (f k)) 0 : ℕ) : ℝ) := by
  intro n
  induction n with
  | zero => intro f a0 D ha0 hD hn; omega
  | succ n ih =>
    intro f a0 D ha0 hD hn
    simp only [Fin.foldl_succ_last]
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Fin.foldl_zero]
      have hV : (0 : ℝ) ≤ a0 + D * ((f (Fin.last 0) : ℕ) : ℝ) :=
        add_nonneg ha0 (mul_nonneg hD (Nat.cast_nonneg _))
      rw [max_eq_right hV, max_eq_right (Nat.zero_le _)]
    · have hih : Fin.foldl n (fun t k => max t (a0 + D * ((f k.castSucc : ℕ) : ℝ))) 0
          = a0 + D * ((Fin.foldl n (fun d k => max d (f k.castSucc)) 0 : ℕ) : ℝ) :=
        ih _ _ _ ha0 hD (Nat.pos_of_ne_zero hn0)
      rw [hih, Nat.cast_max]
      have hmono : Monotone (fun x : ℝ => a0 + D * x) := fun x y h =>
        add_le_add_right (mul_le_mul_of_nonneg_left h hD) a0
      exact (Monotone.map_max hmono).symm

/-- The fold-max from `0` over a nonempty index type is attained. -/
private theorem foldl_max_attained : ∀ {n : ℕ} (f : Fin n → ℕ), 0 < n →
    ∃ k, Fin.foldl n (fun d i => max d (f i)) 0 = f k := by
  intro n
  induction n with
  | zero => intro f hn; omega
  | succ n ih =>
    intro f hn
    simp only [Fin.foldl_succ_last]
    by_cases h : Fin.foldl n (fun d i => max d (f i.castSucc)) 0 ≤ f (Fin.last n)
    · exact ⟨Fin.last n, max_eq_right h⟩
    · simp only [not_le] at h
      by_cases hn0 : n = 0
      · subst hn0
        simp only [Fin.foldl_zero] at h
        omega
      · obtain ⟨i, hi⟩ := ih (fun j => f j.castSucc) (Nat.pos_of_ne_zero hn0)
        have hi' : Fin.foldl n (fun d i => max d (f i.castSucc)) 0 = f i.castSucc := hi
        exact ⟨i.castSucc, by rw [max_eq_left (le_of_lt h), hi']⟩

/-- Uniform wire arrivals follow from uniform gate arrivals. -/
private theorem wireArrivals_uniform_of_arrivals {σ : Signature.{v}} {m g : ℕ}
    (p : Program σ m g) (a0 D : ℝ)
    (hall : ∀ j, p.arrivals (fun _ => D) (fun _ => a0) j
      = a0 + D * ((p.depths j : ℕ) : ℝ))
    (w : Wire m g) :
    p.wireArrivals (fun _ => D) (fun _ => a0) w
      = a0 + D * ((p.wireDepths w : ℕ) : ℝ) := by
  cases w with
  | input i => simp [Program.wireArrivals, Program.wireDepths, Wire.elim]
  | gate i =>
    simp only [Program.wireArrivals, Program.wireDepths, Wire.elim]
    exact hall i

/-- For a program without constant gates, uniform delay `D ≥ 0` and every
input arriving at `a0 ≥ 0`, every gate arrives exactly at `a0` plus `D` times
its depth. -/
theorem Program.arrivals_uniform : ∀ {σ : Signature.{v}} {m g : ℕ} (p : Program σ m g)
    (_hp : p.NoConstantGates) (a0 D : ℝ) (_ha0 : 0 ≤ a0) (_hD : 0 ≤ D) (j : Fin g),
    p.arrivals (fun _ => D) (fun _ => a0) j = a0 + D * ((p.depths j : ℕ) : ℝ) := by
  intro σ m g p
  induction p with
  | empty =>
    intro _ a0 D _ _ j
    exact Fin.elim0 j
  | gate p line ih =>
    intro hp a0 D ha0 hD j
    obtain ⟨hp, hop⟩ := hp
    refine Fin.lastCases ?_ ?_ j
    · simp only [Program.arrivals_gate_last, Program.depths_gate_last, Line.arrival,
        Line.depth]
      have hwire : ∀ k, p.wireArrivals (fun _ => D) (fun _ => a0) (line.wires k)
          = a0 + D * ((p.wireDepths (line.wires k) : ℕ) : ℝ) :=
        fun k => wireArrivals_uniform_of_arrivals p a0 D (fun j => ih hp a0 D ha0 hD j)
          (line.wires k)
      simp only [hwire]
      have hfold : Fin.foldl (σ.Arity line.op)
            (fun t k => max t (a0 + D * ((p.wireDepths (line.wires k) : ℕ) : ℝ))) 0
          = a0 + D * ((Fin.foldl (σ.Arity line.op)
            (fun d k => max d (p.wireDepths (line.wires k))) 0 : ℕ) : ℝ) :=
        foldl_max_add_mul _ _ _ ha0 hD hop
      rw [hfold, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      ac_rfl
    · intro i
      simp only [Program.arrivals_gate_castSucc, Program.depths_gate_castSucc]
      exact ih hp a0 D ha0 hD i

/-- A circuit with at least one output attains its depth at some output. -/
theorem Circuit.exists_outputDepths_eq_depth {σ : Signature.{v}} {m n : ℕ}
    (c : Circuit σ m n) (hn : 0 < n) : ∃ o, c.outputDepths o = c.depth := by
  obtain ⟨k, hk⟩ := foldl_max_attained (fun o => c.outputDepths o) hn
  exact ⟨k, hk.symm⟩

/-- For a circuit without constant gates, uniform delay `D ≥ 0` and every
input arriving at `a0 ≥ 0`, every designated output arrives exactly at
`a0` plus `D` times its depth. -/
theorem Circuit.outputArrivals_uniform_of_noConstantGates {σ : Signature.{v}}
    {inputCount outputCount : ℕ} (c : Circuit σ inputCount outputCount)
    (hc : c.program.NoConstantGates) (a0 D : ℝ) (ha0 : 0 ≤ a0) (hD : 0 ≤ D)
    (o : Fin outputCount) :
    c.outputArrivals (fun _ => D) (fun _ => a0) o = a0 + D * (c.outputDepths o : ℝ) :=
  wireArrivals_uniform_of_arrivals c.program a0 D
    (Program.arrivals_uniform c.program hc a0 D ha0 hD) (c.outputs o)

/-- With every operation of the signature taking at least one argument,
uniform delay `D ≥ 0` and every input arriving at `a0 ≥ 0`, every designated
output arrives exactly at `a0` plus `D` times its depth. For a signature that
also offers constants, use `Circuit.outputArrivals_uniform_of_noConstantGates`. -/
theorem Circuit.outputArrivals_uniform {σ : Signature.{v}} {inputCount outputCount : ℕ}
    (hσ : ∀ op, 0 < σ.Arity op) (c : Circuit σ inputCount outputCount)
    (a0 D : ℝ) (ha0 : 0 ≤ a0) (hD : 0 ≤ D) (o : Fin outputCount) :
    c.outputArrivals (fun _ => D) (fun _ => a0) o = a0 + D * (c.outputDepths o : ℝ) :=
  Circuit.outputArrivals_uniform_of_noConstantGates c
    (Program.noConstantGates_of_arity_pos hσ _) a0 D ha0 hD o

end Cslib.Circuits
