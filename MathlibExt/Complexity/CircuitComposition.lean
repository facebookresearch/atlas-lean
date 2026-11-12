/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

@[expose] public section


/-- Boolean circuits as trees over `n` inputs: leaves are input
wires or constants, internal nodes are gates. -/
inductive Circuit (n : ℕ)
  | input (i : Fin n) : Circuit n
  | const (b : Bool) : Circuit n
  | and (g h : Circuit n) : Circuit n
  | or (g h : Circuit n) : Circuit n
  | not (g : Circuit n) : Circuit n

/-- Evaluation of a circuit on an input assignment. -/
def Circuit.eval {n : ℕ} (σ : Fin n → Bool) : Circuit n → Bool
  | .input i => σ i
  | .const b => b
  | .and g h => g.eval σ && h.eval σ
  | .or g h => g.eval σ || h.eval σ
  | .not g => !g.eval σ

/-- Size: number of gates (internal nodes). -/
def Circuit.size {n : ℕ} : Circuit n → ℕ
  | .input _ => 0
  | .const _ => 0
  | .and g h => g.size + h.size + 1
  | .or g h => g.size + h.size + 1
  | .not g => g.size + 1

/-- Depth: longest input-to-output path. -/
def Circuit.depth {n : ℕ} : Circuit n → ℕ
  | .input _ => 0
  | .const _ => 0
  | .and g h => max g.depth h.depth + 1
  | .or g h => max g.depth h.depth + 1
  | .not g => g.depth + 1

/-- Wire renumbering / composition: substitute for each input
wire `i` of the outer circuit a circuit over `m` inputs. -/
def Circuit.subst {n m : ℕ} (wiring : Fin n → Circuit m) :
    Circuit n → Circuit m
  | .input i => wiring i
  | .const b => .const b
  | .and g h => .and (g.subst wiring) (h.subst wiring)
  | .or g h => .or (g.subst wiring) (h.subst wiring)
  | .not g => .not (g.subst wiring)

/-- Composition evaluates pointwise: evaluating the composite
circuit is evaluating the outer circuit on the values of the
inner circuits. -/
theorem Circuit.eval_subst {n m : ℕ} (wiring : Fin n → Circuit m)
    (g : Circuit n) (τ : Fin m → Bool) :
    (g.subst wiring).eval τ = g.eval (fun i => (wiring i).eval τ) := by
  induction g with
  | input i => rfl
  | const b => rfl
  | and g h ihg ihh => simp [Circuit.subst, Circuit.eval, ihg, ihh]
  | or g h ihg ihh => simp [Circuit.subst, Circuit.eval, ihg, ihh]
  | not g ih => simp [Circuit.subst, Circuit.eval, ih]

/-- Depth of a composition is at most the sum of the depths:
composing circuits does not multiply depth. -/
theorem Circuit.depth_subst_le {n m : ℕ} (wiring : Fin n → Circuit m)
    (g : Circuit n) (D : ℕ) (hD : ∀ i, (wiring i).depth ≤ D) :
    (g.subst wiring).depth ≤ g.depth + D := by
  induction g with
  | input i =>
    simp only [Circuit.subst, Circuit.depth, Nat.zero_add]
    exact hD i
  | const b =>
    simp only [Circuit.subst, Circuit.depth, Nat.zero_add]
    exact Nat.zero_le D
  | and g h ihg ihh =>
    simp only [Circuit.subst, Circuit.depth]
    omega
  | or g h ihg ihh =>
    simp only [Circuit.subst, Circuit.depth]
    omega
  | not g ih =>
    simp only [Circuit.subst, Circuit.depth]
    omega

/-- Tighter size bound used to prove `Circuit.size_subst_le`:
at a leaf this is exactly `hD`, which keeps the `and`/`or`
arithmetic exact (direct induction on the pinned bound is off by
one at binary gates). -/
private theorem Circuit.size_subst_le_aux {n m : ℕ} (wiring : Fin n → Circuit m)
    (g : Circuit n) (D : ℕ) (hD : ∀ i, (wiring i).size ≤ D) :
    (g.subst wiring).size ≤ g.size * (D + 1) + D := by
  induction g with
  | input i =>
    simp only [Circuit.subst, Circuit.size, Nat.zero_mul, Nat.zero_add]
    exact hD i
  | const b =>
    simp only [Circuit.subst, Circuit.size, Nat.zero_mul, Nat.zero_add]
    exact Nat.zero_le D
  | and g h ihg ihh =>
    simp only [Circuit.subst, Circuit.size]
    have h1 : (g.subst wiring).size + (h.subst wiring).size + 1
        ≤ (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add ihg ihh) 1
    have e : (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1
        = (g.size + h.size + 1) * (D + 1) + D := by ring
    rw [e] at h1
    exact h1
  | or g h ihg ihh =>
    simp only [Circuit.subst, Circuit.size]
    have h1 : (g.subst wiring).size + (h.subst wiring).size + 1
        ≤ (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add ihg ihh) 1
    have e : (g.size * (D + 1) + D) + (h.size * (D + 1) + D) + 1
        = (g.size + h.size + 1) * (D + 1) + D := by ring
    rw [e] at h1
    exact h1
  | not g ih =>
    simp only [Circuit.subst, Circuit.size]
    have h1 : (g.subst wiring).size + 1 ≤ (g.size * (D + 1) + D) + 1 :=
      Nat.add_le_add_right ih 1
    have hdist : (g.size + 1) * (D + 1) = g.size * (D + 1) + (D + 1) := by ring
    have e : (g.size * (D + 1) + D) + 1 ≤ (g.size + 1) * (D + 1) + D := by
      omega
    exact h1.trans e

/-- Size of a composition is at most the size of the outer
circuit times the maximal inner size, plus the outer size:
`size (g ∘ wiring) ≤ size g * (D + 1)` when every inner circuit
has size at most `D`. -/
theorem Circuit.size_subst_le {n m : ℕ} (wiring : Fin n → Circuit m)
    (g : Circuit n) (D : ℕ) (hD : ∀ i, (wiring i).size ≤ D) :
    (g.subst wiring).size ≤ g.size * (D + 1) + (D + 1) := by
  have h := Circuit.size_subst_le_aux wiring g D hD
  have hle : g.size * (D + 1) + D ≤ g.size * (D + 1) + (D + 1) :=
    Nat.add_le_add_left (Nat.le_succ D) _
  exact h.trans hle

