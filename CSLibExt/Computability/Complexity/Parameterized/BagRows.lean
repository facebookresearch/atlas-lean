/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.GraphWriter
public import CSLibExt.Computability.Complexity.Parameterized.HardnessClauses
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Tuples

/-!
# Explicit tables of local assignments for signed bounded-width CNF

A color lists at most twice the clause width in selection slots. Different
colors are allowed to list the same set of slots. A row assigns variables to
the slots of one color and rejects any clause already forced false. Edges
require rows from the same formula to agree on their shared slots.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows

open Cslib.Complexity.PolynomialEncoding.Comprehension

abbrev Formula := List (List (ℕ × Bool))
abbrev Local := List (ℕ × ℕ)

/-- The local choices witness that the literal is false under every increasing
global extension of the choices. -/
def forcesFalse (slots : List ℕ) (a : Local) (lit : ℕ × Bool) : Bool :=
  if lit.2 then slots.all fun i => a.any fun j =>
    decide (i ≤ j.1 ∧ j.2 < lit.1 ∨ j.1 ≤ i ∧ lit.1 < j.2)
  else a.any fun j => j.2 == lit.1

/-- The local table covers exactly the indicated slots, gives them increasing
values, and leaves a possible true literal in each clause. -/
def allowed (slots shape : List ℕ) (p : Formula) (a : Local) : Bool :=
  (shape.all fun i => a.any fun e => e.1 == i) &&
  (a.all fun e => shape.contains e.1) &&
  (a.all fun e => a.all fun f =>
    decide ((e.1 = f.1 → e.2 = f.2) ∧ (e.1 < f.1 → e.2 < f.2))) &&
  (p.all fun c => !(c.all (forcesFalse slots a)))

/-- Agreement on every slot listed in both local assignments. -/
def agrees (a b : Local) : Bool :=
  a.all fun e => b.all fun f => decide (e.1 = f.1 → e.2 = f.2)

abbrev Row := (Formula × ℕ) × (List ℕ × ℕ) × Local

/-- All candidates before the local admissibility test. -/
def candidates (B : ℕ) (slots values : List ℕ) (family : List Formula) : List Row :=
  family.zipIdx.flatMap fun p =>
    (tuples slots B).zipIdx.flatMap fun color =>
      (tuples (slots.product values) B).map fun a => (p, color, a)

/-- Vertices keep their branch, color and local assignment. -/
def vertices (B : ℕ) (slots values : List ℕ) (family : List Formula) : List Row :=
  (candidates B slots values family).filter fun row =>
    allowed slots row.2.1.1 row.1.1 row.2.2

/-- Distinct colors from one branch are adjacent when the assignments agree. -/
def adjacent (v w : Row) : Bool :=
  (v.1.2 == w.1.2) && !(v.2.1.2 == w.2.1.2) && agrees v.2.2 w.2.2

/-- Emit a single ordinary clique query for all alternatives. -/
def query (d : ℕ) (slots values : List ℕ) (family : List Formula) : List Bool × ℕ :=
  let B := max 2 (2 * d)
  (GraphWriter.writeGraph (vertices B slots values family) adjacent, (tuples slots B).length)

/-- An increasing list of exactly `k` distinct true variables from the
declared range, satisfying one of the input formulas. -/
def HasAssignment (k n : ℕ) (family : List Formula) : Prop :=
  ∃ p ∈ family, ∃ a : Fin k → ℕ, (∀ i, a i < n) ∧ StrictMono a ∧
    ∀ c ∈ p, ∃ l ∈ c, WeightedClauses.literalTrue (Set.range a) l

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows
