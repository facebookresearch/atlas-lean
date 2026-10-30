/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.Combinatorics.SimpleGraph.Domination

/-!
# Transfer matrices for domination polynomials of grids, cylinders and tori

Statements from Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the
Torus, and the King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 2.

A row of width `m` is the path graph `pathGraph m` (grid) or the cycle graph `cycleGraph m`
(cylinder and torus); the `m × n` grid, cylinder and torus are the box products
`pathGraph m □ pathGraph n`, `cycleGraph m □ pathGraph n` and `cycleGraph m □ cycleGraph n`,
with rows indexed by the second coordinate.  Signatures, compatibility and the transfer matrix
are stated for an arbitrary row graph `R`; for `R = pathGraph m` (resp. `R = cycleGraph m`)
they are the paper's (cyclic) signatures, Definitions 3, 5 and 6.
-/

open Polynomial SimpleGraph

namespace MetaMathlibExt

@[expose] public section

/-- The state of a vertex relative to a vertex set `S` (Mertens, Definition 1): occupied
(in `S`), covered (not in `S` but adjacent to `S`), or uncovered.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
inductive DominationState
  | uncovered
  | covered
  | occupied
  deriving DecidableEq

open DominationState

/-- The three vertex states form a finite type.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
instance : Fintype DominationState :=
  Fintype.ofList [uncovered, covered, occupied] fun x => by cases x <;> simp

section Defs

variable {V W : Type*}

open scoped Classical in
/-- The domination polynomial `∑_S z^{|S|}` of a finite graph, the sum running over the
dominating sets `S` (canonical `SimpleGraph.IsDominating`).

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 1. -/
noncomputable def dominationPolynomial [Fintype W] (G : SimpleGraph W) : ℤ[X] :=
  ∑ S ∈ (Finset.univ : Finset (Finset W)).filter (fun S : Finset W => G.IsDominating (↑S : Set W)),
    X ^ S.card

open scoped Classical in
/-- The state of the vertex `v` relative to the vertex set `S` in the graph `G`
(Mertens, Definition 1).

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
noncomputable def vertexDominationState (G : SimpleGraph W) (S : Finset W) (v : W) :
    DominationState :=
  if v ∈ S then occupied else if ∃ u ∈ S, G.Adj u v then covered else uncovered

/-- A signature for the row graph `R` (Mertens, Definition 3): a state for every vertex of the
row such that no uncovered vertex is adjacent to an occupied one.  For `R = pathGraph m` these
are the strings avoiding the substrings `(∘,•)` and `(•,∘)`; for `R = cycleGraph m` the
constraint also applies to the pair `(σ₁, σₘ)` (cyclic signatures).

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
def IsDominationSignature (R : SimpleGraph V) (σ : V → DominationState) : Prop :=
  ∀ i j, R.Adj i j → ¬(σ i = uncovered ∧ σ j = occupied)

/-- The type of (cyclic) signatures of the row graph `R`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
def DominationSignature (R : SimpleGraph V) : Type _ :=
  {σ : V → DominationState // IsDominationSignature R σ}

/-- Signatures of a finite row form a finite type.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
noncomputable instance [Fintype V] [DecidableEq V] (R : SimpleGraph V) :
    Fintype (DominationSignature R) := by
  classical
  unfold DominationSignature
  infer_instance

/-- Signatures have decidable equality.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 3. -/
noncomputable instance [Fintype V] (R : SimpleGraph V) :
    DecidableEq (DominationSignature R) := by
  classical
  unfold DominationSignature
  infer_instance

/-- The signature that is covered everywhere, `σ_• = (•,…,•)` in gray (Mertens, Theorem 7).

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7. -/
def allCoveredSignature (R : SimpleGraph V) : DominationSignature R :=
  ⟨fun _ => covered, fun _ _ _ h => DominationState.noConfusion h.1⟩

/-- Compatibility of a new row signature `τ` with the previous row signature `σ`
(Mertens, Definition 5): an uncovered vertex of `σ` lies below an occupied vertex of `τ`, an
occupied vertex of `σ` lies below a covered or occupied vertex of `τ`, and a covered vertex of
`τ` lies below an occupied vertex of `σ` or is adjacent in the row to an occupied vertex of `τ`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 5. -/
def DominationCompatible (R : SimpleGraph V) (τ σ : V → DominationState) : Prop :=
  ∀ i, (σ i = uncovered → τ i = occupied) ∧ (σ i = occupied → τ i ≠ uncovered) ∧
    (τ i = covered → σ i = occupied ∨ ∃ j, R.Adj i j ∧ τ j = occupied)

open scoped Classical in
/-- The number `occ(σ)` of occupied vertices of a row state.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 6. -/
noncomputable def occupiedCount [Fintype V] (σ : V → DominationState) : ℕ :=
  ((Finset.univ : Finset V).filter fun i => σ i = occupied).card

open scoped Classical in
/-- Mertens' transfer matrix `A` (Definition 6), rows indexed by the new signature `τ` and
columns by the old signature `σ`: `A τ σ = z^{occ(τ)}` if `τ` is compatible with `σ`, and `0`
otherwise.  For `R = cycleGraph m` this is the paper's `Ā`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 6. -/
noncomputable def dominationTransferMatrix [Fintype V] (R : SimpleGraph V) :
    Matrix (DominationSignature R) (DominationSignature R) ℤ[X] :=
  fun τ σ => if DominationCompatible R τ.1 σ.1 then X ^ occupiedCount τ.1 else 0

open scoped Classical in
/-- The generating function `G^σ_{m×(n+1)}(z)` of almost dominating sets with signature `σ`
on `R □ pathGraph (n + 1)` (Mertens, Definition 2 and Section 2): vertex sets `S` such that no
vertex outside the last row `Fin.last n` is uncovered, and whose last row has state `σ`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 2. -/
noncomputable def almostDominatingPolynomial [Fintype V] (R : SimpleGraph V) (n : ℕ)
    (σ : V → DominationState) : ℤ[X] :=
  ∑ S ∈ (Finset.univ : Finset (Finset (V × Fin (n + 1)))).filter (fun S =>
      (∀ v : V × Fin (n + 1), v.2 ≠ Fin.last n →
        vertexDominationState (R □ pathGraph (n + 1)) S v ≠ uncovered) ∧
      ∀ i, vertexDominationState (R □ pathGraph (n + 1)) S (i, Fin.last n) = σ i),
    X ^ S.card

/-- A vertex is occupied exactly when it lies in `S`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
theorem vertexDominationState_eq_occupied_iff (G : SimpleGraph W) (S : Finset W) (v : W) :
    vertexDominationState G S v = occupied ↔ v ∈ S := by
  unfold vertexDominationState
  split_ifs <;> simp_all

/-- `S` is dominating exactly when no vertex is uncovered.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Definition 1. -/
theorem isDominating_iff_forall_vertexDominationState_ne_uncovered (G : SimpleGraph W)
    (S : Finset W) :
    G.IsDominating (S : Set W) ↔ ∀ v, vertexDominationState G S v ≠ uncovered := by
  unfold vertexDominationState SimpleGraph.IsDominating
  refine forall_congr' fun v => ?_
  split_ifs with h₁ h₂ <;> simp_all

/-- The value of the domination polynomial at `1` is the number of dominating sets.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 1. -/
theorem dominationPolynomial_eval_one [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidablePred fun S : Finset W => G.IsDominating (S : Set W)] :
    (dominationPolynomial G).eval 1 =
      (((Finset.univ : Finset (Finset W)).filter
        fun S : Finset W => G.IsDominating (↑S : Set W)).card : ℤ) := by
  unfold dominationPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  congr

/-- The all-covered signature has no occupied vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7. -/
theorem occupiedCount_allCoveredSignature [Fintype V] (R : SimpleGraph V) :
    occupiedCount (allCoveredSignature R).1 = 0 := by
  simp [occupiedCount, allCoveredSignature]

/-- The transfer matrix entry `A τ σ_•` is `z^{occ(τ)}` exactly when every covered vertex of
`τ` has an occupied neighbour in the row (the initial-value step in the proof of Theorem 7), and
`0` otherwise.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7. -/
theorem dominationTransferMatrix_apply_allCoveredSignature [Fintype V] (R : SimpleGraph V)
    (τ : DominationSignature R)
    [Decidable (∀ i, τ.1 i = covered → ∃ j, R.Adj i j ∧ τ.1 j = occupied)] :
    dominationTransferMatrix R τ (allCoveredSignature R) =
      if ∀ i, τ.1 i = covered → ∃ j, R.Adj i j ∧ τ.1 j = occupied then
        X ^ occupiedCount τ.1 else 0 := by
  unfold dominationTransferMatrix
  have : DominationCompatible R τ.1 (allCoveredSignature R).1 ↔
      ∀ i, τ.1 i = covered → ∃ j, R.Adj i j ∧ τ.1 j = occupied := by
    simp [DominationCompatible, allCoveredSignature]
  simp only [this]

end Defs

open scoped Classical in
/-- Mertens' Lemma 4, grid case: the domination polynomial of the `m × (n + 1)` grid is the sum
of `G^σ` over the signatures `σ` with no uncovered vertex.  Stated for `n + 1 ≥ 1` rows, since
the last row carrying `σ` must exist.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Lemma 4
(`jis-2024-24.7.6-lem-4`). -/
public theorem_wanted dominationPolynomial_grid_eq_sum_almostDominatingPolynomial (m n : ℕ) :
    dominationPolynomial (pathGraph m □ pathGraph (n + 1)) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        almostDominatingPolynomial (pathGraph m) n σ.1

open scoped Classical in
/-- Mertens' Lemma 4, cylinder case: the domination polynomial of the `m × (n + 1)` cylinder is
the sum of `G^σ` over the cyclic signatures `σ` with no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Lemma 4
(`jis-2024-24.7.6-lem-4`). -/
public theorem_wanted dominationPolynomial_cylinder_eq_sum_almostDominatingPolynomial
    (m n : ℕ) :
    dominationPolynomial (cycleGraph m □ pathGraph (n + 1)) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        almostDominatingPolynomial (cycleGraph m) n σ.1

open scoped Classical in
/-- Mertens' Theorem 7, grid case: `G_{m×n}(z) = ∑_{σ : unc(σ) = 0} (A^n)_{σ, σ_•}`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
public theorem_wanted dominationPolynomial_grid_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (pathGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (pathGraph m) ^ n) σ (allCoveredSignature _)

open scoped Classical in
/-- Mertens' Theorem 7, cylinder case: `G_{m̄×n}(z) = ∑_{σ : unc(σ) = 0} (Ā^n)_{σ, σ_•}`, the
sum over cyclic signatures.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
public theorem_wanted dominationPolynomial_cylinder_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (cycleGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (cycleGraph m) ^ n) σ (allCoveredSignature _)

/-- Mertens' Theorem 8: the domination polynomial of the `m × n` torus is `Tr Ā^n`.  Stated for
`n ≥ 1` (at `n = 0` the trace counts the cyclic signatures instead of the empty set); for
`n = 1, 2` the torus is `cycleGraph m □ cycleGraph n` with Mathlib's `cycleGraph 1 = ⊥` and
`cycleGraph 2 = K₂`.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 8
(`jis-2024-24.7.6-thm-8`). -/
public theorem_wanted dominationPolynomial_torus_eq_trace_transferMatrix_pow (m n : ℕ)
    (hn : 1 ≤ n) :
    dominationPolynomial (cycleGraph m □ cycleGraph n) =
      Matrix.trace (dominationTransferMatrix (cycleGraph m) ^ n)

end

end MetaMathlibExt
