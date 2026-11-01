/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Section 2: preliminaries — derived series, solvability, nilpotents

Derived series, solvability, idempotent and absolutely nilpotent elements,
following the paper (`evolution_algebras.pdf`, Preliminaries).

Everything here works for an arbitrary non-associative algebra: no basis, no
`EvolutionAlgebra` hypothesis, and only the minimal bundle
(`NonUnitalNonAssocSemiring` + `Module`, no scalar-tower laws needed). We mirror
Mathlib's `Mathlib/Algebra/Lie/Solvable.lean`, including 0-based indexing:
`derivedSeries 0 = ⊤`, so the paper's `𝓔⁽¹⁾` is our `derivedSeries 0`.

## Main definitions

* `EvolutionAlgebras.square`: the square `V² = Span{x * y | x, y ∈ V}`.
* `EvolutionAlgebras.derivedSeriesOfSubmodule`: derived series from a given start.
* `EvolutionAlgebras.derivedSeries`: derived series from `⊤`.
* `EvolutionAlgebras.IsSolvable`: the series reaches `⊥`.
* `EvolutionAlgebras.IsAbsNilpotent`: `x² = 0` (idempotents reuse Mathlib's
  `IsIdempotentElem`).
* `EvolutionAlgebras.absNilpotent`: the set `N(V) = {y ∈ V | y² = 0}`.

## Main results

* `EvolutionAlgebras.derivedSeries_succ_le`: `E⁽ᵏ⁺¹⁾ ⊆ E⁽ᵏ⁾` (Section 2).
-/

namespace EvolutionAlgebras

universe u v

variable (K E : Type*) [CommSemiring K] [NonUnitalNonAssocSemiring E] [Module K E]

/-- **Section 2.** The square of a submodule: `V² = Span{x * y | x, y ∈ V}` (paper: `V²`).
The operation iterated by the derived series below; it also defines what it
means for a submodule to be idempotent. -/
def square (V : Submodule K E) : Submodule K E :=
  Submodule.span K {z | ∃ x ∈ V, ∃ y ∈ V, x * y = z}

/-- **Helper.** Monotonicity of `square`: a larger submodule has a larger square. Used to
show the derived series decreases, and in the proof that `𝓔^(∞)` is the
greatest idempotent subspace. -/
theorem square_mono {V W : Submodule K E} (h : V ≤ W) :
    square K E V ≤ square K E W := by
  unfold square
  apply Submodule.span_mono
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, h hx, y, h hy, rfl⟩

/-- A submodule is **idempotent** if it equals its own square
(Section 3: `V² = V`). The central predicate of the two characterizations:
solvable algebras are those with no nontrivial idempotent subspace, and
nonzero idempotents correspond to idempotent subspaces with `N(V) = 0`. -/
def IsIdempotentSubmodule (V : Submodule K E) : Prop :=
  square K E V = V

/-- Helper result: derived series starting from a given submodule (cf.
`LieAlgebra.derivedSeriesOfIdeal`). The construction underlying
`derivedSeries` below. -/
def derivedSeriesOfSubmodule (k : ℕ) : Submodule K E → Submodule K E :=
  (fun V => square K E V)^[k]

/-- Base case: iterating zero times returns the submodule. -/
@[simp]
theorem derivedSeriesOfSubmodule_zero (V : Submodule K E) :
    derivedSeriesOfSubmodule K E 0 V = V :=
  rfl

/-- Step case: iterating `k + 1` times squares the `k`-th iterate. -/
@[simp]
theorem derivedSeriesOfSubmodule_succ (k : ℕ) (V : Submodule K E) :
    derivedSeriesOfSubmodule K E (k + 1) V =
      square K E (derivedSeriesOfSubmodule K E k V) :=
  Function.iterate_succ_apply' (fun V => square K E V) k V

/-- The derived series: `E⁽⁰⁾ = E`, `E⁽ᵏ⁺¹⁾ = (E⁽ᵏ⁾)²` (Section 2: `𝓔⁽¹⁾ = 𝓔`,
`𝓔⁽ⁱ⁺¹⁾ = (𝓔⁽ⁱ⁾)²`, shifted by one). Solvability, stabilization, and the
corollary are all stated in terms of this series. -/
abbrev derivedSeries (k : ℕ) : Submodule K E :=
  derivedSeriesOfSubmodule K E k ⊤

/-- The series starts at the whole algebra: `E⁽⁰⁾ = E`. -/
@[simp]
theorem derivedSeries_zero : derivedSeries K E 0 = ⊤ :=
  rfl

/-- Successor terms square the previous term. -/
@[simp]
theorem derivedSeries_succ (k : ℕ) :
    derivedSeries K E (k + 1) = square K E (derivedSeries K E k) :=
  derivedSeriesOfSubmodule_succ K E k ⊤

/-- Consecutive terms decrease: `E⁽ᵏ⁺¹⁾ ⊆ E⁽ᵏ⁾` (Section 2: "it is easy to see that
for `i ≥ 1`, `𝓔⁽ⁱ⁺¹⁾ ⊆ 𝓔⁽ⁱ⁾`"). The series is therefore antitone, which is what
forces it to stabilize in finite dimensions. -/
theorem derivedSeries_succ_le (k : ℕ) :
    derivedSeries K E (k + 1) ≤ derivedSeries K E k := by
  induction k with
  | zero =>
    rw [derivedSeries_zero]
    exact le_top
  | succ k ih =>
    calc derivedSeries K E (k + 1 + 1)
        = square K E (derivedSeries K E (k + 1)) := derivedSeries_succ K E (k + 1)
      _ ≤ square K E (derivedSeries K E k) := square_mono K E ih
      _ = derivedSeries K E (k + 1) := (derivedSeries_succ K E k).symm

/-- `𝓔^(∞)`: the infimum of the derived series (paper: the stabilized
value `𝓔^(ˡ)`; proved equal to the stable term in
`derivedSeriesInf_eq_of_stabilizes`). When the algebra is not solvable, this
nontrivial subspace is the witness used in the proof of the corollary. -/
def derivedSeriesInf : Submodule K E :=
  ⨅ k, derivedSeries K E k

/-- Helper result: an idempotent element lies in every term of the derived series
(`x = x * x ∈ (𝓔⁽ᵏ⁾)² = 𝓔⁽ᵏ⁺¹⁾`). Hence a solvable algebra — whose series
reaches `0` — admits no nonzero idempotents. -/
theorem idempotent_mem_derivedSeries {x : E} (hx : IsIdempotentElem x)
    (k : ℕ) : x ∈ derivedSeries K E k := by
  have hx_eq : x * x = x := hx
  induction k with
  | zero => exact Submodule.mem_top
  | succ k ih =>
    rw [derivedSeries_succ K E k]
    exact Submodule.subset_span ⟨x, ih, x, ih, hx_eq⟩

/-- An algebra is solvable if its derived series reaches `0` in finitely many
steps (Section 2: `𝓔⁽ᵐ⁾ = 0` for some `m ≥ 1`; cf. `LieAlgebra.IsSolvable`).
The predicate appearing in the disproof of the conjecture, the solvable
characterization, and the corollary. -/
class IsSolvable : Prop where
  mk_int ::
  solvable_int : ∃ k, derivedSeries K E k = ⊥

/-- Eliminator: a solvable algebra's series reaches `0`. -/
theorem IsSolvable.solvable [self : IsSolvable K E] :
    ∃ k, derivedSeries K E k = ⊥ :=
  self.solvable_int

/-- Constructor: a series reaching `0` proves solvability. -/
theorem IsSolvable.mk {k : ℕ} (h : derivedSeries K E k = ⊥) : IsSolvable K E :=
  ⟨⟨k, h⟩⟩

/-- An element is absolutely nilpotent if `x² = 0` (Section 2). Idempotent elements
(`x² = x`) reuse Mathlib's `IsIdempotentElem`. -/
def IsAbsNilpotent (x : E) : Prop :=
  x * x = 0

/-- The set `N(V) = {y ∈ V | y² = 0}` (Section 2). The `N(V) = 0`
side-condition of the idempotent characterization, and the hypothesis of
the corollary. -/
def absNilpotent (V : Submodule K E) : Set E :=
  {x | x ∈ V ∧ IsAbsNilpotent E x}

end EvolutionAlgebras
