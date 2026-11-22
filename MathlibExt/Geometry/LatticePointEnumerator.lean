/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Topology.Bornology.Basic

import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Lattice-point enumerators

For a bounded set `P ⊆ ℝᵈ` and a dilation parameter `t > 0`, the lattice-point
enumerator counts integer points in the dilate: `L_P(t) = |(t • P) ∩ ℤᵈ|`.

Source: Rocha-Neves, A Fourier-analytic Uniqueness Theorem for Lattice-point
Enumerators, arXiv:2608.11078v1. The definition `L_P(t)` for bounded `P` and
`t > 0` is on lines 24-31; line 24 assumes `P` is bounded. Lines 62-67 use the
translated version `F_{t,P}(x) = |((t • P) + x) ∩ ℤᵈ|`, translating after
dilating.

Only translate-after-dilate `((t • P) + {x}) ∩ ℤᵈ` matches the source. Dilating
after translating `t • (P + {x})` is a different set; see the regression test
at `P = {0}`, `t = 2`, `x = 1 / 2`.

Main declarations:
- `LatticePointEnumerator.stdLattice`: the standard integer lattice `ℤᵈ`, as the
  integer span of `Pi.basisFun`, in ambient space `Fin d → ℝ`.
- `LatticePointEnumerator.latticePointSet`: the counted set `(t • P) ∩ ℤᵈ`.
- `LatticePointEnumerator.latticeEnumerator`: totalized helper `ncard` count;
  on infinite sets `ncard` returns junk `0`, so source-facing uses need
  boundedness.
- `LatticePointEnumerator.translatedLatticePointSet`: `((t • P) + {x}) ∩ ℤᵈ`.
- `LatticePointEnumerator.translatedLatticeEnumerator`: totalized helper count.
- `LatticePointEnumerator.latticePointSetPos` /
  `LatticePointEnumerator.translatedLatticePointSetPos`: positive-`t` versions.
- `LatticePointEnumerator.latticeEnumeratorPos` /
  `LatticePointEnumerator.translatedLatticeEnumeratorPos`: source-domain
  enumerators requiring a `Bornology.IsBounded P` proof.
- `LatticePointEnumerator.finite_latticePointSet` and translated variants:
  finiteness for bounded `P`, via `ZSpan.setFinite_inter`.
-/

@[expose] public section

namespace LatticePointEnumerator

open scoped Pointwise

/-- Standard integer lattice `ℤᵈ` in `Fin d → ℝ`: integer span of `Pi.basisFun`. -/
noncomputable def stdLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

/-- A vector is in the standard lattice exactly when all its coordinates are integers. -/
theorem mem_stdLattice_iff {d : ℕ} {x : Fin d → ℝ} :
    x ∈ stdLattice d ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
  unfold stdLattice
  rw [(Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ x]
  simp [Pi.basisFun_repr]

/-- Lattice-point set `(t • P) ∩ ℤᵈ` for a real dilate `t`. General helper; the
source only evaluates at `t > 0` (see `latticePointSetPos`). -/
noncomputable def latticePointSet (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ) :
    Set (Fin d → ℝ) :=
  (t • P) ∩ (stdLattice d : Set (Fin d → ℝ))

/-- Totalized enumerator: `ncard` of `latticePointSet`. For unbounded `P` the
intersection can be infinite and `ncard` returns junk `0`; use
`latticeEnumeratorPos` with a boundedness proof for source-faithful counts. -/
noncomputable def latticeEnumerator (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ) : ℕ :=
  Set.ncard (latticePointSet d P t)

/-- Translate-after-dilate set `((t • P) + {x}) ∩ ℤᵈ`, matching `F_{t,P}(x)` on
lines 62-67. Distinct from dilate-after-translate `t • (P + {x})`. -/
noncomputable def translatedLatticePointSet (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  ((t • P) + {x}) ∩ (stdLattice d : Set (Fin d → ℝ))

/-- Totalized translated enumerator; see `translatedLatticeEnumeratorPos` for
the bounded source-domain version. -/
noncomputable def translatedLatticeEnumerator (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) : ℕ :=
  Set.ncard (translatedLatticePointSet d P t x)

/-- Positive-dilation helper, not a full source-domain object: no boundedness carried.
`latticeEnumeratorPos` combines positivity with boundedness proof for Rocha-Neves lines 24-31. -/
noncomputable def latticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) : Set (Fin d → ℝ) :=
  latticePointSet d P t.val

/-- Source-domain enumerator `L_P(t)` for bounded `P` and positive `t`, as in
Rocha-Neves, lines 24-31. The `hb` proof rules out unbounded `P`, where
`ncard` would silently return junk `0`. -/
noncomputable def latticeEnumeratorPos (d : ℕ) (P : Set (Fin d → ℝ))
    (_hb : Bornology.IsBounded P) (t : {t : ℝ // 0 < t}) : ℕ :=
  latticeEnumerator d P t.val

/-- Translate-after-dilate helper, not a full source-domain object: no boundedness.
`translatedLatticeEnumeratorPos` gives the bounded source-facing count. -/
noncomputable def translatedLatticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  translatedLatticePointSet d P t.val x

/-- Source-domain `F_{t,P}(x)` for bounded `P` and positive `t`, lines 62-67. -/
noncomputable def translatedLatticeEnumeratorPos (d : ℕ) (P : Set (Fin d → ℝ))
    (_hb : Bornology.IsBounded P) (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) : ℕ :=
  translatedLatticeEnumerator d P t.val x

/-- The origin lies in the standard integer lattice. -/
theorem zero_mem_stdLattice (d : ℕ) : (0 : Fin d → ℝ) ∈ stdLattice d :=
  Submodule.zero_mem _

/-- The empty set enumerates to zero, at any dilate. -/
@[simp]
theorem latticeEnumerator_empty (d : ℕ) (t : ℝ) :
    latticeEnumerator d ∅ t = 0 := by
  simp [latticeEnumerator, latticePointSet]

/-- The translated empty set enumerates to zero. -/
@[simp]
theorem translatedLatticeEnumerator_empty (d : ℕ) (t : ℝ) (x : Fin d → ℝ) :
    translatedLatticeEnumerator d ∅ t x = 0 := by
  simp [translatedLatticeEnumerator, translatedLatticePointSet]

/-- The counted dilate intersection is finite for bounded `P`
(via `ZSpan.setFinite_inter`). This holds for every real dilate `t`, so no
positivity is assumed here; positivity is tracked structurally in the
source-domain declarations `latticePointSetPos` / `latticeEnumeratorPos`. -/
theorem finite_latticePointSet (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ)
    (hb : Bornology.IsBounded P) :
    Set.Finite (latticePointSet d P t) := by
  unfold latticePointSet stdLattice
  exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin d)) (hb.smul₀ t)

/-- Source-domain finiteness: for bounded `P` and positive `t`. -/
theorem finite_latticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (hb : Bornology.IsBounded P) :
    Set.Finite (latticePointSetPos d P t) :=
  finite_latticePointSet d P t.val hb

/-- Translated finiteness for bounded `P`: `(t • P) + {x}` stays bounded. -/
theorem finite_translatedLatticePointSet (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) (hb : Bornology.IsBounded P) :
    Set.Finite (translatedLatticePointSet d P t x) := by
  unfold translatedLatticePointSet stdLattice
  exact ZSpan.setFinite_inter _ ((hb.smul₀ t).add (Set.finite_singleton x).isBounded)

/-- Source-domain translated finiteness for bounded `P` and positive `t`. -/
theorem finite_translatedLatticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) (hb : Bornology.IsBounded P) :
    Set.Finite (translatedLatticePointSetPos d P t x) :=
  finite_translatedLatticePointSet d P t.val x hb

end LatticePointEnumerator
