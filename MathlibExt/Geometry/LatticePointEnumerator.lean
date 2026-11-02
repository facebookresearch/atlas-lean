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
public import Mathlib.Data.Real.Basic
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

/-- **The standard integer lattice.** For $d \in \mathbb{N}$, the standard integer lattice
$\mathbb{Z}^d$ is the $\mathbb{Z}$-submodule of $\mathbb{R}^d$ (the real-valued functions on
$\{0, \dots, d-1\}$) spanned by the standard basis vectors $e_0, \dots, e_{d-1}$. -/
noncomputable def stdLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

/-- **Membership in the standard lattice.** For a natural number $d$, a vector
$x \in \mathbb{R}^d$ lies in the standard lattice $\mathbb{Z}^d$, the integer span of the standard
basis vectors of $\mathbb{R}^d$, exactly when every coordinate $x_i$ of $x$ is an integer. -/
theorem mem_stdLattice_iff {d : ℕ} {x : Fin d → ℝ} :
    x ∈ stdLattice d ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
  unfold stdLattice
  rw [(Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ x]
  simp [Pi.basisFun_repr]

/-- **Lattice points in a dilate.** For a natural number $d$, a set $P \subseteq \mathbb{R}^d$
and a real number $t$, this is the set $(tP) \cap \mathbb{Z}^d$ of points of the integer lattice
$\mathbb{Z}^d$ in the dilate $tP = \{tp : p \in P\}$.

The source only uses this set for $t > 0$. -/
noncomputable def latticePointSet (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ) :
    Set (Fin d → ℝ) :=
  (t • P) ∩ (stdLattice d : Set (Fin d → ℝ))

/-- **Lattice-point count of a real dilate.** For a natural number $d$, a set
$P \subseteq \mathbb{R}^d$ and a real number $t$, this is the number of elements of the set
$(tP) \cap \mathbb{Z}^d$ of points of the integer lattice $\mathbb{Z}^d$ in the dilate
$tP = \{tp : p \in P\}$, where an infinite set is assigned the value $0$.

For unbounded $P$ the set can be infinite, so the value $0$ is a convention and not a count;
the lattice-point enumerator for bounded $P$ and $t > 0$ is the faithful count. -/
noncomputable def latticeEnumerator (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ) : ℕ :=
  Set.ncard (latticePointSet d P t)

/-- **Translated lattice-point set.** For $d \in \mathbb{N}$, a set $P \subseteq \mathbb{R}^d$, a
real $t$ and $x \in \mathbb{R}^d$, the translated lattice-point set is
$((t \cdot P) + x) \cap \mathbb{Z}^d$, the set of points of the standard integer lattice
$\mathbb{Z}^d$ in the dilate $t \cdot P$ translated by $x$.

The dilation comes first: in general this set differs from $(t \cdot (P + x)) \cap \mathbb{Z}^d$.

Source: Rocha-Neves, arXiv:2608.11078v1, lines 62-67. -/
noncomputable def translatedLatticePointSet (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  ((t • P) + {x}) ∩ (stdLattice d : Set (Fin d → ℝ))

/-- **Translated lattice-point count for arbitrary sets.** For $d \in \mathbb{N}$, a set
$P \subseteq \mathbb{R}^d$, a real $t$ and $x \in \mathbb{R}^d$, the translated lattice-point
count is the number of elements of the translated lattice-point set
$((t \cdot P) + x) \cap \mathbb{Z}^d$, taken to be $0$ when this set is infinite. -/
noncomputable def translatedLatticeEnumerator (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) : ℕ :=
  Set.ncard (translatedLatticePointSet d P t x)

/-- **Lattice points in a positive dilate.** For a natural number $d$, a set
$P \subseteq \mathbb{R}^d$ and a real number $t > 0$, this is the set $(tP) \cap \mathbb{Z}^d$ of
points of the integer lattice $\mathbb{Z}^d$ in the dilate $tP = \{tp : p \in P\}$.

No boundedness of $P$ is assumed. -/
noncomputable def latticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) : Set (Fin d → ℝ) :=
  latticePointSet d P t.val

/-- **Lattice-point enumerator.** For a natural number $d$, a bounded set
$P \subseteq \mathbb{R}^d$ and a real number $t > 0$, the lattice-point enumerator $L_P(t)$ is
the number of points of the integer lattice $\mathbb{Z}^d$ in the dilate
$tP = \{tp : p \in P\}$, that is, $L_P(t) = |(tP) \cap \mathbb{Z}^d|$.

Since $P$ is bounded, the set $(tP) \cap \mathbb{Z}^d$ is finite, so $L_P(t)$ is its actual
number of elements.

Source: Rocha-Neves, A Fourier-analytic Uniqueness Theorem for Lattice-point Enumerators,
arXiv:2608.11078v1, lines 24-31. -/
noncomputable def latticeEnumeratorPos (d : ℕ) (P : Set (Fin d → ℝ))
    (_hb : Bornology.IsBounded P) (t : {t : ℝ // 0 < t}) : ℕ :=
  latticeEnumerator d P t.val

/-- **Translated lattice-point set at a positive dilation.** For $d \in \mathbb{N}$, a set
$P \subseteq \mathbb{R}^d$, a real $t > 0$ and $x \in \mathbb{R}^d$, this is the set
$((t \cdot P) + x) \cap \mathbb{Z}^d$ of points of the standard integer lattice $\mathbb{Z}^d$
in the dilate $t \cdot P$ translated by $x$. No boundedness of $P$ is assumed. -/
noncomputable def translatedLatticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  translatedLatticePointSet d P t.val x

/-- **Translated lattice-point enumerator of a bounded set.** Let $d \in \mathbb{N}$, let
$P \subseteq \mathbb{R}^d$ be a bounded set, let $t > 0$ be real and let $x \in \mathbb{R}^d$. The
translated lattice-point enumerator is $F_{t,P}(x) = |((t \cdot P) + x) \cap \mathbb{Z}^d|$, the
number of points of the standard integer lattice $\mathbb{Z}^d$ in the dilate $t \cdot P$
translated by $x$.

Source: Rocha-Neves, arXiv:2608.11078v1, lines 62-67. -/
noncomputable def translatedLatticeEnumeratorPos (d : ℕ) (P : Set (Fin d → ℝ))
    (_hb : Bornology.IsBounded P) (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) : ℕ :=
  translatedLatticeEnumerator d P t.val x

/-- **The origin is a lattice point.** For every $d \in \mathbb{N}$, the origin of $\mathbb{R}^d$
lies in the standard integer lattice $\mathbb{Z}^d$. -/
theorem zero_mem_stdLattice (d : ℕ) : (0 : Fin d → ℝ) ∈ stdLattice d :=
  Submodule.zero_mem _

/-- **The lattice-point count of the empty set vanishes.** For every natural number $d$ and every
real number $t$, the lattice-point count of the empty set $\emptyset \subseteq \mathbb{R}^d$ at the
dilate $t$ is $0$. -/
@[simp]
theorem latticeEnumerator_empty (d : ℕ) (t : ℝ) :
    latticeEnumerator d ∅ t = 0 := by
  simp [latticeEnumerator, latticePointSet]

/-- **The translated lattice-point count of the empty set is zero.** For every $d \in \mathbb{N}$,
every real $t$ and every $x \in \mathbb{R}^d$, the translated lattice-point count
$|((t \cdot \emptyset) + x) \cap \mathbb{Z}^d|$ is $0$. -/
@[simp]
theorem translatedLatticeEnumerator_empty (d : ℕ) (t : ℝ) (x : Fin d → ℝ) :
    translatedLatticeEnumerator d ∅ t x = 0 := by
  simp [translatedLatticeEnumerator, translatedLatticePointSet]

/-- **Finiteness of the lattice points in a dilate.** For a natural number $d$, a bounded set
$P \subseteq \mathbb{R}^d$ and any real number $t$, the set $(tP) \cap \mathbb{Z}^d$ of points of
the integer lattice $\mathbb{Z}^d$ in the dilate $tP = \{tp : p \in P\}$ is finite.

No positivity of $t$ is needed. -/
theorem finite_latticePointSet (d : ℕ) (P : Set (Fin d → ℝ)) (t : ℝ)
    (hb : Bornology.IsBounded P) :
    Set.Finite (latticePointSet d P t) := by
  unfold latticePointSet stdLattice
  exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin d)) (hb.smul₀ t)

/-- **Finiteness of the lattice points in a positive dilate.** For a natural number $d$, a
bounded set $P \subseteq \mathbb{R}^d$ and a real number $t > 0$, the set $(tP) \cap \mathbb{Z}^d$
of points of the integer lattice $\mathbb{Z}^d$ in the dilate $tP = \{tp : p \in P\}$ is
finite. -/
theorem finite_latticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (hb : Bornology.IsBounded P) :
    Set.Finite (latticePointSetPos d P t) :=
  finite_latticePointSet d P t.val hb

/-- **Finiteness of the lattice points in a translated dilate.** For a natural number $d$, a
bounded set $P \subseteq \mathbb{R}^d$, any real number $t$ and a vector $x \in \mathbb{R}^d$,
the set $(tP + x) \cap \mathbb{Z}^d$ of points of the integer lattice $\mathbb{Z}^d$ in the
translated dilate $tP + x = \{tp + x : p \in P\}$ is finite. -/
theorem finite_translatedLatticePointSet (d : ℕ) (P : Set (Fin d → ℝ))
    (t : ℝ) (x : Fin d → ℝ) (hb : Bornology.IsBounded P) :
    Set.Finite (translatedLatticePointSet d P t x) := by
  unfold translatedLatticePointSet stdLattice
  exact ZSpan.setFinite_inter _ ((hb.smul₀ t).add (Set.finite_singleton x).isBounded)

/-- **Finiteness of the lattice points in a translated positive dilate.** For a natural number
$d$, a bounded set $P \subseteq \mathbb{R}^d$, a real number $t > 0$ and a vector
$x \in \mathbb{R}^d$, the set $(tP + x) \cap \mathbb{Z}^d$ of points of the integer lattice
$\mathbb{Z}^d$ in the translated dilate $tP + x = \{tp + x : p \in P\}$ is finite. -/
theorem finite_translatedLatticePointSetPos (d : ℕ) (P : Set (Fin d → ℝ))
    (t : {t : ℝ // 0 < t}) (x : Fin d → ℝ) (hb : Bornology.IsBounded P) :
    Set.Finite (translatedLatticePointSetPos d P t x) :=
  finite_translatedLatticePointSet d P t.val x hb

end LatticePointEnumerator
