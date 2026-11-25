/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

namespace SymbolicDynamics.FullShift

/-!
# One-dimensional finite full shifts

This file provides a common API for the full two-sided shift on `N` symbols,
its unit shift and automorphism group, and the jointly periodic-point notions
used for one-dimensional cellular automata.
-/

/-- **Full shift space.** For $N \in \mathbb{N}$, the configuration space of the two-sided full
shift on $N$ symbols is the set $\{0, \dots, N-1\}^{\mathbb{Z}}$ of all bi-infinite sequences
$x = (x_i)_{i \in \mathbb{Z}}$ of symbols. It carries the product of the discrete topologies. -/
abbrev FullShiftSpace (N : ℕ) := ℤ → Fin N

/-- **Unit shift.** The unit shift on the full shift on $N$ symbols is the map $\sigma$ from
$\{0, \dots, N-1\}^{\mathbb{Z}}$ to itself given by $(\sigma x)_i = x_{i+1}$ for all
$i \in \mathbb{Z}$, the left translation by one step. -/
def unitShift (N : ℕ) : FullShiftSpace N → FullShiftSpace N :=
  shift (A := Fin N) (1 : ℤ)

@[simp]
theorem unitShift_apply (N : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    unitShift N x i = x (1 + i) :=
  rfl

/-- **The unit shift as a homeomorphism.** The unit shift $\sigma$ of the full shift on $N$
symbols, given by $(\sigma x)_i = x_{i+1}$, is a homeomorphism of
$\{0, \dots, N-1\}^{\mathbb{Z}}$ onto itself, with inverse given by
$(\sigma^{-1} x)_i = x_{i-1}$. -/
def shiftHomeomorph (N : ℕ) : FullShiftSpace N ≃ₜ FullShiftSpace N where
  toFun := unitShift N
  invFun := shift (A := Fin N) (-1 : ℤ)
  left_inv x := by
    change shift (-1) (shift 1 x) = x
    rw [← shift_add]
    simp
  right_inv x := by
    change shift 1 (shift (-1) x) = x
    rw [← shift_add]
    simp
  continuous_toFun := continuous_shift 1
  continuous_invFun := continuous_shift (-1)

@[simp]
theorem shiftHomeomorph_apply (N : ℕ) (x : FullShiftSpace N) :
    shiftHomeomorph N x = unitShift N x :=
  rfl

@[simp]
theorem shiftHomeomorph_symm_apply (N : ℕ) (x : FullShiftSpace N) (i : ℤ) :
    (shiftHomeomorph N).symm x i = x (-1 + i) :=
  rfl

/-- **Automorphism group of the full shift.** The automorphism group of the full shift on $N$
symbols is the subgroup of the group of homeomorphisms of $\{0, \dots, N-1\}^{\mathbb{Z}}$ onto
itself consisting of the homeomorphisms $\varphi$ that commute with the unit shift $\sigma$,
given by $(\sigma x)_i = x_{i+1}$, that is, $\varphi \circ \sigma = \sigma \circ \varphi$. -/
def automorphismGroup (N : ℕ) : Subgroup (FullShiftSpace N ≃ₜ FullShiftSpace N) :=
  Subgroup.centralizer {shiftHomeomorph N}

/-- **One-dimensional cellular automaton.** A map $f$ from the full shift
$\{0, \dots, N-1\}^{\mathbb{Z}}$ on $N$ symbols to itself is a one-dimensional cellular
automaton if $f$ is continuous and commutes with the unit shift $\sigma$, given by
$(\sigma x)_i = x_{i+1}$, that is, $f \circ \sigma = \sigma \circ f$.

This is the Curtis–Hedlund–Lyndon characterization of cellular automata. -/
def IsOneDimensionalCA (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) : Prop :=
  Continuous f ∧ Function.Commute f (unitShift N)

theorem isOneDimensionalCA_iff (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) :
    IsOneDimensionalCA N f ↔ Continuous f ∧ Function.Commute f (unitShift N) :=
  Iff.rfl

/-- **Jointly periodic points.** For a map $f$ from the full shift
$\{0, \dots, N-1\}^{\mathbb{Z}}$ on $N$ symbols to itself, the jointly periodic points of $f$
are the configurations $x$ that are periodic for $f$ and periodic for the unit shift $\sigma$,
given by $(\sigma x)_i = x_{i+1}$: there are $m \ge 1$ and $n \ge 1$ with $f^m(x) = x$ and
$\sigma^n(x) = x$.

No common period for $f$ and $\sigma$ is required. -/
def jointlyPeriodicPoints (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N) :
    Set (FullShiftSpace N) :=
  Function.periodicPts f ∩ Function.periodicPts (unitShift N)

@[simp]
theorem mem_jointlyPeriodicPoints (N : ℕ) (f : FullShiftSpace N → FullShiftSpace N)
    (x : FullShiftSpace N) :
    x ∈ jointlyPeriodicPoints N f ↔
      x ∈ Function.periodicPts f ∧ x ∈ Function.periodicPts (unitShift N) :=
  Iff.rfl

/-- **Joint periodic count.** For $k \in \mathbb{N}$ and a map $f$ from the full shift
$\{0, \dots, N-1\}^{\mathbb{Z}}$ on $N$ symbols to itself, $P(f, k)$ is the number of
configurations $x$ with $\sigma^k(x) = x$, where $\sigma$ is the unit shift given by
$(\sigma x)_i = x_{i+1}$, that are also periodic for $f$, that is, $f^n(x) = x$ for some
$n \ge 1$. Here $k$ need not be the least period of $x$ under $\sigma$.

The count is the cardinality of a set, taken to be $0$ when the set is infinite, which can
happen only for $k = 0$. -/
noncomputable def jointPeriodicCount (N : ℕ)
    (f : FullShiftSpace N → FullShiftSpace N) (k : ℕ) : ℕ :=
  Set.ncard {x | Function.IsPeriodicPt (unitShift N) k x ∧ x ∈ Function.periodicPts f}

/-- **Joint periodic growth rate.** For a map $f$ from the full shift $S_N$ on $N$ symbols to
itself, the joint periodic growth rate is the real number

$$\nu(f, S_N) = \limsup_{k \to \infty} P(f, k)^{1/k},$$

where $k$ ranges over the positive integers and $P(f, k)$ is the joint periodic count: the
number of configurations fixed by the $k$-th power of the unit shift that are also periodic
for $f$. -/
noncomputable def jointPeriodicGrowthRate (N : ℕ)
    (f : FullShiftSpace N → FullShiftSpace N) : ℝ :=
  Filter.limsup
    (fun k : ℕ =>
      Real.rpow (jointPeriodicCount N f (k + 1) : ℝ) (((k + 1 : ℕ) : ℝ)⁻¹))
    Filter.atTop

end SymbolicDynamics.FullShift
