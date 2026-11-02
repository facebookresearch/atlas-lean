/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Darts of the square lattice

A dart is an oriented edge of `ℤ²`, with a tail, a head, and the unit direction vector `head -
tail`. Darts crossing the boundary of a finite set of sites are the building blocks of the boundary
contours used in the lattice Jordan curve arguments.

## Main definitions

* `StatMech.Lattice.Dart`: an oriented nearest-neighbour edge of `ℤ²`.
* `StatMech.Lattice.Dart.rev`: the reversed dart.
* `StatMech.Lattice.Dart.dir`: the direction `head - tail`, a unit vector.
* `StatMech.Lattice.Dart.equivSimpleGraphDart`: the identification with Mathlib's `SimpleGraph.Dart`
  of the square lattice.

## Main results

* `StatMech.Lattice.rot90Fun_four`: the quarter-turn rotation has order four.
* `StatMech.Lattice.Dart.dir_rev`: reversing a dart negates its direction.
-/

@[expose] public section

open SimpleGraph

namespace StatMech

namespace Lattice

theorem rot90Fun_rot90Fun (x : Site 2) : rot90Fun (rot90Fun x) = -x := by
  funext i; fin_cases i <;> simp [rot90Fun]

theorem rot90Fun_four (x : Site 2) :
    rot90Fun (rot90Fun (rot90Fun (rot90Fun x))) = x := by
  rw [rot90Fun_rot90Fun, ← rot90Fun_rot90Fun]
  funext i; fin_cases i <;> simp [rot90Fun]

theorem rot90Fun_iterate_four : rot90Fun ∘ rot90Fun ∘ rot90Fun ∘ rot90Fun = id := by
  funext x; exact rot90Fun_four x

/-- An oriented edge of the square lattice: a pair of nearest-neighbour sites. This is the same data
as Mathlib's `SimpleGraph.Dart` of `hypercubicLattice 2`; see
`StatMech.Lattice.Dart.equivSimpleGraphDart`. -/
structure Dart where
  /-- The site the dart starts at. -/
  tail : Site 2
  /-- The site the dart points to. -/
  head : Site 2
  /-- The tail and head are nearest neighbours. -/
  adj : (hypercubicLattice 2).Adj tail head

namespace Dart

@[ext] theorem ext {d e : Dart} (ht : d.tail = e.tail) (hh : d.head = e.head) :
    d = e := by
  cases d; cases e; cases ht; cases hh; rfl

/-- The dart with tail and head exchanged. -/
def rev (d : Dart) : Dart where
  tail := d.head
  head := d.tail
  adj := d.adj.symm

@[simp] theorem rev_tail (d : Dart) : d.rev.tail = d.head := rfl
@[simp] theorem rev_head (d : Dart) : d.rev.head = d.tail := rfl

@[simp] theorem rev_rev (d : Dart) : d.rev.rev = d := rfl

/-- The direction `head - tail` of a dart, one of the four unit vectors of `ℤ²`. -/
def dir (d : Dart) : Site 2 := d.head - d.tail

@[simp] theorem dir_def (d : Dart) : d.dir = d.head - d.tail := rfl

@[simp] theorem dir_rev (d : Dart) : d.rev.dir = - d.dir := by
  simp only [dir, rev_tail, rev_head]; abel

/-- Lattice darts are exactly Mathlib's darts of the square lattice. -/
def equivSimpleGraphDart : Dart ≃ (hypercubicLattice 2).Dart where
  toFun d := ⟨(d.tail, d.head), d.adj⟩
  invFun d := ⟨d.fst, d.snd, d.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivSimpleGraphDart_fst (d : Dart) :
    (equivSimpleGraphDart d).fst = d.tail := rfl

@[simp] theorem equivSimpleGraphDart_snd (d : Dart) :
    (equivSimpleGraphDart d).snd = d.head := rfl

/-- Reversing a lattice dart corresponds to `SimpleGraph.Dart.symm`. -/
theorem equivSimpleGraphDart_rev (d : Dart) :
    equivSimpleGraphDart d.rev = (equivSimpleGraphDart d).symm := rfl

end Dart

end Lattice

end StatMech
