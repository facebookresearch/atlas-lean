/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual

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







structure Dart where
  
  tail : Site 2
  
  head : Site 2
  
  adj : (hypercubicLattice 2).Adj tail head

namespace Dart



@[ext] theorem ext {d e : Dart} (ht : d.tail = e.tail) (hh : d.head = e.head) :
    d = e := by
  cases d; cases e; cases ht; cases hh; rfl



def rev (d : Dart) : Dart where
  tail := d.head
  head := d.tail
  adj := d.adj.symm

@[simp] theorem rev_tail (d : Dart) : d.rev.tail = d.head := rfl
@[simp] theorem rev_head (d : Dart) : d.rev.head = d.tail := rfl


@[simp] theorem rev_rev (d : Dart) : d.rev.rev = d := rfl



def dir (d : Dart) : Site 2 := d.head - d.tail

@[simp] theorem dir_def (d : Dart) : d.dir = d.head - d.tail := rfl


@[simp] theorem dir_rev (d : Dart) : d.rev.dir = - d.dir := by
  simp only [dir, rev_tail, rev_head]; abel

end Dart

end Lattice

end StatMech
