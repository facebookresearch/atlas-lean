/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.Intervals







namespace StatMech
namespace Exact3D

namespace CaseTableExample


def boolTable : RatInterval.CaseTable Bool where
  cases := Finset.univ
  interval := fun b => if b then RatInterval.point 1 else RatInterval.point 0


def classify (b : Bool) : Bool :=
  b


def value (b : Bool) : ℝ :=
  if b then 1 else 0

theorem boolTable_covers :
    RatInterval.CaseTable.Covers boolTable classify := by
  intro b
  simp [boolTable, classify]

theorem boolTable_sound :
    RatInterval.CaseTable.Sound boolTable classify value := by
  intro b
  cases b <;> simp [boolTable, classify, value, RatInterval.MemR, RatInterval.point]

end CaseTableExample

end Exact3D
end StatMech
