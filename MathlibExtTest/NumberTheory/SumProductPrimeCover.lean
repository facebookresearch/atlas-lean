/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SumProductPrimeCover
import Mathlib.Data.Nat.Prime.Basic

open scoped Pointwise
open MetaMathlibExt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- All four input sets are proper; neither the product nor the pairwise sum covers by itself.
private def nonzeroResidues : Finset (ZMod 7) := {1, 2, 3, 4, 5, 6}

example : nonzeroResidues * nonzeroResidues ≠ Finset.univ := by decide

example : ({0, 1, 2} : Finset (ZMod 7)) + {0, 1, 2, 3} ≠ Finset.univ := by decide

example : nonzeroResidues * nonzeroResidues + {0, 1, 2} + {0, 1, 2, 3} = Finset.univ :=
  product_add_add_eq_univ_of_card_mul_gt (p := 7) (A₁ := nonzeroResidues) (A₂ := {0, 1, 2})
    (A₃ := {0, 1, 2, 3}) (D := nonzeroResidues) (h := by decide)

-- Equality at the threshold does not supply the theorem's strict hypothesis.
example : ¬ (7 ^ 3 < ({0} : Finset (ZMod 7)).card * (Finset.univ : Finset (ZMod 7)).card ^ 3) := by
  rw [Finset.card_singleton, Finset.card_univ, ZMod.card, one_mul]
  exact lt_irrefl _

-- With no size condition, the cover can fail even with all inputs nonempty.
example : ({0} : Finset (ZMod 7)) * nonzeroResidues + {0, 1, 2} + {0, 1, 2, 3} ≠ Finset.univ := by
  decide
