/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 361, Logic 362

/-!
# Unbounded family; Bounding number

## References

* Textbook (Jech) (for `IsUnboundedFamily`, `boundingNumber`)
-/

open Cardinal Ordinal Set Order

namespace MetaMathlibExt

-- Logic 361: Unbounded family

/-- **Unbounded family.** A family $F$ of functions $\mathbb{N} \to \mathbb{N}$ is unbounded if no
function $g : \mathbb{N} \to \mathbb{N}$ bounds every member of $F$, where $g$ bounds $f$ if there
is an $N$ such that $f(n) \le g(n)$ for all $n \ge N$.
-/
def IsUnboundedFamily (F : Set (ℕ → ℕ)) : Prop :=
  ¬ ∃ g : ℕ → ℕ, ∀ f ∈ F, f ≤ᶠ[Filter.atTop] g

-- Logic 362: Bounding number

/-- **Bounding number.** The bounding number $\mathfrak{b}$ is the infimum of the cardinalities of
all unbounded families of functions $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def boundingNumber : Cardinal :=
  sInf {c : Cardinal | ∃ F : Set (ℕ → ℕ), IsUnboundedFamily F ∧ #F = c}

end MetaMathlibExt

end
