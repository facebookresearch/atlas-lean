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

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Pairwise

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 11

/-!
# A Delta system

## References

* Kunen (for `IsDeltaSystem`)
-/

namespace MetaMathlibExt

-- Logic 11: A Delta system

/-- **Δ-system.** A family $A$ of subsets of a type $\alpha$ is a Δ-system with root
$r \subseteq \alpha$ if $s \cap t = r$ for any two distinct members $s$ and $t$ of $A$. -/
def IsDeltaSystem {α : Type*} (A : Set (Set α)) (r : Set α) : Prop :=
    A.Pairwise fun s t => s ∩ t = r

end MetaMathlibExt

end
