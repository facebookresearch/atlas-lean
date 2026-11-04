/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.Data.Finset.Card

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 31

/-!
# Homogeneous set

## References

* Jech (for `IsHomogeneousFor`)
-/

namespace MetaMathlibExt

-- Logic 31: Homogeneous set

/-- **Homogeneous set.** Let $c$ assign a colour in $\gamma$ to each finite subset of a type
$I$, and let $n \in \mathbb{N}$. A set $H \subseteq I$ is homogeneous for $c$ with colour
$k \in \gamma$ if $c(s) = k$ for every $n$-element subset $s$ of $H$.

Only the values of $c$ on $n$-element sets matter, so $c$ plays the role of a colouring
$[I]^n \to \gamma$ of the $n$-element subsets of $I$.
-/
def IsHomogeneousFor {I : Type*} {γ : Type*} (n : ℕ) (c : Finset I → γ) (H : Set I) (k : γ) : Prop :=
  ∀ s : Finset I, s.card = n → (s : Set I) ⊆ H → c s = k

end MetaMathlibExt

end
