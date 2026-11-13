/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic

/-!
# Generalized rascal triangle

Formalizes the required definition clause for the generalized rascal triangle
(concept `jis_sem_50bab0d7e77b4e96e0b23ce0`, statement `jis_3eaa558f60d302159fbb092e`).

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL23/Hotchkiss/hotchkiss4.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Generalized rascal triangle.** An integer array $T(r, k)$, indexed by natural numbers $r$
and $k$, is a generalized rascal triangle when there exist integers $c$, $d$, $d_1$, $d_2$ such
that $T(r, k) = c + k\,d_1 + r\,d_2 + r k\,d$ for all natural numbers $r$ and $k$. -/
public def IsGeneralizedRascalTriangle (T : ℕ → ℕ → ℤ) : Prop :=
  ∃ c d d₁ d₂ : ℤ, ∀ r k : ℕ,
    T r k = c + (k : ℤ) * d₁ + (r : ℤ) * d₂ + (r : ℤ) * (k : ℤ) * d

end MetaMathlibExt

end
