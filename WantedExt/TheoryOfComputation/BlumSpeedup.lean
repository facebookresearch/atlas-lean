/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.Blum

@[expose] public section

set_option autoImplicit false

namespace Cslib.BlumSpeedupWanted

/-- **Blum's speedup theorem**: for every Blum measure and every total
recursive two-argument comparison function `r`, there is a total recursive
function `g` such that every program computing `g` can be sped up by more
than `r`: for every program `c` computing `g` there is another program
`c'` computing `g` with `r n (Φ_{c'}(n)) < Φ_c(n)` for all but finitely
many `n`. The comparison is eventual, depends on the input `n` as well as
the faster cost, and runs in the source direction (`r` bounds the slower
cost in terms of the faster one). Source: Blum, "A machine-independent
theory of the complexity of recursive functions", *Journal of the ACM* 14
(1967), 322–336, Theorem 5. -/
theorem_wanted blum_speedup :
  ∀ (Φ : Cslib.Decidability.BlumMeasure) (r : ℕ → ℕ → ℕ), Computable₂ r →
    ∃ g : ℕ →. ℕ, Partrec g ∧ (∀ n, (g n).Dom) ∧
      ∀ c : Nat.Partrec.Code, c.eval = g →
        ∃ c' : Nat.Partrec.Code, c'.eval = g ∧
          ∃ N, ∀ n, N ≤ n → ∀ m m',
            Φ.cost c n = Part.some m → Φ.cost c' n = Part.some m' →
              r n m' < m

end Cslib.BlumSpeedupWanted
