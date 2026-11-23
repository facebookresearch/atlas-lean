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

namespace Cslib.BlumGapWanted

/-- **Blum's gap theorem**: for every Blum measure and every total recursive
growth function `r` with `n ≤ r n`, there is a total recursive bound `g`
whose Blum class agrees with the Blum class at the substantially larger
bound `r ∘ g` — a gap in cost with no new functions. The previous form
(quantifying over `t` with a bound `g ≥ t` and `class t = class g`) was
trivially witnessed by `g := t`; the gap is between `g` and `r ∘ g`.
Source: Blum, "A machine-independent theory of the complexity of recursive
functions", *Journal of the ACM* 14 (1967), 322–336, Theorem 2
(Borodin–Trakhtenbrot gap theorem). Here `BlumClass` is the eventual class
(`Blum.lean`): the cost bound holds for all but finitely many inputs, as in
Blum's Definition 2. -/
theorem_wanted blum_gap :
  ∀ (Φ : Cslib.Decidability.BlumMeasure) (r : ℕ → ℕ), Computable r →
    (∀ n, n ≤ r n) →
    ∃ g : ℕ → ℕ, Computable g ∧
      Cslib.Decidability.BlumClass Φ g =
        Cslib.Decidability.BlumClass Φ (fun n ↦ r (g n))

end Cslib.BlumGapWanted
