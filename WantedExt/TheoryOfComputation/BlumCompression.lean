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

namespace Cslib.BlumCompressionWanted

/-- **Blum's compression theorem**: for every Blum measure and every total
recursive `g`, there is a total recursive function `f` such that every
program computing `f` has cost exceeding `g` at all but finitely many
inputs. Source: Blum, "A machine-independent theory of the complexity of
recursive functions", *Journal of the ACM* 14 (1967), 322–336,
Theorem 4. -/
theorem_wanted blum_compression :
  ∀ (Φ : Cslib.Decidability.BlumMeasure) (g : ℕ → ℕ), Computable g →
    ∃ f : ℕ →. ℕ, Partrec f ∧ (∀ n, (f n).Dom) ∧
      ∀ c : Nat.Partrec.Code, c.eval = f →
        ∃ N, ∀ n, N ≤ n → ∀ m, Φ.cost c n = Part.some m → g n < m

end Cslib.BlumCompressionWanted
