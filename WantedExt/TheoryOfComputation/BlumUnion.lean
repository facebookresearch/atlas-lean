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

namespace Cslib.BlumUnionWanted

/-- **Blum's union theorem**: for every Blum measure and every uniformly
computable (`Computable₂ t`, i.e. computable as a function on pairs, not
merely pointwise per row) nondecreasing sequence of total bounds, the union
of the Blum
classes is itself a Blum class. Source: Blum, "A machine-independent theory
of the complexity of recursive functions", *Journal of the ACM* 14 (1967),
322–336, Theorem 3; McCreight–Meyer, "Classes of computable functions
defined by bounds on computation", *Proceedings of the ACM Symposium on
Theory of Computing* (1969), 79–88. Here `BlumClass` is the eventual class
(`Blum.lean`): the cost bound holds for all but finitely many inputs, as in
Blum's Definition 2. -/
theorem_wanted blum_union :
  ∀ (Φ : Cslib.Decidability.BlumMeasure) (t : ℕ → ℕ → ℕ),
    Computable₂ t → (∀ i n, t i n ≤ t (i + 1) n) →
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ f : ℕ →. ℕ,
      (∃ i, Cslib.Decidability.BlumClass Φ (t i) f) ↔
        Cslib.Decidability.BlumClass Φ g f

end Cslib.BlumUnionWanted
