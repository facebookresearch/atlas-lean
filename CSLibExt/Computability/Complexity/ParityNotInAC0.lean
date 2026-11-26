/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.Smolensky

/-!
# Parity is not in AC0

Every circuit family witnessing membership in $\mathsf{AC}^0$ also witnesses membership in
$\mathsf{AC}^0[m]$ for every modulus $m$, since it contains no modular gates
(`Cslib.Complexity.Classes.ac0_subset_ac0Mod`).
Applying this inclusion at $m = 3$ to Smolensky's lower bound gives `parity_not_in_ac0`.

Sources for the method: A. A. Razborov, "Lower bounds on the size of bounded depth networks over
a complete basis with logical addition", Mat. Zametki 41 (1987), 598-607; English translation
Math. Notes 41 (1987), 333-338; R. Smolensky, "Algebraic methods in the theory of lower bounds
for Boolean circuit complexity", Proceedings of the Nineteenth Annual ACM Symposium on Theory of
Computing (STOC 1987), 77-82.

Source:
M. Furst, J. Saxe, and M. Sipser, "Parity, circuits, and the polynomial-time hierarchy",
Mathematical Systems Theory 17 (1984), 13-27; M. Ajtai, "Σ₁¹-formulae on finite structures",
Annals of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits", Proceedings of the Eighteenth Annual ACM Symposium on Theory of
Computing (STOC 1986), 6-20.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0

open Cslib.Complexity.Classes

/-- **Parity is not in AC0.** The parity language, which accepts a bitstring exactly when an odd
number of its entries are true, is not in the class $\mathsf{AC}^0$.

Source: M. Furst, J. Saxe, and M. Sipser, "Parity, circuits, and the polynomial-time hierarchy",
Mathematical Systems Theory 17 (1984), 13-27; M. Ajtai, "Σ₁¹-formulae on finite structures",
Annals of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits", Proceedings of the Eighteenth Annual ACM Symposium on Theory of
Computing (STOC 1986), 6-20. -/
public theorem parity_not_in_ac0 :
    parityDec ∉ AC0 :=
  fun h => Smolensky.smolensky (ac0_subset_ac0Mod 3 h)

end MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0
