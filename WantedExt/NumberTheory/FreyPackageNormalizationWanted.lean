/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FreyPackage_of_counterexample.lean` (statement only;
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_of_counterexample.lean):
Copyright (c) 2026 Anthropic, PBC (adapted statement).
Released under the Apache License, Version 2.0; see the upstream LICENSE:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/LICENSE
Authors: Anthropic (project attribution in `formalization.yaml`; no per-file author list).
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FreyCurve
import Batteries.Util.ProofWanted

/-! # Normalizing a prime-exponent Fermat solution -/

@[expose] public section

/-- **Normalizing a prime-exponent Fermat solution.** Suppose $a,b,c$ are nonzero integers,
$p$ is a natural prime with $p\ge5$, and $a^p+b^p=c^p$. Then a Frey package exists: a tuple
of nonzero integers $a',b',c'$ satisfying the Fermat equation at a prime exponent at least five,
with $\gcd(a',b')=1$, $a'\equiv3\pmod4$, and $b'\equiv0\pmod2$. The conclusion is existence
of a package, without an explicit equality identifying its exponent with $p$.

Sources: the Frey–Serre proof strategy and the [Imperial College London Fermat project](https://github.com/ImperialCollegeLondon/FLT) for the normalized package and curve model; Anthropic's [Frey package normalization statement](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_of_counterexample.lean). -/
public theorem_wanted FreyPackage.exists_of_fermat_counterexample (a b c : ℤ) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : a ^ p + b ^ p = c ^ p) : Nonempty FreyPackage
