/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.HyperbolicPascalAlternatingSums
public import MathlibExt.Combinatorics.Enumerative.LinearRecurrenceInhomogeneous

/-!
# Alternating sums in the generalized hyperbolic Pascal triangle

Statements from Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the
Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84: the identity
relating a linear recurrence `f` and an inhomogeneous recurrence `G` with the same
coefficients (Theorem 1, Corollary 1, quoted from the authors' earlier paper), and the
weighted alternating row sums of the generalized hyperbolic Pascal triangle linked to the
mosaic `{4, q}` (Corollary 2).

The recurrence (10) for the alternating row sums (Theorem 2), its generating function
(Theorem 3) and explicit formula (Theorem 4) are not stated: they fail for simple leg
sequences (see the audit table).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Convolution identity for an inhomogeneous linear recurrence.** Let $k \in \mathbb{N}$ and let
$A, f, G, w \colon \mathbb{N} \to \mathbb{C}$ be sequences such that, for every $m \ge k$,
$f_m = \sum_{i=1}^{k} A_i f_{m-i}$ and $G_m = \sum_{i=1}^{k} A_i G_{m-i} + w_{m-k}$. Then for
every $n \ge k$,

$$\sum_{j=0}^{k-1} f_j G_{n+k-j} =
\sum_{j=0}^{k-1} \sum_{i=0}^{k-1-j} f_{n-j} A_{j+1+i} G_{k-1-i} +
\sum_{j=0}^{k-2} \sum_{i=1}^{k-1-j} f_j A_i G_{n+k-j-i} + \sum_{j=0}^{n} f_{n-j} w_j.$$

The identity is quoted from Belbachir–Rami–Szalay 2022; its hypotheses $A_k \neq 0$ and
$k \ge 1$ are not needed.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Theorem 1
(`integers-2024-A84-thm-1`). -/
public theorem_wanted linearRecurrence_inhomogeneous_identity (k : ℕ) (A f G w : ℕ → ℂ)
    (hf : ∀ n, k ≤ n → f n = ∑ i ∈ Finset.Icc 1 k, A i * f (n - i))
    (hG : ∀ n, k ≤ n → G n = ∑ i ∈ Finset.Icc 1 k, A i * G (n - i) + w (n - k))
    {n : ℕ} (hn : k ≤ n) :
    ∑ j ∈ Finset.range k, f j * G (n + k - j) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (k - j), f (n - j) * A (j + 1 + i) * G (k - 1 - i) +
        ∑ j ∈ Finset.range (k - 1), ∑ i ∈ Finset.Icc 1 (k - 1 - j),
          f j * A i * G (n + k - j - i) +
        ∑ j ∈ Finset.range (n + 1), f (n - j) * w j

end

end MetaMathlibExt
