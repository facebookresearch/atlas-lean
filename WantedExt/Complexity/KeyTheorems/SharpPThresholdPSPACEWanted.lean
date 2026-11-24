/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Threshold languages of #P functions are in PSPACE

Source:
L. G. Valiant, "The complexity of enumeration and reliability problems" (1979); S. Arora and B.
Barak, Computational Complexity: A Modern Approach, 2009, Theorem 9.3 (#P ⊆ PSPACE in the
threshold-language form).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.SharpPThresholdPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Threshold languages of #P functions are in PSPACE

For every `#P` function `f`, the threshold language `{ (x, k) | k ≤ f x }` is in `PSPACE`:
counting can be done by enumerating witnesses in polynomial space. The pair `(x, k)` uses the
canonical bitstring encoding.
-/


/-- **Threshold language of a counting function.** For a function $f$ from bitstrings to
natural numbers, the threshold language of $f$ is the decision problem that accepts a bitstring
$y$ exactly when decoding $y$ with the canonical bitstring encoding of pairs of a bitstring and
a natural number succeeds and gives a pair $(x, k)$ with $k \le f(x)$; bitstrings that do not
decode are rejected. -/
noncomputable def thresholdLang (f : List Bool → ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun y =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List Bool × ℕ) y with
  | some (x, k) => decide (k ≤ f x)
  | none => false

/-- **Threshold languages of #P functions are in PSPACE.** For every function $f$ in $\#P$,
the threshold language of $f$, which accepts a bitstring exactly when it decodes, under the
canonical bitstring encoding of pairs, to a pair $(x, k)$ of a bitstring $x$ and a natural
number $k$ with $k \le f(x)$, is in PSPACE.

Source: L. G. Valiant, "The
complexity of enumeration and reliability problems" (1979); S. Arora and B. Barak,
Computational Complexity: A Modern Approach, 2009, Theorem 9.3 (#P ⊆ PSPACE in the
threshold-language form). -/
public theorem_wanted sharpP_threshold_pspace :
    ∀ f ∈ SharpP, thresholdLang f ∈ PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.SharpPThresholdPSPACE
