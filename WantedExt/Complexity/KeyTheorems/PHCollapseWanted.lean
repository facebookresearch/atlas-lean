/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# If P = NP then the polynomial hierarchy collapses to P

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009 (PH collapses to P if
P = NP); L. J. Stockmeyer, "The polynomial-time hierarchy", Theoretical Computer Science 3
(1977), 1-22.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PHCollapse

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# If P = NP then the polynomial hierarchy collapses to P

If `P = NP`, the polynomial hierarchy collapses to `P`: every level `Σ_k` is in `P`, by
induction on the quantifier blocks. `P = NP` implies `P = coNP` (since `P` is closed under
complement), so each universal block can be replaced by an existential one; collapsing the
blocks one at a time shows every `Σ_k` level equals `NP = P`. `PH` is the alternating-
quantifier hierarchy of the shared file.
-/

/-- **If P = NP then the polynomial hierarchy collapses to P.** Source: S. Arora and B. Barak,
Computational Complexity: A Modern Approach, 2009 (PH collapses to P if P = NP); L. J.
Stockmeyer, "The polynomial-time hierarchy", Theoretical Computer Science 3 (1977), 1-22. -/
public theorem_wanted ph_collapses :
    MetaMathlibExt.ComplexityTheory.P = MetaMathlibExt.ComplexityTheory.NP →
      PH = MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.PHCollapse
