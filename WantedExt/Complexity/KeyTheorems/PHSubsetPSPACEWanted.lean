/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The polynomial hierarchy is contained in PSPACE

Source:
L. J. Stockmeyer, "The polynomial-time hierarchy", Theoretical Computer Science 3 (1977), 1-22;
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Theorem 5.4.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PHSubsetPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# The polynomial hierarchy is contained in PSPACE

Every language in the polynomial hierarchy is in polynomial space: a `Σ_k^p` language can be
decided by enumerating its polynomially many witness blocks in polynomial space.
-/

/-- **The polynomial hierarchy is contained in PSPACE.** Source: L. J. Stockmeyer, "The
polynomial-time hierarchy", Theoretical Computer Science 3 (1977), 1-22; S. Arora and B.
Barak, Computational Complexity: A Modern Approach, 2009, Theorem 5.4. -/
public theorem_wanted ph_subset_pspace :
    PH ⊆ PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.PHSubsetPSPACE
