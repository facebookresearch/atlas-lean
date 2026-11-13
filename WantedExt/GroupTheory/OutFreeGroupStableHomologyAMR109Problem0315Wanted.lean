/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The stable rational homology of Out(F_n) is trivial (Farb, Ch. 21, Conjecture 4.9)

B. Farb (ed.), Problems on Mapping Class Groups and Related Topics, Ch. 21, Conjecture 4.9: the
stable rational cohomology of `Out(F_n)` is trivial, namely `lim_{n → ∞} H̃^*(Out(F_n); ℚ) = 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import WantedExt.GroupTheory.OutFreeGroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.OutFreeGroupStableHomologyAMR109Problem0315Wanted

/-!
Source: B. Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 21,
Conjecture 4.9, p. 366. UnsolvedMath record UM-11000315 (`AMR-109-0315`), dataset
ulamai/UnsolvedMath v1.8.0.

Stated in the homology form that the resolving paper gives: for each `k ≥ 1`, `H_k(Out(F_n); ℚ) = 0`
for all large `n`, with Mathlib's group homology of the trivial representation `ℚ` and `Out(F_n)`
the `OutFreeGroup` of `WantedExt/GroupTheory/OutFreeGroupShared.lean`. Galatius proves the vanishing
of `H_k(Aut(F_n); ℚ)` (Corollary 1.2) and quotes the Hatcher–Vogtmann–Wahl theorem that `Aut(F_n) →
Out(F_n)` induces isomorphisms on `H_k` in the stable range (Theorem 1.4); he states no cohomology
form for `Out(F_n)`, so the source's cohomology form (the `ℚ`-dual statement) is not formalized, nor
its further question on twisted coefficients.
-/

open MathlibExt.GroupTheory.OutFreeGroupShared

/-- Conjecture 4.9 of Farb (ed.), Problems on Mapping Class Groups, Ch. 21, in the homology form
proved by Galatius: the stable rational homology of `Out(F_n)` is trivial: for every `k ≥ 1`,
`H_k(Out(F_n); ℚ) = 0` for all large `n`. -/
def outFreeGroupStableRationalHomologyTrivial : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N,
    Subsingleton (groupHomology (Rep.trivial ℚ (OutFreeGroup n) ℚ) k)

/--
Resolved true: Galatius proved that `H_k(Aut(F_n); ℚ) = 0` for `n > 2k + 1` (Corollary 1.2), and
`Aut(F_n) → Out(F_n)` induces an isomorphism on `H_k` for `n > 2k + 3` (Hatcher–Vogtmann–Wahl,
Theorem 1.4 there), so `H_k(Out(F_n); ℚ) = 0` for `n > 2k + 3`. Source: B. Farb (ed.), Problems on
Mapping Class Groups and Related Topics (2006), Ch. 21, Conjecture 4.9, p. 366; resolution: S.
Galatius, Stable homology of automorphism groups of free groups, Ann. of Math. 173 (2011), 705-768,
arXiv:math/0610216, Corollary 1.2: H_k(Aut(F_n); ℚ) = 0 for n > 2k + 1 ("verifies Hatcher-Vogtmann's
conjecture"); Theorem 1.4 (Hatcher-Vogtmann-Wahl, quoted there): the map α : Aut(F_n) = A_n^1 →
A_n^0 = Out(F_n) is an isomorphism on H_k for n > 2k + 3, https://arxiv.org/abs/math/0610216.
-/
public theorem_wanted outFreeGroupStableRationalHomologyTrivial_holds :
    outFreeGroupStableRationalHomologyTrivial

end MathlibExt.GroupTheory.OutFreeGroupStableHomologyAMR109Problem0315Wanted
