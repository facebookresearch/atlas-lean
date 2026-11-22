/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Erdős sumset conjecture (Erdős Problem 109)

Erdős Problem 109: any `A ⊆ ℕ` of positive upper density contains a sumset `B + C` where both `B`
and `C` are infinite.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.Combinatorics.SumsetInPositiveDensityErdosProblem109Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #109, https://www.erdosproblems.com/109 (status PROVED
(LEAN)). UnsolvedMath record UM-30006725 (`EP-109`), dataset ulamai/UnsolvedMath v1.8.0.

Upper density is `MathlibExt`'s `Set.upperDensity`, `limsup_{N → ∞} |A ∩ [0, N)| / N`. Compared with
the formal-conjectures statement `ErdosProblems/109.lean` (equivalent; no code imported).
-/

open Pointwise

/-- Erdős Problem 109 (the Erdős sumset conjecture): every `A ⊆ ℕ` of positive upper density
contains `B + C` for some infinite `B, C ⊆ ℕ`. -/
def sumsetInPositiveUpperDensity : Prop :=
  ∀ A : Set ℕ, 0 < A.upperDensity → ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A

/--
Resolved true: Moreira, Richter and Robertson proved that every `A ⊆ ℕ` of positive upper density
contains `B + C` with `B, C` infinite; erdosproblems.com/109 lists the problem as proved, with a
formal proof in plby/lean-proofs (`Erdos109.lean`). Source: T. F. Bloom, Erdős Problems, Problem
#109, https://www.erdosproblems.com/109 (status PROVED (LEAN)); resolution: J. Moreira, F. K.
Richter and D. Robertson, A proof of a sumset conjecture of Erdős, Ann. of Math. (2) (2019),
605-652, main theorem (erdosproblems.com/109),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos109.lean#L9074.
-/
public theorem_wanted sumsetInPositiveUpperDensity_holds : sumsetInPositiveUpperDensity

end MathlibExt.Combinatorics.SumsetInPositiveDensityErdosProblem109Wanted
