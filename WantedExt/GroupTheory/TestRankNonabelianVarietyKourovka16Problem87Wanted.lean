/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Test rank of relatively free groups and abelian varieties (Kourovka Notebook Problem 16.87)

Kourovka Notebook, Problem 16.87 (E. I. Timoshenko): let `𝔐` be a variety of groups and `G_r` a free
`r`-generator group in `𝔐`. A subset `S ⊆ G_r` is a test set if every endomorphism of `G_r`
identical on `S` is an automorphism; the minimum of the cardinalities of test sets is the test rank
of `G_r`. Suppose that the test rank of `G_r` is `r` for every `r ≥ 1`. a) Is it true that `𝔐` is an
abelian variety? b) Suppose that `𝔐` is not a periodic variety. Is it true that `𝔐` is the variety
of all abelian groups?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87

/-!
This module re-exports the statements and refutations of both parts of Kourovka Notebook
Problem 16.87 from `MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87`.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.87 (E. I. Timoshenko). UnsolvedMath
record UM-00701278 (`KOU-16.87`), dataset ulamai/UnsolvedMath v1.8.0.

A variety is given by a set of laws `W ⊆ FreeGroup ℕ`; a group lies in it when every law takes the
value `1` under every substitution. `G_r` is `Fᵣ` modulo its verbal subgroup, the normal closure of
all values of the laws in `Fᵣ`. The test rank is the minimum of `Set.encard` over test sets. The
variety is abelian when all its groups are abelian, periodic when some exponent `n > 0` holds in all
its groups, and equal to the variety of all abelian groups when its groups are exactly the abelian
groups (groups taken in `Type`).
-/
