/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Blocks of defect zero and solutions of `[x, y] = g` (Kourovka Notebook Problem 12.80)

Kourovka Notebook, Archive of Solved Problems, Problem 12.80 (K. W. Roggenkamp; S. P. Strunkov): (a)
is the number of `p`-blocks of defect 0 of a finite group `G` equal to the number of conjugacy
classes of elements `g ∈ G` such that the number of solutions of `[x, y] = g` in `G` is not
divisible by `p`? (b) The same question for simple groups `G`.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80

@[expose] public section

namespace MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted

/--
**Kourovka Problem 12.80(a) has a negative answer.** It is not true that for every prime $p$ and
every finite group $G$ whose order is divisible by $p$, the number of irreducible complex characters
of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an element $g$
for which the number of pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$ is not
divisible by $p$.

L. Barker's counterexample: for $p = 2$ and $G = \mathbb{Z}_3 \times S_3$ there are three
irreducible characters of degree $2$, all of $2$-defect zero (so three $2$-blocks of defect zero),
but only one class, that of $(1, (123))$, with an odd number of solutions of $[x, y] = g$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale,
letter of 5 May 2021 (part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G =
ℤ_3 × S_3; (b) p = 2, G = A_5: one 2-block of defect zero, three classes ((123), (12345), (13524))
with an odd number of solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted defectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ defectZeroBlocksEqNondivisibleClasses

end MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted
