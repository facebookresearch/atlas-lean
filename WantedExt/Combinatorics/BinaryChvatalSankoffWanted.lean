/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Combinatorics.BinaryChvatalSankoff

/-!
# Binary Chvátal--Sankoff constant and catalogue bounds

Source: Optimization Problems, `constants/31a.md`, at revision
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; Chvátal and Sankoff,
*Longest common subsequences of two random sequences* (1975), 306--315;
Dančík (1994); Dančík and Paterson (1995); Lueker (2009);
Heineman et al., arXiv:2407.10925v1 (2024).

The constant is the limit of the expected LCS length of two independent
uniform binary strings, divided by their length. Finite-level bounds and
superadditivity prove ordinary-limit existence. The deep numerical bounds
below are proof requests, not axioms or completed proofs. Their terminating
decimals are exact rational endpoints, as in the frozen catalogue.

The catalogue's additional `0.79970` claim is explicitly AI and computer
assisted (unverified). Its proposition is recorded separately; no proof or
current resolution status is asserted. Historical computational certificates
are not replayed here. The source specifies no conjectured exact value, so
these known bounds are not registered as open conjectures.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.BinaryChvatalSankoffWanted

/-- **Dančík–Paterson upper bound for the binary Chvátal–Sankoff constant.** The binary
Chvátal–Sankoff constant $\gamma$ satisfies $\gamma \le 0.837623$, where $\gamma$ is the limit
inferior, as $n \to \infty$, of $\mathbb{E}[L_n]/n$ and $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$.

Source: Dančík--Paterson (1995), catalogue upper bound `0.837623`.
Known literature result; its proof is not supplied here. -/
theorem_wanted dancikPatersonUpperBound_wanted : dancikPatersonUpperBound

/-- **Lueker's upper bound for the binary Chvátal–Sankoff constant.** The binary Chvátal–Sankoff
constant $C_{31a}$ is at most $0.826280$.

Source: Lueker (2009), catalogue computer-assisted upper bound `0.826280`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted luekerUpperBound_wanted : luekerUpperBound

/-- **Dančík's lower bound for the binary Chvátal–Sankoff constant.** The binary
Chvátal–Sankoff constant $\gamma$ satisfies $0.773911 \le \gamma$, where $\gamma$ is the limit
inferior, as $n \to \infty$, of $\mathbb{E}[L_n]/n$ and $L_n$ is the length of a longest common
subsequence of two independent uniformly random binary strings of length $n$.

Source: Dančík (1994), catalogue computer-assisted lower bound `0.773911`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted dancikLowerBound_wanted : dancikLowerBound

/-- **Lueker's lower bound for the binary Chvátal–Sankoff constant.** For each $n$, let $E_n$ be
the expected length of a longest common subsequence of two independent uniformly random binary
strings of length $n$, and let $C$, the binary Chvátal–Sankoff constant, be the limit inferior of
$E_n / n$ as $n \to \infty$. Then $0.788071 \le C$.

Source: Lueker (2009), catalogue computer-assisted lower bound `0.788071`.
Known literature result; its proof and certificate are not supplied here. -/
theorem_wanted luekerLowerBound_wanted : luekerLowerBound

/-- **Heineman et al. lower bound for the binary Chvátal–Sankoff constant.** For each $n$, let
$E_n$ be the expected length of a longest common subsequence of two independent uniformly random
binary strings of length $n$, and let $C$, the binary Chvátal–Sankoff constant, be the limit
inferior of $E_n / n$ as $n \to \infty$. Then $0.792665992 \le C$.

Source: Heineman et al., arXiv:2407.10925v1 (2024), catalogue
computer-assisted lower bound `0.792665992`. Known literature result;
its proof and certificate are not supplied here. -/
theorem_wanted heinemanLowerBound_wanted : heinemanLowerBound

end MathlibExt.Combinatorics.BinaryChvatalSankoffWanted
