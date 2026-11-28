# Fermionic swap network

The fermionic swap gate exchanges two modes with the fermionic sign; alternating layers of nearest-neighbour fermionic swaps reverse the mode order in $N$ layers and swap every pair of modes exactly once.

For modes $p<q$ of $\mathcal F_M$ the fermionic swap is

$$
f_{pq}=\mathbf 1+a_p^\dagger a_q+a_q^\dagger a_p-a_p^\dagger a_p-a_q^\dagger a_q .
$$

It is Hermitian and unitary with $f_{pq}^2=\mathbf 1$, and $f_{pq}a_pf_{pq}=a_q$, $f_{pq}a_qf_{pq}=a_p$, $f_{pq}a_rf_{pq}=a_r$ for $r\notin\{p,q\}$. On occupation states it fixes states with both modes empty, multiplies by $-1$ states with both occupied, and when exactly one of $p,q$ is occupied it moves the occupation to the other mode with the sign $(-1)^{\sum_{p<k<q}n_k}$; the sign is $+1$ for adjacent modes ($q=p+1$), and for example $f_{13}|011\rangle=-|110\rangle$. Under the Jordan–Wigner encoding, $f_{p,p+1}$ is a two-qubit nearest-neighbour gate. A **fermionic swap network** on $N$ modes on a line applies $N$ layers: odd layers swap positions $(1,2),(3,4),\dots$ and even layers positions $(2,3),(4,5),\dots$ (for $N=2$ the second layer is empty). After the $N$ layers the order of the modes is reversed and each of the $\binom N2$ pairs of modes has been swapped exactly once; pairs can be adjacent more than once.

## Context

Research. Kivlichan, McClean, Wiebe, Gidney, Aspuru-Guzik, Chan and Babbush use the network to implement a Trotter step of the electronic-structure Hamiltonian in a suitable basis with depth $N$ on a linear qubit array, applying each pair interaction when its two orbitals are adjacent. The network itself is canonical fermionic-circuit combinatorics.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)
- [Jordan–Wigner transformation](../../../ComputerScience/quantum-algorithms/fermion-to-qubit-encodings/jordan-wigner-transformation.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

Operator identities: $a_p^\dagger a_q$ and $a_q^\dagger a_p$ carry the sign of the occupied modes strictly between $p$ and $q$, which gives the ket signs; the conjugation identities follow from the anticommutation relations (even operators commute with $a_r$, $r\notin\{p,q\}$). Network: track each mode's position. Unfold positions onto a cycle of length $2N$ by assigning $i$ to a mode at position $i$ moving right and $2N+1-i$ to one moving left; a mode starting at an odd position moves right in layer 1 and one at an even position moves left (or idles at the end), and the parity of the layers keeps every move aligned, so each layer advances every unfolded coordinate by one, a turn at an end costing one idle layer. After $N$ layers each mode starting at $i$ is at position $N+1-i$. Counting swaps per layer gives $\binom N2$ in total; reversal requires each pair to cross at least once, and each swap crosses exactly one pair, so each pair is swapped exactly once.

## Sources

- Ian D. Kivlichan, Jarrod McClean, Nathan Wiebe, Craig Gidney, Alán Aspuru-Guzik, Garnet Kin-Lic Chan and Ryan Babbush, *Quantum Simulation of Electronic Structure with Linear Depth and Connectivity*, Phys. Rev. Lett. 120 (2018) 110501; numbers from arXiv:1711.04789v2, Eqs. (3)–(4), Fig. 1 and the swap-network argument. <https://arxiv.org/abs/1711.04789v2>
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §5.1.1, Eq. (46). <https://arxiv.org/abs/1812.09976v2>
