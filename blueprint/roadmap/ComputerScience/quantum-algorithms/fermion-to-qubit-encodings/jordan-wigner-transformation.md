# Jordan–Wigner transformation

The Jordan–Wigner transformation identifies the fermionic Fock space of $M$ modes with the state space of $M$ qubits, sending occupation numbers to computational-basis bits and each creation operator to a qubit raising operator preceded by a string of Pauli $Z$ operators on lower-index qubits.

Let $\mathcal F_M$ be the Fock space with occupation basis $|n_1\cdots n_M\rangle$ and $(\mathbb C^2)^{\otimes M}$ the $M$-qubit space with computational basis $|n_1\rangle\otimes\cdots\otimes|n_M\rangle$. The Jordan–Wigner map is the unitary $\Phi_{\mathrm{JW}}:|n_1\cdots n_M\rangle\mapsto|n_1\rangle\otimes\cdots\otimes|n_M\rangle$. With $Z=|0\rangle\langle0|-|1\rangle\langle1|$, $Q^+=|1\rangle\langle0|=\frac12(X-iY)$ and $Q^-=|0\rangle\langle1|$,

$$
\Phi_{\mathrm{JW}}\,a_j^\dagger\,\Phi_{\mathrm{JW}}^{-1}=Z^{\otimes(j-1)}\otimes Q^+\otimes\mathbf 1^{\otimes(M-j)},\qquad \Phi_{\mathrm{JW}}\,a_j\,\Phi_{\mathrm{JW}}^{-1}=Z^{\otimes(j-1)}\otimes Q^-\otimes\mathbf 1^{\otimes(M-j)} .
$$

Consequently the qubit operators on the right satisfy the canonical anticommutation relations, $a_j^\dagger a_j$ maps to $\frac12(\mathbf 1-Z_j)$, and every Hermitian second-quantized Hamiltonian maps to a real linear combination of Pauli strings.

## Context

Undergraduate/graduate. The standard encoding in quantum algorithms for chemistry; its operators $a_j^\dagger$ act on $j$ qubits, which motivates the parity and Bravyi–Kitaev encodings. The encoding itself is canonical fermion-to-qubit algebra, independent of the electronic Hamiltonian.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

The sign $(-1)^{\sum_{l<j}n_l}$ of $a_j^\dagger$ is the eigenvalue of $Z^{\otimes(j-1)}$ on $|n_1\cdots n_{j-1}\rangle$, and $Q^+$ changes $n_j$ from $0$ to $1$ or annihilates, so both sides agree on the basis; the relations transfer by unitary conjugation. Pauli strings with real coefficients: the encoded Hermitian operator expands in the Hermitian Pauli basis with real coefficients. Arxiv:1812.09976v2 Eq. (93) is internally inconsistent: it prints $\sigma^+=\begin{bmatrix}0&1\\0&0\end{bmatrix}$ beside $\sigma_z=\mathrm{diag}(1,-1)$ and maps the vacuum to $|0\cdots0\rangle$, so for one mode its operator annihilates $|0\rangle$ instead of creating $|1\rangle$; and its occupation states use the descending product $(a_K^\dagger)^{i_N}\cdots(a_1^\dagger)^{i_1}|vac\rangle$, which differs from the increasing order used here by $(-1)^{m(m-1)/2}$ on $m$-occupied states. This page follows the internally consistent convention of Seeley, Richard and Love, Eqs. (10)–(11).

## Sources

- Jacob T. Seeley, Martin J. Richard and Peter J. Love, *The Bravyi-Kitaev transformation for quantum computation of electronic structure*, J. Chem. Phys. 137 (2012) 224109; numbers from arXiv:1208.5986v1, §II.B, Eqs. (10)–(11). <https://arxiv.org/abs/1208.5986v1>
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix B.1, Eq. (93). <https://arxiv.org/abs/1812.09976v2>
