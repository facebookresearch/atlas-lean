# Bravyi–Kitaev transformation

The Bravyi–Kitaev transformation encodes occupation numbers into qubits that store parities of dyadic blocks of modes, given by a recursively defined binary matrix.

Define binary matrices $\beta_r$ of size $2^{r-1}\times2^{r-1}$ over $\mathbb F_2$ by $\beta_1=(1)$ and

$$
\beta_{r+1}=\begin{pmatrix}\beta_r&E_r\\0&\beta_r\end{pmatrix},
$$

where $E_r$ is the $2^{r-1}\times2^{r-1}$ matrix whose first row is all ones and whose other rows are zero. For $M=2^{r-1}$ modes the Bravyi–Kitaev encoding sends the occupation vector $n\in\mathbb F_2^M$ to $b=\beta_rn$, that is $b_k=\sum_{l=1}^{M}[\beta_r]_{kl}n_l\bmod2$ over all columns, and the Bravyi–Kitaev map is the unitary $\Phi_{\mathrm{BK}}:|n_1\cdots n_M\rangle\mapsto|b_1\rangle\otimes\cdots\otimes|b_M\rangle$; fermionic operators are transported as $\Phi_{\mathrm{BK}}a_j^\dagger\Phi_{\mathrm{BK}}^{-1}$. Each $\beta_r$ is upper unitriangular, hence invertible over $\mathbb F_2$, so $\Phi_{\mathrm{BK}}$ permutes the computational basis. In this ordering $b_1$ is the total parity; for $M=1$ the encoding is the identity on occupations.

## Context

Graduate. Bravyi and Kitaev introduced the encoding; Seeley, Richard and Love worked it out for electronic-structure Hamiltonians, where each transported creation or annihilation operator acts nontrivially on $O(\log M)$ qubits as $M\to\infty$, compared with $O(M)$ for Jordan–Wigner (an asymptotic statement proved there with parity, update and flip sets, not part of this definition). The four-qubit hydrogen-molecule Hamiltonian of the review of Cao, Aspuru-Guzik and coauthors is written in this encoding. The encoding is canonical fermion-to-qubit algebra.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)

## Proof depends on

None.

## Expansion

A definition. Unitriangularity holds by induction from the block form. Two corrections to arXiv:1812.09976v2: the sum after Eq. (96) is printed over $l\le k$, which for upper-triangular $\beta$ reads only the diagonal (for $r=2$, $\beta_2=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ sends $(0,1)$ to $(1,1)$, not $(0,1)$); and its displayed $8\times8$ example, labelled $\beta_3$, is the fourth matrix of the stated recursion. Seeley, Richard and Love sum over all columns (Eq. (23)) and label matrices by dimension, with reversed index and tensor ordering.

## Sources

- Jacob T. Seeley, Martin J. Richard and Peter J. Love, *The Bravyi-Kitaev transformation for quantum computation of electronic structure*, J. Chem. Phys. 137 (2012) 224109; numbers from arXiv:1208.5986v1, §III.B, Eq. (23) and Fig. 2, and §§IV–V. <https://arxiv.org/abs/1208.5986v1>
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix B.2, Eqs. (96)–(99). <https://arxiv.org/abs/1812.09976v2>
