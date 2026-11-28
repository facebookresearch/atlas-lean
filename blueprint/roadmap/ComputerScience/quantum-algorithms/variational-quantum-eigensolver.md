# Variational quantum eigensolver

The variational quantum eigensolver estimates the lowest eigenvalue of a qubit Hamiltonian by minimizing, with a classical optimizer, sampled estimates of the energy of a parametrized quantum state.

Let $H=\sum_{\ell=1}^{L}w_\ell P_\ell$ be a Hamiltonian on $q$ qubits with real coefficients $w_\ell$ and Pauli strings $P_\ell$, let $|\psi_0\rangle$ be a normalized reference state and $\theta\mapsto U(\theta)$, $\theta\in\mathbb R^m$, a family of unitaries realized by a parametrized circuit. The energy function is

$$
E(\theta)=\langle\psi_0|U(\theta)^\dagger HU(\theta)|\psi_0\rangle=\sum_{\ell=1}^{L}w_\ell\,\langle P_\ell\rangle_{U(\theta)\psi_0}.
$$

The algorithm repeats: prepare $U(\theta)|\psi_0\rangle$, estimate each $\langle P_\ell\rangle$ by measuring in its eigenbasis on independent copies (Hamiltonian averaging), combine the estimates into $\hat E(\theta)$, and update $\theta$ by a classical optimization routine; it returns the best estimate found and its parameters. For every $\theta$ the exact value satisfies $E(\theta)\ge\lambda_{\min}(H)$; the returned sampled estimate need not be an upper bound. When the target is a fixed-electron-number energy (for example the full configuration interaction energy) and $H$ preserves that sector, the bound refers to the minimum over the sector whenever every state $U(\theta)|\psi_0\rangle$ lies in it; an $N$-electron reference with a globally number-conserving ansatz is sufficient, as is restricting $H$ to the sector. Otherwise the relevant minimum is that of the full matrix, which may lie in another sector.

## Context

Graduate/research. Proposed and demonstrated on a photonic processor by Peruzzo, McClean and coauthors with Aspuru-Guzik and O'Brien; reviewed by Cao, Aspuru-Guzik and coauthors as the leading near-term algorithm for chemistry. Convergence of the outer optimization is not guaranteed and experimental accuracies are context. The algorithm is generic over qubit Hamiltonians; chemistry enters through the encoded electronic Hamiltonian and a number-conserving ansatz such as unitary coupled cluster.

## Depends on

- [Expectation value of an observable](../../Physics/quantum-mechanics/postulates-of-finite-dimensional-quantum-mechani/expectation-value.md)

## Proof depends on

- [Variational principle for the smallest eigenvalue](../../Physics/quantum-mechanics/postulates-of-finite-dimensional-quantum-mechani/inf-eigenvalues-le-expectation-value.md)

## Expansion

An algorithm definition. The decomposition of $E(\theta)$ is linearity of the expectation value; the bound is the variational principle applied to the normalized state $U(\theta)|\psi_0\rangle$ (normalization matters: with $|\psi_0\rangle=0$ and $H=\mathbf 1$ one would get $0<1$). If all trial states lie in an invariant sector, the same principle applies to the restricted Hermitian matrix.

## Sources

- Alberto Peruzzo, Jarrod McClean, Peter Shadbolt, Man-Hong Yung, Xiao-Qi Zhou, Peter J. Love, Alán Aspuru-Guzik and Jeremy L. O'Brien, *A variational eigenvalue solver on a photonic quantum processor*, Nat. Commun. 5 (2014) 4213, <https://doi.org/10.1038/ncomms5213> (PMC4124861), main text (quantum expectation estimation and the quantum variational eigensolver, Fig. 1).
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §5.1, steps 1–4. <https://arxiv.org/abs/1812.09976v2>
