# Unitary coupled-cluster ansatz

The unitary coupled-cluster ansatz applies the exponential of an anti-Hermitian combination of excitation operators to a reference determinant, giving a normalized, particle-number-conserving trial state usable in variational quantum algorithms.

Let $|\Phi_0\rangle\in\mathcal F_M$ be a reference occupation state with occupied set $\mathrm{occ}$ ($|\mathrm{occ}|=N$) and unoccupied set $\mathrm{virt}$. For amplitudes $t$, the singles and doubles cluster operators are

$$
T_1=\sum_{i\in\mathrm{occ}}\sum_{a\in\mathrm{virt}}t_i^a\,a_a^\dagger a_i,\qquad T_2=\sum_{i<j\in\mathrm{occ}}\ \sum_{a<b\in\mathrm{virt}}t_{ij}^{ab}\,a_a^\dagger a_b^\dagger a_ja_i ,
$$

and $T=T_1+T_2+\cdots$ (higher ranks analogous). The unitary coupled-cluster state is

$$
|\Psi_{\mathrm{UCC}}(t)\rangle=e^{T-T^\dagger}|\Phi_0\rangle .
$$

Since $T-T^\dagger$ is anti-Hermitian, $e^{T-T^\dagger}$ is unitary and $\|\Psi_{\mathrm{UCC}}\|=1$; it commutes with the number operator, so $\Psi_{\mathrm{UCC}}$ has $N$ electrons, and therefore $\langle\Psi_{\mathrm{UCC}},\hat H\Psi_{\mathrm{UCC}}\rangle\ge E_{\mathrm{FCI}}$ in the same basis. Unlike traditional coupled cluster ($e^{T}|\Phi_0\rangle$ with projected equations), the energy is variational.

## Context

Graduate/research. Proposed as a quantum-computing ansatz by Peruzzo and coauthors and analysed by Romero, Babbush, McClean, Hempel, Love and Aspuru-Guzik; implemented through Trotterized products of excitation gates whose generators are treated on the excitation-generator pages here.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)
- [Full configuration interaction energy](../electron-correlation/full-configuration-interaction-energy.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

A definition. Unitarity: $(T-T^\dagger)^\dagger=-(T-T^\dagger)$. Number conservation: each excitation operator has equally many creation and annihilation operators, hence commutes with $\hat N$, and so does the exponential. The energy bound is the variational characterization of $E_{\mathrm{FCI}}$ on the $N$-particle sector.

## Sources

- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.2.1 and §5.1.1, Eqs. (31)–(36). <https://arxiv.org/abs/1812.09976v2>
- Jonathan Romero, Ryan Babbush, Jarrod R. McClean, Cornelius Hempel, Peter J. Love and Alán Aspuru-Guzik, *Strategies for quantum computing molecular energies using the unitary coupled cluster ansatz*, Quantum Sci. Technol. 4 (2019), <https://doi.org/10.1088/2058-9565/aad3e4>; arXiv:1701.02691v2. <https://arxiv.org/abs/1701.02691v2>
