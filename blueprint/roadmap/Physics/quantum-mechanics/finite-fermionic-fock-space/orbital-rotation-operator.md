# Orbital rotation operator

The exponential of a one-body anti-Hermitian operator on Fock space acts on creation operators by the corresponding unitary matrix, so it maps each Slater determinant to the determinant of the rotated orbitals.

Let $\kappa\in\mathbb C^{M\times M}$ be anti-Hermitian, $\kappa^\dagger=-\kappa$, put $u=e^{\kappa}$ (unitary), $\hat\kappa=\sum_{p,q}\kappa_{pq}a_p^\dagger a_q$ and $U(\kappa)=e^{\hat\kappa}$ on $\mathcal F_M$. Then $U(\kappa)$ is unitary, commutes with the number operator, fixes the vacuum, and

$$
U(\kappa)\,a_q^\dagger\,U(\kappa)^\dagger=\sum_{p=1}^{M}u_{pq}\,a_p^\dagger\qquad(q=1,\dots,M).
$$

Consequently $U(\kappa)\,a_{q_1}^\dagger\cdots a_{q_N}^\dagger|0\rangle=\tilde a_{q_1}^\dagger\cdots\tilde a_{q_N}^\dagger|0\rangle$ with $\tilde a_q^\dagger=\sum_pu_{pq}a_p^\dagger$, so the action of $U(\kappa)$ depends only on $u$: two anti-Hermitian $\kappa,\kappa'$ with $e^\kappa=e^{\kappa'}$ give the same operator. In the determinant picture $U(\kappa)$ replaces each occupied orbital $\varphi_q$ by $\tilde\varphi_q=\sum_pu_{pq}\varphi_p$.

## Context

Graduate. Basis rotations prepare Hartree–Fock and other single-determinant initial states on quantum computers; Kivlichan and coauthors decompose $U$ into nearest-neighbour Givens rotations. This full unitary lift of a basis change differs from the Thouless chart $e^{\hat T_1}$ with occupied-to-virtual excitations only, which reaches the determinants with nonzero overlap with the reference. The general finite-fermion basis change is canonical Fock-space algebra; its chemistry use is determinant preparation.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)
- [Slater determinant](../../../Chemistry/quantum-chemistry-and-spectroscopy/slater-determinants-and-second-quantization/slater-determinant.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

$\hat\kappa^\dagger=\sum\overline{\kappa_{pq}}a_q^\dagger a_p=-\hat\kappa$, so $U$ is unitary (Mathlib `exp_mem_unitary_of_mem_skewAdjoint`). $\hat\kappa|0\rangle=0$ gives $U|0\rangle=|0\rangle$. The anticommutation relations give $[\hat\kappa,a_q^\dagger]=\sum_p\kappa_{pq}a_p^\dagger$, so the linear map $\mathrm{ad}_{\hat\kappa}$ preserves $\mathrm{span}\{a_p^\dagger\}$ and acts there by the matrix $\kappa$; the identity $e^{X}Ye^{-X}=\sum_{n\ge0}\mathrm{ad}_X^n(Y)/n!$ (both sides solve $Z'=[X,Z]$ with $Z(0)=Y$) gives the displayed formula. The product formula follows by inserting $U^\dagger U$ between factors. Note that Eq. (8) of Kivlichan and coauthors writes the generator as $\sum[\log u]_{pq}(a_p^\dagger a_q-a_q^\dagger a_p)$, in which diagonal terms cancel; their Appendix B, Eq. (B11), and its proof use the unsymmetrized $\hat\kappa$, as here (for $u=\mathrm{diag}(e^{it},1)$ one needs $e^{it\hat n_1}$).

## Sources

- Ian D. Kivlichan, Jarrod McClean, Nathan Wiebe, Craig Gidney, Alán Aspuru-Guzik, Garnet Kin-Lic Chan and Ryan Babbush, *Quantum Simulation of Electronic Structure with Linear Depth and Connectivity*, Phys. Rev. Lett. 120 (2018) 110501; numbers from arXiv:1711.04789v2, Eqs. (7)–(10) and Appendix B, Eqs. (B10)–(B14) and (B21). <https://arxiv.org/abs/1711.04789v2>
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §5.1.1, Eq. (53). <https://arxiv.org/abs/1812.09976v2>
