# Spectrum of fermionic excitation generators

The Hermitian generator of an $n$-fold fermionic excitation has spectrum contained in $\{-1,0,1\}$; its null-space projector is an explicit polynomial in number operators, and adding or subtracting it gives two self-inverse generators.

Let $n\ge1$ and let $p_1,\dots,p_n,q_1,\dots,q_n\in\{1,\dots,M\}$ be $2n$ distinct indices. On $\mathcal F_M$ put $A=\prod_{i=1}^{n}a_{p_i}^\dagger a_{q_i}$ (the factors commute) and

$$
G=i\,(A-A^\dagger).
$$

Then $G$ is Hermitian, $G^3=G$, and every eigenvalue of $G$ (on $\mathcal F_M$ or on any invariant subspace, such as a particle-number sector) lies in $\{-1,0,1\}$; not all three need occur in a given sector. The orthogonal projector onto $\ker G$ is

$$
P_0=\mathbf 1-G^2=\mathbf 1-\prod_{i=1}^{n}\hat n_{p_i}(\mathbf 1-\hat n_{q_i})-\prod_{i=1}^{n}\hat n_{q_i}(\mathbf 1-\hat n_{p_i}),\qquad \hat n_k=a_k^\dagger a_k,
$$

and $G_\pm=G\pm P_0$ satisfy $G_\pm^2=\mathbf 1$ and $G=\frac12(G_++G_-)$.

## Context

Graduate/research. Kottmann, Anand and Aspuru-Guzik use this structure to differentiate unitary coupled-cluster circuits on quantum computers with a constant number of shifted expectation values, independent of the fermion-to-qubit encoding. The generator algebra is canonical finite-fermion algebra; its chemistry use is the unitary coupled-cluster ansatz.

## Depends on

- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

$A$ maps each occupation state with all $q_i$ occupied and all $p_i$ empty to $\pm$ the state with these occupations exchanged, and kills every other basis state; hence $A^2=0$, $A^\dagger A=\prod_i\hat n_{q_i}(\mathbf 1-\hat n_{p_i})$ and $AA^\dagger=\prod_i\hat n_{p_i}(\mathbf 1-\hat n_{q_i})$ are orthogonal projectors with orthogonal ranges, and $AA^\dagger A=A$. Then $G^2=AA^\dagger+A^\dagger A$ is a projector and $G^3=G$, so every eigenvalue satisfies $\lambda^3=\lambda$. Finally $G_\pm^2=G^2+P_0=\mathbf 1$ because $GP_0=0$.

## Sources

- Jakob S. Kottmann, Abhinav Anand and Alán Aspuru-Guzik, *A feasible approach for automatically differentiable unitary coupled-cluster on quantum computers*, Chem. Sci. 12 (2021) 3497–3508, <https://doi.org/10.1039/d0sc06627c> (PMC8179519), Eqs. (3)–(5), (8), (10)–(12) and (31)–(33), and ESI.
