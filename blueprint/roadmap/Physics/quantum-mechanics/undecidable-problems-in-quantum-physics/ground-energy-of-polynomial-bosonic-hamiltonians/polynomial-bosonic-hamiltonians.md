# Polynomial bosonic Hamiltonians and their ground-energy problems

A polynomial bosonic Hamiltonian is a polynomial with rational coefficients in the position and momentum operators of finitely many modes; its ground-energy problem asks whether the lowest energy is below one threshold or above another, and its boundedness problem asks whether the spectrum is bounded below.

**Modes and operators.** For $n$ bosonic modes, let $X_1,\dots,X_n$ and $P_1,\dots,P_n$ be the position and momentum operators on the Hilbert space $\mathcal H$ of $n$ modes, with $[X_j,P_k]=i\delta_{jk}$, and let $N_j=(X_j^2+P_j^2-1)/2$ be the number operators. For multi-indices $\boldsymbol\mu,\boldsymbol\nu\in\mathbb Z_+^n$ write $X^{\boldsymbol\mu}=X_1^{\mu_1}\cdots X_n^{\mu_n}$ and $P^{\boldsymbol\nu}=P_1^{\nu_1}\cdots P_n^{\nu_n}$, and $|\boldsymbol\mu|=\mu_1+\cdots+\mu_n$.

**Polynomial Hamiltonians.** A *polynomial bosonic Hamiltonian of degree $d$* on $n$ modes is given in the normal form

$$
H=\sum_{\substack{\boldsymbol\mu,\boldsymbol\nu\in\mathbb Z_+^n\\ |\boldsymbol\mu+\boldsymbol\nu|\le d}}h_{\boldsymbol\mu,\boldsymbol\nu}X^{\boldsymbol\mu}P^{\boldsymbol\nu},
$$

with constant rational coefficients, $|h_{\boldsymbol\mu,\boldsymbol\nu}|=O(1)$. Degree $2$ gives the Gaussian Hamiltonians. Such operators are in general unbounded, and their spectrum need not be bounded below.

**Ground-energy problem.** For a set $\mathcal S$ of states, an instance of $\mathsf{CVLH}^d_{\mathcal S}(a,b)$ is a degree-$d$ Hamiltonian $H$ with constants $a<b$, $b-a\ge1/\mathrm{poly}(n)$, under the promise that either $\inf_{\psi\in\mathcal S}\langle\psi|H|\psi\rangle\le a$ or $\inf_{\psi\in\mathcal S}\langle\psi|H|\psi\rangle\ge b$; the yes instances are those of the first kind. When $\mathcal S=\mathcal H$ is the set of all states, the infimum is the bottom of the spectrum of $H$.

**Boundedness problem.** $\mathsf{HBound}^d_{\mathcal S}$ asks, given a degree-$d$ Hamiltonian in normal form, whether $\inf_{\psi\in\mathcal S}\langle\psi|H|\psi\rangle>-\infty$, that is, whether $H$ is bounded below on $\mathcal S$.

## Depends on

- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)

## Proof depends on

None.

## Sources

- U. Chabaud, M. Joseph, S. Mehraban and A. Motamedi, "Bosonic quantum computational complexity", *Quantum* 10, 2110, 2026, doi:[10.22331/q-2026-05-20-2110](https://doi.org/10.22331/q-2026-05-20-2110); read in arXiv:2410.04274v3 ([arXiv](https://arxiv.org/abs/2410.04274v3)), whose numbering is used: Definition 5.2 (continuous-variable local Hamiltonian problem), Definition 5.3 (Hamiltonian boundedness problem) and the notation for position, momentum and number operators in Section 1.
