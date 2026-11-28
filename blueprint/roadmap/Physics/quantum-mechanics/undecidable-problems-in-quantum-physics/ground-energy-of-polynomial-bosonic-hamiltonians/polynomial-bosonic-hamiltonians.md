# Polynomial bosonic Hamiltonians and their ground-energy problems

A polynomial bosonic Hamiltonian is an essentially self-adjoint polynomial in the position and momentum operators of finitely many modes; its ground-energy problem asks whether the lowest energy is below one threshold or above another, and its boundedness problem asks whether the spectrum is bounded below.

**Modes and operators.** For $n$ bosonic modes, let $\mathcal H=L^2(\mathbb R^n)$ and let $\mathcal S\subset\mathcal H$ be the Schwartz space, a dense subspace on which the position operators $X_1,\dots,X_n$ (multiplication by the coordinates) and the momentum operators $P_1,\dots,P_n$ ($-i$ times the partial derivatives) act and satisfy $[X_j,P_k]=i\delta_{jk}$. The number operators are $N_j=(X_j^2+P_j^2-1)/2$. Write $\mathbb Z_+=\{0,1,2,\dots\}$; for multi-indices $\boldsymbol\mu,\boldsymbol\nu\in\mathbb Z_+^n$ write $X^{\boldsymbol\mu}=X_1^{\mu_1}\cdots X_n^{\mu_n}$, $P^{\boldsymbol\nu}=P_1^{\nu_1}\cdots P_n^{\nu_n}$ and $|\boldsymbol\mu|=\mu_1+\cdots+\mu_n$.

**Polynomial Hamiltonians.** A *polynomial bosonic Hamiltonian of degree $d$* on $n$ modes is an operator on $\mathcal S$ given in the normal form

$$
H=\sum_{\substack{\boldsymbol\mu,\boldsymbol\nu\in\mathbb Z_+^n\\ |\boldsymbol\mu+\boldsymbol\nu|\le d}}h_{\boldsymbol\mu,\boldsymbol\nu}X^{\boldsymbol\mu}P^{\boldsymbol\nu}
$$

with constant coefficients $h_{\boldsymbol\mu,\boldsymbol\nu}\in\mathbb Q(i)$, given as part of the input, such that $H$ is symmetric and essentially self-adjoint on $\mathcal S$; the energy of $H$ is that of its self-adjoint closure. The ordered monomials $X^{\boldsymbol\mu}P^{\boldsymbol\nu}$ are linearly independent, so the coefficients and the degree are determined by the operator. Degree $2$ gives the Gaussian Hamiltonians. Such operators are in general unbounded, and their spectrum need not be bounded below.

The source asks for rational coefficients and, at the end of its Section 2.3.4, restricts to essentially self-adjoint polynomial operators on the Schwartz space. Here the coefficients are taken in $\mathbb Q(i)$ and self-adjointness is part of the definition, which is how the source's convention is read: a symmetric operator written in this normal form can need non-real coefficients, as for $N_1^2$, whose expansion contains the term $-iX_1P_1$, and the operator $X_1P_1$, which has a rational coefficient, is not symmetric, since its expectation in every normalized state has imaginary part $1/2$. The source's Definition 5.2 also writes $|h_{\boldsymbol\mu,\boldsymbol\nu}|=O(1)$ and $b-a\ge1/\mathrm{poly}(n)$, conditions on families of instances as $n$ grows that constrain no single input. Here the coefficients and the thresholds are arbitrary and given as part of the input, with no fixed coefficient bound: the source's proof of Theorem 5.6 starts from an integer polynomial with arbitrary coefficients, and substituting the input into it makes the coefficients of the resulting Hamiltonians grow with the input, so they stay within no fixed bound. The hardness results stated with this definition are claimed for this instance set only.

**Ground-energy problem.** Let $\mathcal T$ be a set of normalized states in $\mathcal S$. An instance of $\mathsf{CVLH}^d_{\mathcal T}(a,b)$ is a degree-$d$ Hamiltonian $H$ together with rational thresholds $a<b$, all given as input, under the promise that either $\inf_{\psi\in\mathcal T}\langle\psi|H|\psi\rangle\le a$ or $\inf_{\psi\in\mathcal T}\langle\psi|H|\psi\rangle\ge b$; the yes instances are those of the first kind. The reductions stated with this definition use $a=0$ and $b=1$. When $\mathcal T$ is the set of all normalized states in $\mathcal S$, written $\mathcal T=\mathcal H$ as in the source, the infimum is the bottom of the spectrum of the closure of $H$, since $\mathcal S$ is a core for it.

**Boundedness problem.** $\mathsf{HBound}^d_{\mathcal T}$ asks, given a degree-$d$ Hamiltonian in normal form, whether $\inf_{\psi\in\mathcal T}\langle\psi|H|\psi\rangle>-\infty$, that is, whether $H$ is bounded below on $\mathcal T$.

## Depends on

- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)

## Proof depends on

None.

## Sources

- U. Chabaud, M. Joseph, S. Mehraban and A. Motamedi, "Bosonic quantum computational complexity", *Quantum* 10, 2110, 2026, doi:[10.22331/q-2026-05-20-2110](https://doi.org/10.22331/q-2026-05-20-2110); read in arXiv:2410.04274v3 ([arXiv](https://arxiv.org/abs/2410.04274v3)), whose numbering is used: Definition 5.2 (continuous-variable local Hamiltonian problem), Definition 5.3 (Hamiltonian boundedness problem), the restriction to essentially self-adjoint polynomial operators on the Schwartz space at the end of Section 2.3.4, and the notation for position, momentum and number operators.
