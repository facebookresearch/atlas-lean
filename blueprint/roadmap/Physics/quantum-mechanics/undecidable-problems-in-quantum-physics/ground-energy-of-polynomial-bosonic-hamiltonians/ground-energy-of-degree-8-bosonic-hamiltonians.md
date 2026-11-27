# The ground energy of degree-8 bosonic Hamiltonians is undecidable

No algorithm decides, for a polynomial of degree 8 in the position and momentum operators of finitely many bosonic modes, whether its lowest energy is below one threshold or above another; the problem is RE-hard.

**Theorem (Chabaud, Joseph, Mehraban and Motamedi).** The ground-energy problem $\mathsf{CVLH}^8_{\mathcal H}$ for [polynomial bosonic Hamiltonians](polynomial-bosonic-hamiltonians.md) of degree $8$, with the infimum taken over all states, is $\mathbf{RE}$-hard, and therefore undecidable.

The source also states that the hardness persists when the states are restricted to Fock states, giving an $\mathbf{RE}$-complete problem $\mathsf{CVLH}^8_{\mathcal F}$, and under a constant bound on the energy of the states. The Hamiltonians produced by the reduction have integer spectrum, so their spectral gap is at least $1$. For Gaussian Hamiltonians (degree $2$) the problem is solvable in polynomial time, and for degree $4$ over Gaussian states of exponentially bounded energy it is NP-complete.

## Depends on

- [Polynomial bosonic Hamiltonians and their ground-energy problems](polynomial-bosonic-hamiltonians.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem to the ground-energy problem through number operators. Following Kieu, for a polynomial $Q$ with integer coefficients the operator $H_Q=Q(N_1,\dots,N_n)$ in the commuting number operators $N_j=(X_j^2+P_j^2-1)/2$ is diagonal in the Fock basis with eigenvalues $Q(x)$, $x\in\mathbb Z_+^n$, so it is essentially self-adjoint on the Schwartz space and $\lambda_{\min}(H_Q)=\min_{x\in\mathbb Z_+^n}Q(x)$. Since each $N_j$ has degree $2$ in $X_j,P_j$, a polynomial $Q$ of degree $k$ in the $N_j$ gives a Hamiltonian of degree $2k$ in the position and momentum operators. The source's proof takes $Q=P^2$ for a polynomial $P$ of degree $4$ from Jones's universal Diophantine representation; that $Q$ has degree $8$ in the number operators, hence degree $16$ in the position and momentum operators, so it does not by itself give degree $8$. A degree-$8$ Hamiltonian is obtained from quadratic equations instead. By the DPRM theorem, for a fixed machine the inputs on which it halts are those $a$ for which a polynomial equation $R(a,x)=0$ has a solution $x$ in $\mathbb Z_+^m$; introducing a new variable for each product that occurs in $R$ turns this equation, computably in $a$, into a system of equations $q_1=\cdots=q_r=0$ of degree at most $2$ with integer coefficients that has a solution in non-negative integers exactly when $R(a,x)=0$ does. Then $Q=\sum_i q_i^2$ has degree at most $4$ in the $N_j$, so $H_Q$ has degree at most $8$, and its ground energy is $0$ if the machine halts on $a$ and at least $1$ otherwise. A good expansion links pages for the reduction of a Diophantine equation over the non-negative integers to a system of quadratic equations and for the spectrum of the number operators.

## Sources

- U. Chabaud, M. Joseph, S. Mehraban and A. Motamedi, "Bosonic quantum computational complexity", *Quantum* 10, 2110, 2026, doi:[10.22331/q-2026-05-20-2110](https://doi.org/10.22331/q-2026-05-20-2110); read in arXiv:2410.04274v3 ([arXiv](https://arxiv.org/abs/2410.04274v3)), whose numbering is used: Theorem 5.6 with its proof and the remark after it, Theorem 5.1 (Gaussian Hamiltonians) and Theorem 5.3 (degree 4 over Gaussian states).
- J. P. Jones, "Three universal representations of recursively enumerable sets", *The Journal of Symbolic Logic* 43(2), pp. 335–351, 1978, doi:[10.2307/2272832](https://doi.org/10.2307/2272832) (cited by the source for the degree-4 equations; not read here, cited beside the copy read above).
- T. D. Kieu, "Quantum algorithm for Hilbert's tenth problem", *International Journal of Theoretical Physics* 42, pp. 1461–1478, 2003, doi:[10.1023/A:1025780028846](https://doi.org/10.1023/A:1025780028846) (cited by the source for the number-operator encoding; not read here, cited beside the copy read above).
