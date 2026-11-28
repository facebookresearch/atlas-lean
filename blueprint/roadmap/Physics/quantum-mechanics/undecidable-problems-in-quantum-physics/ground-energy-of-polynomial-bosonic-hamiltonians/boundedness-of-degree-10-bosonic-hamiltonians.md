# Lower boundedness of degree-10 bosonic Hamiltonians is undecidable

No algorithm decides whether a polynomial of degree 10 or more in the position and momentum operators of finitely many bosonic modes has spectrum bounded below; the problem is co-RE-hard.

**Theorem (Chabaud, Joseph, Mehraban and Motamedi).** There is a constant $C$ such that, for every $d\ge10$, the boundedness problem $\mathsf{HBound}^d_{\mathcal H}$ for [polynomial bosonic Hamiltonians](polynomial-bosonic-hamiltonians.md) of degree $d$ with coefficients bounded by $C$, deciding whether $H$ is bounded below over all states, is undecidable; it is $\mathbf{co}$-$\mathbf{RE}$-hard (Corollary 5.2 of arXiv:2410.04274v3, stated with the coefficient bound of its Definitions 5.2 and 5.3).

By contrast, boundedness is decidable in polynomial time for Gaussian Hamiltonians (degree $2$), and for degree $4$ it is $\mathbf{co}$-$\mathbf{NP}$-hard, by a reduction from matrix copositivity; the source leaves the precise complexity of boundedness open, conjecturing co-QMA-hardness, and asks whether its sound algorithm for degree $4$ has analogues for degrees above $4$.

## Depends on

- [Polynomial bosonic Hamiltonians and their ground-energy problems](polynomial-bosonic-hamiltonians.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [The ground energy of degree-8 bosonic Hamiltonians is undecidable](ground-energy-of-degree-8-bosonic-hamiltonians.md)

## Expansion

The proof reduces the ground-energy problem to boundedness. Given a degree-$8$ Hamiltonian $H$ on some modes whose ground energy is either at most $a$ or at least $b$, set $c=(a+b)/2$, add a fresh mode with number operator $N$, and form

$$
H'=N\otimes(H-c),
$$

of degree $2+8=10$ in the position and momentum operators, since $N$ has degree $2$ and $H$ degree $8$. Apply this to the Hamiltonians $H=r^{-1}\sum_i q_i(N_1,\dots,N_n)^2$ of the degree-8 construction, with $a=0$, $b=1/r$ and $c=1/(2r)$. Then $H'$ is diagonal in the Fock basis, hence essentially self-adjoint on the Schwartz space, and its coefficients are products of the bounded coefficients of $N$ and of $H$, together with $c\le1/2$, so they are bounded by a constant independent of the input. If $\lambda_{\min}(H)\le a$, then $H-c$ has spectrum below $0$ and, since $N$ takes every value in $\mathbb Z_+$, $H'$ is unbounded below; if $\lambda_{\min}(H)\ge b$, then $H-c\ge(b-a)/2=1/(2r)>0$ and $H'\ge0$ is bounded below. A Hamiltonian of degree $10$ also has degree at most $d$ for every $d\ge10$. Thus a decision procedure for boundedness would decide the ground-energy problem. The step that $N$ takes every value in $\mathbb Z_+$ is the spectrum of the number operator, and a good expansion links a page for it.

## Sources

- U. Chabaud, M. Joseph, S. Mehraban and A. Motamedi, "Bosonic quantum computational complexity", *Quantum* 10, 2110, 2026, doi:[10.22331/q-2026-05-20-2110](https://doi.org/10.22331/q-2026-05-20-2110); read in arXiv:2410.04274v3 ([arXiv](https://arxiv.org/abs/2410.04274v3)), whose numbering is used: Definitions 5.2 and 5.3, Corollary 5.2 with its proof, Theorem 5.2 (co-NP-hardness for degree 4), Theorem 5.1 (Gaussian case), and the open questions of Section 1.2.2.
