# The ground energy of degree-8 bosonic Hamiltonians is undecidable

No algorithm decides, for a polynomial of degree 8 in the position and momentum operators of finitely many bosonic modes, whether its lowest energy is below one threshold or above another; the problem is RE-hard.

**Theorem (Chabaud, Joseph, Mehraban and Motamedi).** There are a constant $C$ and a positive polynomial $p$ such that the ground-energy problem $\mathsf{CVLH}^8_{\mathcal H}$ for [polynomial bosonic Hamiltonians](polynomial-bosonic-hamiltonians.md) of degree $8$ with these bounds, with the infimum taken over all states, is $\mathbf{RE}$-hard, and therefore undecidable (Theorem 5.6 of arXiv:2410.04274v3, stated with the bounds of its Definition 5.2).

The source also states that the hardness persists when the states are restricted to Fock states, giving an $\mathbf{RE}$-complete problem $\mathsf{CVLH}^8_{\mathcal F}$. It also remarks that the proof stays valid under a constant bound on the energy of the states; the reductions sketched below do not give this, since the zeros of the polynomial can have arbitrarily large particle number. The distinct eigenvalues of the Hamiltonians $Q(N_1,\dots,N_n)$ in the source's reduction are integers, so they differ by at least $1$; their ground level can be degenerate. For Gaussian Hamiltonians (degree $2$), with these bounds, the problem is solvable in polynomial time, and for degree $4$ over Gaussian states of exponentially bounded energy it is NP-complete.

## Depends on

- [Polynomial bosonic Hamiltonians and their ground-energy problems](polynomial-bosonic-hamiltonians.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Myhill's characterization of creative sets](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/myhill-s-characterization-of-creative-sets.md)

## Expansion

The proof reduces Hilbert's tenth problem to the ground-energy problem through number operators. Following Kieu, for a polynomial $Q$ with integer coefficients the operator $H_Q=Q(N_1,\dots,N_n)$ in the commuting number operators $N_j=(X_j^2+P_j^2-1)/2$ is diagonal in the Fock basis with eigenvalues $Q(x)$, $x\in\mathbb Z_+^n$, so it is essentially self-adjoint on the Schwartz space and the bottom of its spectrum is $\inf_{x\in\mathbb Z_+^n}Q(x)$, possibly $-\infty$ (for $Q(x)=-x_1$ there is no minimum); for the sums of squares used below the infimum is attained. Since each $N_j$ has degree $2$ in $X_j,P_j$, a polynomial of degree $k$ in the $N_j$ gives a Hamiltonian of degree $2k$, and a polynomial of bounded degree with a bounded number of terms and bounded coefficients in the $N_j$ has bounded coefficients in normal form (without the bound on the number of terms this fails: $\sum_{j=1}^n N_j$ has constant term $-n/2$).

The source's proof takes $Q=P^2$ for a polynomial $P$ of degree $4$ from Jones's universal Diophantine representation, with the input substituted into $P$. That $Q$ has degree $16$ in the position and momentum operators, and its coefficients grow with the input, so as written it meets neither the degree $8$ nor the coefficient bound $C$. Both are met as follows. Start from the halting set $K$, which is $m$-complete for the recursively enumerable sets (Myhill), so that every recursively enumerable set reduces to it by a computable map and the bounds $C$ and $p$ below serve all of them at once. By the DPRM theorem there is a fixed integer polynomial $R$ such that $u\in K$ exactly when $R(u,x)=0$ has a solution $x\in\mathbb Z_+^m$; introducing a new variable for each product that occurs in $R$ turns this into a fixed system of equations of degree at most $2$ with integer coefficients. Given the binary digits $b_0,\dots,b_{L-1}$ of $u$, listed from the most significant, add fresh variables $v_0,\dots,v_L$ with the linear equations $v_0=0$ and $v_{j+1}=2v_j+b_j$, whose only solution has $v_L=u$, and use $v_L$ in place of $u$. This gives $r=L+O(1)$ equations $q_1=\dots=q_r=0$ of degree at most $2$ in $n=L+O(1)$ variables, each with a bounded number of terms and bounded integer coefficients, with a solution in non-negative integers exactly when the machine halts on $u$. Let

$$
H=\frac1r\sum_{i=1}^r q_i(N_1,\dots,N_n)^2 .
$$

Each $q_i(N)^2$ has a bounded number of bounded coefficients in normal form, and a monomial collects contributions from at most $r$ summands, so after the division by $r$ every coefficient of $H$ is bounded by a constant $C$ that does not depend on $u$; $H$ has degree at most $8$. Its ground energy is $0$ if $u\in K$ and at least $1/r$ otherwise, and $1/r\ge1/p(n)$ for a linear polynomial $p$, so $H$ with thresholds $0$ and $1/r$ is an instance of the problem with these bounds, and $u\mapsto H$ is a computable many-one reduction of $K$, hence of every recursively enumerable set, to the problem: it is $\mathbf{RE}$-hard. A good expansion links pages for the reduction of a Diophantine equation over the non-negative integers to a system of quadratic equations and for the spectrum of the number operators, and checks this bounded-coefficient encoding of the input, which the source does not spell out.

## Sources

- U. Chabaud, M. Joseph, S. Mehraban and A. Motamedi, "Bosonic quantum computational complexity", *Quantum* 10, 2110, 2026, doi:[10.22331/q-2026-05-20-2110](https://doi.org/10.22331/q-2026-05-20-2110); read in arXiv:2410.04274v3 ([arXiv](https://arxiv.org/abs/2410.04274v3)), whose numbering is used: Definition 5.2, Theorem 5.6 with its proof and the remark after it, Theorem 5.1 (Gaussian Hamiltonians) and Theorem 5.3 (degree 4 over Gaussian states).
- J. P. Jones, "Three universal representations of recursively enumerable sets", *The Journal of Symbolic Logic* 43(2), pp. 335–351, 1978, doi:[10.2307/2272832](https://doi.org/10.2307/2272832) (cited by the source for the degree-4 equations; not read here, cited beside the copy read above).
- T. D. Kieu, "Quantum algorithm for Hilbert's tenth problem", *International Journal of Theoretical Physics* 42, pp. 1461–1478, 2003, doi:[10.1023/A:1025780028846](https://doi.org/10.1023/A:1025780028846) (cited by the source for the number-operator encoding; not read here, cited beside the copy read above).
