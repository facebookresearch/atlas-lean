# The ground energy of degree-8 bosonic Hamiltonians is undecidable

No algorithm decides, for a polynomial of degree 8 in the position and momentum operators of finitely many bosonic modes, whether its lowest energy is below one threshold or above another; the problem is RE-hard.

**Theorem (Chabaud, Joseph, Mehraban and Motamedi).** The ground-energy problem $\mathsf{CVLH}^8_{\mathcal H}$ for [polynomial bosonic Hamiltonians](polynomial-bosonic-hamiltonians.md) of degree $8$, with the infimum taken over all states, is $\mathbf{RE}$-hard, and therefore undecidable.

The hardness persists when the states are restricted to Fock states, giving an $\mathbf{RE}$-complete problem $\mathsf{CVLH}^8_{\mathcal F}$, and under a constant bound on the energy of the states. The Hamiltonians produced by the reduction have integer spectrum, so their spectral gap is at least $1$. For Gaussian Hamiltonians (degree $2$) the problem is solvable in polynomial time, and for degree $4$ over Gaussian states of exponentially bounded energy it is NP-complete.

## Depends on

- [Polynomial bosonic Hamiltonians and their ground-energy problems](polynomial-bosonic-hamiltonians.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem. A polynomial $P\in\mathbb Z[x_1,\dots,x_n]$ has an integer zero exactly when $\min P^2(s_1x_1,\dots,s_nx_n)=0$ over signs $s\in\{\pm1\}^n$ and $x\in\mathbb Z_+^n$, so it suffices to minimize integer polynomials over non-negative integers. Following Kieu, for a polynomial $Q$ the operator $H_Q=Q(N_1,\dots,N_n)$ in the number operators $N_j=(X_j^2+P_j^2-1)/2$ is diagonal in the Fock basis with spectrum equal to the image $Q(\mathbb Z_+^n)$, so $\lambda_{\min}(H_Q)=\min_{x\in\mathbb Z_+^n}Q(x)$; taking $Q=P^2$ the ground energy is $0$ if $P$ has a zero and at least $1$ otherwise. To bound the degree, the proof uses Jones's universal Diophantine representation: there are undecidable polynomial equations of degree $4$ over the non-negative integers with a fixed number of unknowns, so $Q=P^2$ has degree $8$ in the $N_j$. A good expansion links pages for the undecidability of Hilbert's tenth problem over the non-negative integers in degree $4$ (Jones) and for the spectrum of the number operator; neither has a page yet.

## Sources

- U. Chabaud, M. Joseph, S. Mehraban and A. Motamedi, "Bosonic quantum computational complexity", *Quantum* 10, 2110, 2026, doi:[10.22331/q-2026-05-20-2110](https://doi.org/10.22331/q-2026-05-20-2110); read in arXiv:2410.04274v3 ([arXiv](https://arxiv.org/abs/2410.04274v3)), whose numbering is used: Theorem 5.6 with its proof and the remark after it, Theorem 5.1 (Gaussian Hamiltonians) and Theorem 5.3 (degree 4 over Gaussian states).
- J. P. Jones, "Three universal representations of recursively enumerable sets", *The Journal of Symbolic Logic* 43(2), pp. 335–351, 1978, doi:[10.2307/2272832](https://doi.org/10.2307/2272832) (cited by the source for the degree-4 bound; not read here, cited beside the copy read above).
- T. D. Kieu, "Quantum algorithm for Hilbert's tenth problem", *International Journal of Theoretical Physics* 42, pp. 1461–1478, 2003, doi:[10.1023/A:1025780028846](https://doi.org/10.1023/A:1025780028846) (cited by the source for the number-operator encoding; not read here, cited beside the copy read above).
