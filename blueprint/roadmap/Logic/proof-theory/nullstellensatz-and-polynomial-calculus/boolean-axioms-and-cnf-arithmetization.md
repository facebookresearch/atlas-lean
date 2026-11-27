# Boolean axioms and CNF arithmetization

Over a commutative ring $\mathcal{R}$, a system of polynomials $F \subseteq \mathcal{R}[x_1,\dots,x_n]$ has a *Boolean solution* $a \in \{0,1\}^n$ if every $f \in F$ vanishes at $a$. The *Boolean axioms* are $x_i^2 - x_i$. A clause $C$ with positive variables $P$ and negative variables $N$ is arithmetized by $p_C = \prod_{v\in P}(1 - x_v)\prod_{v\in N} x_v$, which vanishes at a Boolean point exactly when the point satisfies $C$; a CNF formula is satisfiable iff its clause polynomials have a common Boolean zero. In the *twin-variable* (PCR) encoding each literal $\ell$ gets its own variable, with complementarity axioms $x_v + x_{\bar v} - 1$, and clauses become squarefree monomials.

## Depends on

- [CNF formula](../../propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi and P. Pudlák, "Lower Bounds on Hilbert's Nullstellensatz and Propositional Proofs", Proceedings of the London Mathematical Society 73(1), 1–26, 1996.
- M. Clegg, J. Edmonds and R. Impagliazzo, "Using the Groebner Basis Algorithm to Find Proofs of Unsatisfiability", Proceedings of the 28th ACM Symposium on Theory of Computing (STOC), 1996.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Sections 7.5.1–7.5.2 (translation (7.16) and the twin-variable axiom (7.20d)).
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
