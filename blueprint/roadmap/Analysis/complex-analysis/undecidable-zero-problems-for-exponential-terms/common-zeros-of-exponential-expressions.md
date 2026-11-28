# Common complex zeros of exponential expressions are undecidable

For complex functions built from the integers and z by addition, multiplication and composition with the exponential function, no algorithm decides whether a given finite list of them has a common zero in ℂ.

**Theorem (Adler).** Let $\mathcal E$ be the set of functions $\mathbb C \to \mathbb C$ built from the integers and $z$ using addition, multiplication and composition with $e^z$. It is impossible to decide, given finitely many functions $f_1, \ldots, f_k \in \mathcal E$ (as expressions), whether there is $z \in \mathbb C$ with $f_1(z) = \cdots = f_k(z) = 0$.

This contrasts with the real case, where, assuming Schanuel's conjecture, Macintyre and Wilkie gave a decision procedure for the first-order theory of the real field with exponentiation.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces Hilbert's tenth problem, the undecidability of solvability of Diophantine equations over $\mathbb Z$, which follows from the Davis–Putnam–Robinson–Matiyasevich theorem and the undecidability of halting. It uses two observations: $\mathbb Q$ is the set of ratios of zeros of $e^z - 1$ in $\mathbb C$, and $\mathbb Z$ is the set of $x \in \mathbb Q$ for which there is $z \in \mathbb C$ with $e^z = 2$ and $e^{zx} \in \mathbb Q$. With these characterizations, solvability of a Diophantine equation is expressed as the existence of a common zero of explicit functions in $\mathcal E$; the details of the construction are in the source. A good expansion links pages for Hilbert's tenth problem over $\mathbb Z$ and for the two characterizations of $\mathbb Q$ and $\mathbb Z$ above.

## Sources

- Andrew Adler, "Some recursively unsolvable problems in analysis", *Proceedings of the American Mathematical Society* 22(2), 1969, pp. 523–526, <https://doi.org/10.1090/S0002-9939-1969-0248020-7>: Theorem 1 (cited after the survey below).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Remark 9.1 in Section 9.1.2 ("Adjoining the exponential function") of that version.
