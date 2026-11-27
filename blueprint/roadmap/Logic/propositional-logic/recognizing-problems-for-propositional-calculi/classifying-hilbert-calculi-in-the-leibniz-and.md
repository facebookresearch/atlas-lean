# Classifying Hilbert calculi in the Leibniz and Frege hierarchies is undecidable

No algorithm determines, for the logic of a finite consistent Hilbert calculus, its level in the Leibniz hierarchy or in the Frege hierarchy of abstract algebraic logic; for the Frege hierarchy this holds even among calculi defining finitely algebraizable logics.

**Theorem (Moraschini).** A *Hilbert calculus* in a finite propositional language consists of finitely many axioms and rules $\Gamma \vdash \varphi$ closed under substitution, and its *logic* is the substitution-invariant consequence relation it derives; the calculus is *consistent* if its logic does not derive every formula from the empty set. Then:

1. for every level $\mathsf K$ of the Leibniz hierarchy as displayed in Figure 1 of the source, from protoalgebraic and truth-equational logics down to finitely regularly algebraizable logics, the problem of determining whether the logic of a given consistent finite Hilbert calculus in a finite language belongs to $\mathsf K$ is undecidable (Theorem 4.10 of the source);
2. for every level $\mathsf K$ of the Frege hierarchy (selfextensional, fully selfextensional, Fregean and fully Fregean logics), the problem of determining whether the logic of a given finite consistent Hilbert calculus in a finite language belongs to $\mathsf K$ is undecidable, and remains undecidable when restricted to calculi that determine a finitely algebraizable logic (Theorem 5.3).

Here a logic $L$ is *protoalgebraic* if it has a set $\rho(x, y)$ of formulas with $\vdash_L \rho(x, x)$ and $x, \rho(x, y) \vdash_L y$, and *selfextensional* if interderivability $\dashv\vdash_L$ is a congruence on the formula algebra; the other levels strengthen these conditions.

## Depends on

None.

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

*Leibniz hierarchy.* To each Diophantine equation $p \approx 0$ one effectively assigns a consistent finite Hilbert calculus whose logic $L(p)$ belongs to $\mathsf K$ iff $p \approx 0$ has an integer solution; this works for every class $\mathsf K$ containing the finitely regularly algebraizable logics and contained in the protoalgebraic logics or in the logics whose truth sets are implicitly definable (Theorem 4.8). An algorithm for membership in $\mathsf K$ would solve Hilbert's tenth problem.

*Frege hierarchy.* For an equation $\alpha \approx \beta$ in the language of a finitely based variety of finite type, a finitely algebraizable logic $L(\alpha, \beta)$ is built that is fully Fregean, and equally lies in any level of the Frege hierarchy, iff $\alpha \approx \beta$ holds in the variety (Theorem 5.2); varieties of this kind with undecidable equational theory in one variable exist, which gives the reduction.

## Sources

- T. Moraschini, "A computational glimpse at the Leibniz and Frege hierarchies", *Annals of Pure and Applied Logic* 169(1):1–20, 2018, <https://doi.org/10.1016/j.apal.2017.07.003>; numbers from arXiv:1908.00922v1, <https://arxiv.org/abs/1908.00922v1>: Section 3 (protoalgebraic and selfextensional logics, Figures 1 and 2), Theorems 4.8 and 4.10, Corollary 4.9, Theorems 5.2 and 5.3.
