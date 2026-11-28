# Model checking existential TeamCTL with Boolean disjunction is Σ¹₁-hard

Model checking finite Kripke structures against the existential fragment of TeamCTL extended with Boolean disjunction is Σ¹₁-hard, hence highly undecidable, because time evaluation functions let traces progress asynchronously.

**Theorem (Gutsfeld, Meier, Ohrem and Virtema).** The model-checking problem for $\exists$TeamCTL$(\varovee)$ is $\Sigma^1_1$-hard: deciding, given a formula $\varphi$ of the existential fragment of [TeamCTL](temporal-team-logics-with-time-evaluation.md) with Boolean disjunction and a finite Kripke structure $\mathcal K$, whether $\mathrm{Traces}(\mathcal K) \models_\exists \varphi$ is $\Sigma^1_1$-hard (Theorem 5.2 of the source, by a reduction from the $\Sigma^1_1$-complete problem whether a nondeterministic two-counter machine has a computation that visits a given instruction infinitely often, Theorem 5.1).

The source attributes the high undecidability to asynchronicity. Model checking $\exists$TeamLTL$(\varovee, \subseteq)$, $\forall$TeamLTL$(\varovee, \subseteq, \mathrm{NE})$ and $\forall$TeamCTL$(\varovee, \subseteq)$ is $\Sigma^0_1$-hard through the embedding of synchronous TeamLTL of Theorem 4.3 combined with the $\Sigma^0_1$-hardness of synchronous TeamLTL$(\varovee, \subseteq)$ model checking (Theorem 2 of Virtema, Hofmann, Finkbeiner, Kontinen and Yang; see [Model checking synchronous TeamLTL with inclusion atoms and Boolean disjunction is undecidable](model-checking-synchronous-teamltl-with.md)), as the source's Section 4 and its complexity overview table record; Corollary 4.5 states the same bound for $\exists$TeamCTL$(\varovee, \subseteq)$. For $k$-synchronous or $k$-context-bounded tefs, model checking TeamCTL* over teams of a fixed size, together with satisfiability over teams of a fixed size and path checking, is decidable via alternating asynchronous Büchi automata (Corollary 6.8); the source notes that the proof of Theorem 5.2 relies on infinite teams and that fixing the team size recovers decidability.

## Depends on

- [Temporal team logics with time evaluation functions](temporal-team-logics-with-time-evaluation.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Recurring computations of two-counter machines are Σ¹₁-hard](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/recurring-computations-of-two-counter-machines.md)

## Expansion

The proof reduces the existence of a $b$-recurring computation of a nondeterministic two-counter machine, one that visits the instruction labeled $b$ infinitely often, which is $\Sigma^1_1$-complete (Alur and Henzinger, *Journal of the ACM* 41(1):181–204, 1994, quoted as Theorem 5.1 of the source). From the instructions $I$ and the label $b$ one builds a fixed-shape Kripke structure $\mathcal K_I$ and a formula $\varphi_{I, b}$ with $\mathrm{Traces}(\mathcal K_I) \models_\exists \varphi_{I, b}$ iff such a computation exists: the formula picks particular traces of $\mathcal K_I$, and the existentially quantified tefs, which let these traces advance at different speeds, align the counter values of consecutive configurations. A good expansion adds a page for the analytical hierarchy, its level $\Sigma^1_1$ and completeness under many-one reductions, which the statement uses.

## Sources

- J. O. Gutsfeld, A. Meier, C. Ohrem and J. Virtema, "Temporal Team Semantics Revisited", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, pp. 1–13, <https://doi.org/10.1145/3531130.3533360>; journal version *Journal of Computer and System Sciences* 163, 2027, article 103859, <https://doi.org/10.1016/j.jcss.2026.103859>; numbers from arXiv:2110.12699v3, <https://arxiv.org/abs/2110.12699v3>: Section 5: Theorem 5.1 and Theorem 5.2 with its proof (the structure $\mathcal K_I$); Theorem 4.3, Corollary 4.5, the complexity overview table, and Corollary 6.8 in Section 6.
