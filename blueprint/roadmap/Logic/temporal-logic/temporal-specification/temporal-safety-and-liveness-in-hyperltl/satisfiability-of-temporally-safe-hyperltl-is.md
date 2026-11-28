# Satisfiability of temporally safe HyperLTL is co-r.e.-complete

Whether a temporal safety HyperLTL formula is satisfied by some nonempty set of traces is a co-r.e.-complete problem, so it is undecidable but, unlike general HyperLTL satisfiability, lies at the first level of the arithmetical hierarchy.

**Theorem (Beutner, Carral, Finkbeiner, Hofmann and Krötzsch).** The satisfiability problem for [temporal safety HyperLTL formulas](temporal-safety-hyperltl-formulas.md), whether a given closed temporal safety HyperLTL formula $\varphi$ is satisfied by some nonempty set of traces, is co-r.e.-complete, that is, complete for the class [$\Pi^0_1$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md). Hardness holds already for formulas of the form $\forall\exists^*.\,G(X^*)$: a single universal and some existential trace quantifiers, and a body $G\phi \wedge \phi'$ with $\phi$ built from propositions, Booleans and $X$ and $\phi'$ propositional (Lemma 3.10).

For general HyperLTL, satisfiability is $\Sigma^1_1$-complete (Fortin, Kuijer, Totzke and Zimmermann); temporal safety therefore lowers it from the analytical to the arithmetical hierarchy. For $\forall^*\exists^*.\,G$ formulas without $X$ the problem is NEXPTIME-complete.

## Depends on

- [Temporal safety HyperLTL formulas](temporal-safety-hyperltl-formulas.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

*Membership.* Given $\varphi = Q_1\pi_1 \dots Q_n\pi_n.\,\phi$, take a safety automaton for $\phi$ (a nondeterministic automaton that accepts a word iff it has an infinite run) and build an equisatisfiable two-sorted first-order sentence with sorts for traces and time points, a successor predicate, predicates $P_a(x, i)$ for "proposition $a$ holds on trace $x$ at time $i$", and predicates $\mathit{State}_q(x_1, \dots, x_n, i)$ for the automaton's run on each tuple of traces. The sentence keeps the trace quantifiers and requires every chosen tuple to have an infinite run from the initial state. First-order satisfiability is co-r.e. by the completeness theorem, so the problem is co-r.e.

*Hardness.* Non-termination of deterministic Turing machines reduces to it: each trace encodes a configuration, and the $\forall\exists$ formula requires every configuration on a trace $\pi$ to have its successor configuration on some trace $\pi'$, which is checked locally by comparing consecutive positions under one $G$.

## Sources

- R. Beutner, D. Carral, B. Finkbeiner, J. Hofmann and M. Krötzsch, "Deciding hyperproperties combined with functional specifications", in *37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, Article 56, pp. 1–13, doi:10.1145/3531130.3533369; read as arXiv:2205.15138v1, <https://arxiv.org/abs/2205.15138v1>: Theorem 3.7 of arXiv:2205.15138v1, with Proposition 3.9 (membership) and Lemma 3.10 (hardness), and Lemma 3.13 and Table 1 for the NEXPTIME case.
