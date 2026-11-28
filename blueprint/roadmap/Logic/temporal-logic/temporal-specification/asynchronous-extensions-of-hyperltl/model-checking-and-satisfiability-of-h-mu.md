# Model checking and satisfiability of H_μ are Σ¹₂-hard

For the fixpoint calculus H_μ of asynchronous hyperproperties, both model checking against a finite Kripke structure and satisfiability are hard for the level Σ¹₂ of the analytical hierarchy, so neither problem is arithmetical, let alone decidable.

**Theorem (Gutsfeld, Müller-Olm and Ohrem).** For the logic [$H_\mu$](the-fixpoint-calculus-h-mu.md):

1. model checking closed $H_\mu$ formulas against finite Kripke structures is $\Sigma^1_2$-hard (Theorem 5.3);
2. the satisfiability problem for $H_\mu$ is $\Sigma^1_2$-hard (Theorem 5.4).

Here $\Sigma^1_2$ is the class of sets of natural numbers definable by an arithmetic formula preceded by a block of existential quantifiers over functions $\mathbb N \to \mathbb N$ followed by a block of universal ones, and a problem is $\Sigma^1_2$-hard if every $\Sigma^1_2$ set many-one reduces to it by a computable function.

Both problems are therefore not arithmetical, and no approximation procedure that enumerates the positive or the negative instances exists. As a remedy, the source defines $k$-synchronous and $k$-context-bounded semantics, which under-approximate the full semantics and yield decidable model checking and satisfiability for fragments, with exact complexity bounds; for instance, satisfiability of the existential and universal fragments is PSPACE-complete in the synchronous case (Theorem 7.1). Existential quantifiers alone already suffice for the hardness of satisfiability, since an alternating asynchronous parity automaton is non-empty exactly when an existential formula built from it is satisfiable.

## Depends on

- [The fixpoint calculus H_μ for asynchronous hyperproperties](the-fixpoint-calculus-h-mu.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof passes through *alternating asynchronous parity automata* (AAPA), alternating parity automata reading a tuple of infinite words in which each transition advances only one of the input words. For each AAPA one can effectively build an $H_\mu$ formula equivalent to it over a fixed path assignment, and conversely. AAPA are closed under union, intersection and complement, and they simulate two-tape Büchi automata; since the inclusion problem for two-tape Büchi automata is $\Pi^1_2$-complete (Finkel and Lecomte), the emptiness problem for AAPA is $\Sigma^1_2$-hard, by reducing non-inclusion $R(\mathcal T)\not\subseteq R(\mathcal T')$ to non-emptiness of an AAPA for $R(\mathcal T)\cap\overline{R(\mathcal T')}$. Model checking the corresponding formula against a Kripke structure generating all words over the alphabet, or checking its satisfiability, then decides AAPA emptiness. A good expansion links pages for the $\Pi^1_2$-completeness of inclusion of two-tape Büchi automata (Proposition A.1 as cited in the source) and for the equivalence between AAPA and $H_\mu$ (Theorem 5.2). A good expansion adds a page for the analytical hierarchy, its levels $\Sigma^1_n$ and $\Pi^1_n$ and completeness under many-one reductions, which this statement uses.

## Sources

- J. O. Gutsfeld, M. Müller-Olm and C. Ohrem, "Automata and fixpoints for asynchronous hyperproperties", *Proceedings of the ACM on Programming Languages* 5(POPL), pp. 1–29, 2021, doi:[10.1145/3434319](https://doi.org/10.1145/3434319), whose abstract states that these decision problems are not even arithmetical; read in arXiv:2010.11605v1 ([arXiv](https://arxiv.org/abs/2010.11605v1)), whose numbering is used: Theorem 3.7 ($\Sigma^1_2$-hardness of AAPA emptiness) with its proof and Proposition A.2 in the appendix, Theorem 5.2 (equivalence of AAPA and $H_\mu$), Theorems 5.3 and 5.4 in Section 5.3, and Theorem 7.1 in Section 7.
- O. Finkel and D. Lecomte, "Decision problems for Turing machines", *Information Processing Letters* 109(23–24), pp. 1223–1226, 2009, doi:[10.1016/j.ipl.2009.09.002](https://doi.org/10.1016/j.ipl.2009.09.002), cited by the source (Proposition A.1) for the $\Pi^1_2$-completeness of inclusion of two-tape Büchi automata.
