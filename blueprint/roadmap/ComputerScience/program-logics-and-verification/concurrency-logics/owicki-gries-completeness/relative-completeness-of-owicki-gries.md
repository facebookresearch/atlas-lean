# Relative completeness of the Owicki–Gries system

With auxiliary variables, the Owicki–Gries system is complete in the sense of Cook: for every interpretation relative to which the assertion language is expressive, every partial-correctness formula true in it is derivable when all formulas true in the interpretation may be used in the rule of consequence.

Use the [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md) over a first-order assertion language $L$, for the class $\mathcal{S}$ of parallel programs $[S_1 \parallel \dots \parallel S_n]$ whose components are while programs with $\mathbf{await}$ statements, parallel composition occurring only at the top level. For an interpretation $I$ of $L$:

- a set of states is *definable* in $I$ if it is $\{\sigma \mid \sigma \models_I \varphi\}$ for some formula $\varphi$;
- $\mathcal{M}_I(S, \sigma)$ is the set of final states of terminating computations of $S$ over $I$ from $\sigma$, and $\mathrm{sp}_I(P, S) = \{\tau \mid \exists \sigma.\ \sigma \models_I P \wedge \tau \in \mathcal{M}_I(S, \sigma)\}$ is the strongest postcondition;
- $L$ is *expressive* relative to $I$ and $\mathcal{S}$ if $\mathrm{sp}_I(P, S)$ is definable for every assertion $P$ and program $S \in \mathcal{S}$.

**Theorem (Owicki).** For every interpretation $I$ such that $L$ is expressive relative to $I$ and $\mathcal{S}$, every correctness formula $\{p\}\,S\,\{q\}$ with $S \in \mathcal{S}$ that is true in $I$ in the sense of partial correctness is derivable in the Owicki–Gries system with auxiliary variables, assuming all formulas true in $I$.

The auxiliary-variable rule cannot be dropped: without it the system is incomplete even with Olderog's adaptation rule ([auxiliary variables are needed for shared-variable parallelism](auxiliary-variables-are-needed-for-shared-vars.md)), and no other rule is needed.

## Depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Proof depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)
- [Reachability annotations give interference-free proof outlines](reachability-annotations-are-interference-free.md)

## Expansion

The proof summarized by Prensa Nieto instruments the program with a history variable, annotates every control point with the reachable states, which form locally correct, interference-free proof outlines matching the precondition and postcondition, applies the parallel rule, and deletes the history variable with the auxiliary-variable rule. That summary codes histories and states as natural numbers, so it applies to the standard interpretation in the natural numbers, for which Prensa Nieto states the result and to which the reachability lemma refers. For an arbitrary interpretation relative to which $L$ is expressive, both the construction of a history variable with its annotations in that interpretation and the step that turns the reachable-state annotations into assertions of $L$ by expressiveness are missing developments: they are in Owicki's original proof, which the sources read here attribute but do not reproduce.

## Sources

- K. R. Apt and E.-R. Olderog, "Fifty years of Hoare's logic", *Formal Aspects of Computing* 31(6):751–807, 2019, <https://doi.org/10.1007/s00165-019-00501-3>, author version arXiv:1904.03917v1, <https://arxiv.org/abs/1904.03917v1>: Section 4.2 (definability, $\mathcal{M}_I$, $\mathrm{sp}_I$, expressiveness and completeness in the sense of Cook) and Section 8.1 (Owicki proved the system for parallel programs with the AUXILIARY VARIABLES rule complete in the sense of Cook; that rule is essential and no other rule is needed).
- L. Prensa Nieto, "Completeness of the Owicki-Gries system for parameterized parallel programs", in *Proceedings 15th International Parallel and Distributed Processing Symposium (IPDPS 2001)*, workshop on Formal Methods for Parallel Programming: Theory and Applications, IEEE, 2001, pp. 1534–1541, <https://doi.org/10.1109/IPDPS.2001.925138>, author copy <https://www-sop.inria.fr/lemme/Leonor.Prensa/publications/Compl.ps.gz>: Section 1 (the system was proved sound and relatively complete with respect to the standard interpretation in the natural numbers) and Section 3 (structure of the completeness construction).
- S. Owicki, "A consistent and complete deductive system for the verification of parallel programs", in *Proceedings of the Eighth Annual ACM Symposium on Theory of Computing (STOC '76)*, ACM, 1976, pp. 73–86, <https://doi.org/10.1145/800113.803634>: not consulted; the theorem as attributed by Apt and Olderog, Section 8.1.
