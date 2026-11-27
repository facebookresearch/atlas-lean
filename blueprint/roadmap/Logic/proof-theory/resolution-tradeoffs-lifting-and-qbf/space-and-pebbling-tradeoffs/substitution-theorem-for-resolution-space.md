# Substitution theorem for resolution space

Substituting a non-authoritarian function into an unsatisfiable CNF formula turns variable-space lower bounds for refuting the original formula into clause-space lower bounds, preserving length-space trade-offs, even against semantic resolution.

Let $f : \{0,1\}^d \to \{0,1\}$. For a CNF formula $F$ over variables $V$, the **substitution formula** $F[f]$ has variables $x_1, \dots, x_d$ for each $x \in V$ and is obtained by replacing each positive literal $x$ by the canonical CNF of $f(x_1, \dots, x_d)$, each negative literal $\overline{x}$ by the canonical CNF of $\neg f(x_1, \dots, x_d)$, and expanding each clause into a CNF. The function $f$ is **non-authoritarian** if no restriction of a single variable fixes its value; examples are XOR of at least $2$ variables and majority of at least $3$ variables.

**Theorem.** Let $f$ be a non-authoritarian Boolean function, let $F$ be an unsatisfiable CNF formula and let $\pi_f$ be any semantic resolution refutation of $F[f]$. Then there is a syntactic resolution refutation $\pi$ of $F$ such that

- $\pi$ makes at most as many axiom downloads as $\pi_f$, and
- $\mathit{VarSp}(\pi) = O(\mathit{CSp}(\pi_f))$, where $\mathit{CSp}$ is clause space.

In particular, if $F$ has no syntactic resolution refutation in variable space $O(s)$ with $O(L)$ axiom downloads, then $F[f]$ has no semantic resolution refutation in simultaneous length $O(L)$ and clause space $O(s)$.

## Expansion

Map each configuration $\mathbb{D}$ of $\pi_f$ to the set of clauses $C$ over $V$ such that $\mathbb{D}$ implies $\bigvee_{x^b \in C} f(\vec{x})^b$ precisely, that is, while no strict subclause has this property (the **resolution projection**). This projection is complete, nontrivial, monotone and incrementally sound, so the projected configurations form the backbone of a syntactic resolution refutation of $F$ whose axiom downloads correspond to downloads in $\pi_f$. For non-authoritarian $f$ the local projection is exactly space-respecting: the number of variables mentioned by the projection is at most the number of clauses of $\mathbb{D}$. For $k$-DNF resolution the same holds with degree $k + 1$ when $f$ is $(k+1)$-non-authoritarian.

## Depends on

- [Variable space and total space of resolution refutations](variable-and-total-space.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", *Logical Methods in Computer Science* 9(3:15), 2013, doi:10.2168/LMCS-9(3:15)2013, arXiv:1307.3913v3 (Definitions 2.12 and 2.13; Section 5.3, the generic substitution theorem; Section 5.4, the projection theorem for non-authoritarian functions).
