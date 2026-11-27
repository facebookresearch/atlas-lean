# Correctness of the ALC tableau algorithm

Let $C_0$ be an ALC concept in negation normal form, and consider the rules of the [tableau algorithm for ALC](alc-tableau-algorithm.md).

1. There is no infinite sequence of rule applications $\{\{C_0(x_0)\}\} \to S_1 \to S_2 \to \cdots$.
2. If $S'$ is obtained from a finite set $S$ of ABoxes by a rule application, then $S$ is consistent if and only if $S'$ is.
3. Every closed ABox is inconsistent.
4. Every complete and open ABox $\mathcal A$ that belongs to a set reachable from $\{\{C_0(x_0)\}\}$ by rule applications is consistent; such an ABox contains $C_0(x_0)$ and only concept assertions $C(x)$ with $C$ a subconcept of $C_0$, so it is nonempty and in negation normal form. Its *canonical interpretation*, with domain the individual names of $\mathcal A$, $P^{\mathcal I} = \{x \mid P(x) \in \mathcal A\}$ and $r^{\mathcal I} = \{(x, y) \mid r(x, y) \in \mathcal A\}$, is a model of $\mathcal A$. The restriction matters: the ABox $\{\neg(P \sqcup \neg P)(a)\}$, not in negation normal form, is complete, open and inconsistent.

Hence the algorithm answers "satisfiable" exactly when $C_0$ is satisfiable (with respect to the empty TBox).

**Proof idea.** Termination holds because every concept assertion $C(x)$ has $C$ a subconcept of $C_0$, and along a role assertion $r(x, y)$ the maximal role depth of the concepts asserted for $y$ is smaller than for $x$. Parts 2 and 3 are direct; part 4 is an induction on concepts.

## Depends on

- [Tableau algorithm for ALC](alc-tableau-algorithm.md)

## Sources

- F. Baader and U. Sattler, "An overview of tableau algorithms for description logics", *Studia Logica* 69(1):5–40, 2001, <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSattler-StudiaLogica.pdf>, Section 3, Lemma 1 and the proof sketch after it, p. 8.
