# The directed Markov properties are equivalent

**The directed Markov properties are equivalent** (Lauritzen 2009): let $\alpha$ be a finite
nonempty type, $P : \alpha^n \to \mathbb{R}$ a probability distribution ($P \ge 0$ and
$\sum_x P(x) = 1$) and $B$ a Bayesian network on the nodes $0, \dots, n - 1$ with values in
$\alpha$. The following are equivalent:

- (F) $P$ is the joint distribution of a Bayesian network with the same parent sets as $B$;
- (G) $P$ has the global Markov property for the graph of $B$;
- (L) $P$ has the local Markov property for the graph of $B$;
- (O) $P$ has the ordered Markov property for the parent sets of $B$.

The cycle of implications is (F) ⇒ (G) by the soundness of d-separation, (G) ⇒ (L) because the
parents of a node d-separate it from its other non-descendants, (L) ⇒ (O) by decomposition
(predecessors are non-descendants), and (O) ⇒ (F) by building the network of conditional laws
given the parents. No positivity is needed anywhere; for undirected graphs the analogous
equivalence of factorization with the Markov properties (Hammersley–Clifford) requires a positive
density.

## Background

- [Completeness of d-separation](exists-not-cond-indep-of-not-d-separated.md): the global
  Markov property is the strongest graphical criterion, since every non-d-separated triple is
  dependent for some factorizing law.
