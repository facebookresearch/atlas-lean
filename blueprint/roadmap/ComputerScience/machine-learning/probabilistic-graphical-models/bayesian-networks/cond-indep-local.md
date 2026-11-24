# The local directed Markov property

**The local directed Markov property** (Lauritzen 2009, lecture 7; the directed Markov
property (L)): let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a
finite nonempty type $\alpha$. Under the joint distribution of $B$, every node $k$ is
conditionally independent of its non-descendants that are not parents of $k$, given its
parents.

Here the non-descendants of $k$ are the nodes $j$ that cannot be reached from $k$ along
arrows; $k$ itself is excluded because every node is its own descendant. The parents of $k$
d-separate $k$ from these nodes, so the property is a case of
[the global Markov property](cond-indep-of-d-separated.md).

## Background

- [The ordered Markov property](cond-eq-cpt.md) and [the global Markov property](cond-indep-of-d-separated.md):
  the other two directed Markov properties (O) and (G) of a factorizing law; for any DAG the three
  are equivalent (Lauritzen 2009).
