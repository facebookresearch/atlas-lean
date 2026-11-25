# Exact Bayesian-network inference is NP-hard

Consider Bayesian networks over binary variables given by a DAG and explicit conditional probability
tables with rational entries, encoded in binary. The decision problem "given such a network, a node
$X$ and a value $x$, is $P(X = x) > 0$?" is NP-complete (NP-hard by a polynomial-time reduction from
3-SAT). Consequently, computing $P(X = x)$ exactly, or exact posterior probabilities, is NP-hard
under polynomial-time Turing reductions. The positive-probability decision problem and exact numeric
computation are separate statements.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Polynomial-time many-one (Karp) reduction.

## Depends on

- [Bayesian network](bayesian-networks/bayes-net.md)

## Sources

- G. F. Cooper, *The computational complexity of probabilistic inference using Bayesian belief networks*, Artificial Intelligence 42 (1990) 393–405, Section 4: the decision problem PIBNETD (is $P(Y = T) > 0$?) and the reduction from 3-SAT showing it NP-hard. Membership in NP is immediate: guess a full assignment with $X = x$ and check that its product of table entries is positive. <https://stat.duke.edu/~sayan/npcomplete.pdf>
