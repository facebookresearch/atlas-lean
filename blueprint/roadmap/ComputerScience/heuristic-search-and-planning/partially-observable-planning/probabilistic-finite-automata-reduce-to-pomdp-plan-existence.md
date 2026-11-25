# Probabilistic finite automata reduce to POMDP plan existence

Plans for an unobservable Markov decision process are finite action sequences of unbounded length. There is a
computable reduction that maps a probabilistic finite automaton $\mathcal{A}$ and a rational threshold $\lambda$ to an
unobservable Markov decision process with a goal set, such that $\mathcal{A}$ accepts some word with probability
greater than $\lambda$ if and only if some plan reaches the goal with probability greater than $\lambda$.

Since the threshold emptiness problem for probabilistic finite automata is undecidable (Paz; Condon and Lipton), the
plan-existence problem is undecidable for unobservable Markov decision processes, and hence for partially
observable ones, of which they are a special case.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Probabilistic finite automata, the probability that one accepts a word, and the threshold emptiness problem.

## Depends on

- [Finite POMDPs](finite-pomdps.md)

## Sources

- O. Madani, S. Hanks and A. Condon, *On the undecidability of probabilistic planning and infinite-horizon partially observable Markov decision problems*, AAAI 1999, Theorem 2.1, §3 (Theorem 3.1) and §4. <https://cdn.aaai.org/AAAI/1999/AAAI99-077.pdf>
