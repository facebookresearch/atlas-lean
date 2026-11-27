# Coin fixing: some fixed coins achieve at least the average success

Let $A$ be a randomized oracle program whose private coins are drawn from a finite uniform set $\Omega$ (in addition to any oracle randomness), and let $E$ be an event on the outcome of an experiment involving $A$. Then there exists $\omega \in \Omega$ such that the deterministic program $A_\omega$ obtained by fixing the coins to $\omega$ satisfies

$$\Pr[E \text{ with } A_\omega] \ge \Pr[E \text{ with } A].$$

Equivalently, the success probability of a randomized program is the average over coins of the success probabilities of its deterministic restrictions.

## Proof sketch

The success probability is the uniform average over $\omega$ of the conditional success probabilities, and an average is at most the maximum term.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](probabilistic-oracle-program.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
