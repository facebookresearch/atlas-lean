# Coin-flipping programs have rational output probabilities, and rational Bernoulli coins are exactly samplable

Every terminating probabilistic program built from uniform choices over finite sets $\{0, \dots, n\}$ assigns to each output a rational probability, computable structurally from the program tree. Conversely, for every rational $p = a/b \in [0,1]$, the program that draws one uniform element $i$ of $\{0, \dots, b-1\}$ and outputs $[i < a]$ is an exact Bernoulli($p$) coin. With only fair bits, an exact Bernoulli($a/b$) coin needs unbounded running time when the reduced denominator of $a/b$ is not a power of two, but a $T$-trial capped sampler is within statistical distance $2^{-T}$.

## Proof sketch

Induction on the program: the probability of an output is an average, with rational weights $1/(n+1)$, of the probabilities in the subprograms. A program using only fair bits and at most $T$ coins has probabilities in $2^{-T}\mathbb{Z}$, which excludes non-dyadic rationals.

## Depends on

- [Probabilistic oracle program and its semantics against a stateful handler](../../cryptography/security-games/probabilistic-oracle-programs/probabilistic-oracle-program.md)

## Proof depends on

- [Capped block rejection sampling from fair bits](capped-block-rejection-sampling.md)

## Sources

- D. E. Knuth and A. C. Yao, "The Complexity of Nonuniform Random Number Generation", in Algorithms and Complexity: New Directions and Recent Results, Academic Press, 1976.
- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd edition, Addison-Wesley, 1997.
