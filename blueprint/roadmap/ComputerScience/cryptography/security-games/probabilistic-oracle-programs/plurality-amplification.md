# Plurality amplification for probabilistic computations with arbitrary outputs

Let $C$ be a probabilistic computation with outputs in a set with decidable equality, and suppose some value $a$ satisfies $\Pr[C = a] \ge \tfrac{1}{2} + \varepsilon$ with $\varepsilon > 0$. Run $C$ independently $t$ times and output the most frequent value (ties broken by first occurrence). Then the output equals $a$ with probability at least $1 - e^{-2t\varepsilon^2}$. The deterministic fact underlying this is that any value occurring in more than half the entries of a list is its plurality.

## Proof sketch

The plurality differs from $a$ only if $a$ occurs in at most half of the runs. The number of occurrences of $a$ is a sum of $t$ independent Bernoulli variables with mean at least $\tfrac12 + \varepsilon$, so Hoeffding's lower-tail bound gives the estimate.

## Depends on

- [Error reduction for BPP](../../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/error-reduction-for-bpp.md)

## Proof depends on

- [Hoeffding lower-tail bound for Bernoulli sums](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-binomial-lower-tail.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
