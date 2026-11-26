# Roberts' theorem

Let there be finitely many agents and finitely many outcomes, and suppose the range of a social choice rule $f$ on the unrestricted valuation domain $\mathbb{R}^\Omega$ contains at least three outcomes. If $f$ is weakly monotone (in particular, if it is implementable in dominant strategies), then $f$ is an affine maximizer over its range: there are nonnegative weights $w$ summing to $1$ and constants $c$ with $f(b) \in \arg\max_{a} (c(a) + \sum_i w_i b_i(a))$.

## Proof sketch

Weak monotonicity implies positive association of differences: for outcomes $a, b$ the set of valuation difference vectors leading to $a$ over $b$ is a convex cone-like set. With at least three outcomes these sets fit together consistently, and a separating hyperplane argument yields common weights and constants.

## Depends on

- [Affine maximizer and weighted Groves mechanism](affine-maximizer-and-weighted-groves-mechanism.md)
- [Weak monotonicity and cyclic monotonicity of social choice rules](weak-monotonicity-and-cyclic-monotonicity-of-social-choice-rules.md)

## Proof depends on

- [Implementable rules are weakly monotone; cyclic monotonicity characterizes implementability](implementable-rules-are-weakly-monotone-cyclic-monotonicity-characterizes-implem.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
