# Conditional expectation given a σ-field

Let $(\Omega, \mathcal F_0, P)$ be a probability space, let $\mathcal F \subseteq \mathcal F_0$ be a σ-field, and
let $X$ be an $\mathcal F_0$-measurable random variable with $E|X| < \infty$. A *conditional expectation of $X$ given
$\mathcal F$*, written $E(X \mid \mathcal F)$, is any random variable $Y$ such that

1. $Y$ is $\mathcal F$-measurable, and
2. $\int_A X \, dP = \int_A Y \, dP$, that is, $E(X 1_A) = E(Y 1_A)$, for every $A \in \mathcal F$.

Each such $Y$ is called a *version* of $E(X \mid \mathcal F)$.

## Depends on

- [Expected value of a random variable](../../laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)
- [Probability measure](../../probability-measures/is-probability-measure.md)
- [Indicator function of a set](../../../../Algebra/algebraic-identities/indicator-one.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 4.1, definition of conditional expectation (version read: the author's January 2019 PDF).
