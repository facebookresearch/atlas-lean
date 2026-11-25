# Martingales, submartingales and supermartingales

Let $(\Omega, \mathcal F, P)$ be a probability space and let $(\mathcal F_n)_{n \ge 0}$ be a filtration, an
increasing sequence of σ-fields contained in $\mathcal F$. A sequence $(X_n)_{n \ge 0}$ of real random variables is
*adapted* to $(\mathcal F_n)$ if each $X_n$ is $\mathcal F_n$-measurable. It is a *martingale* with respect to
$(\mathcal F_n)$ if

1. $E|X_n| < \infty$ for every $n$,
2. $(X_n)$ is adapted to $(\mathcal F_n)$, and
3. $E(X_{n+1} \mid \mathcal F_n) = X_n$ almost surely for every $n$.

It is a *supermartingale* if the equality in the third condition is replaced by $E(X_{n+1} \mid \mathcal F_n) \le X_n$,
and a *submartingale* if it is replaced by $E(X_{n+1} \mid \mathcal F_n) \ge X_n$, almost surely for every $n$.

## Depends on

- [Conditional expectation given a σ-field](../../foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)
- [Expected value of a random variable](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)
- [Probability measure](../../foundations/probability-measures/is-probability-measure.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 4.2, definitions of a filtration, an adapted sequence and a martingale (version read: the author's January 2019 PDF).
