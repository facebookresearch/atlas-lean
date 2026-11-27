# Probability measures

A probability measure on a measurable space $(\alpha, \mathcal M)$ is a measure $\mu$ with $\mu(\alpha) = 1$.
Pushing a probability measure $P$ forward along a random element, a measurable map $X$ into a measurable space, gives
the probability measure $B \mapsto P(X \in B)$ on that space, the law of $X$.

## Idea

A probability space $(\Omega, \mathcal F, P)$ is a measure space of total mass $1$, and a random variable is a
measurable function on it. Lebesgue measure on $[0, 1]$ is a probability measure, and so is the uniform measure on
$\{1, \dots, 6\}$ that gives each point mass $\frac16$. If $X$ is the score of a fair die, its law
$B \mapsto P(X \in B)$, the push-forward of $P$ along $X$, is that uniform measure. Many properties of random
variables, such as their expected values, depend only on their laws.

## Statements

- [Probability measure](is-probability-measure.md)
- [Law of a random element](probability-measure-map.md): the law of a random element
- [Probability mass functions: uniform distributions and coin fixing](probability-mass-functions-uniform-distributions/README.md)
