# Characteristic function

The characteristic function of a real random variable $X$ is $\varphi(t) = E e^{itX} = E \cos(tX) + i \, E \sin(tX)$
for $t \in \mathbb R$, and that of a probability measure $\mu$ on $\mathbb R$ is $t \mapsto \int e^{itx} \, \mu(dx)$. More
generally, a measure $\mu$ on a real inner product space has the characteristic function
$t \mapsto \int e^{i \langle x, t \rangle} \, d\mu(x)$, the second statement of this card; for the law of $X$ on $\mathbb R$ it
gives $\varphi$, by the change of variables formula.

## Idea

The characteristic function of a random variable, or of a probability measure on $\mathbb R$, always exists;
it satisfies $\varphi(0) = 1$ and $|\varphi(t)| \le 1$ and is uniformly continuous. For a finite measure the same
integral gives $\varphi(0) = \mu(\mathbb R)$, which can differ from $1$. It determines the distribution, by the inversion formula, and it turns sums of independent
random variables into products. For a standard normal random variable, $\varphi(t) = e^{-t^2/2}$.

## Statements

- [Characteristic function of a random variable](characteristic-function-random-variable.md)
- [Characteristic function of a measure](char-fun.md): more general: measures on real inner product spaces

## Background

- [Expected value](../../../foundations/laws-of-random-variables-and-identical-distribut/expectation/README.md): expected values
- [Probability measures](../../../foundations/probability-measures/README.md): probability measures and laws
