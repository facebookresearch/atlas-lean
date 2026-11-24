# Tower property

For σ-fields $\mathcal F_1 \subseteq \mathcal F_2$ and an integrable random variable $X$, conditioning on
$\mathcal F_1$ and on $\mathcal F_2$ in either order gives the conditional expectation given the smaller σ-field:
$E(E(X \mid \mathcal F_1) \mid \mathcal F_2) = E(E(X \mid \mathcal F_2) \mid \mathcal F_1) = E(X \mid \mathcal F_1)$ almost
surely.

## Idea

Whatever the order, the coarser information decides the result. Taking $\mathcal F_1$ trivial gives
$E\,E(X \mid \mathcal F_2) = EX$, the law of total expectation. The identity is what makes $E(X \mid \mathcal F_n)$ a
martingale along an increasing sequence of σ-fields $\mathcal F_n$.

## Statements

- [Tower property of conditional expectation](tower-property.md)

## Background

- [Conditional expectation given a σ-field](../conditional-expectation-given-a-sigma-field/README.md): conditional expectation
