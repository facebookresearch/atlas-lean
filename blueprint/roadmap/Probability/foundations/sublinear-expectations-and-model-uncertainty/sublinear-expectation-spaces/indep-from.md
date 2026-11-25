# Independence under a sublinear expectation

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a [sublinear expectation
space](sublinear-expectation-space.md), and let $X : \Omega \to F_1$ and $Y : \Omega \to F_2$
take values in seminormed abelian groups. Then $Y$ is independent from $X$ if

$$\mathbb{E}[\varphi(X, Y)] = \mathbb{E}\big[\, \mathbb{E}[\varphi(x, Y)]_{x = X} \big]$$

for every $\varphi \in C_{l.Lip}(F_1 \times F_2)$ ([Peng's test functions](is-loc-lip.md)). The
relation is not symmetric in $X$ and $Y$ (Remark 3.12 of the source).

## Background

- [Sublinear expectation space](sublinear-expectation-space.md): the setting. Under a linear
  expectation this is classical independence; under a sublinear one the order matters: $Y$ is
  independent from $X$ when the uncertainty of the law of $Y$ does not change with the realised
  value of $X$ (Peng, Remark I.3.11).

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Definition 3.10.
