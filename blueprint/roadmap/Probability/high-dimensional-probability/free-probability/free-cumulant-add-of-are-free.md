# Free cumulants are additive for free variables

Let $(A, \varphi)$ be a noncommutative probability space and let $a, b \in A$ be
[free](are-free.md). Then for every $n \ge 1$,

$$\kappa_n(a + b) = \kappa_n(a) + \kappa_n(b),$$

where $\kappa_n(x)$ is the [free cumulant](free-cumulant.md) of the moment sequence
$k \mapsto \varphi(x^k)$. Equivalently, the [R-transform](r-transform.md) is additive,
$R_{a+b} = R_a + R_b$, and the law of $a + b$ is the free additive convolution of the laws of $a$
and $b$.

The source states it for bounded operators; its proof is algebraic: expand $\kappa_n(a + b)$ by
multilinearity of the multivariate cumulants and use that mixed cumulants of free variables vanish
(Theorem 5.3.15).

## Informally uses

- Vanishing of mixed free cumulants of free variables (Anderson, Guionnet and Zeitouni, Theorem 5.3.15):
  it removes the cross terms in the multilinear expansion of $\kappa_n(a + b)$.

## Background

- [Free random variables](are-free.md): the hypothesis.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Lemma 5.3.21 and Corollary 5.3.23 (via Theorem 5.3.15).
