# The Dirichlet form of linear Brownian motion is $\frac{1}{2} \int f'^2$

Let $f : \mathbb{R} \to \mathbb{R}$ be smooth with compact support, and let
$T_t f(x) = \mathbb E f(x + B_t) = \int f(x + y)\, N(0, t)(dy)$ be the Brownian semigroup, $N(0, t)$
the centred Gaussian law with variance $t$. Then

$$\frac{1}{t} \int_{\mathbb{R}} f(x) \bigl(f(x) - T_t f(x)\bigr)\, dx \to \frac{1}{2} \int_{\mathbb{R}} f'(x)^2\, dx \qquad (t \downarrow 0) .$$

This is the case $d = 1$, $u \in C_c^\infty(\mathbb{R})$ of Example 4.2.1 of Fukushima, Oshima and
Takeda (the Dirichlet form of $d$-dimensional Brownian motion is $(\frac{1}{2} \mathbf D, H^1(\mathbb{R}^d))$,
with the Gaussian semigroup (1.4.25)), combined with their Lemma 1.3.4(i):
$\mathcal E(u, u) = \lim_{t \downarrow 0} \frac{1}{t} (u - T_t u, u)$.

## Background

- [Existence of Brownian motion](../../stochastic-calculus/construction-and-sample-paths-of-brownian-motion/exists-is-brownian-real.md): Le Gall's construction of the process whose semigroup
  $T_t f(x) = \mathbb E f(x + B_t)$ appears here.
- [Dirichlet form of a sub-Markovian generator on a finite set](form.md): the discrete analogue,
  where $\tfrac12 \int |f'|^2$ becomes $\tfrac12 \sum m(x) Q(x,y) (f(x) - f(y))^2$.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Example 4.2.1, equation (1.4.25) and Lemma 1.3.4(i).
