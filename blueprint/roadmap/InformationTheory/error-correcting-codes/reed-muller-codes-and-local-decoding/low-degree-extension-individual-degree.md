# Low-degree extensions with individual degree |H| - 1

Let $\mathbb{F}$ be a field, $H \subseteq \mathbb{F}$ a finite set and $m \ge 1$. For every function $f : H^m \to \mathbb{F}$, the low-degree extension

$$\hat f(x) = \sum_{u \in H^m} f(u) \prod_{i=1}^{m} L_{u_i}(x_i), \qquad L_a(y) = \prod_{b \in H,\ b \ne a} \frac{y - b}{a - b},$$

is the evaluation of an $m$-variate polynomial of degree at most $|H| - 1$ in each variable (hence total degree at most $m(|H| - 1)$, a Reed-Muller codeword when $\mathbb{F}$ is finite) that agrees with $f$ on $H^m$. Moreover, if $\mathbb{F}$ is finite and $m(|H| - 1) < |\mathbb{F}| - 1$, then for every grid point $a \in H^m$ and every direction $\tau \in \mathbb{F}^m$,

$$\sum_{u \in \mathbb{F}^\times} \hat f(u\tau + a) = -f(a).$$

The extension of a constant table is that constant.

## Proof sketch

Each $L_a$ is the Lagrange basis polynomial of degree $|H| - 1$ that is $1$ at $a$ and $0$ at the other points of $H$, so the product $\prod_i L_{u_i}(x_i)$ is the indicator of $u$ on the grid. For the unmasking identity, $c \mapsto \hat f(c\tau + a)$ is a univariate polynomial of degree below $|\mathbb{F}| - 1$, whose values over $\mathbb{F}$ sum to zero; removing the term $c = 0$, which is $f(a)$, leaves $-f(a)$.

## Depends on

- [Lagrange interpolant](../../../Analysis/approximation-theory/lagrange-interpolation/eval-interpolant.md)

## Proof depends on

- [Minimum distance of q-ary Reed-Muller codes](minimum-distance-of-q-ary-reed-muller-codes.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Chapters 7-8, public draft (March 2007), 2007.
- L. Babai, L. Fortnow, L. A. Levin, M. Szegedy, "Checking Computations in Polylogarithmic Time", Proceedings of the 23rd Annual ACM Symposium on Theory of Computing, 1991.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- R. Williams, "Simulating Time With Square-Root Space", Proceedings of the 57th Annual ACM Symposium on Theory of Computing (STOC 2025), 2025.
