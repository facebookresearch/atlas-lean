# Kantorovich–Rubinstein formula

Let $X$ be a Polish metric space and $\mu$ and $\nu$ Borel probability measures on $X$ with finite
first moments. Then

$$W_1(\mu, \nu) = \sup_{\|\psi\|_{\mathrm{Lip}} \le 1} \Bigl( \int_X \psi \, d\mu - \int_X \psi \, d\nu \Bigr),$$

the supremum over all $1$-Lipschitz functions $\psi : X \to \mathbb{R}$.

## Idea

The formula turns a minimisation over couplings into a maximisation over test functions, so that
$W_1$ is the norm dual to Lipschitz functions. The inequality $\ge$ is elementary: for every
coupling $\pi$, $\int \psi \, d\mu - \int \psi \, d\nu = \int (\psi(x) - \psi(y))\, d\pi$, which is at
most $\int d(x, y)\, d\pi$. The converse is Kantorovich duality for the cost $c = d$, where both
potentials can be taken equal to a single $1$-Lipschitz function.

## Statements

- [Kantorovich–Rubinstein formula](wasserstein-one-eq-i-sup-lipschitz.md)
- [Kantorovich–Rubinstein bound for real Lipschitz functions](enorm-integral-sub-le-mul-wasserstein-on.md): the elementary inequality, for $L$-Lipschitz functions.
- [Lipschitz test functions are controlled by $W_1$](lintegral-le-add-mul-wasserstein-one.md): a one-sided form of that inequality for nonnegative functions.

## Background

- [Kantorovich duality](../../kantorovich-duality/README.md): the general duality the formula specialises.
- [Wasserstein distance](../wasserstein-distance/README.md): the distance $W_1$.
