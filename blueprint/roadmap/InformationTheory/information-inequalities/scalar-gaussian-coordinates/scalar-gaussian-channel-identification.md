# Scalar Gaussian channel identification

Let $(\Omega, \mu)$ be a probability space and $X, Z : \Omega \to \mathbb{R}$ measurable and independent, with $Z \sim \mathcal{N}(0, N)$ for some $N > 0$. Let $P \in \mathbb{R}$, let $e(x) = (x) \in \mathbb{R}^1$, and let $N_1$ be the additive-noise kernel at gain $[1]$ and noise covariance $[N]$, which sends $y \in \mathbb{R}^1$ to the law of $y + W$ with $W \sim \mathcal{N}(0, [N])$. Then all of the following hold:

- $e_\ast\,\mathcal{N}(0, N) = \mathcal{N}(0, [N])$;
- the conditional distribution of $e(X + Z)$ given $e(X)$ equals $N_1$ almost everywhere with respect to the law of $e(X)$;
- $\big(e(X), e(X + Z)\big)_\ast\,\mu = e(X)_\ast\mu \otimes N_1$;
- $e \circ X$ satisfies the vector power constraint with budget $P$ if and only if $X$ satisfies the scalar power bound with budget $P$.
