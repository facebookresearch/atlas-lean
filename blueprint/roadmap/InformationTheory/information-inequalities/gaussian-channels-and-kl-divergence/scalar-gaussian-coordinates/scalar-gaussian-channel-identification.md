# Scalar Gaussian channel as a one-dimensional vector channel

Let $\iota : \mathbb{R} \to \mathbb{R}^1$, $x \mapsto (x)$, be the coordinate isometry onto one-dimensional Euclidean space. Let $\mu$ be a probability measure on $\Omega$, let $X, Z : \Omega \to \mathbb{R}$ be measurable and independent, let $N > 0$ with $Z \sim \mathcal{N}(0, N)$, and let $P \in \mathbb{R}$. Write $\mathcal{N}(0, [N])$ for the Gaussian on $\mathbb{R}^1$ with mean $0$ and covariance matrix $[N]$, and $\kappa$ for the noise kernel $\kappa(y) = (w \mapsto [1]\,y + w)_*\,\mathcal{N}(0, [N])$. Then:

1. $\iota_*\mathcal{N}(0, N) = \mathcal{N}(0, [N])$;
2. the conditional distribution of $\iota(X + Z)$ given $\iota(X)$ equals $\kappa$ almost everywhere with respect to the law of $\iota(X)$;
3. the joint law of $(\iota(X), \iota(X + Z))$ is (law of $\iota(X)$) $\otimes \kappa$;
4. $0 \le P$ and $\int^{-} \|\iota(X)\|^2\,d\mu \le P$ hold if and only if $0 \le P$ and $\int^{-} X^2\,d\mu \le P$, where $\int^{-}$ is the lower Lebesgue integral in $[0, \infty]$.

The budget $P$ plays no role in clauses 1–3.
