# Optimal excess empirical risk for private convex empirical risk minimization

Let $\mathcal{W} \subseteq \mathbb{R}^d$ be convex with diameter $D$, let $\ell(w, z)$ be convex and $L$-Lipschitz in $w$ for every data point $z$, let $\hat F_S(w) = \frac1n\sum_i \ell(w, z_i)$ be the empirical risk of a dataset $S$ and $F(w) = \mathbb{E}_{z \sim \mathcal{D}}[\ell(w,z)]$ the population risk. The optimal excess empirical risk achievable by differentially private algorithms is, up to logarithmic factors:

- for $(\varepsilon,\delta)$-DP and convex losses: $\Theta\!\left(LD\,\min\Big\{1, \dfrac{\sqrt{d\log(1/\delta)}}{\varepsilon n}\Big\}\right)$;
- for $\varepsilon$-DP and convex losses: $\Theta\!\left(LD\,\min\Big\{1, \dfrac{d}{\varepsilon n}\Big\}\right)$;
- for $(\varepsilon,\delta)$-DP and $\lambda$-strongly convex losses: $\Theta\!\left(\min\Big\{LD, \dfrac{L^2 d\log(1/\delta)}{\lambda\varepsilon^2 n^2}\Big\}\right)$.

The upper bounds are achieved in polynomial time (noisy gradient descent or SGD for approximate privacy; the exponential mechanism over $\mathcal{W}$, sampled via log-concave sampling, for pure privacy), and the lower bounds hold even for linear and quadratic losses.

## Proof sketch

For $(\varepsilon,\delta)$-DP, noisy (stochastic) gradient descent with Gaussian noise of standard deviation $L\sqrt{T\log(1/\delta)}/(\varepsilon n)$ per step and $T \approx n^2$ steps balances optimization error $LD/\sqrt{T}$ against the noise contribution $LD\sqrt{d\log(1/\delta)}/(\varepsilon n)$. Lower bounds reduce from private estimation of one-way marginals: for linear losses $\ell(w, z) = -\langle w, z\rangle$ over the unit ball with $z \in \{\pm 1/\sqrt{d}\}^d$, minimizing empirical risk to small error recovers the signs of most marginals, which the fingerprinting lower bound forbids for $n \ll \sqrt{d}/\varepsilon$; the packing argument gives the pure-DP bound.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Proof depends on

- [Sample complexity of privately answering one-way marginals](../fingerprinting-lower-bounds-and-adaptive-data-analysis/private-one-way-marginals-lower-bound.md)
- [The exponential mechanism is differentially private](../laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)
- [Packing lower bound for pure differential privacy](../differential-privacy/packing-lower-bound-for-pure-differential.md)

## Sources

- R. Bassily, A. Smith, A. Thakurta, "Differentially Private Empirical Risk Minimization: Efficient Algorithms and Tight Error Bounds", FOCS (2014), arXiv:1405.7085.
