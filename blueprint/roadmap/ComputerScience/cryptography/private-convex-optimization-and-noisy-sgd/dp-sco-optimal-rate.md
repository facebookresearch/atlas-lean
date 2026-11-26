# Private stochastic convex optimization has the non-private rate in the common regime

Let $\mathcal{W} \subseteq \mathbb{R}^d$ be convex with diameter $D$, let $\ell(w, z)$ be convex and $L$-Lipschitz in $w$ for every data point $z$, let $\hat F_S(w) = \frac1n\sum_i \ell(w, z_i)$ be the empirical risk of a dataset $S$ and $F(w) = \mathbb{E}_{z \sim \mathcal{D}}[\ell(w,z)]$ the population risk. The optimal excess population risk of $(\varepsilon,\delta)$-differentially private stochastic convex optimization is, up to logarithmic factors,

$$
\Theta\!\left(LD\left(\frac{1}{\sqrt{n}} + \frac{\sqrt{d\log(1/\delta)}}{\varepsilon n}\right)\right),
$$

the larger of the optimal non-private excess population risk and the optimal private excess empirical risk. In particular, when $d \lesssim n\varepsilon^2/\log(1/\delta)$, private SCO achieves the non-private $1/\sqrt{n}$ rate, improving the previous $n^{-1/4}$ rate obtained through private ERM.

## Proof sketch

For smooth losses, noisy SGD (one or a few passes) is uniformly stable with parameter $O(L^2\eta T/n)$, so its population risk exceeds its empirical risk by at most this amount, and balancing stability against the optimization and noise error gives the rate. Non-smooth losses are handled by Moreau-envelope smoothing or by regularized ERM with privacy noise, whose stability is controlled by the strong convexity of the regularizer. The lower bound is the maximum of the non-private SCO lower bound and the private ERM lower bound.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Proof depends on

- [Optimal excess empirical risk for private convex empirical risk minimization](private-erm-optimal-rates.md)
- [SGM is uniformly stable](../../machine-learning/generalization-bounds-and-concentration/algorithmic-stability/is-uniformly-stable-sgm.md)
- [Uniform stability](../../machine-learning/generalization-bounds-and-concentration/algorithmic-stability/is-uniformly-stable.md)

## Sources

- R. Bassily, V. Feldman, K. Talwar, A. Thakurta, "Private Stochastic Convex Optimization with Optimal Rates", NeurIPS (2019), arXiv:1908.09970.
