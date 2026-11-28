# Private stochastic convex optimization has the non-private rate in the common regime

Let $\mathcal{W} \subseteq \mathbb{R}^d$ be a nonempty, closed, convex set of finite diameter $D$, let $\ell(w, z)$ be convex and $L$-Lipschitz in $w$ for every data point $z$, let $\hat F_S(w) = \frac1n\sum_i \ell(w, z_i)$ be the empirical risk of a dataset $S$ and $F(w) = \mathbb{E}_{z \sim \mathcal{D}}[\ell(w,z)]$ the population risk, assumed finite (finiteness at one point implies it everywhere, by Lipschitzness). Since $\mathcal{W}$ is compact and both risks are continuous, their minima over $\mathcal{W}$ exist, and the Euclidean projection $\Pi_{\mathcal{W}}$ onto $\mathcal{W}$ is well defined. Consider $(\varepsilon,\delta)$-differential privacy with $0 < \varepsilon \le 1$ and $0 < \delta \le 1/n^2$, so that $1/\varepsilon$ and $\log(1/\delta)$ in the bounds below are finite; the endpoints $\varepsilon = 0$ or $\delta = 0$ are outside this statement. The optimal excess population risk is a worst case over the convex $L$-Lipschitz loss families on $\mathcal{W}$ as well as over distributions: for a single loss family it can be much smaller, and for a common linear loss $\ell(w, z) = \langle g, w\rangle$, independent of $z$, a fixed minimizer of $\langle g, \cdot\rangle$ over $\mathcal{W}$ is private and has zero excess risk. In this worst-case sense, there is an $(\varepsilon,\delta)$-differentially private algorithm whose expected excess population risk is

$$
O\!\left(LD\,\min\Big\{1,\ \frac{1}{\sqrt{n}} + \frac{\sqrt{d\log(1/\delta)}}{\varepsilon n}\Big\}\right)
$$

for every such loss family and distribution, the larger of the optimal non-private excess population risk and the optimal private excess empirical risk, capped by $LD$. Conversely, for every $(\varepsilon,\delta)$-differentially private algorithm there are a family of linear losses on a Euclidean ball $\mathcal{W}$ of diameter $D$ and a distribution on which its expected excess population risk is

$$
\Omega\!\left(LD\,\min\Big\{1,\ \frac{1}{\sqrt{n}} + \frac{\sqrt{d}}{\varepsilon n}\Big\}\right)
$$

up to a factor logarithmic in $1/\delta$ in the second term, which is lost when the private empirical risk lower bound is transferred to population risk. The lower bound carries no $\sqrt{\log(1/\delta)}$ factor, so the two bounds match only up to factors logarithmic in $1/\delta$. The cap is necessary: any fixed, data-independent point of $\mathcal{W}$ is private and has excess risk at most $LD$ by Lipschitzness and the diameter, so without the cap the formula would exceed the trivial bound by an unbounded factor for fixed $\varepsilon$ and growing $d$. In particular, when $d \lesssim n\varepsilon^2/\log(1/\delta)$, private SCO achieves the non-private $1/\sqrt{n}$ rate, improving the previous $n^{-1/4}$ rate obtained through private ERM.

## Proof sketch

For smooth losses, noisy SGD (one or a few passes) is uniformly stable with parameter $O(L^2\eta T/n)$, so its population risk exceeds its empirical risk by at most this amount, and balancing stability against the optimization and noise error gives the rate. Non-smooth losses are handled by Moreau-envelope smoothing or by regularized ERM with privacy noise, whose stability is controlled by the strong convexity of the regularizer. The lower bound is the maximum of the non-private SCO lower bound and the private ERM lower bound $\Omega(LD\min\{1, \sqrt d/(\varepsilon n)\})$ (for $\delta = o(1/n)$), the latter transferred to SCO by running a population-risk algorithm on samples drawn from the empirical distribution of a dataset, with privacy parameters adjusted by a logarithmic factor for repeated samples; both are capped at $LD$.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Proof depends on

- [Optimal excess empirical risk for private convex empirical risk minimization](private-erm-optimal-rates.md)
- [SGM is uniformly stable](../../../machine-learning/generalization-bounds-and-concentration/algorithmic-stability/is-uniformly-stable-sgm.md)
- [Uniform stability](../../../machine-learning/generalization-bounds-and-concentration/algorithmic-stability/is-uniformly-stable.md)

## Sources

- R. Bassily, V. Feldman, K. Talwar, A. Thakurta, "Private Stochastic Convex Optimization with Optimal Rates", NeurIPS (2019), arXiv:1908.09970, Section 1.1, Algorithm 1 and Appendix C.
