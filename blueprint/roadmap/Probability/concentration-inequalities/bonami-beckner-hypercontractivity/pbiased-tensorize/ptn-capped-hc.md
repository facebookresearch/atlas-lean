# Capped per-coordinate estimate under the $p$-biased measure

Let $\iota$ be a nonempty finite set, let $0 < p < 1$, $0 \le \rho \le 1$ and $1 \le q \le 2$ with
$\rho^2 = 4p(1-p)(q-1)$, and let $f = \mathbf{1}_A$ be the indicator of a set
$A \subseteq \{0, 1\}^\iota$. With the [$p$-biased Fourier coefficients](ptn-coeff.md) $\hat f(S)$,
the influences $\mathrm{Inf}_e(f) = \mathbb{E}_p|f(\omega^{e \to 1}) - f(\omega^{e \to 0})|$ and
$\delta = \max_e \mathrm{Inf}_e(f)$,

$$\frac{1}{p(1-p)} \sum_{\emptyset \ne S \subseteq \iota} |S|\, \rho^{2(|S|-1)}\, \hat f(S)^2 \le \delta^{2/q - 1} \sum_{e \in \iota} \mathrm{Inf}_e(f) .$$
