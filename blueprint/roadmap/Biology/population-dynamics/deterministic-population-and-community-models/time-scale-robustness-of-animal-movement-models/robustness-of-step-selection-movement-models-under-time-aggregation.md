# Robustness of step-selection movement models under time aggregation

**Model.** An animal's location $X_t \in \mathbb R$ is observed at times spaced by $\tau$. One step is a resource- or step-selection model: a Gaussian movement kernel $k_\sigma(x; y)$ (mean $y$, standard deviation $\sigma$) is reweighted by a positive habitat weighting function $w_\theta(x)$,

$$p_{t-\tau,t}(x \mid y, \sigma, \theta) = \frac{k_\sigma(x;y)\,w_\theta(x)}{\int_{\mathbb R} k_\sigma(z;y)\,w_\theta(z)\,dz}.$$

The $n$-step transition density $p_{t-n\tau,t}$ is the $n$-fold Chapman–Kolmogorov composition.

**Definition.** The model is *robust of degree $n$* if there is an injective parameter map $g_n$ with $p_{t-n\tau,t}(x\mid y, \boldsymbol\theta) = p_{t-\tau,t}(x\mid y, g_n(\boldsymbol\theta))$ for all $t, x, y$: the coarsened model is the same model with transformed parameters. It is *asymptotically robust* if equality holds up to a factor $v(x,y;\tau)$ with $v - 1 = O(\tau)$, and *approximately robust of magnitude $\delta$* if $1 - \delta \le v \le 1 + \delta$.

**Theorem.**
1. *Linear weighting.* If $w(x) = ax + b$, restricted to the interval where $w > 0$, the model is robust of every degree $n$, with $g_n(\sigma, a, b) = (\sqrt n\,\sigma, a, b)$.
2. *Exponential weighting.* If $w(x) = Ce^{ax+b}$, the model is robust of every degree $n$, with $g_n(\sigma, C, a, b) = (\sqrt n\,\sigma, C, a, b)$.
3. *General weighting.* If $w_\theta$ is continuous, bounded away from zero and twice differentiable with bounded second derivative, the model is asymptotically robust of degree $2$ with $g_2(\sigma,\theta) = (\sqrt2\,\sigma, \theta)$.

So only the diffusive scale changes (as $\sqrt{n}$, like Brownian motion), while habitat-preference parameters are invariant to the sampling interval for these weightings; for general habitat weights the invariance holds only approximately when steps are short.

## Proof sketch

For exponential weights, $k_\sigma(x;y)e^{ax}$ normalizes to a Gaussian with mean $y + a\sigma^2$ and variance $\sigma^2$; composing $n$ such steps gives mean $y + na\sigma^2$ and variance $n\sigma^2$, which is the one-step law with $\sigma$ replaced by $\sqrt n\sigma$. For linear weights the one-step density is $k_\sigma(x;y)(ax+b)/(ay+b)$, since the Gaussian mean of $ax+b$ is $ay+b$; in the composition the factors $(az+b)$ telescope, leaving $\frac{ax+b}{ay+b}(k_\sigma * k_\sigma)(x;y) = \frac{ax+b}{ay+b}k_{\sqrt2\sigma}(x;y)$, and induction gives degree $n$. For general $w$, a second-order Taylor expansion of $w$ over the step scale shows that the two-step and rescaled one-step densities differ by a factor $1 + O(\tau)$ when $\sigma^2 \propto \tau$.

## Sources

- Ulrike E. Schlägel and Mark A. Lewis, "Robustness of movement models: can models bridge the gap between temporal scales of data sets and behavioural processes?", *Journal of Mathematical Biology* 73 (2016), 1691–1726, <https://doi.org/10.1007/s00285-016-1005-5>. Preprint version: arXiv:1508.06523 (2015), robustness definitions and the theorems for linear, exponential and general weighting functions, <https://doi.org/10.48550/arXiv.1508.06523>.
