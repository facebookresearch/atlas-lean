# Local asymptotic normality of the log-likelihood ratio

Let $\mathcal{X}$ be a set, $p : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$, $s_\theta(x) = \partial_\theta \log p_\theta(x)$ (here and below $\log y = \log|y|$ for $y \ne 0$ and $\log 0 = 0$, as for the [score](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/score.md); no positivity of $p$ is assumed), and let $\delta > 0$, $\theta_0, h, I, c \in \mathbb{R}$. Suppose that for every $x$ and every $\theta$ with $|\theta - \theta_0| < \delta$ the maps $t \mapsto \log p_t(x)$, $t \mapsto s_t(x)$ and $t \mapsto \partial_t s_t(x)$ are differentiable at $\theta$, and $|\partial_\theta^2 s_\theta(x)| \le M(x)$. Let $P$ be a measure on $\Omega$ and $Y_0, Y_1, \dots : \Omega \to \mathcal{X}$ functions such that, in $P$-measure,

$$-\frac{1}{n} \sum_{i<n} \partial_\theta s_{\theta_0}(Y_i) \to I, \qquad \frac{1}{n} \sum_{i<n} M(Y_i) \to c$$

(laws of large numbers). Then, for the local parameters $\theta_n = \theta_0 + h/\sqrt{n}$ (with $h/\sqrt{0}$ read as $0$),

$$\sum_{i<n} \big(\log p_{\theta_n}(Y_i) - \log p_{\theta_0}(Y_i)\big) - \frac{h}{\sqrt{n}} \sum_{i<n} s_{\theta_0}(Y_i) \to -\frac{h^2 I}{2}$$

in $P$-measure.

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Theorem 7.2 (local asymptotic normality); the statement above assumes Cramér's third-derivative envelope instead of differentiability in quadratic mean.
