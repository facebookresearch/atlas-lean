# Gaussian Test

Let $D, \sigma^2 \ge 0$. For $v \ge 0$ let $\varphi_v(x) = (2\pi v)^{-1/2} \exp\left(-x^2/(2v)\right)$: for $v > 0$ this is the centered Gaussian density with variance $v$, and at $v = 0$ the convention $0^{-1} = 0$ extends it by the zero function, which is not a density of $\mathcal{N}(0, 0) = \delta_0$. The Gaussian test function on a source–reproduction pair $(x, y) \in \mathbb{R}^2$ is

$$t_{D, \sigma^2}(x, y) = \ln \varphi_D(x - y) - \ln \varphi_{\sigma^2}(x),$$

with $\ln 0 = 0$. It has the density-ratio interpretation only when $D > 0$ and $\sigma^2 > 0$.
