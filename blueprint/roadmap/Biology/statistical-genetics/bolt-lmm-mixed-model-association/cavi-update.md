# Coordinate-ascent update of one variational factor

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $\sigma_e^2$ be real, let $\pi$ be a measure on $\mathbb{R}$, let $q_1, \dots, q_m$ be measures on $\mathbb{R}$, and let $j \in \{1, \dots, m\}$. The coordinate-ascent update of factor $j$ is the prior tilted by the [potential](potential.md) $f_j$: the measure $q_j^\ast$ with density

$$\frac{dq_j^\ast}{d\pi}(b) = \frac{e^{f_j(b)}}{\int e^{f_j}\, d\pi}$$

with respect to $\pi$, with the conventions $x/0 = 0$ and that the integral is $0$ when $e^{f_j}$ is not $\pi$-integrable (in both cases $q_j^\ast = 0$). When $\sigma_e^2 > 0$, $\pi$ is a probability measure and the other factors are probability measures with finite second moments, it is the mean-field coordinate-ascent update: $q_j^\ast \propto \pi\, e^{f_j}$, the exponential of the expected log joint density under the other factors.
