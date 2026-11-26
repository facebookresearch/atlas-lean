# Covariance of two strain channels under a probability mass function

Let $q$ be a probability mass function on a finite set $\Omega$ of scenarios, carrying a
$\sigma$-algebra in which every singleton is measurable, and let $\mu_q$ be the probability measure
of $q$. Let $V(\omega) \in \mathbb{R}^n$ be the voltage vector of $n$ gauges with nonzero gains
$g_1, \dots, g_n$ and offsets $b$, and let $\varepsilon_i = (V_i - b_i)/g_i$ be their
[strains](gauge-strain-vec.md). For all channels $i$ and $j$, the covariance of $\varepsilon_i$ and
$\varepsilon_j$ under $\mu_q$ is

$$
\int (\varepsilon_i - \mathbb{E}\,\varepsilon_i)(\varepsilon_j - \mathbb{E}\,\varepsilon_j)\,d\mu_q
= \frac{C_V(i, j)}{g_i\,g_j},
$$

where $\mathbb{E}$ is the expectation under $\mu_q$ and
$C_V(i, j) = \sum_{\omega} q(\omega)\,(V_i(\omega) - \bar V_i)(V_j(\omega) - \bar V_j)$, with
$\bar V_k = \sum_{\omega} q(\omega)\,V_k(\omega)$, is the weighted voltage covariance for the
[real masses](to-real-weights-is-distribution.md) $q(\omega)$, which are nonnegative and sum to one.
On a finite space whose singletons are measurable every function is integrable, so the left side is
the covariance of the random variables $\varepsilon_i$ and $\varepsilon_j$.
