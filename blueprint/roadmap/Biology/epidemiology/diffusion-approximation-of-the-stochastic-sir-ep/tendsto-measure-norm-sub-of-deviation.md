# The ℓ¹ law of large numbers gives the sup-norm one

Let $\mu$ be a measure on $\Omega$, let $S_N, I_N, R_N : \Omega \to (\mathbb{R} \to \mathbb{N})$ be
count paths and $s, i, r : \mathbb{R} \to \mathbb{R}$, and let $T$ be real. Assume that for every
$\varepsilon > 0$, as $N \to \infty$,

$$
\mu\Bigl\{\omega : \exists\, t \in [0, T],\ \Bigl|\frac{S_N(t)}{N} - s(t)\Bigr| +
\Bigl|\frac{I_N(t)}{N} - i(t)\Bigr| +
\Bigl|\frac{R_N(t)}{N} - r(t)\Bigr| \ge \varepsilon\Bigr\} \to 0,
$$

the form of the
[law of large numbers](../stochastic-sir-epidemic-and-its-law-of-large-num/tendsto-measure-deviation.md)
for the SIR chain, with the convention $x / 0 = 0$ at $N = 0$. Then for every $\delta > 0$, with the
sup norm $\|h\| = \max(|h_1|, |h_2|)$ on $\mathbb{R}^2$,

$$
\mu\Bigl\{\omega : \exists\, t \in [0, T],\
\Bigl\|\Bigl(\frac{S_N(t)}{N}, \frac{I_N(t)}{N}\Bigr) - (s(t), i(t))\Bigr\| \ge \delta\Bigr\} \to 0:
$$

the law-of-large-numbers hypothesis of the
[diffusion approximation](tendsto-measure-fluctuation-sub.md) for the density paths
$X_N = (S_N / N, I_N / N)$. The events are not assumed measurable, and $\mu$ is applied to them as
an outer measure.
