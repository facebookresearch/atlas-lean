# Fourier expansion of a power of the distance to the nearest integer

Let $k$ be a
positive integer, let $g(u) = |u - \operatorname{round}(u)|^k$ be the $k$-th power of the
distance from a real $u$ to the nearest integer, let $e(x) = e^{2\pi i x}$, and for every
integer $m$ let $c(m) = \int_0^1 g(u)\, e(-mu)\, du$. Then $c(0) = 1/(2^k (k + 1))$, the mean of
$g$ over a period; there is a real constant $C$ with $|c(m)| \le C / m^2$ for every integer
$m \ne 0$; the series $\sum_{m \in \mathbb{Z}} |c(m)|$ converges; the symmetric partial sums
$\sum_{|m| \le H} c(m)\, e(mu)$ converge to $g(u)$ uniformly in real $u$ as $H \to \infty$; and
there is a real constant $C'$ such that for every integer $H \ge 1$ and every real $u$,

$$\Bigl|g(u) - c(0) - \sum_{0 < |m| \le H} c(m)\, e(mu)\Bigr| \le \frac{C'}{H}.$$

## Sources

- Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.5.5, Lemma 10 (`jis-2026-26.5.5-lem-10`).
