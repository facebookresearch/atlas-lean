# McDiarmid's inequality, sub-Gaussian form

Let $\mu_0, \dots, \mu_{n-1}$ be probability
measures on measurable spaces $\Omega_0, \dots, \Omega_{n-1}$ and $\mu$ their product measure on
$\prod_{i\lt n} \Omega_i$, let $c_0, \dots, c_{n-1} \ge 0$, and let
$f : \prod_{i\lt n} \Omega_i \to \mathbb{R}$ be measurable with $|f(x') - f(x)| \le c_i$ whenever
$x'$ is obtained from $x$ by changing its $i$-th coordinate only. Then $f - \mathbb{E}_\mu[f]$ is
sub-Gaussian with parameter $\frac14 \sum_{i\lt n} c_i^2$: for every real $t$,
$e^{t (f - \mathbb{E}_\mu[f])}$ is $\mu$-integrable and

$$
\mathbb{E}_\mu\big[e^{t (f - \mathbb{E}_\mu[f])}\big] \le
  \exp\Big(\frac{t^2}{8} \sum_{i\lt n} c_i^2\Big).
$$
