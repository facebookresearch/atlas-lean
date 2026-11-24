# McDiarmid's inequality, lower tail

Let $\mu_0, \dots, \mu_{n-1}$ be probability
measures on measurable spaces $\Omega_0, \dots, \Omega_{n-1}$ and $\mu$ their product measure on
$\prod_{i\lt n} \Omega_i$, let $c_0, \dots, c_{n-1} \ge 0$, and let
$f : \prod_{i\lt n} \Omega_i \to \mathbb{R}$ be measurable with $|f(x') - f(x)| \le c_i$ whenever
$x'$ is obtained from $x$ by changing its $i$-th coordinate only. Then for every
$\varepsilon \ge 0$,

$$
\mu\big(\{x : \mathbb{E}_\mu[f] - f(x) \ge \varepsilon\}\big) \le
  \exp\Big(-\frac{2 \varepsilon^2}{\sum_{i\lt n} c_i^2}\Big),
$$

where the right-hand side is read as $1$ when every $c_i$ is $0$.
