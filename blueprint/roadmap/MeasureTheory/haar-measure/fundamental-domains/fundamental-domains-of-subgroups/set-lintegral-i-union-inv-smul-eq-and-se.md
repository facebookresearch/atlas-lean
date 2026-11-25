# Integrals over a subgroup fundamental domain as sums over cosets

In the setting of the [fundamental domain for a subgroup of countable
index](i-union-inv-smul-of-left-coset-represent.md) — $G$ acting measurably on $X$ preserving
$\mu$, $\Gamma_2 \le \Gamma_1$ with $\Gamma_1$ countable, $\mathcal F$ a fundamental domain for
$\Gamma_1$, and $(R_i)_{i \in I}$ ($I$ countable) representatives of the left cosets of $\Gamma_2$ in
$\Gamma_1$ — write $\mathcal F_2 = \bigcup_i R_i^{-1} \mathcal F$. Then:

- for every measurable $f : X \to [0, \infty]$,
  $\int_{\mathcal F_2} f\, d\mu = \int_{\mathcal F} \sum_i f(R_i^{-1} x)\, d\mu(x)$;
- for every Banach space $E$ and $\mu$-a.e. strongly measurable $h : X \to E$ with
  $\int_{\mathcal F} \sum_i \|h(R_i^{-1} x)\|\, d\mu(x) < \infty$, $h$ is integrable on
  $\mathcal F_2$, the series $\sum_i \|h(R_i^{-1} x)\|$ converges for $\mu$-a.e. $x \in \mathcal F$,
  and $\int_{\mathcal F_2} h\, d\mu = \int_{\mathcal F} \sum_i h(R_i^{-1} x)\, d\mu(x)$.
