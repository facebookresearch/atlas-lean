# Itô-approximable process

Let $P$ be a measure, $F$ a filtration and $t \ge 0$. A real process $H$ is Itô-approximable on $[0, t]$ if

1. its [restriction to $(0, t]$](restrict-ioc.md) is jointly measurable in $(u, \omega)$, and
2. there are [elementary integrands](elementary-integrand.md) $H^{(n)}$ with $d_t(H^{(n)}, H) \to 0$, where
   $d_t$ is the [squared $L^2(P \otimes du)$ distance](integrand-dist.md) on $(0, t] \times \Omega$.

Neither condition involves the values of $H$ at time $0$ or after $t$.
