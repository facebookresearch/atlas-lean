# Large-sample limit of critical branching sample genealogies

Use the [coalescent point process](coalescent-point-process-of-a-sample-from-a-critical-birth-death-tree.md) $\pi_n = \sum_{k=1}^{n-1}\delta_{(k/n, H_k)}$ of a sample of size $n$ from a critical birth–death tree, with sampling parameter tied to the sample size by $p = n/\alpha$ for a fixed $\alpha > 0$, so that the expected number of sampled individuals is of order $n$. Let $\pi$ be the Poisson point measure on $(0,1)\times(0,\infty)$ with intensity $\alpha\, dl\, x^{-2}\, dx$, and for $i \ge 0$ let $e_i$ have the inverse-gamma law with parameters $(i+1,\alpha)$, with density

$$t \mapsto \frac{\alpha^{i+1} e^{-\alpha/t}}{i!\, t^{i+2}}\, \mathbf 1_{t>0}.$$

**Theorem (Achaz–Delaporte–Lambert, Theorem 4.1).** As $n \to \infty$:

1. under $P^{(\infty)}_n$, $\pi_n$ converges in law to $\pi$;
2. for every $i \ge 0$, under $P^{(i)}_n$ the pair $(\pi_n, T_{\mathrm{or}})$ converges in law to a pair $(\pi^{(i)}, T^{(i)}_{\mathrm{or}})$, where $T^{(i)}_{\mathrm{or}}$ has the law of $e_i$ and, given the origin time, $\pi^{(i)}$ is a Poisson point measure with the intensity of $\pi$ truncated to depths below the origin.

**Theorem (Achaz–Delaporte–Lambert, Theorem 4.4).** For every $i \ge 0$, $\pi^{(i)}$ has the law of $\pi$ with its $i+1$ largest atoms removed.

**Proposition (Proposition 4.3).** The depths $T_1 > T_2 > \dots$ of the largest atoms of $\pi$ satisfy $(T_1,\dots,T_k) \overset{d}{=} (e_0,\dots,e_{k-1})$, where $e_j = 1/(\rho_0+\dots+\rho_j)$ for i.i.d. exponential $\rho_j$ with rate $\alpha$; under $P^{(i)}_n$ the origin time and the $k$ oldest coalescence times converge jointly to $(e_i, e_{i+1},\dots,e_{i+k})$.

**Proposition (Proposition 4.5).** For fixed $t > 0$, $i \in \{0,1\}$ and $k \ge 1$,

$$\lim_{n\to\infty} E^t_n(\xi_k) = \frac{\alpha\theta}{k}, \qquad \lim_{n\to\infty} E^{(i)}_n(\xi_k) = \frac{\alpha\theta}{k},$$

where $\xi_k$ is the number of mutations (rate $\theta$) carried by $k$ sampled individuals.

So in the large-sample limit, the genealogy with prior $x^{-i}$ on the origin is the scale-invariant Poisson genealogy with the $i+1$ oldest splits removed, and the origin time is the depth of the last removed split.

## Depends on

- [Coalescent point process of a sample from a critical birth–death tree](coalescent-point-process-of-a-sample-from-a-critical-birth-death-tree.md)
- [Expected site frequency spectrum of a critical branching sample](expected-site-frequency-spectrum-of-a-critical-branching-sample.md)

## Expansion

With $p = n/\alpha$, each $H_k$ satisfies $P(H_k > x) = 1/(1+nx/\alpha) \approx \alpha/(nx)$, so among the $n-1$ i.i.d. depths placed at spacing $1/n$ the number exceeding $x$ in a horizontal window of length $l$ is approximately Poisson with mean $l\alpha/x$, which is the intensity $\alpha\, dl\, x^{-2} dx$. The map $x \mapsto 1/x$ sends the depths of $\pi$ to a homogeneous Poisson process of rate $\alpha$ on $(0,\infty)$, so the ordered largest depths are reciprocals of partial sums of exponentials, the inverse-gamma laws $e_j$. Conditioning a critical tree on its origin with prior $x^{-i}$ is, in the limit, the same as declaring the $(i+1)$-th oldest split to be the origin, which explains Theorem 4.4.

## Sources

- G. Achaz, C. Delaporte and A. Lambert, *Sample genealogy and mutational patterns for critical branching populations*, published as "Mutational pattern of a sample from a critical branching population", *Journal of Mathematical Biology* 73 (2016), 627–664, <https://doi.org/10.1007/s00285-015-0964-2>; preprint arXiv:1407.7720, <https://doi.org/10.48550/arXiv.1407.7720>.
