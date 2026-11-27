# Continual evolution of a multi-valued trait under fast and slow feedbacks

**Setting.** A population carries a trait with finitely many values $i \in \{0, 1/n, 2/n, \dots, 1\}$, ordered by how strongly phenotype $i$ interacts with a negative-feedback variable $\varphi \in [0,1]$. With $u_i \ge 0$ the density of phenotype $i$, the mean trait is

$$
M(u) = \frac{\sum_i i\, u_i}{\sum_i u_i}.
$$

The dynamics are

$$
\frac{du_i}{dt} = u_i\left(\mu_i\left(1 - \frac{\sum_j u_j}{k}\right) - d\right) + \epsilon_m\, g_i(u), \qquad \frac{d\varphi}{dt} = \epsilon_e\, h(u,\varphi),
$$

where the growth rates $\mu_i > 0$ depend continuously on $(u,\varphi)$ and, for fixed $(u,\varphi)$, are either constant in $i$ or strictly monotone in $i$; $k, d > 0$; each mutation term $g_i$ is nonnegative at $u_i = 0$, decreasing in $u_i$ and strictly increasing in every $u_j$, $j \ne i$ (any phenotype can mutate into any other). Assume

- **(NF1)** $h < 0$ when $\varphi > M(u)$ and $h > 0$ when $\varphi < M(u)$ (the feedback tracks the mean trait, e.g. $h = M - \varphi$);
- **(NF2)** there are $0 < \varphi_- < \varphi_+ < 1$ such that for every nonzero $u$, $\mu$ is decreasing in $i$ when $\varphi > \varphi_+$ and increasing in $i$ when $\varphi < \varphi_-$;
- **(PF, positive feedback)** for each $\varphi$ there is a unique $M_\varphi$, non-decreasing in $\varphi$, such that $\mu$ is strictly increasing in $i$ when $M(u) > M_\varphi$ and strictly decreasing when $M(u) < M_\varphi$.

**Lemma (sign of the mean-trait drift).** Without mutation, let $u$ have at least two positive components and $\sum_j u_j < k$. If $\mu$ is strictly increasing (resp. decreasing) in $i$ then $dM/dt > 0$ (resp. $< 0$); if $\mu$ is constant, $dM/dt = 0$. For $\sum_j u_j > k$ the signs are reversed, and $dM/dt = 0$ when $\sum_j u_j = k$ or $u$ has a single positive component. (The source's SI Lemma 6 omits the two conditions.)

**Theorem.** For $\epsilon_e$ and $\epsilon_m$ sufficiently small there exist orbits $(u(t),\varphi(t))$ along which $M(t)$ fluctuates arbitrarily close to $0$ and arbitrarily close to $1$, indefinitely.

## Expansion

The lemma follows because the density-dependent factor and the death rate $d$ are common to all phenotypes, so $dM/dt = \big(1 - \sum_j u_j/k\big)\sum_i (i - M)\mu_i u_i / \sum_i u_i$. The sum $\sum_i (i - M)\mu_i u_i$ is a covariance of $i$ and $\mu_i$ under the weights $u_i$: positive when $\mu$ increases strictly in $i$ and at least two phenotypes are present, zero when only one is. The factor $1 - \sum_j u_j/k$ then fixes the sign.

For the theorem, start with $M$ near $1$, $\varphi < \varphi_+$ and $\mu$ increasing. By (NF1) $\varphi$ creeps upward while $M$ stays near $1$. Once $M$ meets $M_\varphi$, (PF) flips $\mu$ to decreasing and $M$ starts to fall. Mutation keeps every $u_i$ at least of order $\epsilon_m$, so the phenotype $i = 0$ is present and, now having the largest growth rate, grows exponentially faster than the others; $M$ collapses toward $0$ in a time independent of $\epsilon_m,\epsilon_e$, during which $\varphi$ barely changes. The resulting state mirrors the starting one, and the cycle repeats. The positive feedback is what makes the switch abrupt relative to the slow feedback; if evolution is too slow relative to $\varphi$, the feedback catches up with $M$ near equilibrium and the oscillation is lost.

## Depends on

- [Red Queen cycles from a fast positive and a slow negative feedback](red-queen-cycles-from-fast-positive-and-slow-negative-feedback.md)

## Sources

- Meike T. Wortel, Han Peters, Juan A. Bonachela, Nils Chr. Stenseth, "Continual evolution through coupled fast and slow feedbacks", Proceedings of the National Academy of Sciences 117 (2020), 4234–4242, <https://doi.org/10.1073/pnas.1916345117>. Published version of arXiv:1901.01885, cited next; locators there refer to the arXiv version.
- Meike T. Wortel, Han Peters, Nils Chr. Stenseth, "Coupled fast and slow feedbacks lead to continual evolution: A general modeling approach," arXiv 2019. Supplementary information, Section "One species with a trait with multiple phenotypes": Lemma 6, Lemma 7, Theorem 8. <https://doi.org/10.48550/arXiv.1901.01885>
