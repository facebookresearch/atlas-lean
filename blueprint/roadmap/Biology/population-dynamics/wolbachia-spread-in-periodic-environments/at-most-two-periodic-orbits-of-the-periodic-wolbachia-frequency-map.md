# At most two periodic orbits of the periodically forced Wolbachia infection-frequency map

**Model.** Let $x_n \in [0,1]$ be the frequency of Wolbachia-infected mosquitoes in generation $n$. With maternal transmission failure rate $\mu_n$, fecundity cost $s_{f_n}$ of infection and cytoplasmic-incompatibility strength $s_{h_n}$,

$$x_{n+1} = f_n(x_n) = \frac{(1-\mu_n)(1-s_{f_n})\,x_n}{s_{h_n}x_n^2 - (s_{h_n}+s_{f_n})x_n + 1}.$$

For constant parameters with $0 \le s_f < s_h \le 1$ and $\mu < \mu^* = \frac{(s_h - s_f)^2}{4s_h(1-s_f)}$, the map has the attracting fixed point $0$ and two further fixed points in $(0,1]$; for $\mu = 0$ they are $s_f/s_h$ (unstable threshold) and $1$. Now let $(\mu_n, s_{f_n}, s_{h_n})$ be $T$-periodic, so the dynamics is driven by the periodic sequence of maps $[f_1,\ldots,f_T]$, and $T$-periodic solutions correspond to fixed points of $F = f_T\circ\cdots\circ f_1$.

**Conjecture (Zheng et al.).** If $0 \le s_{f_n} < s_{h_n} \le 1$ and $\mu_n \le \mu^*_n$ for all $n$, the model has at most two $T$-periodic solutions: exactly two (one stable, one unstable) if $\mu_n \ne 0$, and a unique unstable one if $\mu_n = 0$.

**Theorems.** Under the hypotheses of the conjecture:
1. if $T = 2$ and $\mu_1 = \mu_2 = 0$, then $f_2\circ f_1$ has exactly one fixed point in $(0,1)$;
2. if $T = 2$ and $\mu_1, \mu_2 \ne 0$, then $f_2\circ f_1$ has at most two nonzero fixed points;
3. for every $T \ge 3$, $f_T\circ\cdots\circ f_1$ has at most two nonzero fixed points in $(0,1]$.
Hence the "at most two periodic solutions" part of the conjecture holds for every period $T$.

## Expansion

Each $f_n$ is increasing on $[0,1]$ with $f_n(0)=0$, and the key observation is that the maps have negative Schwarzian derivative $\mathcal{S}(f) = f'''/f' - \frac32(f''/f')^2 < 0$, a property preserved under composition. For an increasing map with negative Schwarzian derivative, $F'$ cannot have an interior local minimum, so $F(x) - x$ has at most three zeros counting $0$ (otherwise Rolle's theorem would produce a forbidden configuration of critical points of $F'$). Since $0$ is always a fixed point, at most two nonzero fixed points remain; when $\mu_n = 0$, $1$ is a common fixed point and the count reduces to a single interior one.

## Sources

- J. S. Canovas, "A note on the periodic orbits of Wolbachia spread dynamics in mosquito populations in periodic environments", arXiv:2411.05439 (2024), Conjecture 1, Definition 2, and Theorems 7, 10 and 12, <https://doi.org/10.48550/arXiv.2411.05439>.
