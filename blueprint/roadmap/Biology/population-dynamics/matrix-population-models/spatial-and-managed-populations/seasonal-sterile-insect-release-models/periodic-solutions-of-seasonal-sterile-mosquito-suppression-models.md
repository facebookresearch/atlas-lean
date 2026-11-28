# Periodic solutions of seasonal sterile-mosquito suppression models

**Model.** The wild mosquito density $w(t) \ge 0$ satisfies

$$w' = w\Bigl(\frac{a(t)\, w}{w + g(t)} - \mu(t) - \xi(t)\bigl(w + g(t)\bigr)\Bigr),$$

where $a, \mu, \xi > 0$ are smooth and $T$-periodic (seasonal birth, death and density-dependent mortality), and the sterile population is released periodically: $g(t) = g_0$ on $[iT, iT + \bar T)$ and $g(t) = 0$ on $[iT + \bar T, (i+1)T)$. The factor $w/(w+g)$ is the probability that a wild female mates with a wild male. Let

$$I_1 = -\int_0^{\bar T} \xi(t) g_0\, dt - \int_0^T \mu(t)\, dt + \int_{\bar T}^T a(t)\, dt .$$

**Theorem.** Solutions exist globally, and $\limsup_t w(t) \le \max_t a(t)/\xi(t)$.
1. The equation has at most three $T$-periodic solutions (including $w \equiv 0$).
2. If $I_1 > 0$, the origin is unstable and a nontrivial $T$-periodic solution attracts every positive solution.
3. If $I_1 < 0$, the origin is asymptotically stable and exactly one of the following holds: (i) no nontrivial periodic solution exists and all solutions tend to $0$ (successful suppression); (ii) a unique nontrivial periodic solution $w^*$ exists, solutions starting below it go to $0$ and those above converge to it; (iii) exactly two nontrivial periodic solutions $w_1^* < w_2^*$ exist, with $(0, w_1^*)$ in the basin of $0$ and $(w_1^*, \infty)$ in the basin of $w_2^*$ (bistability). Case (iii) holds iff the Poincaré map $P$ satisfies $P(K) > K$ for some $K > 0$.
4. If $I_1 = 0$, a nontrivial attracting periodic solution exists when $P''(0) > 0$, and all solutions go extinct when $P''(0) \le 0$.

## Expansion

The Poincaré map satisfies $P'(0) = \exp\bigl(\int_0^T \partial_w F(t, 0)\, dt\bigr) = e^{I_1}$, which gives the stability of the origin. The bound on the number of periodic orbits comes from d-concavity of the nonlinearity in $w$ (for these population models tied to a positive third derivative on each phase where the right-hand side is smooth), which via the formulas for $P'$ and $P''$ in terms of $\partial_w F$ along solutions prevents $P(w) - w$ from having more than three zeros. Combined with $P(w) < w$ for large $w$, the ordering of fixed points yields the trichotomy. The same template covers several published sterile-insect models, giving explicit release thresholds.

## Sources

- R. Fernández-Martínez, A. Ruiz-Herrera, "Mosquito population suppression models with seasonality and d-concave equations", *Journal of Dynamics and Differential Equations* (2026), Propositions 2.1, 3.1 and 3.2, Theorems 2.1, 3.1 and 3.2, Corollary 3.1, <https://doi.org/10.1007/s10884-025-10481-z> (preprint arXiv:2509.05807).
