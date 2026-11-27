# Stability and replacement of clonal dominance under branching with immigration

Founder B cells join a germinal centre at the jump times $T_1 < T_2 < \cdots$ of a Poisson process $\Pi(t)$ with intensity $r(t)$ and cumulative intensity $R(t) = \int_0^t r$. Founder $k$ starts clone $k$. Each cell of clone $k$ lives for a time with c.d.f. $G_k$ (density $g_k$) and then divides into two with probability $p_{2k}$ or dies. Clones evolve independently. Conditional on $(p_{2k}, G_k)$, the **Malthusian parameter** $\alpha_k$ solves

$$2p_{2k}\int_0^\infty e^{-\alpha_k x}\,dG_k(x) = 1,$$

so $\alpha_k = (2p_{2k} - 1)\lambda$ for exponential lifespans with rate $\lambda$, and the clone's extinction probability is $\min\{1, (1-p_{2k})/p_{2k}\}$. Assume (A4): for supercritical clones $e^{-\alpha_k t} Z^{(k)}(t) \to c_k W_k$ a.s., with $W_k = 0$ exactly on extinction. Let $Y(t)$ be the total number of B cells and $F_k(t) = Z^{(k)}(t - T_k)/Y(t)$ the fraction belonging to clone $k$.

**Proposition 3 (no differential fitness).** Suppose all clones have the same offspring and lifespan laws with common $\alpha > 0$, and $R(t - f(t))/R(t) \to 1$ for some increasing $f(t) = o(t)$. Then a.s. as $t \to \infty$

$$F_k(t) \to \frac{W_k e^{-\alpha T_k}}{\sum_{k'\ge 1} W_{k'} e^{-\alpha T_{k'}}}, \qquad \sum_k F_k(t)^2 \to \frac{\sum_k W_k^2 e^{-2\alpha T_k}}{\bigl(\sum_{k'} W_{k'} e^{-\alpha T_{k'}}\bigr)^2} \in (0,1),$$

the Bray–Curtis index between times $t$ and $t + \delta$ tends to $(1 - e^{-\alpha\delta})/(1 + e^{-\alpha\delta})$, and the Bhattacharyya coefficient and proportion of similarity tend to $1$. Clonal composition freezes, and early arrivals are the most likely to dominate.

**Proposition 4 (differential fitness).** Suppose the $\alpha_k$ are i.i.d. and non-degenerate with $P(\alpha_1 > 0) > 0$, the law of $\alpha_1$ given $\alpha_1 > 0$ is absolutely continuous, $R(t) \to \infty$, and $\int_0^\infty g_k(x)^\delta\,dx < \infty$ for some $\delta > 1$. Then a.s. for every clone $k$: (i) $F_k(t) \to 0$, and (ii) there is a later clone $k' > k$ with $F_k(t)/F_{k'}(t) \to 0$. Every dominant clone is eventually outcompeted.

## Expansion

With a common $\alpha$, clone $k$ alive at time $t$ has size about $c W_k e^{\alpha(t - T_k)}$, so its share converges to the stated ratio. A later clone can overtake only if $W_k e^{-\alpha T_k}$ breaks a record, which becomes increasingly unlikely because $T_k \to \infty$, so dominance is stable. With random $\alpha_k$ the relevant record process is the running maximum of the Malthusian parameters. Since immigration never stops and the law of $\alpha_1$ given $\alpha_1 > 0$ is continuous, some later surviving clone eventually has a strictly larger growth rate, and its exponentially faster growth outweighs any head start. Under the same model, richness grows like $(1 - Q)R(t)$, where $Q$ is the extinction probability of a clone. Inverse-Simpson and Hill-number diversities converge when fitness is homogeneous. With fitness differences the repertoire keeps turning over, consistent with the replacement of dominant clones observed in germinal centres.

## Sources

- O. Hyrien, N. M. Yanev, "A branching stochastic evolutionary model of the B-cell repertoire", Journal of Mathematical Biology (2024), Sections 3 and 5, Eqs. (19)–(21), Assumptions (A1)–(A5), Definition 2 and Propositions 3–4, <https://doi.org/10.1007/s00285-024-02102-y>, PMCID PMC11161549.
