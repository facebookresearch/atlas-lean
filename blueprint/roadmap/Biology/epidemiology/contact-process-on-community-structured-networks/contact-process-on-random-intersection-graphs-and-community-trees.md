# Contact process on random intersection graphs and community trees

**Model.** *Random intersection graph.* There are $n$ individuals and $a_n \to \infty$ communities. Individual $x$ has membership degree $m_x$ and community $w$ has size degree $k_w$, with $\sum_x m_x = \sum_w k_w$. Pair membership half-edges with community half-edges uniformly at random (a bipartite configuration model) and join two individuals whenever they share a community; the resulting multigraph is $\mathrm{RIG}_n(\mathbf m, \mathbf k)$. Let $M_n$, $K_n$ be the empirical membership and community-size laws and assume $M_n \to M$, $K_n \to K$ in distribution with $\mathbb{E}[M_n^\eta] \to \mathbb{E}[M^\eta]$ and $\mathbb{E}[K_n^\eta] \to \mathbb{E}[K^\eta]$ for some $\eta > 1$. For $X$ with values in $\mathbb{N}_0$, $\widetilde X$ denotes the size-biased law shifted down by one: $\mathbb{P}(\widetilde X = k) = (k+1)\mathbb{P}(X = k+1)/\mathbb{E}X$.

*Contact process (SIS).* Infected vertices recover at rate $1$ and infect each neighbor at rate $\lambda$.

*Community tree.* The local weak limit of $\mathrm{RIG}_n$ seen from a uniform individual is the branching community tree $\mathrm{CT}(M, \widetilde M, \widetilde K)$: the root belongs to $M$ communities, every other individual to $\widetilde M$ further communities, and every community contains $\widetilde K$ further individuals, all independent, each community being a clique. On a community tree let $\lambda_1$ be the critical rate for global survival from an infected root and $\lambda_2 \ge \lambda_1$ the critical rate for local survival (the root reinfected infinitely often).

**Theorem.** Let $\mathrm{CT} = \mathrm{CT}(X, Y)$ have membership law $X$ and community law $Y$ with $\mathbb{E}X\, \mathbb{E}Y > 1$.
1. If $\mathbb{E}[e^{cX}] = \infty$ for all $c > 0$ or $\mathbb{E}[e^{cY\log Y}] = \infty$ for all $c > 0$, then $\lambda_1 = \lambda_2 = 0$.
2. If for some $c > 0$ both $\mathbb{E}[e^{cX}] < \infty$ and $\mathbb{E}[e^{Y \log(cY)}] < \infty$, then $\lambda_1 > 0$.

On the finite graphs $G_n = \mathrm{RIG}_n$ under the assumptions above, with extinction time $T_{\mathrm{ext}}$ started from all infected:

3. If $\mathbb{E}[\widetilde M]\,\mathbb{E}[\widetilde K] > 1$ and $\mathbb{E}[e^{c\widetilde M}] = \infty$ or $\mathbb{E}[e^{c\widetilde K \log \widetilde K}] = \infty$ for all $c > 0$, then for every $\lambda > 0$ there is $c(\lambda) > 0$ with $\mathbb{P}_\lambda(T_{\mathrm{ext}} \ge e^{cn}) \to 1$: the infection persists exponentially long at every infection rate.
4. For every $\lambda > 0$ there is $C(\lambda)$ with $\mathbb{P}_\lambda(T_{\mathrm{ext}} \ge e^{Cn}) \to 0$. More generally, this holds on any graph sequence with $n$ vertices whose uniform-vertex degree $D_n$ satisfies $\limsup_n \mathbb{E}[\log(1 + \delta D_n)] < \infty$ for some $\delta \in (0,1)$.

## Expansion

Two mechanisms can sustain an epidemic at arbitrarily small $\lambda$. An individual in many communities is a high-degree star, and stars of degree $d$ hold the infection for time $e^{c\lambda^2 d}$; an exponential moment failure of the membership law supplies enough such stars along the tree. A large community is a clique, and a clique of size $k$ keeps the infection for time of order $e^{c k \log(\lambda k)}$, which is why the community condition carries the $K \log K$ scale. If neither tail is heavy enough, a reinforced comparison process dies out for small $\lambda$, giving a subcritical phase. Item 4 shows exponential persistence is the maximum order possible.

## Sources

- J. Komjáthy, M. Seiler, D. Valesin, "How communities help epidemics persist", arXiv:2611.27843 (2026), Definitions 2.3, 2.6 and 2.7, the local weak convergence Theorem 2.8, Theorems 3.1, 3.2, 3.4, 3.6 and 3.7, <https://doi.org/10.48550/arXiv.2611.27843>.
