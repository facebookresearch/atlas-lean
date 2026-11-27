# Sample complexity of locating super-spreaders from SI cascade infection times

**Model.** An unknown connected graph $G$ on $n$ vertices carries a susceptible–infected (SI) cascade: starting from one source $v_0$, a susceptible vertex $v$ becomes infected at rate $\lambda\,|\mathcal N(v) \cap \mathcal C(t)|$, where $\mathcal C(t)$ is the infected set (equivalently first-passage percolation with $\mathrm{Exp}(\lambda)$ edge weights). A *cascade trace* is the list $\mathbf T = \{(v, T(v))\}_{v \in V}$ of infection times. One observes $K$ independent traces $\mathbf T_1, \dots, \mathbf T_K$ from sources $v_{0,1}, \dots, v_{0,K}$ (arbitrary or adversarial). The graph class $\mathcal G(n,m,d,D)$ consists of connected $n$-vertex graphs with at most $m$ vertices of degree at least $D$ (the super-spreaders $\mathrm{HD}(G)$) and all other degrees at most $d$; assume $m$ constant, $d = n^{o(1)}$ and $D = n^\alpha$, $\alpha \in (0,1)$.

**Theorem (easy regime).** If $\alpha \in (3/4, 1)$ and

$$K > \frac{1}{\alpha - 3/4},$$

there is an estimator $\widehat{\mathrm{HD}}$ such that for every $G \in \mathcal G(n,m,d,n^\alpha)$ and every choice of sources, $\mathbb{P}\big(\widehat{\mathrm{HD}}(\mathbf T_1, \dots, \mathbf T_K) = \mathrm{HD}(G)\big) = 1 - o(1)$: a **constant** number of cascades suffices.

**Theorem (hard regime).** Fix $\epsilon > 0$ and $\alpha \in (0, 1/2)$, with $D = n^\alpha$, $d \ge \log^2 n$ and $m = 1$. If

$$K \le \frac{1 - 2\alpha - \epsilon}{5}\cdot\frac{\log n}{\log\log n},$$

there is a distribution over trees in $\mathcal G(n,1,d,D)$ and sources under which every estimator identifies the super-spreader with probability $o(1)$.

Since $C\log n$ traces suffice to reconstruct any tree exactly (Abrahao–Chierichetti–Kleinberg–Panconesi), finding hubs of degree below $\sqrt n$ is, up to a $\log\log n$ factor, as hard as learning the whole tree, while hubs of degree above $n^{3/4}$ are found from $O(1)$ cascades. The regime $\alpha \in [1/2, 3/4]$ is open.

## Expansion

Once a hub of degree $n^\alpha$ is infected, it infects its neighbors at total rate $\lambda n^\alpha$, so the infection curve $I(t)$ bends sharply upward right after the hub's infection time; a second-derivative test on the empirical infection curve locates that time from a single cascade, to precision fine enough when $\alpha > 3/4$. Vertices infected in the short window after that time are mostly the hub's neighbors, and the hub is the vertex consistently infected just before such bursts across the $K$ traces; $K > 1/(\alpha - 3/4)$ makes false candidates surviving all $K$ windows unlikely. For $\alpha < 1/2$ the burst from a hub is masked by the fluctuations of the bulk, and the lower bound builds trees where a hub and a decoy are statistically indistinguishable unless roughly $\log n/\log\log n$ traces are seen.

## Sources

- Elchanan Mossel and Anirudh Sridhar, "Finding Super-spreaders in Network Cascades", Proceedings of Thirty Seventh Conference on Learning Theory, Proceedings of Machine Learning Research 247 (2024), 3874–3914, <https://proceedings.mlr.press/v247/mossel24a.html>; numbering as in arXiv:2403.03205: Section 1 (SI model, Definition of $\mathcal G(n,m,d,D)$, Assumption on $m,d,D$, the possibility theorem for $\alpha > 3/4$ and the impossibility theorem for $\alpha < 1/2$).
