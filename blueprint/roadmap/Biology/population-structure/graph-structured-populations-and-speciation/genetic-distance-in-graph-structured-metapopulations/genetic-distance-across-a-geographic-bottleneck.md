# Genetic distance across a geographic bottleneck

**Setting.** Take the metapopulation model whose limiting genetic distance between subpopulations $i$ and $j$ is $1 - \mathbb{E}(e^{-2b_\infty\tau_{ij}})$, where $\tau_{ij}$ is the meeting time of two independent random walks on the migration graph started at $i$ and $j$ with backward rates $\tilde M_{kp} = M_{pk}/N_k$ ([hitting-time formula](genetic-distance-as-a-hitting-time-of-two-random-walks.md)). Let $\mathcal{G}_1$ and $\mathcal{G}_2$ be two complete graphs on $d$ vertices, joined by a single edge $(v_1,v_2)$ with $v_k \in \mathcal{G}_k$. Set $M_{ij} = 1/d$ for every edge and $N_i = 1$, so that $\tilde M_{ij} = 1/d$: two well-mixed groups of demes connected through one bottleneck.

**Theorem.** Fix $c > 0$ and let the scaled mutation rate be $b_\infty = c/d$. As $d \to \infty$, for neighbouring demes $i,j$,

$$1 - \mathbb{E}\big(e^{-2b_\infty\tau_{ij}}\big) = \begin{cases} \dfrac{c}{1+c} + o(1), & i,j \in \mathcal{G}_1 \text{ or } i,j \in \mathcal{G}_2, \\[2mm] 1 - \dfrac1d + o\Big(\dfrac1d\Big), & i = v_1,\ j = v_2. \end{cases}$$

Thus the two demes at the ends of the bottleneck are directly connected by migration at the same rate as any other neighbouring pair, yet their genetic distance tends to $1$ (almost every locus differs), while neighbours within a group stay at a distance bounded away from $1$.

## Depends on

- [Genetic distance between subpopulations as a hitting time of two random walks](genetic-distance-as-a-hitting-time-of-two-random-walks.md)

## Expansion

Within one complete graph the two walks meet after a geometric number of jumps with parameter $1/d$; jumps occur at total rate of order $2$, so the meeting time is asymptotically exponential with mean of order $d/2$, and $\mathbb{E}(e^{-2(c/d)\tau})$ tends to $1/(1+c)$. The walks rarely leave their group before meeting. For $v_1$ and $v_2$, the first jump of either walk almost surely moves it into the interior of its own complete graph, after which the walks sit in different groups and can meet only after one of them crosses the single bridge, which takes time of order $d^2$; then $2b_\infty\tau$ is of order $d$ and the Laplace transform is $O(1/d)$, the leading contribution coming from the chance $\approx 1/d$ that the walks meet at the first jump across the bridge.

## Sources

- Verónica Miró Pina and Emmanuel Schertzer, "How does geographical distance translate into genetic distance?", *Stochastic Process. Appl.* 129(10) (2019), 3893–3921. <https://doi.org/10.1016/j.spa.2018.11.004>
- Preprint version (the locators in this item follow its numbering): Verónica Miró Pina and Emmanuel Schertzer, "How does geographical distance translate into genetic distance?", arXiv:1703.00357 (2017), Section 6, Theorem 6.1 and its heuristics, <https://doi.org/10.48550/arXiv.1703.00357>.
