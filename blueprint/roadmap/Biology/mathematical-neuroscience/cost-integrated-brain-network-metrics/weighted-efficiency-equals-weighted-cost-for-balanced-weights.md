# Weighted efficiency equals weighted cost when weights are within a factor of two

Let $G$ be a fully weighted undirected network on $N_V \ge 2$ nodes with weights $w_{ij} = w_{ji} \in (0, 1]$ for all $i \ne j$. Give each edge the length $1/w_{ij}$ and let $d^W_{ij}$ be the length of a shortest path from $i$ to $j$,

$$d^W_{ij} = \min_{P \in \mathcal{P}_{ij}} \sum_{\{u,v\} \in P} \frac{1}{w_{uv}},$$

where $\mathcal{P}_{ij}$ is the set of paths from $i$ to $j$. The **weighted global efficiency** and the **weighted cost** of $G$ are

$$E_W(G) = \frac{1}{N_V(N_V - 1)} \sum_{i \ne j} \frac{1}{d^W_{ij}}, \qquad K_W(G) = \frac{1}{N_V(N_V - 1)} \sum_{i \ne j} w_{ij}.$$

**Theorem (Proposition 2 of the source).** If

$$\min_{i \ne j} w_{ij} \ \ge\ \frac{1}{2} \max_{i \ne j} w_{ij},$$

then $E_W(G) = K_W(G)$.

## Expansion

It suffices to show $d^W_{ij} = 1/w_{ij}$ for every pair, that is, that the direct edge is a shortest path. Any other path $P$ from $i$ to $j$ has at least two edges, so its length is at least $|P| / \max w \ge 2/\max w \ge 1/\min w \ge 1/w_{ij}$. Hence $1/d^W_{ij} = w_{ij}$ for all pairs and the two averages coincide. The hypothesis is met, approximately, by correlation-based fMRI networks after standardization of the weights into the unit interval, which is why the source argues that weighted efficiency adds little beyond mean connectivity strength and recommends reporting the weighted cost together with [cost-integrated topological metrics](cost-integrated-topological-metrics-are-invariant-under-monotone-reweighting.md).

## Sources

- C. E. Ginestet, T. E. Nichols, E. T. Bullmore and A. Simmons, *Brain network analysis: separating cost from topology using cost-integration*, PLoS ONE 6(7) (2011), e21570. DOI: <https://doi.org/10.1371/journal.pone.0021570>. PMCID: PMC3145634.
