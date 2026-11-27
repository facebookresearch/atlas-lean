# Simpson degree and effective degree of an isothermal graph

Let $G$ be a connected weighted graph on $N$ vertices with symmetric weights $w_{ij} = w_{ji} \ge 0$,
no self-loops ($w_{ii} = 0$), which is **isothermal** with the normalization

$$\sum_{j \in G} w_{ij} = 1 \qquad \text{for every vertex } i,$$

so that the weights out of each vertex are a probability distribution over its neighbours. The
**Simpson degree** of vertex $i$ is

$$\kappa_i = \Bigl(\sum_{j \in G} w_{ij}^2\Bigr)^{-1},$$

the inverse probability that two neighbours drawn independently with probability proportional to
edge weight coincide; it equals the number of neighbours $k_i$ when all edges at $i$ have equal
weight, and is smaller otherwise. Let $\tau_i$ be the expected remeeting time of two independent
random walks on $G$ started at $i$, where a step from $u$ goes to $v$ with probability $w_{uv}$:
$\tau_i = 1 + \sum_j w_{ij}\tau_{ij}$, where the coalescence times $\tau_{ij}$ solve $\tau_{ii} = 0$ and
$\tau_{ij} = 1 + \tfrac12 \sum_k (w_{ik}\tau_{jk} + w_{jk}\tau_{ik})$ for $i \ne j$ (in each step one of
the two walks, chosen with probability $\tfrac12$, moves).
The **effective degree** of $G$ is the $\tau$-weighted harmonic average of the Simpson degrees,

$$\tilde{\kappa} = \frac{\sum_i \tau_i}{\sum_i \tau_i \kappa_i^{-1}}
= \frac{N^2}{\sum_i \tau_i \kappa_i^{-1}},$$

the second equality using $\sum_i \tau_i = N^2$ for an isothermal graph. For an unweighted
$k$-regular graph, $\kappa_i = k$ for all $i$ and $\tilde{\kappa} = k$.

## Remarks

Both statistics measure an effective number of neighbours. The Simpson degree is the diversity
index of the weight distribution at a vertex, by analogy with the Simpson index of biodiversity: it
counts contacts, discounting those that receive little interaction time. The weighting by remeeting
times arises because the condition for strategy success is expressed through coalescence times of
random walks run backwards along ancestries, and $\tau_i$ is exactly the weight with which vertex
$i$ enters that condition.

## Sources

- B. Allen, G. Lippner, M. A. Nowak, "Evolutionary games on isothermal graphs",
  Nature Communications 10 (2019) 5107, Eqs. (1) and (3),
  <https://doi.org/10.1038/s41467-019-13006-7> (PMC6841731).
