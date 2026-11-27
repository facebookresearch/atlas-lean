# Emergence probability on a configuration-model network

Let a large configuration-model contact network have degree distribution $p(k)$ with mean $\langle k\rangle$ and no degree correlations, and classify individuals by degree. A pathogen with per-contact transmission rate $\beta$ and recovery rate $\gamma$ is introduced; $\nu_j \in [0,1]$ is the susceptibility of degree-$j$ individuals. In the [continuous offspring-production model](offspring-generating-function-of-continuous-offspring-production.md) set

$$R_{ij} = \frac{\beta}{\gamma}\,\pi_{ij}\,\nu_j, \qquad \pi_{ij} = \frac{k_i\,k_j\,p(k_j)}{\langle k\rangle}$$

for the first infected individual, where $\pi_{ij}$ is the expected number of degree-$j$ neighbours of a degree-$i$ node. Every later case was infected through one of its edges, so its mixing matrix uses the excess degree,

$$\pi'_{ij} = \frac{(k_i - 1)\,k_j\,p(k_j)}{\langle k\rangle}, \qquad R'_{ij} = \frac{\beta}{\gamma}\,\pi'_{ij}\,\nu_j .$$

With $F_i$ and $F'_i$ the generating functions built from $R$ and $R'$, let $\mathbf x'$ be the least solution of $\mathbf x' = \mathbf F'(\mathbf x')$; the extinction probability from a degree-$i$ index case is $x_i = F_i(\mathbf x')$ and $P_{\mathrm{emerge},i} = 1 - x_i$.

**Consequences.**

1. *Threshold.* In a fully susceptible network ($\nu \equiv 1$), $R'$ has rank one with spectral radius $\dfrac{\beta}{\gamma}\,\dfrac{\langle k^2\rangle - \langle k\rangle}{\langle k\rangle}$, so emergence is possible only if $\dfrac{\beta}{\gamma} > \dfrac{\langle k\rangle}{\langle k^2\rangle - \langle k\rangle}$; at fixed mean degree, greater degree variance lowers the threshold.
2. *Regular network.* If every node has degree $k$ and susceptibility $\nu$ ($\nu_j \equiv \nu$), then $R_0 = \beta k\nu/\gamma$, $R'_0 = \beta(k-1)\nu/\gamma$, $x' = \min(1, 1/R'_0)$ and

$$P_{\mathrm{emerge}} = 1 - \frac{1}{1 + R_0\bigl(1 - x'\bigr)},$$

so $P_{\mathrm{emerge}} \le \max(0, 1 - 1/R_0)$, and $P_{\mathrm{emerge}} = 0$ whenever $R'_0 \le 1$.

## Depends on

- [Offspring generating function of the continuous offspring-production model](offspring-generating-function-of-continuous-offspring-production.md)

## Expansion

Under the configuration model an edge from a degree-$i$ node lands on a degree-$j$ node with probability $k_jp(k_j)/\langle k\rangle$ (size-biased by degree), giving $\pi_{ij}$; the infector's edge is used up, giving $\pi'_{ij}$. $R'$ factors as $u v^{\top}$ with $u_i = \tfrac{\beta}{\gamma}(k_i - 1)$ and $v_j = k_jp(k_j)/\langle k\rangle$, so its only nonzero eigenvalue is $v^{\top}u = \tfrac{\beta}{\gamma}\sum_j k_j(k_j-1)p(k_j)/\langle k\rangle$. For the regular case with $R'_0 > 1$, so that $x' = 1/R'_0$ and $R_0 > 1$, $1/(1 + R_0(1 - x'))$ is at least $1/R_0$ exactly when $R_0/R'_0 \ge 1$, which always holds; when $R'_0 \le 1$, $x' = 1$ and $P_{\mathrm{emerge}} = 0$. For an invading strain at the endemic equilibrium of a resident strain, $\nu_j$ is the equilibrium susceptible fraction among degree-$j$ nodes, obtained from pair-approximation equations. Because high-degree nodes are preferentially infected by the resident, the residual susceptible network is less heterogeneous, which is why degree heterogeneity that aids the first strain's emergence lowers the fixation probability of later strains.

## Sources

- G. E. Leventhal, A. L. Hill, M. A. Nowak, S. Bonhoeffer, "Evolution and emergence of infectious diseases in theoretical and real-world networks", Nature Communications 6 (2015) 6101, Methods ("Branching process calculations for disease emergence in networks", "Combining techniques to approximate invasion of a second disease") and Results, <https://doi.org/10.1038/ncomms7101> (PMC4335509).
