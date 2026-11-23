# $q = 1$ probability of an edge pattern is its Bernoulli weight

Let $G$ be a simple graph on a finite vertex set $V$ with edge set $E(G)$, let $\mathcal{P}$ be the set of unordered pairs of elements of $V$ and let $p \in \mathbb{R}$. For $\omega \in \{0, 1\}^{\mathcal{P}}$ let

$$\phi_{G, p, 1}(\omega) = \frac{1}{Z} \prod_{e \in E(G)} p^{\omega(e)} (1 - p)^{1 - \omega(e)}, \qquad Z = \sum_{\omega' \in \{0, 1\}^{\mathcal{P}}} \prod_{e \in E(G)} p^{\omega'(e)} (1 - p)^{1 - \omega'(e)},$$

the random-cluster weight with $q = 1$ (the cluster factor $q^{k(\omega)}$ equals $1$), with the coordinates off $E(G)$ left free; here $Z = 2^{|\mathcal{P} \setminus E(G)|}$. For every pattern $\eta \in \{0, 1\}^{E(G)}$,

$$\sum_{\omega \,:\, \omega|_{E(G)} = \eta} \phi_{G, p, 1}(\omega) = \prod_{e \in E(G)} p^{\eta(e)} (1 - p)^{1 - \eta(e)}.$$
