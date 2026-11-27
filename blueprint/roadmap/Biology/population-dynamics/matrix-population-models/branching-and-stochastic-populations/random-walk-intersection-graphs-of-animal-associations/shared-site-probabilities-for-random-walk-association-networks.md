# Shared-site probabilities for random-walk association networks

**Model.** Agents $i=1,\dots,N$ move as independent simple random walks on $\mathbb Z^2$ started at the origin, and $F=\{\mathbf x_1,\dots,\mathbf x_M\}$ is a fixed set of sites. Let $S[1,T]$ be the set of sites a walk visits during $[1,T]$ and $e_i=S_i[1,T]\cap F$ the sites used by agent $i$. The association hypergraph has hyperedges $\{i:\mathbf x\in e_i\}$, $\mathbf x\in F$; its 2-section (the one-mode projection of the agent–site bipartite graph) links $i\ne j$ iff $e_i\cap e_j\ne\emptyset$. For $\mathbf x_A\subseteq F$ set

$$Q_{\mathbf x_A}(T)=\mathbb P(\mathbf x_A\subseteq S[1,T]),\qquad \mathbb P(\mathbf x_A)=\mathbb P(\mathbf x_A\subseteq S[1,T],\ \mathbf x_{F\setminus A}\cap S[1,T]=\emptyset).$$

**Inclusion–exclusion.** The law of the visited set is determined by the marginals:

$$\mathbb P(\mathbf x_A)=\sum_{\mathbf x_{A'}\supseteq\mathbf x_A}(-1)^{|\mathbf x_{A'}|-|\mathbf x_A|}\,Q_{\mathbf x_{A'}}(T).$$

**Association probability.** For any $K$ agents $i_1,\dots,i_K$,

$$\mathbb P(e_{i_1}\cap\dots\cap e_{i_K}\ne\emptyset)=\sum_{\emptyset\ne\mathbf x_A\subseteq F}(-1)^{|\mathbf x_A|+1}\,\big[Q_{\mathbf x_A}(T)\big]^K ;$$

$K=2$ gives the edge probability of the association network.

**Single sites.** With $p_{\mathbf x}(n)$ the $n$-step transition probability, the first-arrival law $q_{\mathbf x}(n)=\mathbb P(\tau_{\mathbf x}=n)$ solves the renewal equation $p_{\mathbf x}(n)=\sum_{k=1}^nq_{\mathbf x}(k)\,p_{\mathbf 0}(n-k)$, explicitly: with $a_0=1$ and

$$a_{2k}=\sum_{k_1+\dots+k_j=k}(-1)^j\,p_{\mathbf 0}(2k_1)\cdots p_{\mathbf 0}(2k_j)\qquad(k\ge1),$$

the sum running over all compositions of $k$ into positive parts ($j$ the number of parts), $q_{\mathbf x}(2m)=\sum_{k=0}^{m-1}a_{2k}\,p_{\mathbf x}(2m-2k)$ for $\mathbf x$ with $x_1+x_2$ even and $q_{\mathbf x}(2m+1)=\sum_{k=0}^{m}a_{2k}\,p_{\mathbf x}(2m+1-2k)$ for $x_1+x_2$ odd (and $q_{\mathbf x}(n)=0$ otherwise or when $n<|x_1|+|x_2|$). Consequently $Q_{\{\mathbf x\}}(T)=\mathbb P(\tau_{\mathbf x}\le T)$ equals

$$\sum_{h=1}^mb_{m-h}\,p_{\mathbf x}(2h)\quad(x_1+x_2\text{ even},\ m=\lfloor T/2\rfloor),\qquad \sum_{h=0}^mb_{m-h}\,p_{\mathbf x}(2h+1)\quad(x_1+x_2\text{ odd},\ m=\lfloor (T-1)/2\rfloor),$$

with the universal, nonnegative coefficients $b_h=\sum_{k=0}^ha_{2k}$.

## Expansion

Independence of the walks makes the joint event factor: the $K$ agents share a site iff some site lies in all of their visited sets, and inclusion–exclusion over the shared set $\mathbf x_A$ turns this into powers of $Q_{\mathbf x_A}(T)$. Each $Q$ reduces, by decomposing a path at the first visit to each target site, to convolutions of first-passage distributions of simple random walk, all expressible through $p_{\mathbf x}(n)$. The resulting networks are random intersection graphs with strongly correlated edges, unlike Erdős–Rényi graphs, because nearby agents share sites.

## Sources

- P. Cermelli, S. Marchese, L. Sacerdote, C. Zucca, "Animal social networks as intersections graphs of random walks", *Journal of Mathematical Biology* 93(6) (2026), 72, Proposition 1, Corollary 1, Propositions 2–4, Theorems 5–8, Proposition 9, <https://doi.org/10.1007/s00285-026-02484-1> (preprint arXiv:2511.11130).
