# Convex maximum likelihood for branch lengths under irreversible mutation

**Model.** Let $\mathcal T$ be a rooted tree topology on $n$ sampled cells with edge set $E$ and branch lengths $l \in \mathbb R_{\ge 0}^{E}$. Each of $k$ independent characters starts in the unmutated state $0$ at the root and evolves along the chronogram $\mathcal T_l$ by the irreversible continuous-time Markov chain with rate matrix

$$Q = \begin{pmatrix} -c & c q_1 & c q_2 & \cdots \\ 0 & 0 & 0 & \cdots \\ \vdots & & \ddots \end{pmatrix}, \qquad P(t) = \begin{pmatrix} e^{-ct} & (1 - e^{-ct}) q_1 & (1 - e^{-ct}) q_2 & \cdots \\ 0 & 1 & 0 & \cdots \\ \vdots & & \ddots \end{pmatrix},$$

where $c > 0$ is the mutation (cut) rate and $q$ a distribution over mutated states $1, 2, \dots$; mutated states never change again. Missing entries are assumed ignorable (missing at random with parameters distinct from $(l, c, q)$). Ancestral states are filled in by a conservative maximum-parsimony reconstruction $\tilde x$ that leaves ambiguous states missing. For node $v$ and character $i$ let $u = \mathrm{gpa}_i(v)$ be the nearest ancestor with an observed state, $l_{uv}$ the path length from $u$ to $v$, and let

$$\mathrm{uncuts}(u \to v) = \#\{i : \tilde x_{u,i} = \tilde x_{v,i} = 0\}, \qquad \mathrm{cuts}(u \to v) = \#\{i : \tilde x_{u,i} = 0,\ \tilde x_{v,i} > 0\}.$$

**Proposition 1 (ignorability).** Under ignorable missingness, the likelihood factors as $p_{\theta,\phi}(\tilde X = \tilde x) = g_\phi(\tilde R = \tilde r)\, p_\theta(\tilde Z^{(1)} = \tilde x^{(1)})$, so branch lengths can be estimated from the marginal law of the observed entries alone.

**Theorem (convex reformulation).** The maximum likelihood estimator of the branch lengths does not depend on $q$, and, after fixing the scale by requiring unit tree depth, equals the rescaled solution of

$$\max_{l \ge 0,\ \mathcal T_l \text{ ultrametric}} \ \sum_{u, v} \Big[ -\mathrm{uncuts}(u \to v)\, l_{uv} + \mathrm{cuts}(u \to v)\, \log\big(1 - e^{-l_{uv}}\big) \Big]$$

(taking $c = 1$). This is a convex optimization problem in the edge lengths, and it remains convex after adding a minimum branch length $l_e \ge \epsilon$ and $\lambda$ pseudocount cuts and uncuts per edge (a MAP estimator).

## Expansion

By independence of sites and the structure of the conservative reconstruction, the log-likelihood is a sum over observed ancestor-descendant transitions $u \to v$ of $\log P(t)$ entries: an unmutated-to-unmutated transition contributes $-c\, l_{uv}$, a fresh mutation contributes $\log(1 - e^{-c l_{uv}}) + \log q_{\tilde x_{v,i}}$, and a retained mutation contributes $0$. The $\log q$ terms are free of $l$ and drop out. Lengths and rate are confounded only through the product $c\,l$, so normalizing depth to $1$ is equivalent to solving at $c = 1$ and rescaling. Each $l_{uv}$ is a linear function of the edge lengths, $x \mapsto -a x$ is linear and $x \mapsto \log(1 - e^{-x})$ is concave on $(0, \infty)$, and ultrametricity is a set of linear equalities, so the problem is the maximization of a concave function over a polyhedron. A coupling argument shows that a proper subtree whose leaves and reconstructed nodes share one state can always be collapsed to zero length without lowering the likelihood (the homogeneous subtree collapse theorem), which is why the minimum-length and pseudocount regularizers are needed.

## Sources

- S. Prillo, A. Ravoor, N. Yosef, Y. S. Song, "ConvexML: Fast and Accurate Branch Length Estimation under Irreversible Mutation Models, Illustrated through Applications to CRISPR/Cas9-Based Lineage Tracing", Systematic Biology 75(1) (2026) 115, Materials and Methods, Equations (1)-(16), Definition 1, Proposition 1 and Theorem 1, <https://doi.org/10.1093/sysbio/syaf054>, PMCID PMC12805672.
