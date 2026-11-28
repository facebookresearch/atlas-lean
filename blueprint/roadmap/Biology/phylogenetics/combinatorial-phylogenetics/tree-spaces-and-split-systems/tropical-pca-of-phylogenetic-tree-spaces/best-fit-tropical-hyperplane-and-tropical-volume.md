# Best-fit tropical hyperplane and tropical volume

**Setting.** Work in the tropical projective torus $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ with max-plus arithmetic ($a \oplus b = \max(a,b)$, $a \odot b = a + b$) and the tropical metric

$$d_{\mathrm{tr}}(u,v) = \max_{k,l}\big|u_k - v_k - u_l + v_l\big| = \max_i(u_i - v_i) - \min_i(u_i - v_i).$$

Phylogenetic trees with $m$ leaves embed as tree metrics (or ultrametrics) in $\mathbb{R}^{\binom m2}/\mathbb{R}\mathbf{1}$, $e = \binom m2$: the space of tree metrics is the tropical Grassmannian $\mathrm{Gr}(2,m)$ (four-point condition), and the space of ultrametrics is the tropicalization of the linear space of the complete graph, a tropical linear space, so both are natural ambient spaces for tropical statistics.

A **tropical hyperplane** is the set of $x$ at which $\max_i(x_i - v_i)$ is attained at least twice, for some $v \in \mathbb{R}^e$; it is the Stiefel tropical linear space of an $(e-1)\times e$ tropical matrix, i.e. the tropical linear space of the tropical Plücker vector $\omega \mapsto \mathrm{tdet}(A_\omega)$. For an $e\times e$ tropical matrix $A$, with $\mathrm{tdet}\,A = \max_{\sigma\in S_e}\sum_i a_{i\sigma(i)}$ attained at $\sigma_{\mathrm{opt}}$, the **tropical volume** is the gap between the best and second-best permutation,

$$\mathrm{tvol}\,A = \mathrm{tdet}\,A - \max_{\tau \ne \sigma_{\mathrm{opt}}}\sum_i a_{i\tau(i)} \ \ge 0.$$

$A$ is tropically singular ($\mathrm{tvol}\,A = 0$) if and only if its $e$ rows lie on a common tropical hyperplane.

**Theorem (best-fit hyperplane).** Let $D^{(1)},\dots,D^{(e)} \in \mathbb{R}^e/\mathbb{R}\mathbf{1}$ and let $A$ have rows $D^{(i)}$. Then

$$\min_{\mathcal{H}\ \text{tropical hyperplane}}\ \sum_{j=1}^e d_{\mathrm{tr}}\big(D^{(j)}, \mathcal{H}\big) = \mathrm{tvol}\,A,$$

and a minimizing hyperplane can be chosen spanned by $e-1$ of the data points.

**Tropical PCA.** Two analogues of $(s-1)$st principal components are proposed for data $d_1,\dots,d_n$: (i) the Stiefel tropical linear space of an $s\times e$ matrix minimizing $\sum_i d_{\mathrm{tr}}(d_i, L)$, the projection onto $L$ being computed by the Blue Rule $w_i = \max_\tau\min_{j\notin\tau}(u_j + p(\tau\cup\{i\}) - p(\tau\cup\{j\}))$, with the Red Rule giving the residual $u - w$; and (ii) the tropical polytope spanned by $s$ points $D^{(1)},\dots,D^{(s)}$ minimizing $\sum_i d_{\mathrm{tr}}(d_i, d_i')$, where $d_i' = \bigoplus_k \lambda^i_k \odot D^{(k)}$ with $\lambda^i_k = \min(d_i - D^{(k)})$ is the tropical projection onto the polytope. For $s = 3$ the polytope problem is equivalent to a mixed-integer linear program with binary variables recording which generator attains each coordinate of $d_i'$.

## Expansion

The distance from a point $u$ to the hyperplane with apex $-v$ is the gap between the largest and second-largest entries of $u - v$. Summing over the $e$ data points and choosing $v$ optimally is an assignment-type problem: the total cost is bounded below by the gap between the two best permutations of a rescaled matrix with the same tropical volume as $A$, and a perturbation argument moves an optimal hyperplane until it passes through $e-1$ data points, where the cost equals the volume. Unlike the classical case, a Stiefel tropical linear space spanned by data points need not be contained in a tropical linear space containing those points, which is one reason the two tropical PCA notions differ. Applied to gene trees, the second-order tropical polytope PCA projects tree samples onto a tropical triangle in tree space for visualization.

## Sources

- Ruriko Yoshida, Leon Zhang and Xu Zhang, "Tropical principal component analysis and its application to phylogenetics", arXiv:1710.02682 (2017), Section 2 (tropical linear spaces, Blue and Red Rules, ultrametrics and tree metrics), Section 3.1 (tropical volume, tropical singularity lemma, best-fit hyperplane theorem) and Section 4 (tropical polytope PCA and its mixed-integer formulation), <https://doi.org/10.48550/arXiv.1710.02682>. Published version: Bulletin of Mathematical Biology 81 (2018) 568–597, <https://doi.org/10.1007/s11538-018-0493-4>.
