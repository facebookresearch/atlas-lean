# Generic identifiability of the multitype pure-birth tree model from edge lengths around a node

**Model.** Fix $m$ types. Parameters are a root distribution $\boldsymbol\pi$, speciation rates $\boldsymbol\lambda = (\lambda_1,\dots,\lambda_m) \ge 0$ and a type-switching rate matrix $S = (s_{ij})$ with non-negative off-diagonal entries and zero row sums. Each lineage (edge) carries a hidden type that switches $i \to j$ at rate $s_{ij}$ and speciates at rate $\lambda_i$ when of type $i$; at a speciation the edge ends and two independent daughter edges start in the current type. The tree is grown to depth $T$ and only its (uncolored) metric shape is observed. Let $D = \operatorname{diag}(\boldsymbol\lambda)$, $U = S - D$ and $A = S + D$.

**Edge process.** On states $1_-,\dots,m_-$ (growing, type $i$) and absorbing $1_+,\dots,m_+$ (speciated in type $i$) the edge is a Markov chain with rate matrix $\begin{pmatrix} U & D \\ 0 & 0 \end{pmatrix}$. If all $\lambda_i > 0$:

- the cdf of the edge length $\mathcal{T}$ started in type $i$ is $F_i(\tau) = \big(\mathbf{1} - e^{U\tau}\mathbf{1}\big)_i$, and $\mathcal{T} < \infty$ a.s.;
- the probability of speciating in type $j$ from type $i$ is $P_{i_-,j_+} = (-U^{-1}D)_{ij}$.

**Type frequencies.** If moreover all $s_{ij} > 0$ ($i \neq j$), the vector $R_t$ of type proportions among lineages alive at time $t$ satisfies $R_t \to \mathbf{u}$ a.s., where $\mathbf{u}$ is the positive normalized leading left eigenvector of $A$.

**Asymptotic node distribution.** As $T \to \infty$, pick an edge uniformly among those alive at time $T/2$; let $\tau_0$ be the residual time from $T/2$ to its speciation and $\tau_1,\tau_2$ the lengths of its two daughter edges. Conditioned on these daughter edges not being truncated at $T$, the joint law of $(\tau_0,\tau_1,\tau_2)$ converges to

$$G_\infty = \sum_{j=1}^m w_j\, \mu_j^1(\tau_0)\, F_j(\tau_1)\, F_j(\tau_2), \qquad w_j = \sum_i u_i P_{i_-,j_+},\quad \mu_j^1(\tau_0) = \frac{\sum_i u_i P_{i_-,j_+}(\tau_0)}{w_j},$$

an $m$-component mixture of products of three univariate distributions (the hidden mixture label is the node type $j$).

**Theorem.** Assume $\lambda_i > 0$ for all $i$, $s_{ij} > 0$ for all $i \neq j$, $\lambda_i \neq \lambda_j$ for $i \neq j$, and the $m \times m$ matrix $\big(\mathbf{1}\ \ U\mathbf{1}\ \ U^2\mathbf{1}\ \cdots\ U^{m-1}\mathbf{1}\big)$ is non-singular (all generic conditions). Then $(\boldsymbol\lambda, S)$ is identifiable up to permutation of type labels from $G_\infty$.

## Expansion

By Kruskal-type uniqueness for mixtures of products (Allman–Matias–Rhodes), an $m$-component mixture of three-fold product distributions with each family of factors linearly independent is determined up to label swapping. The daughter-edge factors $F_1,\dots,F_m$ are linear combinations of the exponentials $e^{U\tau}$, and the non-singularity condition makes them linearly independent; the parent-edge factors are handled similarly. Recovering each $F_j$ determines the vectors $e^{U\tau}\mathbf{1}$ for all $\tau$, hence the action of $U$ on the Krylov space spanned by $U^k \mathbf{1}$, which is all of $\mathbb{R}^m$ under the non-singularity assumption; so $U$ is determined, and $D$ and $S$ follow from $U = S - D$ with $S\mathbf{1} = 0$, with distinct $\lambda_i$ fixing the labelling.

## Sources

- Dakota Dragomir, Elizabeth S. Allman and John A. Rhodes, "Parameter Identifiability of a Multitype Pure-Birth Model of Speciation", Journal of Computational Biology 30 (2023), 277–292, <https://doi.org/10.1089/cmb.2022.0330>; numbering as in arXiv:2206.09057: Definition 2.1, Propositions 3.3–3.4, Corollary 4.6, the limiting node-distribution lemma and Corollary 5.4 (Section 5), Theorem 5.6 (with Theorem 5.1 from Allman, Matias and Rhodes 2009).
