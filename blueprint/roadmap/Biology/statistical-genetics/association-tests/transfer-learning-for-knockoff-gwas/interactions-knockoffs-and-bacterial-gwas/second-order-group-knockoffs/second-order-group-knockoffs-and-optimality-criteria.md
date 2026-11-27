# Second-order group knockoffs and their optimality criteria

**Hypotheses.** Features $X = (X_1, \dots, X_p)$ with known covariance $\Sigma$ (standardized, mean zero) are partitioned into groups $A_1, \dots, A_g$, for example blocks of correlated SNPs. For a response $Y$ with arbitrary law given $X$, the group conditional independence hypotheses are

$$H_\gamma : X_\gamma \perp Y \mid X_{-\gamma}, \qquad \gamma = 1, \dots, g .$$

**Group knockoffs.** Variables $\tilde X$ are group knockoffs if $\tilde X \perp Y \mid X$ and $(X, \tilde X)_{\mathrm{swap}(C)} \overset{d}{=} (X, \tilde X)$ for every $C$ that is a union of groups. Individual knockoffs require this for every $C \subseteq [p]$. *Second-order* group knockoffs require only equal first two moments, which for standardized features means

$$\mathrm{Cov}(X, \tilde X) = G_S = \begin{pmatrix} \Sigma & \Sigma - S \\ \Sigma - S & \Sigma \end{pmatrix}, \qquad S = \mathrm{diag}(S_1, \dots, S_g),$$

with $S$ block-diagonal along the groups, subject to $0 \preceq S \preceq 2\Sigma$ (so that $G_S \succeq 0$). For $m$ knockoff copies, $G_S$ is the $(m+1) \times (m+1)$ block matrix with $\Sigma$ on the diagonal and $\Sigma - S$ off it, with constraint $0 \preceq S \preceq \tfrac{m+1}{m}\Sigma$. Gaussian $X$ gives exact knockoffs.

**Choosing $S$.** Any valid $S$ gives FDR control through the knockoff filter. Power depends on how distinguishable $X$ and $\tilde X$ are. Three criteria, minimized over block-diagonal $S$ in the feasible set:

$$L_{\mathrm{SDP}}(S) = \sum_{\gamma=1}^g \frac{1}{|A_\gamma|^2} \sum_{i, j \in A_\gamma} |S_{ij} - \Sigma_{ij}|, \qquad L_{\mathrm{MVR}}(S) = \mathrm{Tr}(G_S^{-1}), \qquad L_{\mathrm{ME}}(S) = \log\det(G_S^{-1}).$$

SDP minimizes within-group correlation between features and knockoffs. MVR minimizes $\sum_j \bigl(\mathbb{E}[\mathrm{Var}(X_j \mid X_{-j}, \tilde X)]\bigr)^{-1}$ (minimum variance-based reconstructability). ME maximizes the entropy of $(X, \tilde X)$, equivalently minimizes their mutual information. ME is convex in $S$. The equivariant special case $S_\gamma = \tau \Sigma_\gamma$ has the closed form $\tau = \min\{1, 2\lambda_{\min}(B \Sigma B)\}$ with $B = \mathrm{diag}(\Sigma_1^{-1/2}, \dots, \Sigma_g^{-1/2})$.

**Coordinate updates.** Write $D = \tfrac{m+1}{m}\Sigma - S$. A symmetric update $S_{ij} \leftarrow S_{ij} + \delta_{ij}$ (and $S_{ji} \leftarrow S_{ji} + \delta_{ij}$) keeps $S \succ 0$ and $D \succ 0$ if and only if $\delta_{ij}$ lies in the following feasible region: for $i = j$,

$$-\frac{1}{e_j^\top S^{-1} e_j} < \delta_{jj} < \frac{1}{e_j^\top D^{-1} e_j},$$

and, for $i \ne j$, writing $a = e_i^\top S^{-1} e_i$, $b = e_j^\top S^{-1} e_j$, $c = e_i^\top S^{-1} e_j$ and $a' = e_i^\top D^{-1} e_i$, $b' = e_j^\top D^{-1} e_j$, $c' = e_i^\top D^{-1} e_j$, the exact condition $(1 + \delta_{ij} c)^2 - \delta_{ij}^2 ab > 0$ for $S$ and $(1 - \delta_{ij} c')^2 - \delta_{ij}^2 a' b' > 0$ for $D$ gives

$$\max\!\left(-\frac{1}{\sqrt{ab} + c},\ -\frac{1}{\sqrt{a' b'} - c'}\right) < \delta_{ij} < \min\!\left(\frac{1}{\sqrt{ab} - c},\ \frac{1}{\sqrt{a' b'} + c'}\right).$$

Both intervals contain $0$. A simpler sufficient inner region for $i \ne j$ is obtained from $a + b \ge 2\sqrt{ab}$ by intersecting Chu et al.'s Eq. (8) bounds $-2/(v^\top S^{-1} v) < \delta_{ij} < 2/(v^\top D^{-1} v)$ ($v = e_i + e_j$) with the complementary bounds $-2/(w^\top D^{-1} w) < \delta_{ij} < 2/(w^\top S^{-1} w)$ ($w = e_i - e_j$); Chu et al.'s Eq. (8) omits the $w$-bounds and is not by itself sufficient for both $S \succ 0$ and $D \succ 0$. Global moves $S \leftarrow S + \delta_i v_i v_i^\top$, with $v_i$ the eigenvectors of $\mathrm{diag}(\Sigma_1, \dots, \Sigma_g)$, have for ME the closed-form step

$$\delta_i = \frac{m\, v_i^\top S^{-1} v_i - v_i^\top D^{-1} v_i}{(m+1)\, v_i^\top S^{-1} v_i \; v_i^\top D^{-1} v_i},$$

which lies in the feasible interval $[-1/(v_i^\top S^{-1} v_i),\ 1/(v_i^\top D^{-1} v_i)]$. Each full sweep of these moves costs $O(p^3)$.

## Expansion

Group exchangeability imposes fewer constraints than individual exchangeability, so $S$ gains all within-group entries as free parameters. Highly correlated variants can then be paired with knockoffs that are far from them as a group, which restores power that individual knockoffs lose on tightly linked SNPs. For ME the log-determinant of $G_S$ factors through Schur complements, so a coordinate step reduces to maximizing a scalar function of $\delta_{ij}$ built from stored quadratic forms in $S^{-1}$ and $D^{-1}$. Cholesky factors of $S$ and $D$ are maintained by rank-2 updates. Alternating local coordinate moves with eigenvector moves avoids stalls at the positive-definiteness boundary. Because second-order knockoffs only need $\Sigma$, they apply to GWAS summary statistics using reference LD matrices. In the reported simulations ME gave the highest power, followed by MVR, SDP and the equivariant SDP. A summary-statistic analysis of albuminuria at target FDR $0.1$ found 35 independent signals, against 28 for conventional marginal testing.

## Sources

- B. B. Chu, J. Gu, Z. Chen, T. Morrison, E. Candès, Z. He, C. Sabatti, "Second-order group knockoffs with applications to genome-wide association studies", Bioinformatics 40 (2024) btae580, Equations (1)–(13), criteria (SDP), (ME), (MVR) and Algorithm 1, <https://doi.org/10.1093/bioinformatics/btae580> (PMC11639161).
