# Dissipativity of SIS nodes and LMI redesign of inter-group interactions

**Setting.** A spreading network consists of $N$ groups of nodes; node $k$ of group $i$ has infected proportion $x_{i,k}(t) \in [0,1]$ obeying the networked SIS dynamics

$$\dot x_{i,k} = -\gamma_{i,k}(t)\,x_{i,k} + (1 - x_{i,k})\,u_{i,k}, \qquad u_{i,k} = \sum_{j=1}^N\sum_{l} M_{ij,kl}\,x_{j,l} + w_{i,k},$$

with uncertain recovery rate $|\gamma_{i,k}(t) - \bar\gamma_{i,k}| \le \delta_{i,k}$, nonnegative transmission rates $M_{ij,kl}$ (intra-group for $i = j$, inter-group otherwise) and an external disturbance $w_{i,k}$. A system with input $u$ and output $y$ is **$X$-dissipative** for a symmetric $X = [X^{kl}]$ if some storage function $V \ge 0$, $V(0) = 0$, satisfies $\dot V \le [u;\,y]^\top X\,[u;\,y]$ along all trajectories.

**Theorem.**
1. (Node dissipativity, Proposition 7 and Lemma 1) The scalar node $\dot x = -\gamma(t)x + (1-x)u$, $y = x$, with $x \in [0,1]$, $u \ge 0$ and $|\gamma - \bar\gamma| \le \delta$, is $X$-dissipative with $X = \begin{bmatrix} a & b \\ b & c\end{bmatrix}$ whenever there is $p > 0$ with $a > 0$, $b \le 0$ and

$$\begin{bmatrix} a & b \\ b & c + p(\bar\gamma - \delta)\end{bmatrix} \succeq 0,$$

the storage function being $V(x) = px^2$; in particular, a node with $\bar\gamma - \delta \ge 0$ is passive (Corollary 2).
2. (Network redesign, Theorems 1–2 and Algorithm 1) Given node recovery data, the intra-group matrices and nominal inter-group interactions $\bar M$, the inter-group matrix $\tilde M$ can be redesigned, by solving a convex LMI problem that minimizes $\lVert\tilde M - \bar M\rVert$ subject to $\lVert\tilde M - \bar M\rVert_2 \le \delta_2\lVert\bar M\rVert_2$ and elementwise bounds $-\delta_l\bar M \le \tilde M - \bar M \le \delta_u\bar M$, so that the infection-free state $x = 0$ of the whole network is stable, $\mathfrak X$-dissipative from the disturbance $w$ to the state $x$, and **scalable mesh stable**: disturbance effects stay uniformly bounded independently of the number of groups.
3. (Local necessary conditions, Proposition 2 and Lemmas 3–4) Feasibility of the global LMI requires local LMI conditions at each group and at each node, so the design can be carried out hierarchically, node by node, then group by group, then for the network.

## Expansion

With $V = px^2$, $\dot V = 2px\big(-\gamma x + (1-x)u\big) \le -2p(\bar\gamma - \delta)x^2 + 2pxu$ on $x \in [0,1]$, $u \ge 0$, and the LMI (using $b \le 0$ together with $xu \ge 0$) guarantees that this is dominated by the quadratic supply rate. Dissipativity then composes: if each subsystem is $X_i$-dissipative, a network with interconnection matrix $M$ is $\mathcal X$-dissipative whenever a block LMI in $(p_i)$ and $L = \mathbf X_p^{11}M$ holds, which is linear after this change of variables, so redesigning contact rates between groups (e.g. travel or mixing restrictions) becomes a convex program. Scalable mesh stability is added through a small-gain bound on each subsystem's input-to-state gains, and the resulting design keeps the infection-free state robustly stable under recovery-rate uncertainty and external infection pressure.

## Sources

- Shirantha Welikala, Hai Lin and Panos J. Antsaklis, "Hierarchical analysis and control of epidemic spreading over networks using dissipativity and mesh stability", arXiv:2509.24665 (2025), Section 2 (Definitions 1–2 of dissipativity and $X$-dissipativity), Section 3 (Propositions 1, 2, 5, 6 and 7, Corollaries 1–2), Section 4 (spreading network model and Problem 1), Section 5 (Lemmas 1–4, Theorems 1–2, Algorithm 1), <https://doi.org/10.48550/arXiv.2509.24665>.
