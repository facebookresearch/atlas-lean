# Sub-Poissonian noise requires autoregulation in acyclic networks

Consider $m$ genes whose expression levels $X=(X_1,\dots,X_m)$ evolve as a continuous-time one-step Markov chain on $\{0,1,\dots\}^m$: gene $i$ moves $n_i-1\to n_i$ at rate $f_i(n)$ and $n_i\to n_i-1$ at rate $g_i(n)n_i$, and no transition changes more than one coordinate by one. If a gene's expression is not autonomous, its interior factors (gene state, nascent mRNA) are included as extra coordinates.

**Proposition.** Fix a gene $V_k$ that lies on no directed cycle of the gene regulatory network (automatic if the network is acyclic), and assume its per-molecule degradation rate $g_k$ is a constant. If $V_k$ has no autoregulation, i.e. $f_k(n)$ does not depend on $n_k$, and $V_k$ does not regulate its own interior factors, then at stationarity

$$\mathrm{VMR}(X_k)=\frac{\mathrm{Var}(X_k)}{\mathbb E(X_k)}\ge1 .$$

Hence an observed $\mathrm{VMR}(X_k)<1$ means that $V_k$ autoregulates, or that the one-step model fails (for example because of bursty or multi-step transitions).

## Expansion

Let $Y$ be the joint state of the ancestors of $V_k$ and $W=X_k$. Because $V_k$ is on no cycle and does not autoregulate, $Y$ evolves as an autonomous Markov chain unaffected by $W$, and given $Y$ the count $W$ is an immigration–death process with immigration rate $F_Y$ and per-molecule death rate $G$. Conditionally on the whole path of $Y$, $W(t)$ is Poisson with mean $\Lambda(t)=\int_{-\infty}^tF_{Y(s)}e^{-G(t-s)}\,ds$, so at stationarity $W$ is a mixed Poisson variable and

$$\mathrm{Var}(W)=\mathbb E[\Lambda]+\mathrm{Var}(\Lambda)\ge\mathbb E[\Lambda]=\mathbb E[W],$$

with equality iff $\Lambda$ is deterministic. Feedback or self-regulation would break the conditional-Poisson structure, which is why they are the only routes to sub-Poissonian noise in this class. The constant-$g_k$ assumption matters: if other genes change the degradation rate, the conditional law is no longer a time-changed Poisson with deterministic thinning.

## Sources

- Y. Wang, S. He, "Inference on autoregulation in gene expression with variance-to-mean ratio", Journal of Mathematical Biology (2023), multi-gene setup (Eq. (3)), Proposition 2 and its proof, <https://doi.org/10.1007/s00285-023-01924-6>, PMCID PMC10154285.
