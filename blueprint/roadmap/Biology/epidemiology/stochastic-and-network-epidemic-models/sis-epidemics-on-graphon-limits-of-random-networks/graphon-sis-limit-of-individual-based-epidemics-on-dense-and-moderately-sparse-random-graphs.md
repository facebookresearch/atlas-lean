# Graphon SIS limit of individual-based epidemics on dense and moderately sparse random graphs

**Model.** Nodes $i\le n$ carry features $x_i$ in a space $\mathbb{X}$ with empirical distribution $\mu^{(n)}$. Edges $\{i,j\}$ are present independently with probability $w^{(n)}_E(x_i,x_j)$; along an edge an infected node infects a susceptible neighbour at rate $w^{(n)}_I(x_i,x_j)$, and infected nodes recover at rate $\gamma^{(n)}(x_i)$. The state is the empirical measure $\eta^{(n)}_t=\frac1n\sum_i\delta_{(x_i,E_i(t))}$ on $\mathbb{X}\times\{S,I\}$, a pure-jump Markov process given the graph. Define the effective transmission kernel

$$w^{(n)}(x,y)=n\,w^{(n)}_E(x,y)\,w^{(n)}_I(x,y)$$

and $\mathcal{I}_n(g)=\mathbb{E}\int g\,d\mu^{(n)}\otimes d\mu^{(n)}$.

**Assumptions.** $\eta^{(n)}_0\to\eta_0$ in probability; $w^{(n)}\to w$ and $\gamma^{(n)}\to\gamma$ uniformly, with $w$ bounded and $\mu^{\otimes2}$-a.e. continuous and $\gamma$ bounded and $\mu$-a.e. continuous; and the per-edge infection rate vanishes on average,

$$\mathcal{I}_n\big(w^{(n)}_I\wedge1\big)\to0 .$$

For $w^{(n)}_E=\kappa_nw$ this is $n\kappa_n\to\infty$: the mean degree, hence the number of edges per node, diverges (dense graphs and sparse graphs with $\gg n$ edges, but not graphs with $O(n)$ edges).

**Statement.** $\eta^{(n)}$ converges in probability in Skorokhod space to the deterministic continuous process

$$\eta_t(dx,de)=\mu(dx)\big((1-u(t,x))\,\delta_S(de)+u(t,x)\,\delta_I(de)\big),$$

where $\mu$ is the feature marginal of $\eta_0$ and $u$ is the unique solution of the graphon SIS equation

$$\partial_tu(t,x)=(1-u(t,x))\int_{\mathbb{X}}u(t,y)\,w(x,y)\,\mu(dy)-\gamma(x)u(t,x),\qquad u(0,\cdot)=u_0 .$$

Moreover, there is a coupling with an epidemic on the complete graph with infection rate $w^{(n)}_Iw^{(n)}_E$ such that $\mathbb{E}\sup_{t\le T}\|\eta^{(n)}_t-\tilde\eta^{(n)}_t\|_{TV}\le C_T\,\mathcal{I}_n(w^{(n)}_I\wedge1)$.

## Expansion

On the complete graph with infection rate $w^{(n)}_Ew^{(n)}_I$ per pair, the infection pressure on node $i$ is $\frac1n\sum_jw^{(n)}(x_i,x_j)\mathbf{1}_{E_j=I}$, which converges to the integral term, and standard martingale and tightness arguments give the integro-differential limit. The random graph replaces the deterministic rate $w_Ew_I$ by the random rate $\mathbf{1}_{\{i\sim j\}}w_I$ with the same mean; the coupling thins or adds infection events edge by edge, and the probability that the two epidemics differ at a given infection attempt is bounded by $w_I\wedge1$, giving the total-variation bound. When degrees stay bounded this error does not vanish, which is why very sparse graphs need a different (local, not mean-field) limit.

## Sources

- Jean-François Delmas, Paolo Frasca, Federica Garin, Viet Chi Tran, Aurélien Velleret and Pierre-André Zitt, "Individual-based SIS models on (not so) dense large random networks", Latin American Journal of Probability and Mathematical Statistics 21 (2024), 1375, <https://doi.org/10.30757/alea.v21-52>; numbering as in arXiv:2302.13385: Section 2 (Proposition 2.2, Assumptions 2.3 and 2.6, Theorem 2.7), Propositions 3.2, 3.5 and 3.6.
