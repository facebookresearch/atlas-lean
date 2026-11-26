# Graphon limit of the metapopulation Keller–Segel model

Let $I=[0,1]$, let $W$ be a measurable kernel on $I^2$ with finite row and column norms $M_x(|W|),M_y(|W|)<\infty$, and let $S(a,b)=e^{\chi a}/(e^{\chi a}+e^{\chi b})$. The **graphon Keller–Segel system** for $U=(n,c)$ is $\partial_tU=\mathcal F_W[U]$:

$$\begin{aligned}
\partial_tn(x)&=\eta_n\int_IW(x,y)\big(S(c(x),c(y))\,n(y)-\big(1-S(c(x),c(y))\big)n(x)\big)\,dy+f(n(x)),\\
\partial_tc(x)&=\frac{\eta_c}2\int_IW(x,y)\big(c(y)-c(x)\big)\,dy+\alpha n(x)-\beta c(x).
\end{aligned}$$

On $N$ patches with weights $\mathsf w^{(N)}_{k\ell}$, the discrete model replaces $\int_I W(x,y)\,\cdot\,dy$ by $\frac1N\sum_\ell\mathsf w^{(N)}_{k\ell}(\cdot)$. Write $\Pi_N$ for the step reconstruction on the intervals $I_k=[(k-1)/N,k/N)$ and $W^{(N)}$ for the step kernel of the weights.

**Theorem.**

1. (Well-posedness and bounds) For locally Lipschitz $f$ and $U_{\rm in}\in L^\infty(I)^2$ there is a unique maximal solution $U\in C^1([0,t_{\max});L^\infty(I)^2)$, with blow-up of the $L^\infty$ norm if $t_{\max}<\infty$. Suppose $W\ge0$, the data are nonnegative and $f(r)=rh(r)$ with $\sup h<\infty$. Then solutions are global, nonnegative and bounded on bounded time intervals, uniformly in $N$ for the discrete systems. For logistic $f(n)=rn(1-n/\bar n)$ the bounds $\|n\|_\infty\le\max\{\|n_{\rm in}\|_\infty,\bar n(1+\eta_nM_x(W)/r)\}$ and $\|c\|_\infty\le\max\{\|c_{\rm in}\|_\infty,\alpha R_n/\beta\}$ (with $R_n$ the first bound) hold for all $t\ge0$.
2. (Deterministic limit in $L^p$) If $W\in L^p(I^2)$, $1\le p<\infty$, and the graphon and reconstructed discrete solutions are bounded by $R_T$ on $[0,T]$, then for some $C_T$ independent of $N$

$$\sup_{t\le T}\|\Pi_NU^{(N)}(t)-U(t)\|_{L^p}\le e^{C_TT}\Big(\|\Pi_NU_{\rm in}-U_{\rm in}\|_{L^p}+C_TT\|W^{(N)}-W\|_{L^p}\Big).$$

3. (Random graphs) For graphs sampled from $W$, with probability at least $1-\delta$ the sampled solution $U^{\xi,(N)}$ satisfies the same estimate up to an additional error $C_{T,p}\sqrt{\log(2/\delta)/N}$. Hence $\Pi_NU^{\xi,(N)}\to U$ in probability in $C([0,T];L^p(I)^2)$.
4. (Cut distance) If nonnegative kernels $K_N$ with uniformly bounded row and column norms satisfy $\delta_\square(K_N,W)\to0$, the corresponding solutions converge to the graphon solution after relabelling by measure-preserving bijections.

## Expansion

The right-hand side $\mathcal F_W$ is locally Lipschitz on $L^\infty(I)^2$, which gives local well-posedness by Picard iteration. Nonnegativity and a priori bounds follow from comparison, since the loss term is proportional to $n(x)$ and $S\in[0,1]$. The convergence estimates come from Grönwall's inequality applied to the difference of the integral equations. Here the step reconstruction solves $\Pi_NU^{(N)}(t)=\Pi_NU_{\rm in}+\int_0^t\mathcal F_{W^{(N)}}[\Pi_NU^{(N)}]\,ds$, so the discrete model is the graphon model driven by the step kernel. For sampled graphs, a concentration inequality controls the gap between the random adjacency and its expectation. This places the network chemotaxis model of [the graph instability threshold](chemotactic-instability-threshold-on-metapopulation-graphs.md) and its continuum integro-differential limit in one framework.

## Sources

- Daecheol Kim, Yefei Zhang, Yuxuan Zhao, Daniel B. Cooney, "The Keller-Segel Model for Chemotaxis on Metapopulation Graphs and Graphons", arXiv:2610.31049 (2026), Section 4: Proposition 4.2, Corollaries 4.8–4.9, Theorems 4.13, 4.16 and 4.23, <https://doi.org/10.48550/arXiv.2610.31049>.
