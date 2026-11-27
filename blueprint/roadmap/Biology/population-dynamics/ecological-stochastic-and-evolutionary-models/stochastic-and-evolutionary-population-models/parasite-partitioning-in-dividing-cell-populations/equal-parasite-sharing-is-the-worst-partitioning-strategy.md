# Equal parasite sharing is the worst partitioning strategy

**Setting.** Consider the parasite-infected dividing cell population with division rate $r$, constant death rate $q<r$, deterministic exponential parasite growth at rate $g$ (no diffusion, $\sigma=0$) with explosive stable-type bursts, and a symmetric partitioning kernel $\kappa$ for the fraction $\Theta$ of parasites inherited by one daughter. Let $\mathfrak{C}_t$ be the number of living cells and $\vartheta=\mathbb{E}[\min(\Theta,1-\Theta)]$ the mean share of the less-infected daughter.

**Theorem.**

1. (Explicit thresholds) Let $g_{\lim}$ be the parasite growth rate above which $\mathbb{E}[\mathfrak{C}_t]\to0$ and below which $\mathbb{E}[\mathfrak{C}_t]\to\infty$. For uniform sharing $\kappa(d\theta)=d\theta$,

$$g_{\lim}=3r-q+2\sqrt{2r(r-q)} .$$

For equal sharing $\kappa=\delta_{1/2}$, $g_{\lim}=r\,x_0(q/r)\ln2$, where $x_0(q/r)>2$ is the unique solution of

$$x_0=\Big(1+\frac qr\Big)\big(1+\ln2-\ln x_0\big)^{-1}.$$

2. (Equal sharing is worst) For every partitioning kernel $\kappa$, if $g/r<x_0(q/r)\ln2$ then $\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to\infty$ for all $x\ge0$: any population that survives (in mean) under equal sharing also survives under any other strategy.
3. (Deterministic is worst at fixed asymmetry) For any symmetric $\kappa$ with $\mathbb{E}[\min(\Theta,1-\Theta)]=\vartheta\in(0,1/2]$, and the deterministic kernel $\kappa_\vartheta=\tfrac12(\delta_\vartheta+\delta_{1-\vartheta})$,

$$\lim_{t\to\infty}\mathbb{E}^{(\kappa)}_{\delta_x}[\mathfrak{C}_t]\ \ge\ \lim_{t\to\infty}\mathbb{E}^{(\kappa_\vartheta)}_{\delta_x}[\mathfrak{C}_t].$$

4. (No upper bound) For any $g,r,q$ with $q<r$ and any $\vartheta\in(0,1/2)$, there is a four-atom kernel $\kappa_2=\sum_{i=1}^2p_i(\delta_{z_i}+\delta_{1-z_i})$, $2(p_1+p_2)=1$, with $\mathbb{E}[\min(\Theta,1-\Theta)]=\vartheta$ and $\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to\infty$ for all $x>0$; it suffices to make the smallest atom $z_1$ very small.

## Depends on

- [Survival regimes of a parasite-infected dividing cell population](survival-regimes-of-a-parasite-infected-cell-population.md)

## Expansion

Survival in mean is decided by the sign of $\mathfrak{m}=g+2r\mathbb{E}[\ln\Theta]$ and, when $\mathfrak{m}>0$, of $\kappa_{r,q}=\min_{\lambda<0}\{\lambda g+2r(\mathbb{E}[\Theta^\lambda]-1)\}+r-q$. Jensen's inequality for the concave $\ln$ and convex $\theta\mapsto\theta^\lambda$ ($\lambda<0$) shows that, among symmetric kernels, $\delta_{1/2}$ maximizes $\mathbb{E}[\ln\Theta]$ and minimizes $\mathbb{E}[\Theta^\lambda]$, making both criteria least favourable; a finer comparison at a fixed value of $\mathbb{E}[\min(\Theta,1-\Theta)]$ singles out the two-point kernel $\kappa_\vartheta$ as least favourable within that class. Biologically, unequal sharing sacrifices some lineages by loading them with parasites, so that other lineages are nearly cleared and keep the population alive; a tiny atom $z_1$ makes $\mathbb{E}[\Theta^\lambda]$ arbitrarily large, which can beat any growth rate $g$. The explicit thresholds come from evaluating $\Lambda$ for $\Theta$ uniform ($\mathbb{E}\Theta^\lambda=1/(1+\lambda)$) and $\Theta=1/2$ ($\mathbb{E}\Theta^\lambda=2^{-\lambda}$) and solving $\kappa_{r,q}=0$.

## Sources

- Aline Marguet and Charline Smadi, "Parasite infection in a cell population: role of the partitioning kernel", Journal of Mathematical Biology 89 (2024), 14, <https://doi.org/10.1007/s00285-024-02110-y>; numbering as in arXiv:2305.06962: Corollary 3.1 and Propositions 3.2, 3.3 and 3.4.
