# Kernel-smoothed and total-variation neighbourhood selection for time-varying Ising networks

**Model.** Observations $x^t\in\{-1,1\}^p$ arrive at times $t\in\mathcal T_n=\{1/n,2/n,\dots,1\}$, one sample per time point, for example binarized expression of $p$ genes over a developmental time course. They are drawn independently from time-varying pairwise Markov random fields (Ising models)

$$\mathbb P_{\theta^t}(x)=\frac1{Z(\theta^t)}\exp\Big(\sum_{(u,v)\in E^t}\theta^t_{uv}x_ux_v\Big).$$

The goal is the graph $G^\tau=(V,E^\tau)$ at any $\tau\in[0,1]$, which is the nonzero pattern of $\theta^\tau$. The neighbourhood $S^\tau(u)=\{v:\theta^\tau_{uv}\ne0\}$ of node $u$ is read off from the conditional law of $x_u$ given the rest. This law is logistic, with log-likelihood $\gamma(\theta_u;x)=\log\mathbb P(x_u\mid x_{\setminus u};\theta_u)$. Neighbourhoods are estimated node by node and then symmetrized by AND or OR.

**Estimators.**

- *smooth* (parameters vary smoothly in time). Fix a symmetric nonnegative kernel $K$, bandwidth $h$ and weights $w^\tau_t=K_h(t-\tau)/\sum_{t'}K_h(t'-\tau)$. Then

$$\hat\theta^\tau_u=\arg\min_{\theta_u\in\mathbb R^{p-1}}\Big\{-\sum_{t\in\mathcal T_n}w^\tau_t\,\gamma(\theta_u;x^t)+\lambda_1\|\theta_u\|_1\Big\}.$$

This is a weighted $\ell_1$-penalized logistic regression.
- *TV* (parameters piecewise constant in time, with abrupt rewiring). Jointly over $t\in\mathcal T_n$,

$$\{\hat\theta^t_u\}=\arg\min\Big\{-\sum_t\gamma(\theta^t_u;x^t)+\lambda_1\sum_t\|\theta^t_u\|_1+\lambda_{\rm TV}\sum_{v\ne u}\sum_{i=2}^n\big|\theta^{i/n}_{uv}-\theta^{(i-1)/n}_{uv}\big|\Big\}.$$

This is a fused-lasso logistic regression.

Both are convex programs, solvable by coordinate descent or generic solvers and scalable to thousands of nodes.

**Theorem (sparsistency of smooth).** Assume the following:

1. bounded maximum degree $s$;
2. incoherence among the relevant covariates and between relevant and irrelevant covariates;
3. a minimum signal $\theta_{\min}$;
4. smooth dependence of $\theta^t$ on $t$;
5. regularity of the kernel.

Take $\lambda_1\ge C\sqrt{\log p}/n^{1/3}$, $h=O(n^{-1/3})$, $s=o(n^{1/3})$, $s^3\log p/n^{2/3}=o(1)$ and $\theta_{\min}=\Omega(\sqrt{s\log p}/n^{1/3})$. Then for every $\tau\in\mathcal T_n$

$$\mathbb P\big[\hat G^\tau\ne G^\tau\big]=O\Big(\exp\Big(-C\frac{n^{2/3}}{s^3}+C'\log p\Big)\Big)\to0 .$$

So the whole time-indexed sequence of graphs is recovered with high probability even when $p\gg n$ and there is only one sample per time point.

## Expansion

Kernel reweighting borrows strength from neighbouring time points. With $h\asymp n^{-1/3}$ the effective sample size is $nh\asymp n^{2/3}$. The bias from parameter drift within the window is of order $h$. Balancing the two gives the $n^{-1/3}$ rates for $\lambda_1$ and $\theta_{\min}$.The incoherence and minimum-signal assumptions play the same role as in static $\ell_1$ neighbourhood selection: they make the support identifiable and separable from noise. The TV estimator instead encourages piecewise-constant coefficient paths and recovers change points in network structure. Applied to developmental gene-expression time courses of *Drosophila melanogaster*, the methods reveal rewiring of the inferred regulatory network across the life cycle.

These are the estimators of Section 2 and the sparsistency theorem of Section 5 (quoted there from the companion analysis) of the source.

## Sources

- M. Kolar, L. Song, A. Ahmed, E. P. Xing, "Estimating time-varying networks", arXiv:0812.5087 (2008). <https://doi.org/10.48550/arXiv.0812.5087>
