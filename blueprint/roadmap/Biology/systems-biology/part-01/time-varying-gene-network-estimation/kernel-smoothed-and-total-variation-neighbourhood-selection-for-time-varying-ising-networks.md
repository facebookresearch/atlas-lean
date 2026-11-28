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

## Expansion

Kernel reweighting borrows strength from neighbouring time points: with bandwidth $h$ the effective sample size at $\tau$ is of order $nh$, at the price of a bias from parameter drift within the window. The TV estimator instead encourages piecewise-constant coefficient paths and recovers change points in network structure. Applied to developmental gene-expression time courses of *Drosophila melanogaster*, the methods reveal rewiring of the inferred regulatory network across the life cycle.

These are the estimators of Sections 2–3 of the source. Its Section 5 also quotes a sparsistency theorem for *smooth* from the companion analysis of Kolar and Xing (arXiv:0907.2337), whose proof has no refereed version, so the page does not state it.

## Sources

- M. Kolar, L. Song, A. Ahmed, E. P. Xing, "Estimating time-varying networks", arXiv:0812.5087 (2008). <https://doi.org/10.48550/arXiv.0812.5087>
- Published version: M. Kolar, L. Song, A. Ahmed, E. P. Xing, "Estimating time-varying networks", Annals of Applied Statistics 4 (2010), 94–123, Sections 2–3, <https://doi.org/10.1214/09-AOAS308>.
