# Assortativity decides whether to vaccinate small or large groups first

**Setting.** A metapopulation has groups $i\in\Omega=\{1,\dots,N\}$ (or $\mathbb{N}^*$) of relative sizes $\mu_1\ge\mu_2\ge\dots>0$, $\sum_i\mu_i=1$, and next generation kernel

$$\mathrm{k}(i,j)=\begin{cases}a,& i=j,\\ b,& i\ne j,\end{cases}\qquad b>0,\ a\ge0,$$

so that the next generation matrix is $K_{ij}=\mathrm{k}(i,j)\mu_j$. A strategy $\eta\in[0,1]^\Omega$ leaves the fraction $\eta_i$ of group $i$ unvaccinated; its cost is $C(\eta)=1-\sum_i\eta_i\mu_i$ and its effective reproduction number is $R_e(\eta)=\rho(K\,\mathrm{Diag}(\eta))$. Pareto (best) and anti-Pareto (worst) strategies are defined as in [Pareto frontier of vaccination strategies in the kernel SIS model](../pareto-optimal-vaccination-in-heterogeneous-sis-models/pareto-frontier-of-vaccination-strategies-in-the-kernel-sis-model.md). Two greedy paths of strategies, parametrized by cost $c\in[0,1]$, are:

- *horizontal* $\mathscr{P}_h$: leave $\min(\alpha,\mu_i)$ unvaccinated individuals in group $i$, with $\alpha$ chosen so the cost is $c$; that is, vaccinate the largest groups down to a common level;
- *vertical* $\mathscr{P}_v$: vaccinate entire groups starting from the smallest, $j>\ell$, plus a fraction of group $\ell$.

A path is *greedy* if its strategies decrease pointwise in $\eta$ as cost grows, so doses can be given one at a time without regret.

**Theorem.**

1. (Assortative, $a\ge b>0$.) $T_\mathrm{k}$ is positive semi-definite and $R_e$ is convex; the horizontal path is a greedy parametrization of the Pareto frontier and the vertical path of the anti-Pareto frontier.
2. (Disassortative, $b\ge a>0$.) $R_0$ is the only positive eigenvalue of $T_\mathrm{k}$, simple, and $R_e$ is concave; the vertical path parametrizes the Pareto frontier and the horizontal path the anti-Pareto frontier.
3. (Complete multipartite, $a=0<b$.) The horizontal path parametrizes the anti-Pareto frontier, and the vertical strategies with cost at most $1-\mu_1$ parametrize the Pareto frontier; the minimal cost of stopping transmission completely ($R_e=0$, the source's $c_\star=\inf\{c:R_e^\star(c)=0\}$) is $1-\mu_1$ (vaccinate everyone outside the largest group) and the largest cost of a totally useless strategy is $0$.

So with assortative mixing it is best to protect the largest (highest-degree) groups first, while with disassortative mixing it is best to vaccinate small groups completely, which then have the highest degree.

## Expansion

The effective degree of group $i$ is $(a-b)\mu_i+b$, increasing in $\mu_i$ when $a>b$ and decreasing when $a<b$. Writing $\xi_i=\eta_i\mu_i$ for the unvaccinated mass, the spectral radius depends on $\xi$ through a symmetric function that is Schur-convex in the assortative case and Schur-concave in the disassortative case, a consequence of the convexity or concavity of $R_e$ coming from the sign of the spectrum. Among vectors $\xi$ with $\xi_i\le\mu_i$ and fixed total, the vertical profile majorizes every other and the horizontal profile is majorized by every other; Schur monotonicity then sends the extreme profiles to the extreme values of $R_e$, at every cost simultaneously, which is the greedy property.

## Depends on

- [Pareto frontier of vaccination strategies in the kernel SIS model](../pareto-optimal-vaccination-in-heterogeneous-sis-models/pareto-frontier-of-vaccination-strategies-in-the-kernel-sis-model.md)

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "Optimal vaccination: Various (counter) intuitive examples", arXiv:2112.08756 (2021): Section 4 (kernel with intra-group rate $a$ and inter-group rate $b$; proposition on convexity or concavity of $R_e$; horizontal and vertical vaccination paths; the assortative versus disassortative theorem; proposition on extreme vaccinations via majorization; remark on highest-degree vaccination). <https://doi.org/10.48550/arXiv.2112.08756> Published version: Journal of Mathematical Biology 86 (2023) 26, <https://doi.org/10.1007/s00285-022-01858-5>.
