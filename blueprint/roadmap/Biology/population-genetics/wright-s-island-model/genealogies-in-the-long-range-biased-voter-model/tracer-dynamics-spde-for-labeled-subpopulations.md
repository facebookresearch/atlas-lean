# Tracer dynamics in the biased voter model: coupled SPDEs for labeled lineages

In the [long-range biased voter model](stochastic-fkpp-limit-and-branching-coalescing-brownian-dual.md), label some of the type-$1$ cells at time $0$ and let labels be inherited. Let $u^n_t$ be the density of type-$1$ cells and $\ell^n_t\le u^n_t$ the density of labeled type-$1$ cells (both interpolated in space). Tracking $\ell$ shows which part of the initial population, for instance the cells near the front of an expansion, the future population descends from.

**Theorem.** Under the scaling of the density limit ($\alpha_n\to\alpha$, $\beta_n\to\beta$, $\gamma_n\to\gamma$, $L_n\to\infty$, $L_nR_n\to\infty$), if $(u^n_0,\ell^n_0)\to(f_0,g_0)$ in $C_b(\mathbb R)^2$, then $(u^n,\ell^n)$ converges in distribution in $D([0,\infty),C_b(\mathbb R)^2)$ to the continuous weak solution of

$$\partial_tu=\alpha\Delta u+2\theta\beta\,u(1-u)+\sqrt{4\gamma\,\ell(1-u)}\,\dot W^0+\sqrt{4\gamma\,(u-\ell)(1-u)}\,\dot W^1,$$

$$\partial_t\ell=\alpha\Delta\ell+2\theta\beta\,\ell(1-u)+\sqrt{4\gamma\,\ell(1-u)}\,\dot W^0+\sqrt{4\gamma\,\ell(u-\ell)}\,\dot W^2,$$

with $(u_0,\ell_0)=(f_0,g_0)$ and $\dot W^0,\dot W^1,\dot W^2$ independent space-time white noises. The solution is unique in law.

The three noises correspond to the three kinds of resampling events that change the pair: labeled versus type-$0$ ($\dot W^0$, moves both $u$ and $\ell$), unlabeled type-$1$ versus type-$0$ ($\dot W^1$, moves only $u$), and labeled versus unlabeled type-$1$ ($\dot W^2$, moves only $\ell$). Labeled cells feel selection only against type $0$, hence the drift $2\theta\beta\,\ell(1-u)$.

## Depends on

- [Stochastic Fisher–KPP limit of the long-range biased voter model and its branching–coalescing Brownian dual](stochastic-fkpp-limit-and-branching-coalescing-brownian-dual.md)

## Expansion

Convergence of the pair is proved by tightness of $(u^n,\ell^n)$ and identification of the limit through approximate martingale problems for the three cell classes (labeled type $1$, unlabeled type $1$, type $0$); the drift and covariation terms follow from the jump rates, each pairwise resampling contributing noise with variance proportional to the product of the two densities involved. Uniqueness in law comes from a new duality relation generalizing Shiga's duality for the Wright–Fisher SPDE: suitable product moments of $(u_t,\ell_t)$ are expressed through a branching–coalescing Brownian particle system, which determines the one-dimensional distributions and hence the law.

## Sources

- Rick Durrett, Wai-Tong (Louis) Fan, "Genealogies in expanding populations", *The Annals of Applied Probability* 26 (2016), 3456–3490, <https://doi.org/10.1214/16-AAP1181>; preprint arXiv:1507.00918, <https://doi.org/10.48550/arXiv.1507.00918>. Numbering of the arXiv version: Section 1 (tracer dynamics, Theorem 4), Lemma 2 (uniqueness via duality), Section 3 (approximate martingale problems).
