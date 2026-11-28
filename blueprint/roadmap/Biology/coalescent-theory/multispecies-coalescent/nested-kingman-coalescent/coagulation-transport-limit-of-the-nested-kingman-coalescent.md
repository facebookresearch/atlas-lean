# Coagulation–transport limit of the nested Kingman coalescent

**Setting.** In the **nested Kingman coalescent**, species lineages form a Kingman coalescent (each pair of species merges at rate $1$, pooling their gene lineages), and, conditionally on the species tree, each pair of gene lineages lying in the same species merges at rate $c > 0$. In the $n$-th model let $s^n_t$ be the number of species and $\Pi^n_t(i)$ the number of gene lineages in species $i$, and define the rescaled empirical measure of genes per species

$$\tilde\mu^n_t = \frac{1}{s^n_{t/n}} \sum_{i=1}^{s^n_{t/n}} \delta_{\Pi^n_{t/n}(i)/n}.$$

With $\psi(x) = \frac{c}{2}x^2$ and $\delta > 0$, the **Smoluchowski coagulation–transport equation** for a density $d(t,x)$, $t,x \ge 0$, is

$$\partial_t d(t,x) = \partial_x(\psi d)(t,x) + \frac{1}{t+\delta}\big(d \star d(t,x) - d(t,x)\big), \qquad d\star d(t,x) = \int_0^x d(t,x-y)\,d(t,y)\,dy.$$

**Theorem.**
1. (Finite initial population, Theorem 5.1) Suppose the rescaled initial counts $\Pi^n_0(i)/n$ are i.i.d., independent of the species coalescent, with $\limsup_n \mathbb E[(\Pi^n_0(1)/n)^2] < \infty$, $s^n_0/n \to r \in (0,\infty)$ in $L^{2+\varepsilon}$, and $\tilde\mu^n_0 \Rightarrow \nu$. Then $(\tilde\mu^n_t, s^n_{t/n}/n)_{t \ge 0}$ converges in law to $(\mu_t, \frac{2}{2/r + t})_{t\ge 0}$, where $\mu$ is the unique weak solution of the equation above with initial condition $\nu$ and $\delta = 2/r$.
2. (Coming down from infinity, Theorems 5.4 and 5.6) For the nested Kingman coalescent started with infinitely many species, each containing at least one gene lineage (an $\infty$-population nested Kingman coalescent: $s_t \to \infty$ as $t \downarrow 0$ and $\Pi_t(i) \ge 1$ for every $i \in [s_t]$ and every $t > 0$), the rescaled empirical measures converge to the unique proper solution $\mu^{(0)}$ of the equation with $\delta = 0$, and $\mu^{(0)}_t$ is the law of $\Upsilon/t$ for a random variable $\Upsilon$ independent of $t$. The total number $\rho_t$ of gene lineages satisfies

$$\frac{1}{n^2}\,\rho_{t/n} \Longrightarrow \frac{2}{t}\int_0^\infty x\,\mu^{(0)}_t(dx) = \frac{2\,\mathbb E(\Upsilon)}{t^2} < \infty.$$

3. (Self-similarity, Theorem 2.8) $h(x) = \mathbb E[e^{-x\Upsilon}]$ satisfies $h(x) \le e^{-2x/c}$ (Theorem 2.8(ii) gives $h(x) \le \exp(-x(\beta/c')^\beta)$ for $\psi(x) = c'x^\gamma$ and $\beta = 1/(\gamma-1)$; here $c' = c/2$, $\gamma = 2$ and $\beta = 1$) and is the unique solution, in a suitable class, of $A_\beta h + h^2 - h = 0$ with $h(0)=1$ and $\limsup_{x\to\infty} h(x) < 1$, where $A_\beta$ is the generator of a continuous-state branching process; $\Upsilon$ is the total mass of a Yule tree of particles carrying such branching masses, restricted to the event that the mass does not go extinct.

## Depends on

- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)

## Expansion

The transport term encodes the deterministic descent from infinity of Kingman's coalescent within each species: $x$ gene lineages in a species decrease like $\dot x = -\frac{c}{2}x^2$. The coagulation term encodes species mergers: following a focal species, its gene mass gains, at rate $1/(t+\delta)$, an independent copy of the current mass, which produces the convolution. Solutions are represented through a time-inhomogeneous binary branching tree with birth rate $1/(T-t+\delta)$ whose particles carry masses evolving as continuous-state branching processes with Laplace exponent $\psi$, a duality that gives uniqueness. With of order $1/t$ species each carrying of order $1/t$ genes, the number of gene lineages comes down from infinity like $t^{-2}$, far more slowly than the $2/(ct)$ of a single Kingman coalescent.

## Sources

- Amaury Lambert and Emmanuel Schertzer, "Coagulation-transport equations and the nested coalescents", *Probab. Theory Related Fields* 176(1-2) (2020), 77–147. <https://doi.org/10.1007/s00440-019-00914-4>
- Preprint version (the locators in this item follow its numbering): Amaury Lambert and Emmanuel Schertzer, "Coagulation-transport equations and the nested coalescents", arXiv:1807.09153 (2018), Section 1 (model and Result statements), Theorems 2.4, 2.7 and 2.8, Theorems 5.1, 5.4 and 5.6, <https://doi.org/10.48550/arXiv.1807.09153>.
