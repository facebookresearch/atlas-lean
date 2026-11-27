# Beta-distribution steady states of two-scale selection

Let $\mu_t$ be the measure-valued solution of the deterministic two-scale selection equation on $[0,1]$ with parameter $\lambda=wr/s>0$ (ratio of between-group to within-group selection strength),

$$
\frac{d}{dt}\langle f,\mu_t\rangle=-\langle x(1-x)f',\mu_t\rangle+\lambda\big[\langle xf,\mu_t\rangle-\langle f,\mu_t\rangle\langle x,\mu_t\rangle\big],
$$

with initial probability measure $\mu_0$; $x$ is the fraction of group-favored individuals in a group.

**Fixed points.** $\delta_0$, $\delta_1$, and the Beta densities

$$
\frac{1}{B(\lambda-\alpha,\alpha)}\,x^{\lambda-\alpha-1}(1-x)^{\alpha-1},\qquad \alpha\in(0,\lambda),
$$

are stationary solutions.

**Theorem (long-time behavior).**

1. If $\mu_0(\{1\})>0$, then $\mu_t\to\delta_1$.
2. If $\mu_0([1-\epsilon,1])=0$ for some $\epsilon>0$, then $\mu_t\to\delta_0$.
3. If $x^{-\alpha}\mu_0([1-x,1])\to C\in(0,\infty)$ as $x\to0$ for some $\alpha>0$, then $\mu_t\to\mathrm{Beta}(\lambda-\alpha,\alpha)$ when $\alpha<\lambda$, and $\mu_t\to\delta_0$ when $\alpha\ge\lambda$.

So the limit is selected by the tail of the initial data at $x=1$ (groups made almost entirely of the group-favored type): heavier mass near $1$ (smaller $\alpha$) relative to the between-group strength $\lambda$ sustains a coexistence distribution, otherwise within-group selection wins.

## Depends on

- [Deterministic scaling limit of the two-scale selection process](deterministic-scaling-limit-of-the-two-scale-selection-process.md)

## Expansion

The explicit solution $\mu_t=(\mu_0\circ\phi_t^{-1})\,w_t$ shows that the mass near $x=1$ at time $t$ comes from mass within distance about $e^{-t}$ of $1$ at time $0$; if $\mu_0([1-x,1])\sim Cx^{\alpha}$, transport shrinks that mass like $e^{-\alpha t}$, while the reweighting $w_t$ multiplies it by up to $e^{\lambda t}$. The competition between the exponents $\alpha$ and $\lambda$ decides whether the mean $h(t)=\langle x,\mu_t\rangle$ stays positive. When it does, $\int_0^t h$ grows linearly and the transported density converges to the Beta profile whose behavior near $1$ matches $(1-x)^{\alpha-1}$; integrability criteria on $h$ ($\int_0^\infty h<\infty$ forces $h\to0$, and $\int_0^\infty(1-h)<\infty$ forces $h\to1$) handle the degenerate limits $\delta_0$ and $\delta_1$.

## Sources

- Shishi Luo and Jonathan C. Mattingly, *Scaling limits of a model for selection at two scales*, arXiv:1507.00397 (2015), Lemma 2 (fixed points), Theorem 3 (steady-state behavior), Lemmas 7–8. <https://doi.org/10.48550/arXiv.1507.00397>. Published version: Nonlinearity 30(4) (2017), 1682–1707, <https://doi.org/10.1088/1361-6544/aa5499>; locators above refer to the arXiv version.
