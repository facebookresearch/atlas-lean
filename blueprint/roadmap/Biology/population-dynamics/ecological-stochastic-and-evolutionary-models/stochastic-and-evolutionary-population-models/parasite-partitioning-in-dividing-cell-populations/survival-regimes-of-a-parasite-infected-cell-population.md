# Survival regimes of a parasite-infected dividing cell population

**Model.** Cells divide at rate $r>0$ and die at rate $q\ge0$. The parasite load $\mathfrak{X}_t$ of a cell follows, between divisions,

$$\mathfrak{X}_t=x+g\int_0^t\mathfrak{X}_s\,ds+\int_0^t\sqrt{2\sigma^2\mathfrak{X}_s^2}\,dB_s+\int_0^t\int_0^{\mathfrak{X}_{s-}}\int_{\mathbb{R}_+}z\,R(ds,du,dz),$$

with $g,\sigma\ge0$ and $R$ a Poisson point measure with intensity $ds\,du\,\rho(dz)$, $\rho(dz)\propto z^{-2-b}dz$ with $b\in(-1,0)$ (stable-type bursts, which can make the load explode in finite time). At division, a mother with load $x$ is replaced by two daughters with loads $\Theta x$ and $(1-\Theta)x$, where $\Theta\in(0,1)$ is symmetric with law $\kappa$ and $\mathbb{E}|\ln\Theta|<\infty$. A cell is dead once its load reaches $+\infty$. Let $\mathfrak{C}_t$ be the number of living cells (finite load) at time $t$.

**Key exponents.** With

$$\Lambda(\lambda)=\lambda(g-\sigma^2)+\lambda^2\sigma^2+2r\big(\mathbb{E}[\Theta^\lambda]-1\big),\qquad \lambda^-=\inf\{\lambda<0:\Lambda(\lambda)<\infty\},$$

(the Laplace exponent of the log-load along a typical lineage, convex on $(\lambda^-,\infty)$), set

$$\mathfrak{m}=\Lambda'(0+)=g-\sigma^2+2r\,\mathbb{E}[\ln\Theta],\qquad \hat\tau=\operatorname{argmin}_{(\lambda^-,0)}\Lambda,\qquad \kappa_{r,q}=\Lambda(\hat\tau)+r-q .$$

**Theorem.** Suppose $q\ne r$. For every initial load $x>0$:

1. If $\mathfrak{m}<0$: $e^{(q-r)t}\,\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to c_1(x)\in(0,1)$.
2. If $\mathfrak{m}=0$ and $\lambda^-<0$: $\sqrt t\,e^{(q-r)t}\,\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to c_2(x)>0$.
3. If $\mathfrak{m}>0$: $t^{3/2}e^{-\kappa_{r,q}t}\,\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to c_3(x)>0$.

Consequently $\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to0$ if $q\ge r$ or ($\mathfrak{m}>0$ and $\kappa_{r,q}\le0$), and $\mathbb{E}_{\delta_x}[\mathfrak{C}_t]\to\infty$ if ($\mathfrak{m}\le0$ and $r>q$) or ($\mathfrak{m}>0$ and $\kappa_{r,q}>0$). Thus $r>q$, which suffices without parasites (survival probability $1-q/r$), no longer ensures survival. Each of $q,r,g,\sigma$ has a threshold value at which the limit switches between $0$ and $\infty$, with fewer survivors for larger $g$ or $q$ and more for larger $r$ or $\sigma$.

The sufficient condition for $\mathbb{E}[\mathfrak{C}_t]\to\infty$ extends to load-dependent dynamics: drift $g(x)\le gx$, variance $\sigma^2(x)=\mathfrak{s}^2(x)x+\sigma^2x^2$ with $\mathfrak s$ $\tfrac12$-Hölder on compacts and $\mathfrak s(x)\sqrt x\le c\vee cx$ for some $c>0$, compensated jumps at rate $p(x)=x$, $q(x)\le q<r$, and $\Theta(x)$ stochastically dominated by a $\Theta$ with $\mathbb{E}|\ln\Theta|<\infty$. Since $\mathbb{E}[\ln\Theta]$ can be made arbitrarily negative, a sufficiently asymmetric kernel ensures $\mathfrak{m}\le0$ for any $(g,\sigma,r)$.

## Expansion

A many-to-one formula expresses $\mathbb{E}[\mathfrak{C}_t]$ as $e^{(r-q)t}$ times the probability that the auxiliary "typical lineage" load is still finite at time $t$; along that lineage, divisions occur at the size-biased rate $2r$ and multiply the load by $\Theta$, so $\ln\mathfrak{X}$ behaves like a Lévy process with exponent $\Lambda$, perturbed by stable bursts that cause explosion at a rate proportional to the load. If $\mathfrak{m}<0$ the log-load drifts to $-\infty$ and explosion along the lineage has probability bounded away from $1$; at $\mathfrak{m}=0$, the survival probability decays like $t^{-1/2}$ (fluctuation theory of oscillating Lévy processes); if $\mathfrak{m}>0$, survival requires a large-deviation excursion with cost $e^{\Lambda(\hat\tau)t}t^{-3/2}$ (Cramér-type estimate). Comparing these decay rates with the cell growth $e^{(r-q)t}$ gives the three regimes, as for branching processes in random environment.

## Sources

- Aline Marguet and Charline Smadi, "Parasite infection in a cell population: role of the partitioning kernel", Journal of Mathematical Biology 89 (2024), 14, <https://doi.org/10.1007/s00285-024-02110-y>; numbering as in arXiv:2305.06962: Proposition 2.1, Proposition 2.3, Corollary 2.4 and Lemma 2.5.
