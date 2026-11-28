# Equilibria of the mutation–selection equation with pairwise interaction

**Model.** Two types: type $0$ (fit) and type $1$ (unfit). Type $0$ reproduces at the extra selective rate $s\ge0$ and at the extra interactive rate $\gamma(1-y)$, $\gamma\ge0$, where $y$ is the type-1 frequency (a type-0 individual reproduces if a random partner is also type $0$). Both types mutate at rate $u>0$, to type $0$ with probability $\nu_0$ and to type $1$ with probability $\nu_1=1-\nu_0$. In an infinite population,

$$\frac{dy}{dt}=-y(1-y)\big[s+\gamma(1-y)\big]+u\nu_1(1-y)-u\nu_0y,\qquad y(0)=y_0\in[0,1].$$

Equivalently, it is the diploid mutation–selection equation with genotype fitnesses $w_{00}=1+2s+\gamma$, $w_{01}=w_{10}=1+s$, $w_{11}=1$ (type $0$ partially recessive), $y$ being the allele frequency of $1$.

**Proposition (equilibria, unidirectional mutation $\nu_0=0$).**

- If $\gamma=s=0$, $y=1$ is the only equilibrium and is stable.
- If $\gamma=0<s$, the equilibria are $1$ and $u/s$; the smaller one is stable in $[0,1]$, the other unstable.
- If $\gamma>0$, set $u^\star=\frac1\gamma\big(\frac{s+\gamma}2\big)^2$. For $u>u^\star$, $y=1$ is the only equilibrium and is stable. For $u\le u^\star$ the equilibria are $1$ and

$$\bar y_\pm=\frac{\gamma+s\pm\sqrt{(\gamma+s)^2-4u\gamma}}{2\gamma}.$$

**Corollary (long-term behaviour, $\gamma>0$, $\nu_0=0$).** Partition parameters into $\Theta_1=\{u>u^\star\}\cup\{\gamma\le s\le u\le u^\star\}$, $\Theta_2^a=\{u<s\}\cup\{u=s<\gamma\}$, $\Theta_2^b=\{s<\gamma,\ u=u^\star\}$, $\Theta_3=\{s<u<u^\star,\ s<\gamma\}$. Then $y(t;y_0)\to y_\infty(y_0)$ with

- in $\Theta_1$: $y_\infty\equiv1$ (the fit type goes extinct);
- in $\Theta_2^a$: $y_\infty(1)=1$ and $y_\infty(y_0)=\bar y_-$ for $y_0<1$ (the fit type persists from any positive frequency);
- in $\Theta_2^b\cup\Theta_3$: $y_\infty(y_0)=\bar y_-$ if $y_0<\bar y_+$, $=\bar y_+$ if $y_0=\bar y_+$, and $=1$ if $y_0>\bar y_+$ (bistability: a rare beneficial mutant dies out).

As $\gamma\to0$, $\bar y_-\to u/s$, recovering the genic case.

## Expansion

With $\nu_0=0$ the right-hand side factors as $+(1-y)\big[\gamma y^2-(\gamma+s)y+u\big]$ (it equals $u>0$ at $y=0$), so the interior equilibria are the roots of a quadratic with discriminant $(\gamma+s)^2-4u\gamma$, which vanishes exactly at $u=u^\star$: a saddle-node bifurcation. On $[0,1]$ the sign of the quadratic decides stability; when both roots lie in $(0,1)$, $\bar y_+$ is a threshold separating the basins of $\bar y_-$ and $1$. Interaction ($\gamma>s$) thus creates an Allee-type effect for the fit type, which the classical genic model ($\gamma=0$) lacks.

## Sources

- Ellen Baake, Fernando Cordero and Sebastian Hummel, "Lines of descent in the deterministic mutation–selection model with pairwise interaction", *Ann. Appl. Probab.* 32(4) (2022), 2400–2447. <https://doi.org/10.1214/21-AAP1736>
- Preprint version (the locators in this item follow its numbering): Ellen Baake, Fernando Cordero, Sebastian Hummel, "Lines of descent in the deterministic mutation-selection model with pairwise interaction", arXiv:1812.00872: Section 2.1 (the ODE and Remark 2.1 on the diploid equation), Proposition 2.3 (equilibria and stability), Corollary 2.4 (convergence by parameter region), Proposition 3.1 (limit $\gamma\to0$). <https://doi.org/10.48550/arXiv.1812.00872>
