# Monomorphic invasion fronts in phenotype-structured pressure-driven models

Let $n_\varepsilon(t,x,y)\ge 0$, $x\in\mathbb R$, $y\in(0,Y)$, be the density of cells with phenotype $y$, where small $y$ means high proliferation and low motility and large $y$ the reverse. Let $\rho_\varepsilon=\int_0^Y n_\varepsilon\,dy$ and $P_\varepsilon=\Pi[\rho_\varepsilon]$ be the cell density and the pressure, with $\Pi(0)=0$ and $\Pi'(\rho)>0$ for $\rho>0$. Consider the rescaled pressure-driven model

$$\varepsilon\,\partial_t n_\varepsilon-\varepsilon\,\partial_x\!\big(n_\varepsilon\,\mu(y)\,\partial_x P_\varepsilon\big)=\varepsilon^2\,\partial_{yy}^2 n_\varepsilon+n_\varepsilon\,R(y,P_\varepsilon),$$

with zero-flux conditions at $y=0$ and $y=Y$, mobility $\mu$ increasing with $0<\mu(0)<\mu(Y)<\infty$, and fitness $R(y,P)=r(y)-P/P_M$, where $r$ is decreasing with $r(0)=1$, $r(Y)=0$ and $P_M>0$. Then, formally as $\varepsilon\to0$, the model admits travelling waves $n_\varepsilon(t,x,y)=n_\varepsilon(z,y)$, $z=x-ct$, $c>0$, that are monomorphic at each position:

$$n_\varepsilon(z,y)\approx\rho(z)\,\delta_{\bar y(z)}(y),$$

where the locally expressed phenotype $\bar y(z)$ satisfies

$$\Big(c+\mu(\bar y)\frac{dP}{dz}\Big)\frac{d\bar y}{dz}=\frac{\partial_y R(\bar y,P)}{\partial_{yy}^2 u(z,\bar y)},\qquad z\in\operatorname{Supp}P,$$

$u$ being the limit of $\varepsilon\log n_\varepsilon$, which solves a constrained Hamilton–Jacobi equation with $\max_y u(z,y)=u(z,\bar y(z))=0$ and $\partial_{yy}^2u(z,\bar y(z))<0$, while the pressure and density are slaved to the phenotype:

$$P(z)=P_M\,r(\bar y(z)),\qquad \rho(z)=\Pi^{-1}P.$$

With $\bar y(-\infty)=0$ (bulk of the population behind the front), there is a minimal speed $c^\ast>0$ such that for $c>c^\ast$ the phenotype $\bar y(z)$ increases from $0$ towards $Y$ across the front while $\rho(z)$ decreases from $\rho_M=\Pi^{-1}(P_M)$: proliferative cells occupy the bulk and highly mobile, weakly proliferative cells lead the invasion.

## Expansion

The WKB ansatz $n_\varepsilon=\exp(u_\varepsilon/\varepsilon)$ turns the equation into a Hamilton–Jacobi equation; positivity of the total mass forces $\max_y u=0$, which concentrates $n_\varepsilon$ at the maximiser $\bar y(z)$. Differentiating the condition $\partial_y u(z,\bar y(z))=0$ along the wave gives the ODE for $\bar y$, and the condition $u(z,\bar y)=0$ forces zero net growth, $R(\bar y,P)=0$, which with the linear pressure penalty gives $P=P_Mr(\bar y)$. Because $r$ is decreasing and $\mu$ increasing, the phenotypic gradient across the front is a spatial sorting of a proliferation–migration trade-off. The results are formal asymptotics; the analogous statements hold for taxis-driven models with chemotactic sensitivity $\chi(y)$ in place of $\mu(y)$.

## Sources

- T. Lorenzi, K. J. Painter, C. Villa, "Phenotype structuring in collective cell migration: a tutorial of mathematical models and methods", J. Math. Biol. (2025), Section "Concentration phenomena across travelling waves", Equations (17), (49), (57), (58), (61)–(63), (65), (66), (68), <https://doi.org/10.1007/s00285-025-02223-y>, PMCID PMC12084280.
