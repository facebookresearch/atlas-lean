# Gaussian solutions of the phenotype-structured logistic model

Let $n(t,y)\ge 0$, $t\ge 0$, $y\in\mathbb R$, be the density of a population structured by a continuous phenotypic trait, with total size $\rho(t)=\int_{\mathbb R} n(t,y)\,dy$, evolving by

$$\partial_t n=\bar D\,\partial_{yy}^2 n+n\,R(y,\rho),\qquad R(y,\rho)=\gamma-(y-\varphi)^2-\kappa\rho,$$

where $\bar D>0$ is the rate of spontaneous phenotypic changes, $\varphi\in\mathbb R$ is the fittest phenotype, $\gamma>0$ is the maximal fitness and $\kappa>0$ is inversely related to the carrying capacity. Suppose the initial datum is Gaussian,

$$n(0,y)=\frac{\rho_0}{\sqrt{2\pi\sigma_0^2}}\exp\!\Big(-\frac{(y-\bar y_0)^2}{2\sigma_0^2}\Big),\qquad \rho_0,\sigma_0>0,\ \bar y_0\in\mathbb R .$$

Then the solution stays Gaussian for all $t\ge 0$,

$$n(t,y)=\frac{\rho(t)}{\sqrt{2\pi\sigma^2(t)}}\exp\!\Big(-\frac{(y-\bar y(t))^2}{2\sigma^2(t)}\Big),$$

and the inverse variance $v=1/\sigma^2$, the mean phenotype $\bar y$ and the population size $\rho$ solve the closed Cauchy problem

$$\frac{dv}{dt}=2\big(1-\bar D v^2\big),\qquad \frac{d\bar y}{dt}=\frac{2}{v}\big(\varphi-\bar y\big),\qquad \frac{d\rho}{dt}=\Big(\gamma-\frac1v-(\bar y-\varphi)^2-\kappa\rho\Big)\rho,$$

with $v(0)=1/\sigma_0^2$, $\bar y(0)=\bar y_0$, $\rho(0)=\rho_0$. Consequently $v(t)\to 1/\sqrt{\bar D}$ and $\bar y(t)\to\varphi$ as $t\to\infty$, and if $\gamma>\sqrt{\bar D}$ then $\rho(t)\to(\gamma-\sqrt{\bar D})/\kappa$.

## Expansion

Substitute the Gaussian ansatz into the equation and divide by $n$. Both sides become quadratic polynomials in $y$; matching the coefficients of $y^2$, $y$ and $1$ gives the three ODEs. The $y^2$ coefficient gives $\frac{d}{dt}\sigma^2=2\bar D-2\sigma^4$, which is the $v$ equation; the linear coefficient pulls the mean towards $\varphi$ at a rate proportional to the variance (a Fisher-type relation: the response of the mean equals the variance times the fitness gradient); integrating the equation in $y$ gives the $\rho$ equation, where the mean fitness is $\gamma-\sigma^2-(\bar y-\varphi)^2-\kappa\rho$. The $v$ equation is autonomous with stable equilibrium $1/\sqrt{\bar D}$, after which $\bar y$ relaxes exponentially to $\varphi$ and $\rho$ follows a logistic equation. The equilibrium variance $\sqrt{\bar D}$ formalises that the rate of phenotypic change sets the phenotypic heterogeneity, and the variance load $\sqrt{\bar D}$ lowers the equilibrium size. Under the scaling $\bar D=\varepsilon^2$, $t\mapsto t/\varepsilon$, $\sigma_0^2=\varepsilon$, the Gaussian concentrates to a Dirac mass at the prevailing phenotype as $\varepsilon\to 0$.

## Sources

- T. Lorenzi, K. J. Painter, C. Villa, "Phenotype structuring in collective cell migration: a tutorial of mathematical models and methods", J. Math. Biol. (2025), Section "Concentration phenomena in non-local PDE models of evolutionary dynamics", Equations (10)–(12) and (31)–(33), <https://doi.org/10.1007/s00285-025-02223-y>, PMCID PMC12084280.
