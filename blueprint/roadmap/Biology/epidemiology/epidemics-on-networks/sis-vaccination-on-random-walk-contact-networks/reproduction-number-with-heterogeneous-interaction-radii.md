# Reproduction number of SIS with vaccination among random walkers with heterogeneous interaction radii

**Model.** $N$ individuals perform random walks (with occasional long-range jumps) on a $D\times D$ torus at density $\rho=N/D^2$. Individual contacts are those within its interaction radius; radii take values $r_1,\dots,r_m$ with probabilities $P(r_j)$. In the homogeneous-mixing (mean-field) limit an individual of radius $r$ meets on average $\rho\pi r^2$ others per step. Let $s(r,t)$, $i(r,t)$, $v(r,t)=1-s-i$ be the susceptible, infected and vaccinated fractions among individuals of radius $r$; infection occurs at rate $\beta$ per contact, infecteds recover to susceptible at rate $\lambda$, susceptibles of radius $r$ are vaccinated at rate $\theta(r)$, and vaccinated individuals lose protection at rate $\varphi$:

$$\frac{ds}{dt}=\lambda i-s\,\beta\rho\pi r^2\sum_{j=1}^mP(r_j)\,i(r_j,t)-\theta(r)\,s+\varphi(1-s-i),\qquad \frac{di}{dt}=-\lambda i+s\,\beta\rho\pi r^2\sum_{j=1}^mP(r_j)\,i(r_j,t).$$

The region $\{0\le s,i,\ s+i\le1\}$ is positively invariant and the disease-free equilibrium is $s_r^0=\varphi/(\varphi+\theta(r))$, $i_r^0=0$.

**Theorem.** Define

$$\mathcal R_0=\frac{\beta\varphi\rho\pi}{\lambda}\sum_{j=1}^mP(r_j)\,\frac{r_j^2}{\varphi+\theta(r_j)}.$$

1. An endemic equilibrium exists, and is then unique, if and only if $\mathcal R_0>1$; it is $i_r^\ast=\dfrac{\beta\varphi\rho\pi r^2I^\ast}{\lambda(\varphi+\theta(r))+\beta\varphi\rho\pi r^2I^\ast}$, where $I^\ast=\sum_jP(r_j)i^\ast_{r_j}\in(0,1)$ is the unique positive root of the corresponding fixed-point equation.
2. If $\mathcal R_0<1$ the disease-free equilibrium is locally asymptotically stable, and globally asymptotically stable when moreover $\lambda\le\varphi$; if $\mathcal R_0>1$ it is unstable.
3. If $\mathcal R_0>1$ the endemic equilibrium is locally asymptotically stable and the disease is uniformly persistent.

With a constant vaccination rate $\theta(r)\equiv\theta$, $\mathcal R_0=\dfrac{\beta\varphi\rho\pi}{\lambda(\varphi+\theta)}\langle r^2\rangle$ is proportional to the second moment of the interaction radius, so at fixed mean radius greater heterogeneity of contact ranges increases $\mathcal R_0$; targeting vaccination at individuals with large radii lowers $\mathcal R_0$ most.

## Expansion

At an equilibrium, solving the $i$-equation for $s$ and substituting into the $s$-equation expresses each $i^\ast_r$ through the single scalar $I^\ast=\sum_jP(r_j)i^\ast_{r_j}$, giving an equation $F(I^\ast)=0$ with $F(I)=\sum_jP(r_j)\frac{\beta\varphi\rho\pi r_j^2I}{\lambda(\varphi+\theta(r_j))+\beta\varphi\rho\pi r_j^2I}-I$ strictly concave on $[0,1]$, $F(0)=0$ and $F(1)<0$; a positive root exists, and is unique, iff $F'(0)>0$, which is exactly $\mathcal R_0>1$. Linearizing at the disease-free equilibrium gives a rank-one perturbation of a diagonal matrix, whose leading eigenvalue changes sign exactly when $\mathcal R_0$ crosses $1$. Global stability for $\mathcal R_0<1$ uses a comparison argument in which the condition $\lambda\le\varphi$ keeps each susceptible fraction asymptotically below its disease-free value, so the infected fractions are dominated by a linear system with spectral bound of the sign of $\mathcal R_0-1$; persistence for $\mathcal R_0>1$ follows from uniform persistence theory with the disease-free set as a repeller.

## Sources

- Xiao-Long Peng, Ze-Qiong Zhang, Junyuan Yang, Zhen Jin, "An SIS epidemic model with vaccination in a dynamical contact network of mobile individuals with heterogeneous spatial constraints", arXiv (2019). Section 2 (model and Lemma 1), Section 3 (Theorem 2, $\mathcal R_0$ in equation (9)), Section 4 (Theorems 3, 4 and 5), Section 5 (Theorem 6, persistence). <https://doi.org/10.48550/arXiv.1902.06393>. Published version: Communications in Nonlinear Science and Numerical Simulation 73 (2019), 52–73, <https://doi.org/10.1016/j.cnsns.2019.02.004>; locators above refer to the arXiv version.
