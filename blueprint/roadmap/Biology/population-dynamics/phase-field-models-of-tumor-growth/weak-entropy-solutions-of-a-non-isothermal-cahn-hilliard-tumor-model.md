# Weak entropy solutions of a non-isothermal Cahn–Hilliard tumor model

**Setting.** In a smooth bounded domain $\Omega\subset\mathbb R^3$ ($|\Omega|=1$), a tumor surrounded by healthy tissue is described by the phase field $\varphi$ ($\varphi=1$ tumor, $\varphi=-1$ healthy), the chemical potential $\mu$, the absolute temperature $\theta>0$ and a nutrient concentration $\sigma$. A thermodynamically consistent derivation (free energy with a temperature–phase coupling, Fourier's law, and a nutrient balance) gives

$$\varphi_t=\Delta\mu+(\mathcal P\sigma-\mathcal A)h(\varphi),\qquad \mu=-\Delta\varphi+F'(\varphi)-\theta,$$

$$\theta_t+\theta\varphi_t-\operatorname{div}(\kappa(\theta)\nabla\theta)=|\nabla\mu|^2,\qquad \sigma_t=\Delta\sigma-\mathcal C\sigma h(\varphi)+\mathcal B(\sigma_B-\sigma),$$

with homogeneous Neumann conditions for all unknowns. Here $\mathcal P,\mathcal A,\mathcal B,\mathcal C>0$ are proliferation, apoptosis, vascular supply and consumption rates, $\sigma_B\in(0,1)$ is the vascular nutrient level, and $|\nabla\mu|^2$ is the heat released by phase dissipation.

**Hypotheses.** $F>0$ with $F'(r)=\beta(r)-\lambda r$, $\lambda\ge0$, $\beta$ monotone increasing, $\beta(0)=0$, $|\beta(r)|\le c_\beta(1+F(r))$ and $|\beta(r)|\ge k|r|$; $h\in C^1$ is increasing with $h(-1)=0$, $h\equiv1$ on $[1,\infty)$ and $h$ constant for $r\le\underline\varphi\le-1$; the conductivity is $\kappa(\theta)=1+\theta^q$ with $q\ge2$; the initial data satisfy $\varphi_0\in H^1$, $F(\varphi_0)\in L^1$, $\theta_0>0$ with $\theta_0,\log\theta_0\in L^1$, and $0\le\sigma_0\le1$.

**Theorem.** Under these hypotheses, for every $T>0$ there exists a weak entropy solution $(\varphi,\mu,\theta,\sigma)$ with

$$\varphi\in C([0,T];H^1)\cap H^1(0,T;(H^1)')\cap L^2(0,T;H^2),\qquad \beta(\varphi)\in L^2(0,T;L^2),\qquad \mu\in L^2(0,T;H^1),$$

$$\theta\in L^2(0,T;H^1)\cap L^\infty(0,T;L^1)\cap L^q(0,T;L^{3q}),\quad \theta>0\ \text{a.e.},\qquad \sigma\in C([0,T];L^2)\cap L^2(0,T;H^1)\cap L^\infty,$$

satisfying the $\varphi$, $\mu$ and $\sigma$ equations weakly and, instead of the temperature equation, the entropy production inequality: the entropy $s=\log\theta+\varphi$ is transported with nonnegative production at least $|\nabla\mu|^2/\theta+\kappa(\theta)|\nabla\theta|^2/\theta^2$, tested against all non-negative smooth test functions vanishing at time $T$.

## Expansion

The nutrient stays in $[0,1]$ by testing with its negative part and with $(\sigma-1)_+$. The total energy (Ginzburg–Landau free energy plus thermal energy) is controlled using the fact that the heat source $|\nabla\mu|^2$ exactly compensates the dissipation in the phase equation, while the proliferation term is bounded through $h$ and $\sigma$. The entropy balance, obtained by dividing the temperature equation by $\theta$, gives $L^2$ bounds on $\nabla\log\theta$ and on $\theta^{q/2}$ gradients, which with the nonlinear Poincaré inequality yield the $L^q(L^{3q})$ bound. The quadratic source $|\nabla\mu|^2$ is only $L^1$, so the temperature equation cannot be passed to the limit as an equality; the entropy inequality is weakly lower semicontinuous (Ioffe's theorem), which is why the solution concept is the weak entropy one.

## Sources

- Erica Ipocoana, "On a non-isothermal Cahn-Hilliard model for tumor growth", arXiv:2102.13615 (2021), Section 2 (derivation and constitutive relations), system (3.1)–(3.4), assumptions of Section 3.2, Definition 3.1 and Theorem 3.1, <https://doi.org/10.48550/arXiv.2102.13615>.
