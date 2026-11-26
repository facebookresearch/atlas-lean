# Minimal invasion speed of age-structured cell populations

**Setting.** Let $u(a,x,t)$ be the density of motile cells of age $a$ (time since last division) at $x\in\mathbb R$, with total density $P=\int_0^\infty u\,da$. Cells age at unit rate, diffuse with coefficient $\kappa>0$, die at rate $\mu(a,P)\ge0$ and divide at rate $\beta(a,P)\ge0$, each division producing two newborn cells:

$$\partial_tu+\partial_au=\kappa\,\partial_x^2u-\big[\mu(a,P)+\beta(a,P)\big]u,\qquad u(0,x,t)=2\int_0^\infty\beta(a,P)\,u(a,x,t)\,da .$$

Division rates of gamma type, $\beta(a,P)=\beta\,a\,e^{-\alpha a}(1-P)$, encode a maturation delay (newborn cells cannot divide immediately); constant rates recover memoryless proliferation.

**Theorem.**
1. (Closure for age-independent rates) If $\mu(a,P)=\mu(P)$ and $\beta(a,P)=\beta(P)$, then $P$ solves $\partial_tP=\kappa\,\partial_x^2P+[\beta(P)-\mu(P)]P$; for affine feedback $\beta=\beta_0-\beta_1P$, $\mu=\mu_0+\mu_1P$ this is the Fisher–KPP equation with $r=\beta_0-\mu_0$ and $K=(\beta_0-\mu_0)/(\beta_1+\mu_1)$.
2. (Dispersion relation) Travelling fronts $u=\phi(a,x-ct)$ with leading edge $\phi\sim A(a)e^{-\lambda(x-ct)}$, $\lambda>0$, have age profile $A(a)=A(0)\exp\big(-\int_0^a(c\lambda-\kappa\lambda^2+\mu(s,0)+\beta(s,0))\,ds\big)$ and must satisfy

$$1=2\int_0^\infty\beta(a,0)\exp\Big[-\int_0^a\big(c\lambda-\kappa\lambda^2+\mu(s,0)+\beta(s,0)\big)\,ds\Big]da .$$

The minimal wave speed $c_{\min}$ is the least $c>0$ for which some $\lambda>0$ solves it.
3. (Speed and threshold) Let $r^*$ be the Malthusian growth rate of the low-density age-structured population, the root of $2\int_0^\infty\beta(a,0)\exp\big[-r^*a-\int_0^a(\mu+\beta)(s,0)\,ds\big]da=1$. Then

$$c_{\min}=2\sqrt{\kappa\,r^*},$$

and a positive invasion speed exists exactly when $\mathcal R=2\int_0^\infty\beta(a,0)e^{-\int_0^a(\mu+\beta)(s,0)ds}\,da>1$, which is the condition for persistence of the well-mixed population. For constant rates $r^*=\beta-\mu$ and $c_{\min}=2\sqrt{\kappa(\beta-\mu)}$ (Fisher–KPP). For age-dependent rates, the moment-closure prediction $c_{\mathrm{lin}}=2\sqrt{\kappa\,r_{\mathrm{eff}}}$ satisfies $c_{\min}\le c_{\mathrm{lin}}$, so classical linear theory overestimates invasion speed.

## Expansion

For age-independent rates, integrating the transport equation in $a$ and using the renewal condition gives the closure in part 1. At the leading edge $P\to0$, so the system linearizes; the exponential ansatz turns the transport equation into a linear ODE in age, and the renewal condition becomes the dispersion relation. The right side depends on $(c,\lambda)$ only through $s=c\lambda-\kappa\lambda^2$ and is strictly decreasing in $s$, so the relation reads $s=r^*$. Since $\max_{\lambda>0}(c\lambda-\kappa\lambda^2)=c^2/(4\kappa)$, a solution with $\lambda>0$ exists iff $0<r^*\le c^2/(4\kappa)$, which gives the formula for $c_{\min}$ and shows that $c_{\min}>0$ iff $r^*>0$, i.e. iff $\mathcal R>1$. Young cells dominate the leading edge and have little division potential under a maturation delay, which is why the exact speed falls below the moment-closure speed that assumes all ages decay uniformly.

## Sources

- Stéphanie M. C. Abo, Ruth E. Baker, "Survival and invasion dynamics in cell populations: an analytical framework for threshold behaviour in nonlinear age-structured models", arXiv:2511.17279 (2025), model (2.2)–(2.3), Lemma 1, Section 3 (survival conditions and steady-state age distributions) and Section 5 (moment-system speed $c_{\mathrm{lin}}$, dispersion relation and $c_{\min}$), <https://doi.org/10.48550/arXiv.2511.17279>.
