# Minimal invasion speed of age-structured cell populations

**Setting.** Let $u(a,x,t)$ be the density of motile cells of age $a$ (time since last division) at $x\in\mathbb R$, with total density $P=\int_0^\infty u\,da$. Cells age at unit rate, diffuse with coefficient $\kappa>0$, die at rate $\mu(a,P)\ge0$ and divide at rate $\beta(a,P)\ge0$, each division producing two newborn cells:

$$\partial_tu+\partial_au=\kappa\,\partial_x^2u-\big[\mu(a,P)+\beta(a,P)\big]u,\qquad u(0,x,t)=2\int_0^\infty\beta(a,P)\,u(a,x,t)\,da .$$

Division rates of gamma type, $\beta(a,P)=\beta\,a\,e^{-\alpha a}(1-P)$, encode a maturation delay (newborn cells cannot divide immediately); constant rates recover memoryless proliferation.

**Theorem.**
1. (Closure for age-independent rates) If $\mu(a,P)=\mu(P)$ and $\beta(a,P)=\beta(P)$, then $P$ solves $\partial_tP=\kappa\,\partial_x^2P+[\beta(P)-\mu(P)]P$; for affine feedback $\beta=\beta_0-\beta_1P$, $\mu=\mu_0+\mu_1P$ this is the Fisher–KPP equation with $r=\beta_0-\mu_0$ and $K=(\beta_0-\mu_0)/(\beta_1+\mu_1)$.
2. (Dispersion relation) Travelling fronts $u=\phi(a,x-ct)$ with leading edge $\phi\sim A(a)e^{-\lambda(x-ct)}$, $\lambda>0$, have age profile $A(a)=A(0)\exp\big(-\int_0^a(c\lambda-\kappa\lambda^2+\mu(s,0)+\beta(s,0))\,ds\big)$ and must satisfy

$$1=2\int_0^\infty\beta(a,0)\exp\Big[-\int_0^a\big(c\lambda-\kappa\lambda^2+\mu(s,0)+\beta(s,0)\big)\,ds\Big]da .$$

The minimal wave speed $c_{\min}$ is the least $c>0$ for which some $\lambda>0$ solves it.
3. (Explicit speeds) For $\mu(a,P)=\mu$ and $\beta(a,P)=\beta(1-P)$ the dispersion relation reduces to $\kappa\lambda^2-c\lambda+(\beta-\mu)=0$, so the population invades exactly when $\beta>\mu$, with

$$c_{\min}=c_{\mathrm{lin}}=2\sqrt{\kappa(\beta-\mu)}$$

(the source's (5.13), the Fisher–KPP speed), where $c_{\mathrm{lin}}$ denotes the speed obtained by linearizing the source's moment system about extinction. For $\mu(a,P)=\mu P$ and $\beta(a,P)=\beta(1-P)$ one gets $c_{\min}=c_{\mathrm{lin}}=2\sqrt{\kappa\beta}$ ((5.15)). For the maturation delay $\mu(a,P)=(\mu-\gamma ae^{-\alpha a})P$, $\beta(a,P)=\beta ae^{-\alpha a}(1-P)$ with $\mu>\gamma/(\alpha e)$, linearizing the moment system gives $c_{\mathrm{lin}}=2\sqrt{\kappa(\sqrt{2\beta}-\alpha)}$ ((5.18)), invasion requires $2\beta>\alpha^2$, and $c_{\min}$ is the least $c$ for which some $\lambda>0$ solves

$$1=2\beta\int_0^\infty ae^{-\alpha a}\exp\Big[-(c\lambda-\kappa\lambda^2)a-\frac{\beta}{\alpha^2}\big(1-e^{-\alpha a}(1+\alpha a)\big)\Big]da$$

((5.19), the dispersion relation with $\mu(a,0)=0$); the source finds numerically that $c_{\min}<c_{\mathrm{lin}}$ there, so the moment-closure speed overestimates the invasion speed.

## Expansion

For age-independent rates, integrating the transport equation in $a$ and using the renewal condition gives the closure in part 1. At the leading edge $P\to0$, so the system linearizes; the exponential ansatz turns the transport equation into a linear ODE in age, and the renewal condition becomes the dispersion relation. For age-independent rates the exponential in the dispersion relation integrates explicitly and leaves a quadratic in $\lambda$, whose real positive roots exist exactly when $c$ is at least twice the square root of $\kappa$ times the low-density growth rate; for the maturation-delay rates the relation is solved numerically. Young cells dominate the leading edge and have little division potential under a maturation delay, which is why the exact speed falls below the moment-closure speed that assumes all ages decay uniformly.

## Sources

- Stéphanie M. C. Abo, Ruth E. Baker, "Survival and invasion dynamics in cell populations: an analytical framework for threshold behaviour in nonlinear age-structured models", arXiv:2511.17279 (2025), model (2.2)–(2.3), Lemma 1, Section 3 (survival conditions and steady-state age distributions) and Section 5 (moment-system speed $c_{\mathrm{lin}}$, dispersion relation (5.9) and the cases (5.10)–(5.19)), <https://doi.org/10.48550/arXiv.2511.17279>.
