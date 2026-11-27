# Measure-valued filopodia process for chemotactic crawling migration

**Model.** A crawling cell is driven by its adhering filopodia, each exerting a unit force in its own direction $\theta\in[0,2\pi)$, balanced by substrate friction $\gamma$. The population of filopodia is the finite point measure $\nu_t=\sum_{i=1}^{N_t}\delta_{\theta_i}$, and the velocity is

$$\gamma\vec V_t=\big(\langle\nu_t,\cos\rangle,\ \langle\nu_t,\sin\rangle\big),\qquad \vec V_t=v_t(\cos\theta_t,\sin\theta_t).$$

Filopodia evolve like an adaptive structured population with logistic resource limitation at capacity $\lambda$:

- *creation*: new filopodia appear isotropically, with intensity $\frac{c}{2\pi}(1-N_t/\lambda)_+\,d\theta$ in direction $\theta\in[0,2\pi)$, so at total rate $c(1-N_t/\lambda)_+$. The source's (4)–(5) print the intensity $c(1-N_t/\lambda)_+\,d\theta$, whose total rate $2\pi c(1-N_t/\lambda)_+$ is incompatible with its moment and jump-rate bounds in $c$ (for $N_0=0$, $r\equiv0$, $d=0$ and $\lambda\to\infty$ one gets $\mathbb E N_T\to2\pi cT>cT$); the page normalizes the intensity so that those bounds hold;
- *reproduction*: each filopodium of direction $\theta_i$ reproduces at rate $r(t,\theta_i;\nu_t)(1-N_t/\lambda)_+$, the offspring keeping the direction with probability $1-\mu$ and otherwise taking a direction drawn from a kernel $g(\cdot;\theta_i)$ around $\theta_i$;
- *death*: each filopodium disappears at rate $d$.

Polarization enters through the reproduction rate. Write $f(\cdot;m,\kappa)$ for the von Mises density with mean direction $m$ and concentration $\kappa$. Under a chemical gradient in direction $\theta_g$,

$$r(t,\theta_i;\nu_t)=r^*\Big(\big[1-\tfrac{\kappa_2(t)}{2\beta}\big]f(\theta_i;\theta_t,\kappa(v_t))+\tfrac{\kappa_2(t)}{2\beta}f(\theta_i;\theta_g,\kappa_2)\Big),\qquad \kappa(v)=\beta\tanh(\alpha v).$$

This mixes self-reinforcement of the current direction of motion with a bias towards the signal of sensitivity $\kappa_2(t)\le2\beta$. The process is constructed pathwise as the solution of a stochastic differential equation driven by independent Poisson point measures, with thinning by indicator functions and with individuals labelled through an ordering of their traits.

**Theorem.** Assume the reproduction rate is bounded, $0\le r\le\bar r$, and $\mathbb E[N_0]<\infty$.

1. *(Existence and moment bound.)* The Poisson-driven equation has a càdlàg solution $\nu\in\mathbb D(\mathbb R_+,\mathcal M)$, and for every $T>0$

$$\mathbb E\Big[\sup_{t\le T}N_t\Big]\le\mathbb E[N_0]\,e^{\bar rT}+\frac{c}{\bar r}\big(e^{\bar rT}-1\big)<\infty .$$

2. *(Uniqueness.)* Strong (pathwise) uniqueness holds.
3. *(Markov property.)* The solution is a Markov process with generator

$$L\Phi(\nu)=\frac{c}{2\pi}\Big(1-\tfrac{N}{\lambda}\Big)_+\int_0^{2\pi}\big[\Phi(\nu+\delta_\theta)-\Phi(\nu)\big]d\theta+\sum_{i=1}^{N}\Big(1-\tfrac{N}{\lambda}\Big)_+r(t,\theta_i;\nu)\Big[(1-\mu)\big(\Phi(\nu+\delta_{\theta_i})-\Phi(\nu)\big)+\mu\int\big(\Phi(\nu+\delta_z)-\Phi(\nu)\big)g(z;\theta_i)\,dz\Big]+d\sum_{i=1}^N\big[\Phi(\nu-\delta_{\theta_i})-\Phi(\nu)\big],$$

acting on bounded measurable $\Phi$, with $N=\langle\nu,1\rangle$. In particular the law of $(\nu_t)$ does not depend on the arbitrary ordering used to label filopodia.

Without interactions the filopodia count is an immigration–birth–death process with the branching property. The coupling through $\vec V_t$, both in $\theta_t$ and in $\kappa(v_t)$, destroys it, which is why the measure-valued description is needed. Simulations show repolarization towards the signal and memory effects when the gradient changes in time.

## Expansion

Existence uses the bounded rates. The stopping times $\tau_N$ at which the population first exceeds $N$ tend to infinity. Taking expectations of $\sup_{s\le t\wedge\tau_N}N_s$ and dropping deaths gives a linear Gronwall inequality, hence the bound and the absence of explosion. The solution is built step by step along the successive jump times $T_k$, which is possible a.s. because the global jump rate is at most $c+(\bar r+d)N_t$. This construction also yields pathwise uniqueness. For the generator, write $\Phi(\nu_t)$ as $\Phi(\nu_0)$ plus a sum of jumps, express each family of jumps as an integral against the corresponding Poisson measure, and take expectations of the compensated integrals.

These are the existence and uniqueness proposition and the Markov property proposition of Section 3 of the source.

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- C. Etchegaray, N. Meunier, "Crawling migration under chemical signalling: a stochastic particle model", arXiv:1808.00210 (2018). <https://doi.org/10.48550/arXiv.1808.00210>
