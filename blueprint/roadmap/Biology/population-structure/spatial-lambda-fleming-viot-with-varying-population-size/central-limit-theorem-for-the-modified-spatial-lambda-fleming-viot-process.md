# Central limit theorem for the spatial Λ-Fleming–Viot process with fluctuating population size

**Model.** On the torus $\mathbb{T}^d$ with types in $[0,1]$, the *modified spatial $\Lambda$-Fleming–Viot process* (mSLFV) is a measure-valued process $\rho_t(z, dk)$ with local population size $n_t(z) = \int_{[0,1]} \rho_t(z, dk)$. Fix an impact $u \in (0,1)$, a radius $R > 0$, a mutation rate $\mu > 0$, and a growth function $r_x(n)$ that is bounded below, positive near $n = 0$, keeps $(1 + r_x(n))\,n < n_{\max}$, and has bounded $n$-derivatives up to order $4$. Reproduction events are the points $(t,x,w)$ of a Poisson point process on $\mathbb{R}_+\times\mathbb{T}^d\times[0,1]$ with intensity $(n_{\max}+1)\,dt\otimes dx\otimes dw$; with $\bar n(x,R) = \bar n_t(x,R)$ the average of $n_{t-}$ over the ball $B(x,R)$, an event is ignored if $w\ge(\bar n(x,R)+1)/(n_{\max}+1)$ and kept otherwise, so that events centered near $x$ occur at rate $\bar n(x,R)+1$. When it is kept, a parental type $k_0$ is drawn from the type distribution in $B(x,R)$, a proportion $u' = u/(\bar n(x,R)+1)$ of the mass in $B(x,R)$ dies, and a mass $u'(1 + r(\bar n(x,R)))\,\bar n(x,R)$ of type $k_0$ is added. Between events, mass mutates to a fresh uniform type at rate $\mu$. Let $V_R$ be the volume of $B(0,R)$.

**Population size limit.** Let $\delta_N\to0$. The rescaled process $\rho^N$ is obtained by running the mSLFV with parameters $u_N=u/N$, $\mu_N=\delta_N^2\mu/N$ and growth function $r^N_z=\delta_N^2\,r_{\delta_N z}$ ($z\in\delta_N^{-1}\mathbb{T}^d$), giving a process $p^N$, and setting $\rho^N_t(z,dk)=p^N_{Nt/\delta_N^2}(z/\delta_N,dk)$. Under this rescaling the population size satisfies $\lim_{N\to\infty}\mathbb{E}\big[\sup_{t\le T} d(n^N_t, n_t)\big] = 0$ for every $T>0$, with $d$ a metric for the vague topology, where $n_t$ is the solution of the reaction–diffusion equation

$$\partial_t n_t = u V_R \Big( \frac{R^2}{d+2}\, \Delta n_t + r(n_t)\, n_t \Big).$$

**Theorem (CLT).** Assume $N\delta_N^{2-d} \to \infty$ (and $N^{1/2}\delta_N^{1+d/2} \to \infty$). Let $\lambda$ be Lebesgue measure on $\mathbb{T}^d\times[0,1]$, write $\bar\psi(x,\varepsilon)$ for the average of $\psi$ over $B(x,\varepsilon)$ and $\bar{\bar\psi}(z,\varepsilon)$ for the average of $\bar\psi(\cdot,\varepsilon)$ over $B(z,\varepsilon)$, and define the double-average and growth operators

$$\mathcal{L}^N\psi(z) = uV_R\,\delta_N^{-2}\big(\bar{\bar\psi}(z,\delta_NR) - \psi(z)\big),\qquad \mathcal{R}^N_m\psi(z) = \frac{uV_R}{V_{\delta_NR}^2}\int_{B(z,\delta_NR)} r_x\big(\bar m(x,\delta_NR)\big)\int_{B(x,\delta_NR)}\psi(y)\,dy\,dx .$$

The deterministic approximation $m^N_t$ of $n^N_t$ is defined by

$$\langle m^N_t,\phi\rangle = \langle m^N_0,\phi\rangle + \int_0^t\big\langle m^N_s,\big(\mathcal{L}^N+\mathcal{R}^N_{m^N_s}\big)\phi\big\rangle\,ds,$$

and the process starts from $\rho^N_0=\lambda$ with $m^N_0=n^N_0$. The fluctuations $Z^N_t = \sqrt{N\delta_N^{2-d}}\,(\rho^N_t - \lambda\, m^N_t)$ converge in distribution in $D(\mathbb{R}_+, \mathcal{D}'(\mathbb{T}^d \times [0,1]))$ to the mild solution of

$$dZ_t = \Big[ u V_R\Big(\frac{R^2}{d+2}\Delta + r(n_t)\Big) Z_t - \mu Z_t + \big(\mu + u V_R\, n_t\, r'(n_t)\big)\, \mathcal{H} Z_t \Big] dt + dW_t, \qquad Z_0 = 0,$$

where $\mathcal{H} Z_t(\cdot) = \int_0^1 Z_t(\cdot, dk)$ and $W$ is a Gaussian field, white in time, with covariation

$$\langle \mathcal{Q}_t, \phi\otimes\phi\rangle = u^2 V_R^2 \int_{\mathbb{T}^d} \frac{n_t(z)^2}{n_t(z)+1} \int_{[0,1]} \Big(\phi(z,k) - \int_{[0,1]}\phi(z,k')\,dk'\Big)^2 dk\, dz .$$

Centering by $\lambda\,n^N_t$ instead of $\lambda\,m^N_t$ gives the same equation without the $\mathcal{H} Z_t$ term.

## Depends on

- [Isolation by distance](../../coalescent-theory/structured-coalescent/isolation-by-distance.md)

## Expansion

The generator of the rescaled process splits into a dispersal part, which becomes the Laplacian with coefficient $uV_R R^2/(d+2)$ (the variance of a uniform displacement in a ball), and a growth part, which becomes the reaction term. The fluctuation field is written as a stochastic integral against a worthy martingale measure plus error terms caused by the varying population size; the errors vanish because the population-size field converges, and tightness plus convergence of the quadratic variation give the Gaussian limit. The noise acts only on the type-centered part of test functions, because reproduction preserves local mass to first order.

## Sources

- Raphaël Forien and Bastian Wiederhold, "Central limit theorems describing isolation by distance under varying population size", ALEA Lat. Am. J. Probab. Math. Stat. 22 (2025), 283, <https://doi.org/10.30757/ALEA.v22-11>. Numbering follows the arXiv version, arXiv:2407.10211 (2024): Assumption 2.1, Definition 2.2, the operators (3.3)–(3.4), Proposition 3.2, the deterministic approximation (3.6), Theorem 3.3 and the remark after it, <https://doi.org/10.48550/arXiv.2407.10211>.
