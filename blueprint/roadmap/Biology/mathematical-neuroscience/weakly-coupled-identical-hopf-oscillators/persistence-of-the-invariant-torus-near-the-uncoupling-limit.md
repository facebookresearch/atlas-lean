# Persistence of the invariant torus near the uncoupling limit

Consider two identical oscillators in Hopf normal form with $\mathbb Z_2$-symmetric coupling,

$$\dot z_1=z_1(\lambda+i\omega+\alpha_{01}|z_1|^2)+\epsilon\,G(z_1,z_2),\qquad \dot z_2=z_2(\lambda+i\omega+\alpha_{01}|z_2|^2)+\epsilon\,G(z_2,z_1),$$

$z_j\in\mathbb C$, where $G$ collects the coupling terms up to cubic order (linear and cubic terms in $z_1,z_2,\bar z_1,\bar z_2$ with coefficients $\alpha_{\epsilon k},\beta_{\epsilon k}$), $\alpha_{01}=\alpha_{01R}+i\alpha_{01I}$ with $\alpha_{01R}<0$ (supercritical) and $\lambda>0$.

**Uncoupled limit.** For $\epsilon=0$, with $s=|z_1|+|z_2|$, $d=|z_1|-|z_2|$ and phase difference $\Delta\varphi$,

$$\dot s=s\Bigl(\lambda+\tfrac{\alpha_{01R}}4(s^2+3d^2)\Bigr),\qquad \dot d=d\Bigl(\lambda+\tfrac{\alpha_{01R}}4(d^2+3s^2)\Bigr),\qquad \dot{\Delta\varphi}=-\alpha_{01I}\,sd .$$

The invariant sets are the origin $\mathcal S_0$ (unstable), the 2-torus $\mathcal T_0=\{|z_1|=|z_2|=\sqrt{-\lambda/\alpha_{01R}}\}$, which is filled with periodic orbits of the same period and has normal characteristic exponents $-2\lambda$ (double), and the two saddle periodic orbits $\mathcal S^2=\{z_2=0\}$, $\mathcal S^3=\{z_1=0\}$ with exponents $-2\lambda$ and $\lambda\pm i\omega$.

**Lemma.** For fixed $\lambda>0$ there is $\epsilon_0(\lambda)>0$ such that for $0\le\epsilon\le\epsilon_0$ the coupled system has a stable invariant 2-torus $\mathcal T_\epsilon$ that is $C^1$-close to $\mathcal T_0$, and hyperbolic saddle periodic orbits $\mathcal S^2_\epsilon,\mathcal S^3_\epsilon$ close to $\mathcal S^2,\mathcal S^3$.

## Expansion

In the uncoupled system the amplitudes relax independently to the Hopf radius at rate $2\lambda$ while the phases rotate rigidly, so $\mathcal T_0$ attracts in its normal directions much faster than anything happens along it (only a rotation): it is normally hyperbolic. Fenichel's theorem then gives a nearby invariant torus for small perturbations, and the hyperbolic orbits $\mathcal S^{2,3}$ persist by the implicit function theorem. The coupling selects what happens on $\mathcal T_\epsilon$: after averaging, the phase difference obeys a slow equation whose equilibria give in-phase and anti-phase locked states, while $\mathcal S^{2,3}_\epsilon$ are winner-take-all states. How these continue as $\epsilon$ grows, and how they produce the switching regimes of perceptual bistability models, is studied numerically and via the full normal form.

## Sources

- A. Pérez-Cervera, P. Ashwin, G. Huguet, T. M. Seara, J. Rankin, "The uncoupling limit of identical Hopf bifurcations with an application to perceptual bistability", Journal of Mathematical Neuroscience 9 (2019) 7, <https://doi.org/10.1186/s13408-019-0075-2>, PMCID PMC6682846. Eqs. (1)–(3) and (14)–(17), and Lemma 1.
