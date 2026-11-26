# Steady states and global stability of pump-leak models of cell volume

**Model.** A cell of volume $v$ contains $N$ ion species with concentrations $c_k$ and valences $z_k$, and an amount $A$ of impermeant organic solute of valence $z$. It is bathed in a fixed extracellular medium with concentrations $c_k^{\rm e}>0$ satisfying $\sum_kz_kc_k^{\rm e}=0$. With membrane potential $\phi$ and chemical potential jumps $\mu_k=\ln(c_k/c_k^{\rm e})+z_k\phi$, the (dimensionless) **pump-leak model** is the differential-algebraic system

$$\frac{d}{dt}(vc_k)=-j_k-p_k,\qquad \sum_kz_kc_k+\frac{zA}{v}=0,\qquad \frac{dv}{dt}=-j_{\rm w}(\pi_{\rm w}),\quad \pi_{\rm w}=\sum_kc_k^{\rm e}-\Big(\sum_kc_k+\frac Av\Big),$$

with passive fluxes $j_k$, active (pump) fluxes $p_k$ and osmotic water flux $j_{\rm w}$.

**Free energy identity.** Solutions satisfy

$$\frac{dG}{dt}=-\sum_k\mu_k(j_k+p_k)-\pi_{\rm w}j_{\rm w},\qquad G=v\Big[\sum_k\Big(c_k\big(\ln\tfrac{c_k}{c_k^{\rm e}}-1\big)+c_k^{\rm e}\Big)+\frac Av\Big(\ln\frac Av-1\Big)\Big].$$

**Theorem (linear fluxes).** Let $j=L\mu$ with $L$ symmetric positive definite, $j_{\rm w}=\zeta\pi_{\rm w}$ with $\zeta>0$, and constant pump vector $p$. Put $q=L^{-1}p$, and let $f(\phi)=\sum_kc_k^{\rm e}\big(e^{-q_k-z_k\phi}-1\big)$, which has a unique minimizer $\phi_{\min}$.

1. If $f_{\min}=f(\phi_{\min})<0$, there is exactly one steady state. It is globally asymptotically stable, the approach is exponential, and the linearization is diagonalizable with real negative eigenvalues.
2. If $f_{\min}>0$, there is no steady state and $v(t)\to\infty$ for every solution: the cell swells without bound.
3. If $f_{\min}=0$, then $v(t)\to\infty$ and $c_k(t)\to c_k^{\rm e}e^{-q_k-z_k\phi_{\min}}$.

The same dichotomy holds for two-membrane epithelial models with $L=L_{\rm m}+L_{\rm s}$ and $\zeta=\zeta_{\rm m}+\zeta_{\rm s}$.

**Theorem (general fluxes, weak pumps).** Suppose $j_k(\phi,0)=0$, $j_{\rm w}(0)=0$, $j_{\rm w}'(0)>0$, and $\partial j/\partial\mu(\phi,0)$ is symmetric positive definite for all $\phi$. Let the pump be $\alpha p$. If $\big\langle c^{\rm e},(\partial j/\partial\mu)^{-1}p\big\rangle>0$ at $\phi=0$, $\mu=0$, then for all sufficiently small $\alpha>0$ there is a steady state with $v>0$, and it is exponentially asymptotically stable.

## Expansion

Without pumps, $G$ is a Lyapunov function and the cell relaxes to Donnan equilibrium only if the impermeant solute can be balanced osmotically, which generically fails: passive cells swell. Pumps supply the free energy that holds the volume finite. With linear fluxes, the shifted functional $\tilde G$ (with $\mu$ replaced by $\mu+q$) is convex in $(vc,v)$ and satisfies $d\tilde G/dt=-\langle\mu+q,L(\mu+q)\rangle-\zeta\pi_{\rm w}^2\le0$. A second Lyapunov function $J$ (the dissipation itself) blows up at the boundary of the positive orthant and rules out escape to zero concentrations. The sign of $f_{\min}$ decides whether electroneutrality and osmotic balance can hold simultaneously: $\pi_{\rm w}=0$ at the candidate steady state reduces to $f(\phi)=-A/v<0$. Pumping must therefore be strong enough, and in the right direction relative to the leaks, to keep $f_{\min}<0$; this is the mathematical form of the pump-leak hypothesis of Tosteson and Hoffman.

## Sources

- Yoichiro Mori, "Mathematical Properties of Pump-Leak Models of Cell Volume Control and Electrolyte Balance", arXiv:1104.4097 (2011), Section 2 (model, Proposition 2.1), Proposition 3.1, Lemmas 3.2–3.3, Proposition 3.4, Theorems 3.5, 3.7–3.8, Proposition 4.4 and Theorem 4.8, <https://doi.org/10.48550/arXiv.1104.4097>.
