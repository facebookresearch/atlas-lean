# Age-structured self-organized hydrodynamics of reversing myxobacteria

**Setting.** Myxobacteria glide in the plane at constant speed $v_0$, align *nematically* with neighbours, and reverse direction at a rate that depends on the density of oppositely moving cells (contact C-signalling), except during a refractory period of fixed length $T$ after each reversal. In the individual-based model each cell carries a position, an orientation $\Theta$ subject to nematic alignment of frequency $\nu$ and angular noise of strength $D$, and an age $s$ (time since the last reversal, measured in units of $T$). Let $d$ be the noise-to-alignment ratio and

$$M_{\bar\theta}(\theta)=\frac1{Z_d}\exp\Big(-\frac1{d\,|\cos(\theta-\bar\theta)|}\Big),\qquad \langle\phi\rangle_M=\frac{\int_0^{\pi/2}\phi(\theta)e^{-1/(d\cos\theta)}\,d\theta}{\int_0^{\pi/2}e^{-1/(d\cos\theta)}\,d\theta},$$

the generalized von Mises distribution. The reversal rate $\Lambda(\sigma,s)$ vanishes for $s\in[0,1]$ (refractory period) and depends on the opposing density $\sigma$ for $s>1$.

**Equilibria.** The nematic alignment operator has the equilibria $\bar f(\theta)=\rho_+M_{\bar\theta}(\theta)$ for $\cos(\theta-\bar\theta)>0$ and $\rho_-M_{\bar\theta}(\theta)$ for $\cos(\theta-\bar\theta)<0$: two counter-moving populations of densities $\rho_\pm(s)$ along a common axis $\bar\theta$ (defined modulo $\pi$). Its generalized collision invariants associated with $\bar\theta$ are spanned by the age-weighted indicators of the two half-circles and an explicit function $g(\theta-\bar\theta)$.

**Theorem (formal hydrodynamic limit).** In the hydrodynamic scaling of the kinetic equation (the source's (2.9)–(2.10)), with local interactions, the rescaled distribution $f^\varepsilon(x,\theta,s,t)$ solves

$$\varepsilon\,\partial_tf^\varepsilon+\nabla_x\cdot\big(v(\theta)f^\varepsilon\big)+\frac1T\partial_sf^\varepsilon=Q_{\rm al}(f^\varepsilon)+\varepsilon\,Q_{\rm rev}(f^\varepsilon),\qquad Q_{\rm al}(f)=\partial_\theta\Big(\operatorname{Sign}\big(\cos(\theta-\bar\theta_f)\big)\sin(\theta-\bar\theta_f)f+d\cos^2(\theta-\bar\theta_f)\,\partial_\theta f\Big),$$

where $\bar\theta_f$ is the local nematic mean direction of $f$, $\sigma_f^\pm$ the local masses of the two half-circles, $Q_{\rm rev}(f)=-\big(\Lambda(\sigma_f^-,s)\chi_{\{\cos(\theta-\bar\theta_f)>0\}}+\Lambda(\sigma_f^+,s)\chi_{\{\cos(\theta-\bar\theta_f)<0\}}\big)f$, and the age-zero boundary condition is

$$f(x,\theta,0,t)=T\int_0^\infty\Big(\Lambda(\sigma_f^-,s')\chi_{\{\cos(\theta-\bar\theta_f)<0\}}+\Lambda(\sigma_f^+,s')\chi_{\{\cos(\theta-\bar\theta_f)>0\}}\Big)f(x,\theta+\pi,s',t)\,ds'.$$

As $\varepsilon\to0$ (formally) $f^\varepsilon$ converges to $\bar f_{\rho_+,\rho_-,\bar\theta}$, where $\rho_\pm(x,s,t)\ge0$ and $\bar\theta(x,t)$ solve, written back in physical units,

$$\partial_t\rho_+ + d_1v_0\nabla_x\cdot(\rho_+v(\bar\theta))+\frac1T\partial_s\rho_+=-\Lambda(\sigma_-,s)\rho_+,$$

$$\partial_t\rho_- - d_1v_0\nabla_x\cdot(\rho_-v(\bar\theta))+\frac1T\partial_s\rho_-=-\Lambda(\sigma_+,s)\rho_-,$$

$$(\sigma_++\sigma_-)\partial_t\bar\theta+d_2v_0(\sigma_+-\sigma_-)(v(\bar\theta)\cdot\nabla_x)\bar\theta+\mu v_0\,v(\bar\theta)^\perp\cdot\nabla_x(\sigma_+-\sigma_-)=0,$$

with $v(\bar\theta)=(\cos\bar\theta,\sin\bar\theta)$, total group masses $\sigma_\pm=\int_0^\infty\rho_\pm\,ds$, renewal boundary conditions at age zero

$$\rho_+(x,0,t)=T\int_0^\infty\Lambda(\sigma_+,s)\rho_-\,ds,\qquad \rho_-(x,0,t)=T\int_0^\infty\Lambda(\sigma_-,s)\rho_+\,ds,$$

and coefficients

$$d_1=\langle\cos\rangle_M,\qquad d_2=\frac{\langle g\sin/\cos\rangle_M}{\langle g\sin/\cos^2\rangle_M},\qquad \mu=d\,\frac{\langle g\sin\rangle_M}{\langle g\sin/\cos^2\rangle_M}.$$

Reversed cells re-enter the opposite group at age zero, so the age structure carries the refractory memory that produces counter-propagating rippling waves.

## Expansion

The kinetic equation for $f(x,\theta,s,t)$ combines free transport, ageing at rate $1/T$, the nematic alignment operator and a reversal operator that moves mass between half-circles. At leading order $f$ lies in the kernel of the alignment operator, which forces the two-population generalized von Mises form. The alignment operator does not conserve momentum, so the evolution of $\bar\theta$ is closed with generalized collision invariants (the self-organized hydrodynamics method): integrating the kinetic equation against them removes the singular term and yields the transport equations for $\rho_\pm$ and the orientation equation. Discretizing age into a refractory class and a sensitive class gives a two-age macroscopic model whose numerics reproduce the reversal-driven waves seen in experiments.

## Sources

- Pierre Degond, Angelika Manhart, Hui Yu, "An age-structured continuum model for myxobacteria", arXiv:1702.06939 (2017), individual-based model (assumptions M1–M4), (2.9)–(2.10), Lemmas 2.1–2.2, Proposition 2.3 and the macroscopic continuous-age model in physical units ((2.17)–(2.18)), <https://doi.org/10.48550/arXiv.1702.06939>.
