# Lie symmetry classification of the flux-limited Keller–Segel system with time-varying decay

**Model.** In one space dimension, cells of density $u(x,t)$ follow a chemoattractant $v(x,t)$ with a saturating (flux-limited) chemotactic velocity and grow logistically. The chemoattractant decays at a prescribed time-dependent rate $\kappa(t)$, reflecting enzymatic regulation or environmental variability:

$$u_t = Du_{xx} - \big(u\,F(v_x)\big)_x + ru\Big(1 - \frac{u}{K}\Big),\qquad \tau v_t = v_{xx} - \kappa(t)v + u,\qquad F(p) = \frac{p}{\sqrt{1+p^2}},$$

with constants $D,\tau,r,K > 0$ and a smooth function $\kappa$.

**Theorem 1 (kernel and gauge symmetry).** For the class of such systems with $D,\tau,r,K$ fixed, the kernel Lie algebra (the symmetries shared by every member) is $\langle\partial_x\rangle$. Each fixed member also admits the $\kappa$-dependent gauge generator

$$G_\kappa = \Theta_\kappa(t)\,\partial_v,\qquad \Theta_\kappa(t) = \exp\Big(-\frac{1}{\tau}\int^t\kappa(s)\,ds\Big).$$

So for generic $\kappa$ the maximal Lie invariance algebra of a member is two-dimensional, $\langle\partial_x, G_\kappa\rangle$.

**Theorem 2 (complete classification).** Among Lie point symmetries of the equations, with no initial or boundary data imposed, the maximal algebra is larger than this generic one if and only if $\kappa(t) \equiv \kappa_0$ is constant. In that case the only additional generator is time translation:

$$A^{\max}_{\kappa_0} = \big\langle\partial_x,\ e^{-\kappa_0 t/\tau}\partial_v,\ \partial_t\big\rangle .$$

Degenerate limits $D = 0$, $\tau = 0$ or $r = 0$ fall outside this classification.

## Expansion

The gauge symmetry is checked directly. Since $u$ couples to $v$ only through $v_x$, the shift $v\mapsto v + \varepsilon\Theta(t)$ leaves the $u$-equation unchanged. It changes the $v$-equation by $\varepsilon(\tau\Theta' + \kappa\Theta)$, which vanishes exactly when $\Theta = \Theta_\kappa$. Solving the determining equations reduces the problem to a classifying relation in which a time-translation component $c_1\ne0$ is possible only if $\kappa_t = 0$. With constant decay, combinations of $\partial_t$ and $\partial_x$ give travelling-wave reductions $u = U(x - ct)$ and $v = V(x-ct) + a e^{-\kappa_0 t/\tau}$. The paper derives the optimal system of one-dimensional subalgebras and the corresponding similarity reductions to ODEs. For genuinely time-dependent decay, the available reductions come from the two-dimensional algebra $\langle\partial_x, G_\kappa\rangle$.

## Sources

- A. A. J. Al-Furaiji, G. Haghighatdoost and M. Bazghandi, "Similarity Solutions for the Flux limited Keller Segel System with Time Varying Chemical Decay Rate", arXiv:2605.21394 (2026), Section 4 (Theorems 1 and 2) and Sections 5–6 (optimal systems and reductions), <https://doi.org/10.48550/arXiv.2605.21394>.
