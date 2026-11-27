# Weak Allee effect is necessary for Turing patterns in female harvesting–male stocking

**Model.** The female-harvesting, male-stocking (FHMS) strategy mimics the Trojan Y chromosome biocontrol by removing females and adding males of an invasive species. In dimensionless form, with female and male densities $f,m$, female birth fraction $r\in(0,1)$, mating rate $\alpha$, harvesting rate $h$ and stocking rate $0\le s<1$,

$$\frac{df}{dt}=r\alpha fm(1-f-m)-(1+h)f,\qquad \frac{dm}{dt}=(1-r)\alpha fm(1-f-m)+(s-1)m .$$

A *weak Allee effect* in females replaces the mating term $fm$ by $f^2m$:

$$\frac{df}{dt}=r\alpha f^2m(1-f-m)-(1+h)f,\qquad \frac{dm}{dt}=(1-r)\alpha f^2m(1-f-m)+(s-1)m .$$

Spatial versions add diffusion $d_1\Delta f$, $d_2\Delta m$ with Neumann boundary conditions.

**Results (ODE).** In both models solutions stay nonnegative and bounded, and, since $0\le s<1$, the extinction state $E_0=(0,0)$ is locally asymptotically stable (its eigenvalues are $-(1+h)$ and $s-1$; for $s>1$ it is unstable). With the weak Allee effect, the invader is eliminated through a saddle–node bifurcation as the harvesting rate $h$ increases through a critical value $h^*$; a Hopf bifurcation produces oscillations when the trace condition holds as $s$ varies. With the weak Allee effect the separatrix between extinction and persistence basins (the extinction boundary) need not be hyperbola-shaped, unlike in earlier mating models: in the source's numerical simulations it changes from the hyperbolic shape to a loop as the stocking rate $s$ increases (Section 3.3); the exact shape of the boundary is not determined analytically.

**Theorem (Turing instability).** For a positive homogeneous steady state with reaction Jacobian $J=(J_{ij})$, the four inequalities $J_{11}+J_{22}<0$, $\det J>0$, $d_2J_{11}+d_1J_{22}>0$ and $(d_2J_{11}+d_1J_{22})^2>4d_1d_2\det J$ are necessary for diffusion-driven instability; they hold if and only if some band of wavenumbers $k^2$ is unstable, and on the bounded domain with Neumann conditions diffusion-driven instability occurs if and only if, in addition, a Neumann eigenvalue of $-\Delta$ lies in that band (the source states the four inequalities as sufficient). A necessary condition is that $J_{11}$ and $J_{22}$ have opposite signs. The spatial FHMS model without an Allee effect never exhibits a Turing instability, whereas the model with the weak Allee effect does for suitable parameters. Hence the weak Allee effect is both necessary and sufficient (within this model family) for Turing patterns.

## Expansion

At an interior equilibrium of the model without an Allee effect, the self-interaction entries $J_{11}$ and $J_{22}$ cannot take opposite signs, so the classical activator–inhibitor structure required for Turing instability is absent. With mating term $f^2m$, female density reinforces its own growth, which allows the opposite-sign pattern of self-interactions, and sufficiently unequal diffusivities can then destabilize the homogeneous state.

## Sources

- Eric Takyi, Joydeb Bhattacharyya, Rana D. Parshad and Matthew A. Beauregard, "Mimicking the TYC strategy: Weak Allee effects, and a nonhyperbolic extinction boundary", arXiv:2006.10115 (2020), Sections 3–4 (FHMS model with and without weak Allee effect; saddle-node and Hopf bifurcation lemmas; Turing instability conditions and the theorems on presence and absence of Turing instability), <https://doi.org/10.48550/arXiv.2006.10115>.
