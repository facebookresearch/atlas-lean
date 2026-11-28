# Cell–ECM mechanical model with a linear viscoelastic constitutive law

**Constitutive laws.** In one space dimension let $\sigma(t,x)$ be stress and $\varepsilon(t,x)$ strain. The generic four-parameter linear viscoelastic law is

$$a_2\partial_{tt}\sigma+a_1\partial_t\sigma+a_0\sigma=b_2\partial_{tt}\varepsilon+b_1\partial_t\varepsilon+b_0\varepsilon,\qquad a_i,b_i\ge0,$$

written $\mathcal L_a[\sigma]=\mathcal L_b[\varepsilon]$ with $\mathcal L_a=a_2\partial_{tt}+a_1\partial_t+a_0$ and $\mathcal L_b=b_2\partial_{tt}+b_1\partial_t+b_0$. It contains the linear elastic law $\sigma=E\varepsilon$, the viscous law $\sigma=\eta\partial_t\varepsilon$, Kelvin–Voigt $\sigma=E\varepsilon+\eta\partial_t\varepsilon$, Maxwell $\frac1E\partial_t\sigma+\frac\sigma\eta=\partial_t\varepsilon$, the standard linear solid $\frac1{E_2}\partial_t\sigma+\frac1\eta\bigl(1+\frac{E_1}{E_2}\bigr)\sigma=\partial_t\varepsilon+\frac{E_1}\eta\varepsilon$ and the Jeffrey model $\bigl(1+\frac{\eta_1}{\eta_2}\bigr)\partial_t\sigma+\frac E{\eta_2}\sigma=\eta_1\partial_{tt}\varepsilon+E\partial_t\varepsilon$.

**Model.** On $x\in[\ell,L]$ let $n(t,x)$ and $\rho(t,x)$ be normalized cell and ECM densities and $u(t,x)$ the displacement of the cell–ECM continuum. Cells diffuse with motility $D>0$, move up ECM gradients with haptotactic sensitivity $\alpha>0$, are advected with velocity $\partial_tu$, and grow logistically with rate $r>0$; the ECM is advected:

$$\partial_tn=\partial_x\bigl[D\partial_xn-n(\alpha\partial_x\rho+\partial_tu)\bigr]+rn(1-n),\qquad \partial_t\rho=-\partial_x(\rho\,\partial_tu).$$

At low Reynolds number the force balance is $\partial_x(\sigma_c+\sigma_m)+\rho F=0$, with cell traction stress, external tethering force and matrix stress

$$\sigma_c=\frac{\tau n}{1+\lambda n^2}\bigl(\rho+\beta\partial_{xx}\rho\bigr),\qquad F=-su,\qquad \mathcal L_a[\sigma_m]=\mathcal L_b[\partial_xu],$$

where $\tau>0$ is the mean traction per cell, $\lambda\ge0$ the contact inhibition of traction, $\beta$ the long-range traction constant and $s>0$ the elastic modulus of the substratum. Applying $\mathcal L_a$ to the force balance closes the system:

$$\mathcal L_b[\partial_{xx}u]=\mathcal L_a\Bigl[s\rho u-\partial_x\Bigl(\frac{\tau n}{1+\lambda n^2}(\rho+\beta\partial_{xx}\rho)\Bigr)\Bigr],$$

with periodic boundary conditions: $n$, $\rho$ and $u$ are smooth functions of $x$ that are periodic with period $L-\ell$ (equivalently, the problem is posed on a circle of length $L-\ell$), so that all their $x$-derivatives, the cell flux $D\partial_xn-n(\alpha\partial_x\rho+\partial_tu)$, the ECM flux $\rho\,\partial_tu$ and the total stress are periodic. Matching only the endpoint values of $n,\partial_xn,\rho,\partial_{xx}\rho,u,\partial_xu$ is not enough: on $[0,1]$ the fields $n=1$, $u=0$, $\rho=1+x(1-x)$ satisfy those equalities, but $\partial_x\rho$ takes the values $1$ and $-1$ at the two ends, so the haptotactic flux differs. This corrects the source's boundary conditions (17) as printed, which are exactly these six endpoint equalities, "$n(t,\ell)=n(t,L)$, $\partial_xn(t,\ell)=\partial_xn(t,L)$, $\rho(t,\ell)=\rho(t,L)$, $\partial^2_{xx}\rho(t,\ell)=\partial^2_{xx}\rho(t,L)$, $u(t,\ell)=u(t,L)$, $\partial_xu(t,\ell)=\partial_xu(t,L)$", and which the source says "ensure that the fluxes in Eqs. (10) and (11), and the overall stress … are periodic on the boundary": the cell flux contains $n\alpha\partial_x\rho$, and (17) does not constrain $\partial_x\rho$.

## Expansion

The elimination uses that $\mathcal L_a$ commutes with $\partial_x$, so $\mathcal L_a[\partial_x\sigma_m]=\partial_x\mathcal L_b[\partial_xu]=\mathcal L_b[\partial_{xx}u]$. Solid-like laws (elastic, Kelvin–Voigt, standard linear solid) have no permanent set; fluid-like ones (viscous, Maxwell, Jeffrey) allow unbounded creep. The coupling that can produce patterns is mechanical: traction compacts the matrix, compaction raises local matrix density, which raises traction and attracts cells by haptotaxis. Compare the purely chemical route of [Turing instability](../turing-patterns-and-diffusion-driven-instability/README.md).

## Sources

- C. Villa, M. A. J. Chaplain, A. Gerisch, T. Lorenzi, *Mechanical models of pattern and form in biological tissues: the role of stress–strain constitutive equations*, Bulletin of Mathematical Biology 83 (2021), <https://doi.org/10.1007/s11538-021-00912-5> (PMCID: PMC8154836). Section 2.2, equations (1)–(9) and Table 1; Section 3, equations (10)–(17); the model follows Murray, Oster and coworkers (1983, 1988) as cited there.
