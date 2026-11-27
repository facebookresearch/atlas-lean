# Two-type branching representation of the birth–death–shift process for transposable elements

**Model.** Copies of a transposable element (e.g. IS*6110* in *Mycobacterium tuberculosis*, observed as RFLP bands) evolve independently: each copy duplicates into a new genomic location at rate $\lambda$ (birth), moves to a new location at rate $\nu$ (shift), and is lost at rate $\mu$ (death). Genotyping a strain at two times records which bands (locations) are shared, so the observable state is $(X_1(t), X_2(t))$: the number of **old** copies still at their original locations and the number of **new** copies at locations not present initially. This is a continuous-time two-type branching process in which a type-1 (old) particle is replaced by one old and one new particle at rate $\lambda$, by one new particle at rate $\nu$, and dies at rate $\mu$; a type-2 (new) particle splits into two new particles at rate $\lambda$ and dies at rate $\mu$ (its shifts leave the new count unchanged).

**Transition probabilities.** The generating functions $\phi_j(t,s_1,s_2) = \mathbb E[s_1^{X_1(t)}s_2^{X_2(t)} \mid X(0) = e_j]$ satisfy the backward equations

$$\frac{d}{dt}\phi_1 = \lambda\phi_1\phi_2 + \nu\phi_2 + \mu - (\lambda+\nu+\mu)\phi_1, \qquad \frac{d}{dt}\phi_2 = \lambda\phi_2^2 + \mu - (\lambda+\mu)\phi_2,$$

with $\phi_j(0) = s_j$; $\phi_2$ is the explicit linear birth–death generating function, so $\phi_1$ solves a single linear ODE, and by independence $\phi_{jk} = \phi_1^j\phi_2^k$. Evaluating on $s_\ell = e^{2\pi i w_\ell}$ turns $\phi_{jk}$ into a Fourier series whose coefficients are the transition probabilities $p_{(j,k),(l,m)}(t)$, recovered by a discrete Fourier transform. This gives the exact likelihood of discretely observed processes, with rates linked to covariates by log-linear regression.

**Theorem (expected sufficient statistics).** Let $b_t$ be the number of births in $[0,t)$ and $H_j^+(r,s_1,s_2,t) = \mathbb E[r^{b_t}s_1^{X_1(t)}s_2^{X_2(t)} \mid X(0) = e_j]$. With $y_b = \big(\lambda + \mu + \sqrt{(\lambda+\mu)^2 - 4\lambda\mu r}\big)/(2\lambda r)$,

$$H_2^+ = y_b + \Big[\frac{-\lambda r}{2\lambda r y_b - \lambda - \mu} + \Big(\frac{1}{s_2 - y_b} + \frac{\lambda r}{2\lambda r y_b - \lambda - \mu}\Big)e^{-(2y_b\lambda r - \lambda - \mu)t}\Big]^{-1},$$

and $H_1^+$ solves $\frac{d}{dt}H_1^+ = \lambda r H_1^+H_2^+ + \nu H_2^+ + \mu - (\lambda+\mu+\nu)H_1^+$ with $H_1^+(0) = s_1$. Analogous closed forms hold for the numbers of shifts and deaths and for the total particle time. Differentiating in $r$ at $r = 1$ gives the conditional expectations of these sufficient statistics given the endpoints, which drive an EM algorithm for the rates.

## Expansion

Old and new copies are distinguishable through the band patterns, and since each copy acts independently the old/new counts form a branching process; births and deaths of new copies follow the linear birth–death process, whose generating function solves a Riccati equation in closed form. Marking each birth with a factor $r$ modifies the offspring generating function to $\lambda r s^2 + \mu - (\lambda+\mu)s$ for new particles, again a Riccati equation solved explicitly, with $y_b$ its fixed point. For old particles the equation is linear in $H_1^+$ once $H_2^+$ is known. The Fourier inversion avoids repeated numerical differentiation of generating functions, which is unstable.

## Sources

- Jason Xu, Peter Guttorp, Midori Kato-Maeda, Vladimir N. Minin, "Likelihood-Based Inference for Discretely Observed Birth-Death-Shift Processes, with Applications to Evolution of Mobile Genetic Elements", *Biometrics* 71 (2015), 1009–1021, <https://doi.org/10.1111/biom.12352>; preprint arXiv:1411.0031, <https://doi.org/10.48550/arXiv.1411.0031>. Numbering of the arXiv version: Section 2 (birth–death–shift model, two-type branching formulation, generating functions and Fourier inversion, Theorem 2.1), Appendices A–B.
