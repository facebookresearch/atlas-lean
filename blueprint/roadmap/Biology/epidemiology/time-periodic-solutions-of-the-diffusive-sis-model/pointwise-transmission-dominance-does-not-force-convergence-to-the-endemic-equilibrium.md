# Pointwise transmission dominance does not force convergence to the endemic equilibrium

**Model.** On an interval $(0,\ell)$ with homogeneous Neumann boundary conditions, the spatially heterogeneous SIS model with standard incidence is

$$S_t = d_S S_{xx} - \beta(x)\frac{SI}{S+I} + \gamma(x)I, \qquad I_t = d_I I_{xx} + \beta(x)\frac{SI}{S+I} - \gamma(x)I,$$

with diffusion rates $d_S, d_I > 0$ and positive transmission and recovery rates $\beta(x)$, $\gamma(x)$. The total population $M = \int_0^\ell (S+I)\,dx$ is conserved.

**Theorem.** For every $d_S > 0$ there exist $d_I > d_S$ and smooth time-independent coefficients $\widehat\beta, \widehat\gamma$ with

$$\widehat\beta(x) > \widehat\gamma(x) > 0 \qquad \text{for all } x \in [0,\ell],$$

such that for every total population $M > 0$ the system has a unique endemic equilibrium **and** a strictly positive classical solution that is periodic and nonconstant in time.

**Path lemma.** Let $(s,h)$ be a positive equilibrium for smooth $\beta > \gamma > 0$ whose linearization, restricted to zero-mass perturbations $\int_0^\ell (u+v)\,dx = 0$, has an eigenvalue with positive real part. Along the path $\beta_\tau = \tau\beta$, $\gamma_\tau = \gamma + (\tau-1)\beta s/(s+h)$, $\tau \ge 1$, which keeps $(s,h)$ an equilibrium and keeps $\beta_\tau > \gamma_\tau$, there are $\tau_* \in (1,\tau_1)$ and $\tau_j \to \tau_*$ for which the system with coefficients $(\beta_{\tau_j},\gamma_{\tau_j})$ has nonconstant positive periodic solutions of the same total mass, converging uniformly to $(s,h)$.

## Expansion

Uniqueness of the endemic equilibrium does not imply its global stability: with $d_I > d_S$ a periodic orbit can coexist with it even though transmission beats recovery at every point. The construction runs in reverse: first build (by an inverse construction) coefficients with an unstable endemic equilibrium under $\beta > \gamma$. Then follow the coefficient path, along which large $\tau$ restores stability, so the number of unstable eigenvalues changes at some $\tau_*$. A center-type invariant-surface (normal form) reduction at $\tau_*$ and a generalized Hopf bifurcation argument produce small-amplitude periodic orbits near $\tau_*$. Scaling invariance of standard incidence then transfers the result to every total mass $M$.

## Sources

- Fang Li, Pengfei Song, Kexin Zhang and Maolin Zhou, "Time-periodic solutions of an SIS epidemic model", arXiv:2610.29062 (2026), Theorems 1.1 and 2.1, <https://doi.org/10.48550/arXiv.2610.29062>.
