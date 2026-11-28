# Well-posedness and mass bounds for a plasticity-structured cell population model

**Model.** Cells carry a trait $z = (x, y, \theta)$: viability $x$, fecundity $y$ and plasticity $\theta$, with $(x, y) \in \Omega = \{C(x, y) \le K\} \subset [0,1]^2$ (a constraint between traits) and $\theta \in [0,1]$, so $z \in D = \Omega \times [0,1]$. The density $n(t, z) \ge 0$ solves

$$\partial_t n + \nabla \cdot \big(V n - A(\theta)\nabla n\big) = \big(r(z) - d(z)\rho(t)\big) n, \qquad \rho(t) = \int_D n(t, z)\,dz,$$

with zero-flux boundary condition $(V n - A(\theta)\nabla n)\cdot \mathbf{n} = 0$ on $\partial D$ and $n(0, \cdot) = n_0$. Here $A(\theta) = \mathrm{diag}(a_{11}(\theta), a_{22}(\theta), a_{33})$ models non-genetic epimutations (strictly positive, $a_{11}, a_{22}$ non-decreasing in $\theta$), $V(t, z)$ is a continuously differentiable stress-induced drift, and $0 < r_- \le r(z) \le r_+$, $0 < d_- \le d(z) \le d_+$.

**Theorem.** For every non-negative $n_0 \in L^p(D)$ with $p > 2$, the problem has a unique global non-negative weak solution

$$n \in C([0,T]; L^2(D)) \cap L^2(0,T; H^1(D)) \cap H^1(0,T; H^1(D)')$$

for every $T > 0$. It is the $L^2(D_T)$ limit, as the cell size $h \to 0$, of a finite-volume semi-discretisation, whose total mass obeys

$$\min\Big\{\rho(0), \frac{r_-}{d_+}\Big\} \le \rho_h(t) \le \max\Big\{\rho(0), \frac{r_+}{d_-}\Big\}, \qquad t \ge 0.$$

An implicit time discretisation with step $\Delta t < 1/(r_+ + d_+\bar\rho + d_+\bar\rho^2)$, where $\bar\rho$ is the upper mass bound, also has a unique non-negative solution converging as $\Delta t \to 0$.

## Expansion

Integrating the finite-volume system over all cells cancels the conservative flux terms, leaving $\rho_h' = \sum_j (r_j - d_j \rho_h) h^3 \nu_j$, so $(r_- - d_+\rho_h)\rho_h \le \rho_h' \le (r_+ - d_-\rho_h)\rho_h$ and the logistic comparison gives the mass bounds; these rule out finite-time blow-up of the Lipschitz ODE system. Discrete gradient and $L^2$ estimates give compactness, and the limit is a weak solution; uniqueness follows from the variational formulation and the mass bound. For the implicit scheme the step-size condition makes the linear system matrix an M-matrix, preserving positivity. Numerically the model can split an initially unimodal population into two trait clusters, read as bet hedging.

## Sources

- F. E. Alvarez, J. A. Carrillo, J. Clairambault, *Evolution of a structured cell population endowed with plasticity of traits under constraints on and between the traits*, J. Math. Biol. 85 (2022), 64 (Eqs. (1)–(4), Theorems 1–2, Propositions 3–5, Theorem 15). <https://doi.org/10.1007/s00285-022-01820-5> (PMCID: PMC9636305)
