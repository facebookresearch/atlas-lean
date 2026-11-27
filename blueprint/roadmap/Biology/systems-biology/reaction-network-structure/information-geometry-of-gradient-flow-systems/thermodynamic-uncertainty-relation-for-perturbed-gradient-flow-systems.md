# Thermodynamic uncertainty relation for perturbed gradient flow systems

**Setting.** Let $\mathcal H = (V, E)$ be a finite oriented hypergraph with divergence $\mathrm{div}: \mathbb R^E \to \mathbb R^V$ and gradient $\mathrm{grad} = -\mathrm{div}^*$, let $\mathcal X$ be the space of positive measures on $V$, and let $\mathcal E: \mathcal X \to \mathbb R$ be a driving functional. A dissipation function $\Psi^*(x, f)$ on forces, with Legendre dual $\Psi(x, j)$ on fluxes, is strictly convex, superlinear, even and vanishes only at $0$ in its second argument. The *perturbed gradient flow* is

$$\dot x = -\mathrm{div}\,j, \qquad j = D_f\Psi^*(x, f_x), \qquad f_x = \mathrm{grad}\big[-D_x\mathcal E(x)\big] + f^{\mathrm{ex}}_x,$$

with a perturbation force field $f^{\mathrm{ex}}$. The dissipation rate is $\sigma(x, j) = \Psi(x, j) + \Psi^*(x, f_x) = \langle j, D_j\Psi(x, j)\rangle$, and the Hessian $g^{\mathcal J}_{x,j} = D^2_j\Psi(x, j)$ is a Riemannian metric on flux space. The relative precision of the flux is $\mathcal P_x(j) = j^T[\mathrm{Cov}_x(j)]^{-1}j$ with the flux covariance given by $[\mathrm{Cov}_x(j)]^{-1} = \frac12 D^2_j\Psi(x, j)$, so $\mathcal P_x(j) = \frac12\|j\|^2_{g^{\mathcal J}_{x,j}}$.

**Integral representation.** $\sigma(x, j) = \int_0^1 \|j\|^2_{g^{\mathcal J}_{x,\tau j}}\,d\tau$.

**Lemma (thermodynamic uncertainty relation).** If $\|j\|_{g^{\mathcal J}_{x,\tau j}} \ge \|j\|_{g^{\mathcal J}_{x,j}}$ for all $\tau \in [0,1]$, then

$$\tfrac12\sigma(x, j) \ge \mathcal P_x(j).$$

**Chemical reaction networks.** For a reversible mass-action network with stoichiometric matrix $-\mathrm{div}$, energy $\mathcal E(x) = \sum_i x_i\log(x_i/x_i^*) - x_i + x_i^*$ and cosh-type dissipation with frequency $\omega_r(x)$ per reaction, one has $\|j\|_{g^{\mathcal J}_{x,\tau j}} = \sum_r 2j_r^2/\sqrt{(\tau j_r)^2 + 4\omega_r^2}$, which is nonincreasing in $\tau$, so the condition holds and the uncertainty relation applies to all such networks (and more generally to cosh-type gradient flow systems).

**Theorem (moduli of perturbations).** Two perturbation fields are equivalent when they produce the same dynamics; the moduli space of continuous perturbation fields is the set of continuous sections of the subbundle of the flux bundle with fibers $\ker[\mathrm{div}]$, that is, of cycle fluxes. This generalizes Schnakenberg's decomposition of nonequilibrium steady-state forces into cycle components.

## Expansion

Integrating $\frac{d}{d\tau}D_j\Psi(x, \tau j) = D^2_j\Psi(x, \tau j)\,j$ from $0$ to $1$ and using $D_j\Psi(x, 0) = 0$ gives $D_j\Psi(x, j) = \int_0^1 D^2_j\Psi(x, \tau j)j\,d\tau$; pairing with $j$ yields the integral representation of $\sigma$, which is the symmetrized Bregman divergence of $\Psi$. Under the monotonicity hypothesis the integrand is bounded below by its value at $\tau = 1$, which is $2\mathcal P_x(j)$. For cosh dissipation the metric weight $1/\sqrt{(\tau j_r)^2 + 4\omega_r^2}$ grows as $\tau$ decreases, which is why mass-action networks satisfy the relation. For the moduli statement, the equivalence classes of perturbation forces at each point are the leaves of a foliation of force space dual (under the Legendre transform) to a foliation of flux space; the leaf through zero force corresponds to the divergence-free fluxes, so each class is labeled by a cycle flux.

## Sources

- D. Loutchko, K. Sugie and T. J. Kobayashi, "Information geometry of perturbed gradient flow systems on hypergraphs: A perspective towards nonequilibrium physics", *Information Geometry* 9(2) (2026), 781–813, Sections 2.2 and 2.3, Example 2.1, Theorem 3.1, Section 4.2.1, Lemma 4.1 and Example 4.1, <https://doi.org/10.1007/s41884-026-00221-7> (preprint arXiv:2510.27268).