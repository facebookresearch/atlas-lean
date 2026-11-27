# Weyl law for self-adjoint Kimura diffusions

Let $P$ be a compact manifold with corners of dimension $d$ and $L$ a generalized Kimura diffusion operator, self-adjoint on $L^2(P; d\mu_L)$ and defined by a globally defined symmetric Dirichlet form, whose weights are strictly positive (they need not be constant along the boundary). Let $N(\lambda)$ count the eigenvalues of $-L$ that are at most $\lambda$, with multiplicity.

**Theorem (Epstein–Mazzeo, Theorem 5.3).** The heat operator $e^{tL}$ is trace class, and there is a dimensional constant $K_d$ such that

$$\lim_{t\to 0^+} t^{d/2}\, \mathrm{Tr}\, e^{tL} = K_d\, \mu_L(P).$$

Consequently

$$N(\lambda) = \lambda^{d/2} \left( \frac{K_d\, \mu_L(P)}{\Gamma(1 + d/2)} + o(1) \right) \qquad (\lambda \to \infty).$$

So the spectrum of a Kimura operator obeys Weyl's law with the Riemannian volume replaced by the total mass of the weighted measure $\mu_L$, whose density $\prod_i x_i^{b_i - 1}$ is determined by the mutation rates at the boundary.

## Depends on

- [Heat-kernel bounds for Kimura diffusions with positive weights](heat-kernel-bounds-for-kimura-diffusions-with-positive-weights.md)

## Expansion

The trace is $\int_P p_t(\xi,\xi)\, d\mu_L(\xi)$. On $P_\delta = \{\xi : \rho_i(\xi,\partial P) \ge \delta\}$ the operator is uniformly elliptic, so $t^{d/2} p_t(\xi,\xi) \to K_d$ uniformly there; this gives the lower bound $K_d\,\mu_L(P_\delta)$ for the liminf. For the upper bound, the Gaussian heat-kernel estimate gives $p_t(\xi,\xi) \le C/\mu_L(B^i_{\sqrt t}(\xi))$; bounding the volume of intrinsic balls from below in square-root coordinates shows $t^{d/2}\int_{P\setminus P_\delta} p_t(\xi,\xi)\,d\mu_L(\xi) \le C\delta$, uniformly in $t$. Letting $\delta \to 0$ gives the limit, and Karamata's Tauberian theorem converts the small-time trace asymptotics into the eigenvalue counting asymptotics.

## Sources

- C. L. Epstein and R. Mazzeo, *Harnack inequalities and heat-kernel estimates for degenerate diffusion operators arising in population biology*, *Applied Mathematics Research eXpress* 2016(2) (2016), 217–280, <https://doi.org/10.1093/amrx/abw002>; preprint arXiv:1406.1426, <https://doi.org/10.48550/arXiv.1406.1426>.
