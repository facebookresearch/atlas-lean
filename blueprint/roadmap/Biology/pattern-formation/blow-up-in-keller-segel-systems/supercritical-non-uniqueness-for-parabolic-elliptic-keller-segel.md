# Supercritical non-uniqueness for the parabolic–elliptic Keller–Segel system

**Model.** The parabolic–elliptic Keller–Segel system on $\mathbb R^n$ for a cell density $\rho$ and chemical concentration $c$ is

$$\partial_t\rho=\Delta\rho-\nabla\cdot(\rho\nabla c),\qquad -\Delta c=\rho .$$

It is invariant under $\rho_\lambda(x,t)=\lambda^2\rho(\lambda x,\lambda^2t)$, so $L^{n/2}(\mathbb R^n)$ is the critical Lebesgue space and $L^q$, $q<n/2$, is supercritical. Mild $L^q$-solutions are defined through the Duhamel formula.

**Theorem.** Let $n\in\{3,\dots,9\}$.
1. For every $q\in[1,n/2)$ there exist nontrivial initial data in $L^q(\mathbb R^n)$, a time $T\in(0,\infty)$, and two distinct mild $L^q$-solutions on $[0,T]$ with that datum. Hence the Cauchy problem is locally ill-posed in the whole supercritical range.
2. In the critical weak space there exist nontrivial data in $L^{n/2,\infty}(\mathbb R^n)$ and two distinct weak solutions in $L^\infty([0,T];L^{n/2,\infty}(\mathbb R^n))$ attaining the same datum in the sense of distributions.

**Instability mechanism.** For every $\eta\in(1,n/2)$, $\gamma\ge\eta$ and $\bar\lambda>0$ there is a stationary self-similar profile $\bar\Xi$ whose linearized operator $L_{\bar\Xi}$, realized on radial functions in $L^\eta\cap L^\gamma$, has a positive eigenvalue $\lambda\in(0,\bar\lambda]$ with an exponentially decaying eigenfunction, and spectrum contained in $\{\mathrm{Re}\,\mu\le\lambda\}$.

## Expansion

In self-similar variables, radial profiles reduce to an ODE whose solutions $u_\alpha$ are indexed by their central value $\alpha$; for large $\alpha$ the linearized ODE has many sign changes when $3\le n\le 9$, which is what produces an unstable eigenvalue. Following the Jia–Šverák program for Navier–Stokes, one solution is the self-similar profile itself and a second solution is built by growing the unstable mode out of the same initial datum, giving two different evolutions.

## Sources

- Eliseo Luongo and Umberto Pappalettera, "Spectral instability and non-uniqueness for the Keller-Segel system", arXiv:2605.13592 (2026), Theorems 1.2, 1.3 and 1.4, Section 2, <https://doi.org/10.48550/arXiv.2605.13592>.
