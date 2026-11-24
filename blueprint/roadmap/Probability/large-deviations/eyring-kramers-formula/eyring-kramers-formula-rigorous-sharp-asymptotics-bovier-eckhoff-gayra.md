# Eyring–Kramers formula for reversible diffusions

Let $X$ solve $dX(t) = -\nabla F(X(t))\,dt + \sqrt{2\varepsilon}\, dW(t)$ in a domain of $\mathbb{R}^d$, where $F$ satisfies the growth condition (1.3) and the assumptions (H1), (ND) and (IB) of Bovier, Eckhoff, Gayrard and Klein (2004): finitely many local minima, saddle points between minima that are finite sets of isolated points, and non-degenerate Hessians at minima and saddle points. For a local minimum $x_i$, let $D$ be a closed set containing small balls around all minima $y_j$ with $F(y_j) \le F(x_i)$ and staying a fixed distance from the relevant saddle points. Theorem 3.2 of the source gives the mean hitting time $E_{x_i}\tau_D$ in terms of the saddle points; when there is a single saddle point $z^*$, with negative Hessian eigenvalue $\lambda_1^*(z^*)$, it reduces to the Eyring formula (Eq. (3.3))
$$E_{x_i}\tau_D = \frac{2\pi}{|\lambda_1^*(z^*)|}\sqrt{\frac{|\det\nabla^2 F(z^*)|}{\det\nabla^2 F(x_i)}}\; e^{[F(z^*) - F(x_i)]/\varepsilon}\,\bigl(1 + O(\varepsilon^{1/2}|\ln\varepsilon|)\bigr).$$
The proof rests on the sharp capacity estimate of Theorem 3.1 and the representation of mean hitting times through capacities and equilibrium potentials (Section 2).

## Expansion

1. The model: the reversible diffusion, its generator and invariant measure $e^{-F/\varepsilon}$, and assumptions (H1), (ND), (IB) with the definition of saddle points through gates (Definition 1.1).
2. The potential-theoretic representation of mean hitting times, Eqs. (2.22)–(2.28).
3. Theorem 3.1: sharp asymptotics of capacities by the Dirichlet principle near the saddle points.
4. Theorem 3.2 with several saddle points, a priori regularity estimates for mean times (Section 4), and the reduction to Eq. (3.3).

## Sources

- A. Bovier, M. Eckhoff, V. Gayrard and M. Klein, Metastability in reversible diffusion processes I: sharp asymptotics for capacities and exit times, J. Eur. Math. Soc. 6 (2004), 399–424, Theorems 3.1 and 3.2, Eq. (3.3). <https://doi.org/10.4171/jems/14>
