# Weak solutions of elliptic equations

The $L^2$ theory of second-order elliptic equations in divergence form,
$Lu = -\sum_{i,j} (a^{ij} u_{x_i})_{x_j} + \sum_i b^i u_{x_i} + c u = f$ on a bounded open
$U \subseteq \mathbb{R}^n$. A weak solution is a function $u$ in the Sobolev space $H^1(U)$ with
$B[u, v] = \int_U \big(\sum a^{ij} u_{x_i} v_{x_j} + \sum b^i u_{x_i} v + c u v\big) = \int_U f v$
for all test functions $v$; the Dirichlet condition $u = 0$ on $\partial U$ is $u \in H^1_0(U)$.
Existence comes from the Lax–Milgram theorem: for $-\Delta$ with $n \ge 1$, Poincaré's inequality makes
$B[u, v] = \int_U Du \cdot Dv$ coercive on $H^1_0(U)$, so every $f \in L^2(U)$ has a unique weak
solution, which is also the minimizer of the Dirichlet energy $\int_U \tfrac12 |Du|^2 - f u$.
Regularity then upgrades weak solutions: for uniformly elliptic $L$ with $C^1$ principal coefficients, lower-order coefficients in $L^\infty(U)$ and $f \in L^2(U)$, a weak solution lies in
$H^2_{\mathrm{loc}}(U)$ with an interior estimate, and so solves $Lu = f$ almost everywhere.

The pages below give the abstract Hilbert-space form of the existence theorem (a gradient-type
operator with a Poincaré bound), the energy estimate and Dirichlet's principle, all from the
Lax–Milgram theorem; Sobolev spaces on domains, weak derivatives and weak solutions; existence in
$H^1_0(U)$ for Poisson's equation; and interior $H^2$ regularity.

- [Dirichlet form of a gradient operator](gradient-form.md)
- [Poincaré-type bound gives coercivity](is-coercive-gradient-form.md)
- [Existence and uniqueness of weak solutions of the abstract Poisson problem](exists-unique-weak-solution.md)
- [Energy estimate for the abstract Poisson problem](norm-le-of-weak-solution.md)
- [Dirichlet energy of a bilinear form and a load](energy.md)
- [Dirichlet's principle](is-min-on-energy-iff.md)
- [Test function on an open set](is-test-function-on.md)
- [Weak partial derivative on an open set](is-weak-partial-deriv-on.md)
- [Weak partial derivatives on the whole space](is-weak-partial-deriv-on-univ-iff.md)
- [Sobolev space $H^1(U)$](mem-h1-on.md)
- [$H^1$ on the whole space](mem-h1-on-univ-iff.md)
- [Sobolev space $H^1_0(U)$](mem-h10-on.md)
- [Weak solution of a divergence-form elliptic equation](is-weak-solution-on.md)
- [Coefficients of the Laplacian](laplacian-coeff.md)
- [The Laplacian is uniformly elliptic](laplacian-coeff-uniformly-elliptic.md)
- [Existence and uniqueness of weak solutions of the Dirichlet problem for Poisson's equation](exists-unique-weak-solution-poisson.md)
- [The hypotheses of interior $H^2$ regularity are satisfiable](interior-h2-regularity-hypotheses-laplac.md)
- [Interior $H^2$ regularity](interior-h2-regularity.md)
- [Elements of H¹₀(0, 1) as primitives of square-integrable derivatives](weak-h10.md)
- [Weak solutions of steady diffusion on (0, 1) exist and are unique](weak-diffusion-exists-unique.md)
- [Integration by parts of a primitive against a function of H¹₀(0, 1)](weak-diffusion-ibp.md)

## Related topics

- [Céa's lemma](../../numerical-analysis/c-a-s-lemma/README.md): the Lax–Milgram solution of a
  coercive variational problem and its Galerkin approximation in subspaces, the basis of the finite
  element method for these weak formulations.
- [Stampacchia's theorem](../../convex-analysis-and-variations/stampacchia-s-theorem/README.md):
  the extension of Lax–Milgram to variational inequalities on closed convex sets (obstacle
  problems).
- [Sobolev embedding theorem](../../function-spaces/sobolev-embedding-theorem/README.md): Sobolev
  spaces on $\mathbb{R}^n$ defined by weak derivatives, and their embedding into Hölder spaces.
- [Green's operator of the Dirichlet Laplacian on [0, 1]](../../ordinary-differential-equations/green-s-operator-of-the-dirichlet-laplacian-on-0/README.md):
  the one-dimensional Dirichlet problem $-u'' = f$, solved explicitly.
- [Pólya's conjecture on Laplacian eigenvalues](../p-lya-s-conjecture-on-laplacian-eigenvalues/README.md):
  the spectrum of the Dirichlet Laplacian, whose weak formulation lives on $H^1_0(U)$.
- [Bayesian inverse problems](../../../Probability/bayesian-statistics/bayesian-inverse-problems/README.md):
  the well-posedness theory there is stated for an abstract forward map; solution operators of
  elliptic equations are a standard example of such maps.
