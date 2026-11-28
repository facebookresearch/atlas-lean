# Transport-cost inequalities

A probability measure $m$ satisfies Talagrand's quadratic transport-cost inequality with constant $C$
if $W_2(\mu, m)^2 \le C \operatorname{Ent}_m(\mu)$ for every probability measure $\mu$, where
$\operatorname{Ent}_m$ is the relative entropy. It satisfies the logarithmic Sobolev inequality with
constant $\alpha > 0$ if $2\alpha \int f \log f \, dm \le \int_{\{f > 0\}} |\nabla f|^2 / f \, dm$ for
every nonnegative Lipschitz density $f$. Otto and Villani (2000) showed, through Otto's formal
Riemannian calculus on the Wasserstein space, that the logarithmic Sobolev inequality with constant
$\alpha$ implies the transport inequality with constant $2/\alpha$, and proved the HWI inequality
relating entropy, Wasserstein distance and Fisher information. Gigli and Ledoux (2013) extended the
Otto–Villani theorem to complete separable metric measure spaces.

- [Local Lipschitz constant (slope)](local-lipschitz-constant.md)
- [Logarithmic Sobolev inequality](satisfies-log-sobolev.md)
- [Talagrand's quadratic transport-cost inequality](satisfies-talagrand.md)
- [Talagrand's inequality bounds $W_1$](wasserstein-one-sq-le.md)
- [Otto–Villani theorem](satisfies-talagrand-of-satisfies-log-sob.md)
- [HWI inequality](kl-div-le-wasserstein-mul-sqrt-fisher.md)
- [Gross' logarithmic Sobolev inequality](kl-div-with-density-std-gaussian-le.md)
- [Dirac masses satisfy the logarithmic Sobolev inequality](satisfies-log-sobolev-dirac.md)
- [Probability measures dominated by a Dirac mass](eq-dirac-of-absolutely-continuous.md)
- [Dirac masses satisfy the Talagrand inequality](satisfies-talagrand-dirac.md)

See also [Talagrand's transport inequality for the Gaussian measure](../talagrand-std-gaussian.md),
the model case, listed directly under concentration inequalities.

## Related topics

- [Wasserstein distances](../../../MeasureTheory/optimal-transport/wasserstein-distances/README.md):
  the distance $W_2$ of the transport inequality.
- [Displacement convexity](../../../MeasureTheory/optimal-transport/displacement-convexity/README.md):
  Otto and Villani's proofs read the log-Sobolev and HWI inequalities as convexity statements for
  the relative entropy on the Wasserstein space.
- [Large deviations](../../large-deviations/README.md): Sanov's theorem has the relative entropy
  as rate function, the quantity that transport inequalities compare with $W_2$.
- [Dirichlet forms](../../markov-chains/dirichlet-forms/README.md): the log-Sobolev constant of a finite Markov chain, defined through its Dirichlet form (Diaconis and Saloff-Coste).

- [Squared norm of an affine combination](convex-comb-norm-sq.md)

- [Prékopa–Leindler inequality for the standard Gaussian measure](lintegral-rpow-mul-le-std-gaussian.md)

- [Prékopa–Leindler inequality for the standard Gaussian on Euclidean space](lintegral-rpow-mul-le-std-gaussian-eucli.md)

- [Interpolation identity for the standard Gaussian density](std-gaussian-pdfreal-rpow-mul-rpow.md)
