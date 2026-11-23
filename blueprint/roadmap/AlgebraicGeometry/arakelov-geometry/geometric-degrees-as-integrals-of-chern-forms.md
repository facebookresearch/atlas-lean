# Geometric degrees as integrals of first Chern forms

This node is still to be broken down: the statement is precise, but its proof is not.

Let $V$ be a projective complex variety, possibly singular, $Z \subseteq V$ an integral closed
subvariety of dimension $k$, and $\bar L_1, \dots, \bar L_k$ holomorphic line bundles on $V$ with smooth
hermitian metrics, smooth in the sense of local ambient extensions. Then the form $c_1(\bar L_1) \wedge
\dots \wedge c_1(\bar L_k)$ restricted to the regular locus $Z_{\mathrm{reg}}$ is integrable, and
$$\int_{Z_{\mathrm{reg}}} c_1(\bar L_1) \wedge \dots \wedge c_1(\bar L_k) = \deg\bigl( c_1(L_1) \cdots
c_1(L_k) \mid Z \bigr),$$
the intersection number of the line bundles on $Z$. Applied to $V = X(\mathbb{C})$ for a proper flat
scheme $X$ over $\mathbb{Z}$ and to the complex points of a horizontal cycle, it identifies the integral
in Chambert-Loir's recursion for arithmetic degrees, for the trivial line bundle with a variable
metric, with the geometric degree of the generic fibre; in particular it gives the effect of a constant
rescaling of a metric on an arithmetic intersection number.

A good expansion has pages for:

- Lelong's theorem that integration over $Z_{\mathrm{reg}}$ is a closed positive current $[Z]$ of
  locally finite mass (the [Poincaré–Lelong formula](../birational-geometry/poincare-lelong-formula.md)
  page recalls it);
- the Chern–Weil theorem that $c_1(\bar L)$ represents the first Chern class of $L$ in de Rham
  cohomology, and the fact that $[Z]$ represents the cohomology class of the cycle $Z$;
- the reduction to a smooth $Z$ by a [resolution of singularities](../birational-geometry/resolution-of-singularities-of-quasi-projective-varieties.md),
  which leaves both sides unchanged.

## Sources

- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), <https://arxiv.org/abs/1904.05630v3>: 2.3 (smooth metrics on singular
  complex spaces) and Theorem (2.5), pp. 2–4.
- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter III, (2.5)–(2.7)
  (currents of integration on analytic sets), p. 140.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the integrability and the identity, for powers of one
  line bundle with a smooth metric, inside `GlobalTheory.Published.ArDegree`.
