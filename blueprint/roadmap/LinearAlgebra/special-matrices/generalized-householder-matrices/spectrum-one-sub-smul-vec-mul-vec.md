# Spectrum, determinant and norm of a generalized Householder matrix

Let $v \in \mathbb{R}^n$ be a unit vector, $\|v\|_2 = 1$, let $\beta \in \mathbb{R}$ and let
$H = I - \beta v v^{\mathsf{T}}$. Then:

- $H v = (1 - \beta) v$, and $H$ is the identity on the hyperplane $v^{\perp}$;
- $\det H = 1 - \beta$ (for every $n \ge 1$);
- for $n \ge 2$, the spectrum of $H$ is $\{1, 1 - \beta\}$; when $\beta \ne 0$, the eigenvalue
  $1$ has multiplicity $n - 1$ with eigenspace $v^{\perp}$ and the eigenvalue $1 - \beta$ is
  simple with eigenvector $v$ (when $\beta = 0$, $H = I$);
- $\|x - \beta v v^{\mathsf{T}} x\|_2^2 = \|x\|_2^2 - \beta (2 - \beta) (v^{\mathsf{T}} x)^2$
  for every $x \in \mathbb{R}^n$, so the operator $2$-norm of $H$ is at most $1$ if and only if
  $\beta \in [0, 2]$.

For $\beta = 1$, $H$ is the orthogonal projection onto $v^{\perp}$; for $\beta = 2$, it is the
Householder reflection across $v^{\perp}$.

Proof: $H v = v - \beta v (v^{\mathsf{T}} v) = (1 - \beta) v$ and $H w = w$ for every $w \perp v$;
since $\mathbb{R}^n$ is the direct sum of the line spanned by $v$ and $v^{\perp}$, this gives the
spectrum, the multiplicities and the determinant. Expanding the square, with $v^{\mathsf{T}} v = 1$,
gives the norm identity: the norm is at most $1$ when $\beta (2 - \beta) \ge 0$, and $x = v$ shows
it exceeds $1$ otherwise.

For a nonzero vector $k$ that is not a unit vector, the same argument shows that
$I - \beta k k^{\mathsf{T}}$ has the eigenvalues $1$ (on $k^{\perp}$) and $1 - \beta \|k\|_2^2$ (on
$k$), with the same multiplicities when $\beta \ne 0$; it is the orthogonal projection onto
$k^{\perp}$ when $\beta \|k\|_2^2 = 1$ and the Householder reflection across $k^{\perp}$ when
$\beta \|k\|_2^2 = 2$.

Grazzi et al. state the norm bound for products of such matrices with unit vectors; the "if and
only if" for a single factor, and this page's proofs, are derived here.

## Background

- [Nonzero eigenvalues of matrix products AB and BA coincide](../../eigenvalues-and-canonical-forms/eigenvalues-of-the-products-ab-and-ba/nonzero-eigenvalues-of-ab-and-ba/has-eigenvalue-mul-iff-3.md):
  background, another route to the nonzero eigenvalue of $v v^{\mathsf{T}}$, which is that of
  $v^{\mathsf{T}} v = 1$; the multiplicities and the norm still need the direct argument above.

## Sources

- R. Grazzi, J. Siems, A. Zela, J. K. H. Franke, F. Hutter and M. Pontil, "Unlocking State-Tracking in Linear RNNs Through Negative Eigenvalues", ICLR 2025, arXiv:2411.12537 (version 5), Section 4.2, equation (2), Section 4.3, equation (3), and Proposition 1, item 1.
