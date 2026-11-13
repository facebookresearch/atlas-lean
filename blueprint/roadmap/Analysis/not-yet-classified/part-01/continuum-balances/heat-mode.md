# Separated heat mode

**Separated heat mode** (MF08.3): `exp(-D λₖ t) uₖ(x)` on `[0, 1]` (length `L = 1`), with
the Dirichlet eigenfunction `uₖ = sineBasisFun k = √2 sin(kπ ·)` and its eigenvalue
`λₖ = dirichletLaplacianEigenvalue k = (kπ)²`, both reused from `GreensOperator` and
`DirichletSineEigenfunctions`; only the time factor is new.
