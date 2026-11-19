# Matrix-aware optimizers

Optimizers that treat a layer's weights as a matrix rather than as a vector of entries, and whose
updates are built from linear algebra of the gradient matrix: Muon steps along minus the canonical
polar factor of its momentum, which minimizes the pairing with the momentum over the unit
spectral-norm ball (uniquely when the momentum has full rank). The pages are
expositions of published methods; each names the linear algebra it relies on, and how, under
Informally uses. The polar factor and the iterations that compute it are under [polar
decomposition](../../../../LinearAlgebra/matrix-decompositions/polar-decomposition/README.md).
