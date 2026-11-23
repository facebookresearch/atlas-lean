# Grm

The genetic relationship matrix (GRM) of Yang et al. (2010) built from a (standardized)
genotype matrix `X : Matrix (Fin N) (Fin M) ℝ` (individuals × markers):
`A_ij = (1 / M) ∑_k X_ik X_jk`, i.e. `A = X Xᵀ / M`.
