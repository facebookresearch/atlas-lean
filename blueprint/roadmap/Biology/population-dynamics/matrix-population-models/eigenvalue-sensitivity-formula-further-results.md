# Eigenvalue sensitivity formula: further results

The [eigenvalue sensitivity formula](eigenvalue-sensitivity-formula.md) is stated for the dominant eigenvalue of a projection matrix; it holds more generally. (1) A simple eigenvalue $\lambda$ of a real or complex $n \times n$ matrix $A$ is a differentiable function of the entries near $A$, by the implicit function theorem applied to the characteristic polynomial, of which $\lambda$ is a simple root. (2) For any simple eigenvalue, with right eigenvector $w$ ($Aw = \lambda w$) and left eigenvector $v$ ($v^TA = \lambda v^T$), $v^Tw \ne 0$ and $\partial\lambda/\partial a_{ij} = v_iw_j/(v^Tw)$, with the bilinear (not Hermitian) pairing. (3) If $\lambda \ne 0$, the elasticities $e_{ij} = \frac{a_{ij}}{\lambda}\frac{\partial\lambda}{\partial a_{ij}}$ sum to $1$, since $\sum_{i,j}a_{ij}v_iw_j = v^TAw = \lambda v^Tw$.

## Expansion

1. Simple roots of a polynomial depend smoothly on its coefficients, and the coefficients of the characteristic polynomial are polynomials in the entries.
2. Non-orthogonality of the left and right eigenvectors of a simple eigenvalue (otherwise $\lambda$ would have algebraic multiplicity at least two).
3. The derivative formula by differentiating $Aw = \lambda w$ and pairing with $v$.
4. The elasticity identity.

## Sources

- H. Caswell, *Sensitivity Analysis: Matrix Methods in Demography and Ecology*, Demographic Research Monographs, Springer, 2019, Sec. 3.3, eqs. (3.27)–(3.29), and Sec. 3.4, eqs. (3.42)–(3.46). <https://doi.org/10.1007/978-3-030-10534-1>
- Original result: H. Caswell, A general formula for the sensitivity of population growth rate to changes in life history parameters, Theor. Popul. Biol. 14 (1978), 215–230. <https://doi.org/10.1016/0040-5809(78)90025-4> The formula follows Caswell (2019), eq. (3.29).
