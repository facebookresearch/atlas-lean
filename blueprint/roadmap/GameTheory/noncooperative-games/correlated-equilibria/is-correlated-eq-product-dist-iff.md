# The product correlated equilibria are the Nash equilibria

For mixed strategies $\sigma_i$, the product distribution $\prod_i \sigma_i(s_i)$ is a correlated
equilibrium if and only if no player can lower its expected cost by switching to a pure strategy,
that is, if and only if $\sigma$ is a mixed Nash equilibrium. Summing the correlated equilibrium
sums $\sigma_i(j)(\bar c_i(j) - \bar c_i(k)) \le 0$ over $j$ gives
$\mathbb E_\psi[c_i] \le \bar c_i(k)$; the other direction is
[Nash equilibria are correlated equilibria](is-correlated-eq-product-dist.md).

## Informally uses

- [Correlated-equilibrium sums of a product distribution](sum-product-dist-mul-switch-gain.md):
  the computation of the sums.
- [Expected cost under a product distribution](sum-product-dist-mul.md): the average over $j$.
- [Nash equilibria are correlated equilibria](is-correlated-eq-product-dist.md): the converse.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §2 ("Nash equilibria correspond to the special case where $\psi$ is a product
  measure").
