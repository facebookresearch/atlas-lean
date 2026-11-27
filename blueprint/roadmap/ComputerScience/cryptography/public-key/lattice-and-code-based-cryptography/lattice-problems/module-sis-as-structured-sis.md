# Module-SIS solutions are SIS solutions of the expanded matrix

Let $\mathbf{A} \in R_q^{d \times k}$ with $R_q = \mathbb{Z}_q[X]/(X^n+1)$, and let $\mathrm{rot}(\mathbf{A}) \in \mathbb{Z}_q^{dn \times kn}$ be its block-anticirculant expansion. For every $\mathbf{z} \in (\mathbb{Z}[X]/(X^n+1))^k$ and every bound $\beta$, $\mathbf{z}$ is a Module-SIS solution for $(\mathbf{A}, \beta)$ if and only if its coefficient flattening $\mathrm{flat}(\mathbf{z}) \in \mathbb{Z}^{kn}$ is a SIS solution for $(\mathrm{rot}(\mathbf{A}), \beta)$.

## Proof sketch

Flattening is a bijection that preserves being nonzero and the $\ell_\infty$ norm, and $\mathrm{flat}(\mathbf{A}\mathbf{z}) = \mathrm{rot}(\mathbf{A})\, \mathrm{flat}(\mathbf{z})$ by the coefficient formula for negacyclic multiplication.

## Depends on

- [Module-SIS and Ring-SIS](module-sis.md)
- [The short integer solution problem (SIS)](short-integer-solution-problem.md)

## Proof depends on

- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](negacyclic-ring.md)

## Sources

- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
