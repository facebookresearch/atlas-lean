# Module-LWE is LWE over the negacyclic ring

For every distinguisher, its decision Module-LWE advantage for secret law $\chi_s$ and error law $\chi_e$ over $R_q = \mathbb{Z}_q[X]/(X^n+1)$ equals its decision-LWE advantage over the finite commutative ring $R_q$ (matrices and vectors with entries in $R_q$) for the same laws. Moreover the coefficient flattening of a Module-LWE sample $(\mathbf{A}, \mathbf{A}\mathbf{s}+\mathbf{e})$ is the structured LWE sample $(\mathrm{rot}(\mathbf{A}), \mathrm{rot}(\mathbf{A})\,\mathrm{flat}(\mathbf{s}) + \mathrm{flat}(\mathbf{e}))$ over $\mathbb{Z}_q$.

## Proof sketch

Both games are the same probabilistic experiment once $R_q$ is viewed as a ring of scalars; the flattening statement is the identity $\mathrm{flat}(\mathbf{A}\mathbf{s}) = \mathrm{rot}(\mathbf{A})\,\mathrm{flat}(\mathbf{s})$.

## Depends on

- [Decision Module-LWE](decision-module-lwe.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [The negacyclic ring $\mathbb{Z}_q[X]/(X^n+1)$](negacyclic-ring.md)

## Sources

- Vadim Lyubashevsky, Chris Peikert and Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", Advances in Cryptology – EUROCRYPT 2010, 2010.
- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
