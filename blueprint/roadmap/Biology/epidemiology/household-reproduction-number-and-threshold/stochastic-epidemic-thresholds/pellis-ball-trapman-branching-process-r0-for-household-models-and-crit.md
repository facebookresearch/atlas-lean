# Critical vaccination coverage for a random-mixing multitype branching approximation

Pellis, Ball and Trapman (2012) define reproduction numbers through the branching process that approximates the early epidemic, with individuals placed in generations by their minimal path length from the initial infective (Section 1). Section 2.2 treats random-mixing multitype populations: each individual has one of finitely many types, the early epidemic is approximated by a multitype branching process with mean offspring matrix $M$, whose entry $m_{ij}$ is the expected number of type-$j$ children of a type-$i$ individual, and $M$ is assumed positively regular (primitive): some power $M^k$ has every entry strictly positive. Write $\rho_M$ for the Perron root of $M$, which Section 2.2 calls $R_0$; it is a simple eigenvalue strictly larger in modulus than every other eigenvalue, while mere irreducibility does not give this, since $M = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ is irreducible with eigenvalues $1$ and $-1$. Assume, as Section 2.2 does, that all types have the same vaccine response and that a perfect vaccine is given uniformly at random, blocking a fraction $p$ of infectious contacts. Then the mean matrix becomes $(1 - p)M$, so the approximating process is critical exactly when $(1 - p)\rho_M = 1$, that is at the coverage $p_c = 1 - 1/\rho_M$ (Section 2.2); for a nonsingular process (one in which not every individual has exactly one offspring almost surely), it dies out almost surely for every vaccination coverage $p \ge p_c$.

This scaling needs the random-mixing hypothesis. In households models naive branching process approximations do not work (Section 2.3), so the scaling above does not apply to their basic reproduction number $R_0$, [the dominant eigenvalue of the household matrix](../tendsto-expected-cases-rpow.md). For households models, vaccinating a uniformly random fraction $1 - 1/R_0$ of the population with a perfect vaccine is in general insufficient to prevent large epidemics (Ball, Pellis and Trapman 2016).

## Proof depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Expansion

1. Scaling of the mean offspring matrix by $1 - p$ under uniform vaccination with equal vaccine response, primitivity of $(1 - p)M$ for $p < 1$, and its Perron root $(1 - p)\rho_M$ as the strictly dominant eigenvalue.
2. The extinction criterion for a primitive, nonsingular multitype branching process at and below criticality.
3. The critical fraction $1 - 1/\rho_M$; vaccination of selected types calls for the type reproduction number instead.
4. For households models, the insufficiency in general of uniform vaccination of a fraction $1 - 1/R_0$ (Ball, Pellis and Trapman 2016), as a separate statement.

## Sources

- L. Pellis, F. Ball and P. Trapman, Reproduction numbers for epidemic models with households and other social structures. I. Definition and calculation of $R_0$, Math. Biosci. 235 (2012), 85–97, Sections 1 and 2.2–2.3. <https://doi.org/10.1016/j.mbs.2011.10.009>
- F. Ball, L. Pellis and P. Trapman, Reproduction numbers for epidemic models with households and other social structures II: Comparisons and implications for vaccination, Math. Biosci. 274 (2016), 108–139. <https://doi.org/10.1016/j.mbs.2016.01.006>
