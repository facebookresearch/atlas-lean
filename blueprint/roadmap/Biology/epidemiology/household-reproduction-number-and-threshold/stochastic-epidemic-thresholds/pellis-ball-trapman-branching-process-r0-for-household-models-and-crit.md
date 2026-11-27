# Critical vaccination coverage from the household reproduction number

Pellis, Ball and Trapman (2012) define $R_0$ through the branching process that approximates the early epidemic, with individuals placed in generations by their minimal path length from the initial infective (Eq. (2.3)); for the households model, [$R_0$ is the dominant eigenvalue](../tendsto-expected-cases-rpow.md) of the household matrix, [the household process survives with positive probability exactly when $R_0 > 1$](../extinction-prob-lt-one-iff.md), outside the singular case in which every individual has exactly one offspring almost surely (that deterministic process survives with $R_0 = 1$), and [$R_0$ and $R_*$ have the same threshold](../spectral-radius-threshold.md). For a multitype approximating process with mean offspring matrix $M$, Section 2.2 assumes that $M$ is positively regular (primitive): some power $M^k$ has every entry strictly positive. Then $R_0$, the Perron root of $M$, is a simple eigenvalue strictly larger in modulus than every other eigenvalue; mere irreducibility does not give this, since $M = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ is irreducible with eigenvalues $1$ and $-1$. A perfect vaccine given uniformly at random that blocks a fraction $p_c$ of infectious contacts turns the mean matrix into $(1 - p_c)M$, so the approximating process is critical exactly when $(1 - p_c)R_0 = 1$, that is $p_c = 1 - 1/R_0$ (Section 2.2); for a nonsingular process (one in which not every individual has exactly one offspring almost surely), it then dies out almost surely for every vaccination coverage at least $p_c$.

## Depends on

- [The household `R₀` is the dominant eigenvalue](../tendsto-expected-cases-rpow.md)

## Proof depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Expansion

1. Scaling of the mean offspring matrix by $1 - p_c$ under uniform vaccination, primitivity of $(1 - p_c)M$ for $p_c < 1$, and its Perron root $(1 - p_c)R_0$ as the strictly dominant eigenvalue.
2. The extinction criterion for a primitive, nonsingular multitype branching process at and below criticality.
3. The critical fraction $1 - 1/R_0$; vaccination of selected types calls for the type reproduction number instead.

## Sources

- L. Pellis, F. Ball and P. Trapman, Reproduction numbers for epidemic models with households and other social structures. I. Definition and calculation of $R_0$, Math. Biosci. 235 (2012), 85–97, Sections 2.2–3.2 and Eq. (2.3). <https://doi.org/10.1016/j.mbs.2011.10.009>
