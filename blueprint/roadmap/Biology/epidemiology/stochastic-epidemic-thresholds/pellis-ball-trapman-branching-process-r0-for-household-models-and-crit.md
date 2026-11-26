# Critical vaccination coverage from the household reproduction number

Pellis, Ball and Trapman (2012) define $R_0$ through the branching process that approximates the early epidemic, with individuals placed in generations by their minimal path length from the initial infective (Eq. (2.3)); for the households model, [$R_0$ is the dominant eigenvalue](../household-reproduction-number-and-threshold/tendsto-expected-cases-rpow.md) of the household matrix, [the household process survives exactly when $R_0 > 1$](../household-reproduction-number-and-threshold/extinction-prob-lt-one-iff.md), and [$R_0$ and $R_*$ have the same threshold](../household-reproduction-number-and-threshold/spectral-radius-threshold.md). For a multitype approximating process with mean offspring matrix $M$ and $R_0$ its Perron root, a perfect vaccine given uniformly at random that blocks a fraction $p_c$ of infectious contacts turns the mean matrix into $(1 - p_c)M$, so the approximating process is critical exactly when $(1 - p_c)R_0 = 1$, that is $p_c = 1 - 1/R_0$ (Section 2.2).

## Depends on

- [The household $R_0$ is the dominant eigenvalue](../household-reproduction-number-and-threshold/tendsto-expected-cases-rpow.md)

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Expansion

1. Scaling of the mean offspring matrix by $1 - p_c$ under uniform vaccination, and the Perron root of $(1 - p_c)M$.
2. The critical fraction $1 - 1/R_0$; vaccination of selected types calls for the type reproduction number instead.

## Sources

- L. Pellis, F. Ball and P. Trapman, Reproduction numbers for epidemic models with households and other social structures. I. Definition and calculation of $R_0$, Math. Biosci. 235 (2012), 85–97, Sections 2.2–3.2 and Eq. (2.3). <https://doi.org/10.1016/j.mbs.2011.10.009>
