# Nisan–Szegedy: Boolean functions of degree d depend on at most d·2^{d−1} coordinates

A Boolean function $f : \{-1,1\}^n \to \{-1,1\}$ of degree at most $d \ge 1$ has at most $d\, 2^{d-1}$ relevant coordinates (coordinates whose flip changes $f$ somewhere). Consequently every Boolean function depending on all $n$ variables has degree at least $\log_2 n - O(\log\log n)$.

## Proof sketch

Each relevant coordinate has influence at least $2^{1-d}$ by Schwartz–Zippel on the derivative, and the influences sum to $\mathbf{I}[f] \le d$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Proof depends on

- [Schwartz–Zippel on the cube and influences of low-degree functions](schwartz-zippel-on-the-boolean-cube.md)

## Sources

- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
