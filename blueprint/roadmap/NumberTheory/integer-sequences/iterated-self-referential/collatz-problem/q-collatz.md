# The q-analog of the 3x+1 map

For a power series $y = \sum_n y_n q^n \in \mathbb{F}_2[[q]]$,
write $y/q$ for the power series $\sum_n y_{n+1} q^n$: the constant term of $y$ is discarded and the
rest is divided by $q$. For power series $A, B \in \mathbb{F}_2[[q]]$, the map
$T_{A,B} : \mathbb{F}_2[[q]] \to \mathbb{F}_2[[q]]$ is defined by $T_{A,B}(x) = x/q$ if the
constant term of $x$ is $0$, and $T_{A,B}(x) = (Ax + B)/q$ otherwise.

When $A$ and $B$ have constant term $1$, the numerator $Ax + B$ has constant term $0$ whenever
$x$ has constant term $1$, so in that case the division by $q$ is exact.

## Sources

- Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer Sequences 28 (2025), Article 25.6.8, Section 1 (definition of `T_{A,B}`).
