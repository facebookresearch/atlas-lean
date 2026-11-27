# Minimax property of the Chebyshev polynomials

If $p$ is a monic real polynomial of degree $n$ and $|p(x)| \le M$ for every $x \in [-1, 1]$,
then $M \ge 2^{1-n}$. Among monic polynomials of degree $n$, none is smaller on $[-1, 1]$ than
$2^{1-n} T_n$.

Proof: $2^{n-1} p / M$ is bounded by $1$ on $[-1, 1]$ and has leading coefficient
$2^{n-1}/M$, which by the extremal property of the leading coefficient of $T_n$ is at most
$2^{n-1}$.

## Background

- [Chebyshev equioscillation theorem (sufficiency)](../chebyshev-equioscillation-theorem/not-lt-of-equioscillates.md): the same fact seen as best approximation: $x^n - 2^{1-n}T_n$ is the best uniform approximation of $x^n$ by polynomials of degree $n - 1$, since $2^{1-n}T_n$ equioscillates at the $n + 1$ points $\cos(j\pi/n)$.
- [The Chebyshev bound for Krylov energy minimizers](../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/energy-norm-le-of-is-min-krylov.md): where the scaled Chebyshev polynomial gives the CG bound $2((\sqrt\kappa - 1)/(\sqrt\kappa + 1))^k$.

## Sources

- P. L. Chebyshev, Théorie des mécanismes connus sous le nom de parallélogrammes, Mém. Acad. Sci. Pétersb. 7 (1854), 539–568.
- Encyclopedia of Mathematics, Extremal properties of polynomials, https://encyclopediaofmath.org/wiki/Extremal_properties_of_polynomials.
- L. N. Trefethen, Approximation Theory and Approximation Practice, SIAM (2013; extended edition 2019), Chapters 3 and 10.
