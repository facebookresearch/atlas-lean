# Lucas–Lehmer test with a general seed

Let $n \ge 3$ be an odd natural number, let
$M_n = 2^n - 1$, and let $s_1$ be an integer. Define $s_{k+1} = s_k^2 - 2$ for $k \ge 1$. If the
Jacobi symbols satisfy $\left(\frac{s_1 + 2}{M_n}\right) = -1$ and
$\left(\frac{s_1 - 2}{M_n}\right) = 1$, then $M_n$ is prime if and only if $M_n$ divides
$s_{n-1}$.

In the terminology of Roettger and Williams, such a seed $s_1$ is acceptable: the Lucas–Lehmer
test started at $s_1$ decides the primality of $M_n$ (their Assertion A).

Proof: Following Mathlib's Lucas-Lehmer order argument, sufficiency uses a quadratic extension
and the least prime factor; necessity uses the Jacobi conditions and Frobenius conjugation as in
Lehmer (1930) and Roettger-Williams (2025).

## Sources

- E. L. Roettger and H. C. Williams, "Some Remarks Concerning the Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem (label acceptableseed), lines 814–819; Assertion A (label assertionA) at lines 187–190, https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex
