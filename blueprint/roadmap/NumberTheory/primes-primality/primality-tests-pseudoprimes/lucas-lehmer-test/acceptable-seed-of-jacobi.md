# Lucas–Lehmer test with a general seed

Let $n \ge 3$ be an odd natural number, let
$M_n = 2^n - 1$, and let $s_1$ be an integer. Define $s_{k+1} = s_k^2 - 2$ for $k \ge 1$. If the
Jacobi symbols satisfy $\left(\frac{s_1 + 2}{M_n}\right) = -1$ and
$\left(\frac{s_1 - 2}{M_n}\right) = 1$, then $M_n$ is prime if and only if $M_n$ divides
$s_{n-1}$.

In the terminology of Roettger and Williams, such a seed $s_1$ is acceptable: the Lucas–Lehmer
test started at $s_1$ decides the primality of $M_n$ (their Assertion A).

Proof: sufficiency is the order argument of the classical test. Let $q$ be the least prime factor
of $M_n$ and $D = s_1^2 - 4$. In the ring $(\mathbb{Z}/q\mathbb{Z})[\sqrt D]$, which has $q^2$
elements, $\omega = (s_1 + \sqrt D)/2$ is a unit with $\omega + \omega^{-1} = s_1$, so
$s_k = \omega^{2^{k-1}} + \omega^{-2^{k-1}}$. If $M_n \mid s_{n-1}$, then $\omega^{2^{n-1}} = -1$,
so $\omega$ has order $2^n$; hence $2^n < q^2$, so $q^2 > M_n$ and $M_n$ is prime. Necessity uses
the two Jacobi conditions and Frobenius conjugation, as in Lehmer (1930) and Roettger and Williams
(2025).

## Sources

- E. L. Roettger and H. C. Williams, "Some Remarks Concerning the Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem, lines 814–819; Assertion A at lines 187–190, https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex
- The order argument is adapted from the formal proof of the classical test ($s_1 = 4$) in Mathlib, `Mathlib/NumberTheory/LucasLehmer.lean`, by M. Carneiro, A. Irving, K. Morrison and A. Pahljina.
