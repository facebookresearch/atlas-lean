# Hilbert basis of orthogonal polynomials on $(-1, 1)$

Let $L^2([-1, 1])$ be the real
Hilbert space of square-integrable real-valued functions on $[-1, 1]$ with respect to
Lebesgue measure. There is a Hilbert basis $(b_n)_{n \in \mathbb{N}}$ of $L^2([-1, 1])$ such
that for every $n \in \mathbb{N}$ there is a real polynomial $q_n$ of degree exactly $n$ (for
$n = 0$, a constant polynomial) with $b_n(x) = q_n(x)$ for almost every $x \in [-1, 1]$.

The normalized Legendre polynomials form such a basis.

## Sources

- - Mathlib `docs/undergrad.yaml`, section "Topology / Hilbert spaces", entry "example, classical Hilbert bases of orthogonal polynomials" (currently missing: empty entry, no Mathlib declaration). - NIST Digital Library of Mathematical Functions, §18.3, Table 18.3.1 (Legendre polynomials: weight `1` on `(-1, 1)`, `∫ P_n ^ 2 = 2 / (2n + 1)`). - E. Kreyszig, *Introductory Functional Analysis with Applications*, Wiley, 1978, §3.6 ("Total Orthonormal Sets and Sequences") and §3.7 ("Legendre, Hermite and Laguerre Polynomials": the normalized Legendre polynomials are a total orthonormal sequence in `L²[-1, 1]`). - https://en.wikipedia.org/wiki/Legendre_polynomials#Orthogonality_and_completeness
