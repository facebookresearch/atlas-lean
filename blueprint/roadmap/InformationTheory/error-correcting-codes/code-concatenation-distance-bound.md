# Code concatenation distance bound

Let $q$ be a prime power and $k \ge 1$, and identify $\mathbb{F}_{q^k}$ with $\mathbb{F}_q^k$ by a fixed $\mathbb{F}_q$-linear
basis. If $C_{\mathrm{out}}$ is a linear $[N, K, D]_{q^k}$ code and $C_{\mathrm{in}}$ a linear $[n, k, d]_q$ code, the
concatenated code, obtained by encoding each symbol of an outer codeword with the inner code, is a linear
$[Nn, Kk, \ge Dd]_q$ code.

Consequently (the Zyablov bound), for every prime power $q$, every $0 < \delta < 1 - 1/q$ and every $\varepsilon > 0$,
concatenating Reed–Solomon outer codes with inner linear codes on the Gilbert–Varshamov bound gives, for infinitely many
block lengths, $q$-ary linear codes of relative distance at least $\delta$ and rate at least
$\max_{0 < r < 1 - H_q(\delta + \varepsilon)} r \bigl(1 - \delta / (H_q^{-1}(1 - r) - \varepsilon)\bigr)$, where $H_q$ is the $q$-ary entropy
function, with generator matrices computable in time polynomial in the block length.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under
the dependency sections.

- Statement prerequisite: The $q$-ary entropy function and its inverse on $[0, 1 - 1/q]$.

## Depends on

- [Linear code](linear-codes/linear-code.md)
- [Minimum distance](linear-codes/min-dist.md)
- [Reed-Solomon code](reed-solomon-codes/code.md)

## Proof depends on

- [Reed-Solomon codes meet the Singleton bound](reed-solomon-codes/min-dist-code-eq-singleton.md)
- [Gilbert–Varshamov bound for linear codes](bounds-on-code-size/exists-linear-code-finrank-eq.md)

## Sources

- V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 10.1.1 and the remark
  after its proof (linearity), Section 10.2 and Theorem 10.2.1 (Zyablov bound). <https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf>
