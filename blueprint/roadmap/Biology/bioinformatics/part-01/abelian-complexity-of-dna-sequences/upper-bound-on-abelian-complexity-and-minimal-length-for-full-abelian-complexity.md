# Upper bound on abelian complexity and minimal length for full abelian complexity

Let $\Omega = \{A, C, G, T\}$ and let $\omega$ be a finite DNA word over $\Omega$. The subword complexity is $p_\omega(n) = \#\{\mu : \mu \text{ a factor of } \omega,\ |\mu| = n\}$, with $1 \le p_\omega(n) \le 4^n$; for every $n \ge 0$ there is a word of length $4^n + n - 1$ with $p_\omega(i) = 4^i$ for $i = 1, \dots, n$ (a de Bruijn-type word). The Parikh vector of a word $\mu$ is

$$\psi(\mu) = \left(|\mu|_A, |\mu|_C, |\mu|_G, |\mu|_T\right),$$

and the abelian complexity of $\omega$ is

$$\rho^{ab}_\omega(n) = \#\{\psi(\mu) : \mu \text{ a factor of } \omega,\ |\mu| = n\},$$

so $1 \le \rho^{ab}_\omega(n) \le p_\omega(n)$; unlike $p_\omega$, $\rho^{ab}_\omega$ need not be monotone (for $\omega = AAGCAGTCGG$, $\rho^{ab}_\omega(2) = 7 > 5 = \rho^{ab}_\omega(3)$).

(1) **Upper bound.** For every finite word $\omega$ and $1 \le n \le |\omega|$,

$$1 \le \rho^{ab}_\omega(n) \le \binom{n+3}{3} = \frac{(n+3)(n+2)(n+1)}{6}.$$

(2) **Minimal length.** If $\rho^{ab}_\omega(i) = \binom{i+3}{3}$ for $i = 1, \dots, m$, then

$$|\omega| \ge \binom{m+3}{3} + m - 1 .$$

For a sequence of length $1000$ this gives $m_0 = 16$ as the largest window length at which full abelian complexity is possible, which motivates discarding the low-$n$ end of the profile when using abelian complexity values as features for predicting regulatory elements such as enhancers.

## Expansion

A Parikh vector of a length-$n$ word over a 4-letter alphabet is a composition of $n$ into four nonnegative parts, and there are $\binom{n+3}{3}$ of these (stars and bars), giving the bound. A word with full abelian complexity at window length $m$ has at least $\binom{m+3}{3}$ factors of length $m$, hence at least that many starting positions, so its length is at least $\binom{m+3}{3} + m - 1$. This is the abelian analogue of the length $4^n + n - 1$ needed for full subword complexity, which underlies the finite-sequence estimate of topological entropy.

## Sources

- C. Wu, J. Chen, Y. Liu and X. Hu, "Improved prediction of regulatory element using hybrid abelian complexity features with DNA sequences", *International Journal of Molecular Sciences* 20 (2019), 1704, Section 3.2, Definitions 1–2, Theorem 1 and Corollary 1; Section 3.3, Definitions 3–4; and Section 3.4, Theorems 2–3. <https://doi.org/10.3390/ijms20071704> (PMC6480087)
