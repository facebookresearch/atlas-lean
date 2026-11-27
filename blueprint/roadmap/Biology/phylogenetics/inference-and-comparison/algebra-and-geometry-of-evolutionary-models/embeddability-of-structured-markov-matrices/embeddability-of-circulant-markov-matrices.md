# Embeddability of circulant Markov matrices

**Circulant matrices.** Let $P$ be the $d \times d$ cyclic permutation matrix and $K_j = P^j - \mathbb{1}$ for $j \in \{1, \dots, d-1\}$; each $K_j$ is a Markov generator, $K_i K_j = K_{i+j} - K_i - K_j$, and the $K_j$ span a commutative algebra of dimension $d - 1$. The circulant Markov matrices are exactly the convex combinations of $\mathbb{1}, P, \dots, P^{d-1}$; they are doubly stochastic, form a $(d-1)$-simplex and a monoid, and can be written

$$
M(x_1, \dots, x_{d-1}) = \mathbb{1} + \sum_{r=1}^{d-1} x_r K_r, \qquad x_r \ge 0,\quad x_1 + \dots + x_{d-1} \le 1.
$$

A Markov matrix is *embeddable* if it equals $e^Q$ for a Markov generator $Q$, and *circulant-embeddable* if $Q$ can be taken circulant.

**Theorem.**

1. Every embeddable circulant Markov matrix is circulant-embeddable; if its centraliser is Abelian, every generator $Q$ with $e^Q = M$ is circulant.
2. $M(x_1, \dots, x_{d-1})$ is embeddable iff there are $\alpha_1, \dots, \alpha_{d-1} \ge 0$ with

$$
x_r\, e^{\alpha_1 + \dots + \alpha_{d-1}} = a_r(\alpha_1, \dots, \alpha_{d-1}) \quad (1 \le r \le d-1), \qquad a_r = \sum_{\substack{m_1, \dots, m_{d-1} \in \{0, \dots, d-1\} \\ \sum_i i\, m_i \equiv r \ (\mathrm{mod}\ d)}} \ \prod_{j=1}^{d-1} f^{(d)}_{m_j}(\alpha_j),
$$

   where $f^{(d)}_m(t) = \sum_{\ell \ge 0} t^{\ell d + m}/(\ell d + m)!$; then $Q = \sum_i \alpha_i K_i$.
3. For $d = 3$, $M(a, b) = \mathbb{1} + aK_1 + bK_2$ is embeddable iff it is circulant-embeddable iff $(a,b)$ lies in an explicit closed region bounded by two parametrized curves, excluding the point $(1/3, 1/3)$ (the matrix with all entries $1/3$, which is not embeddable). For $d = 4$ the analogous region is bounded by three explicit surface sheets.

## Proof depends on

- [Equal-input embeddability in every dimension](equal-input-embeddability-in-every-dimension.md)

## Expansion

Circulant matrices are polynomials in $P$, so a circulant generator $Q = \sum_i \alpha_i K_i$ has $\alpha_i \ge 0$ exactly when it is Markov. Since the $K_i$ commute, $e^Q = e^{-\sum_i \alpha_i} \prod_i e^{\alpha_i P^i}$, and $e^{\alpha P^i} = \sum_\ell f^{(d)}_\ell(\alpha) P^{i\ell}$ by splitting the exponential series according to the residue of the exponent mod $d$ (these $f^{(d)}_m$ are the components of $e^t$ along the characters of the cyclic group). Collecting powers of $P$ gives the coefficients $a_r$. Part 1 is an instance of the stable-property principle: if a property holds for $A = M - \mathbb{1}$ and all generators in its algebra, is closed under limits, and $M$ can be approximated by cyclic embeddable matrices with the property, then $M$ has a generator with that property, and when $M$ is cyclic (Abelian centraliser) every generator of $M$ has it; being circulant is such a property.

## Sources

- M. Baake, J. Sumner, "Notes on Markov embedding", arXiv:1903.08736 (2019): Section 2 (Facts 2.10, 2.14, Definition 2.12, Proposition 2.13 on stable properties), Section 5 (Fact 5.1, Corollary 5.2, Fact 5.3, Theorems 5.4, 5.6 and 5.7, coefficient formula for $a_r$). <https://doi.org/10.48550/arXiv.1903.08736> Published version: Linear Algebra and its Applications 594 (2020) 262--299.
