# Equal-input embeddability in every dimension

**Embedding problem.** A $d \times d$ Markov matrix $M$ is *embeddable* if $M = e^Q$ for a Markov generator $Q$ (nonnegative off-diagonal entries, zero row sums), i.e. if $M$ is the transition matrix of a time-homogeneous continuous-time chain. Necessary conditions: $\sigma(M) = e^{\sigma(Q)}$; $0 < \det M \le 1$ with equality only for $M = \mathbb{1}$; every eigenvalue $\lambda \ne 1$ has $|\lambda| < 1$; and each negative real eigenvalue has even algebraic multiplicity.

**Equal-input matrices.** Let $C$ have $d$ equal rows $(c_1, \dots, c_d)$ with $c_i \ge 0$ and *parameter sum* $c = c_1 + \dots + c_d$. Then $C^2 = cC$, and

$$
M_C = (1 - c)\,\mathbb{1} + C
$$

is Markov when $c \le 1 + c_i$ for all $i$; such $M_C$ (the Felsenstein, or equal-input, substitution matrices, in which the rate of $i \to j$, $i \ne j$, depends only on $j$) have spectrum $\{1, 1-c, \dots, 1-c\}$.

**Theorem.** Let $d \ge 2$.

1. $M_C$ is embeddable with an equal-input generator iff $0 \le c < 1$. Then the equal-input generator is unique: $Q = 0$ for $c = 0$, and for $0 < c < 1$

$$
Q = \log M_C = -\frac{\log(1 - c)}{c}\,(C - c\,\mathbb{1}).
$$

2. For $d$ even, $M_C$ is embeddable (with any generator) iff $0 \le c < 1$.
3. For $d$ odd there are further embeddable equal-input matrices, all with $c > 1$, for which $1 - c$ is a negative eigenvalue of even algebraic multiplicity $d - 1$.
4. The embeddable equal-input matrices with $0 \le c < 1$ form a monoid under multiplication, and the positive ones form a semigroup that is a two-sided ideal in it.

Moreover, a generator $Q$ with $Q^2 = -cQ$, $c > 0$, has $0$ as a simple eigenvalue iff $Q$ is an equal-input generator with parameter sum $c$.

## Expansion

Since $A = M_C - \mathbb{1} = C - c\mathbb{1}$ satisfies $A^2 = -cA$, the power series of $\log(\mathbb{1} + A)$ collapses to a multiple of $A$ whenever the spectral radius $c$ of $A$ is below $1$, giving the displayed generator; its off-diagonal entries $-\frac{\log(1-c)}{c} c_j$ are nonnegative. For $c \ge 1$ the eigenvalue $1 - c \le 0$ appears with multiplicity $d - 1$; for even $d$ this multiplicity is odd, contradicting the necessary condition on negative eigenvalues, so no generator of any type exists. For odd $d$ the multiplicity is even, and a negative eigenvalue can be produced by a generator with complex-conjugate eigenvalue pairs $\mu \pm i\pi$, which is how the extra cases arise.

## Sources

- M. Baake, J. Sumner, "Notes on Markov embedding", arXiv:1903.08736 (2019): Proposition 2.1 (necessary conditions), Section 4 (equal-input matrices: Fact 4.1, Proposition 4.2, Theorem 4.6, Corollaries 4.7 and 4.9, generator formula). <https://doi.org/10.48550/arXiv.1903.08736> Published version: Linear Algebra and its Applications 594 (2020) 262--299.
