# Probability measures on the real line from distribution functions

Let $f : \mathbb{R} \to \mathbb{R}$ be non-decreasing and right-continuous, with $f(x) \to 0$ as $x \to -\infty$ and $f(x) \to 1$ as $x \to \infty$. Then the Stieltjes measure $\mu_f$ of $f$ is a probability measure on $\mathbb{R}$ with $\mu_f((a, b]) = f(b) - f(a)$ for all real $a \le b$, and every finite measure $\nu$ on $\mathbb{R}$ with $\nu((a, b]) = f(b) - f(a)$ for all real $a \le b$ equals $\mu_f$.

## Idea

Probability laws on the real line and distribution functions are the same thing. A law $\mu$ gives the function $F(x) = \mu((-\infty, x])$, which is non-decreasing, right-continuous and goes from $0$ to $1$; this theorem is the converse. For existence, one assigns the length $f(b) - f(a)$ to each half-open interval $(a, b]$ and extends it to all Borel sets; right-continuity is what makes this assignment countably additive. Uniqueness holds because the intervals $(a, b]$ are closed under intersection and generate the Borel σ-algebra, and two finite measures that agree on such a family and have the same total mass agree everywhere. For example, $f(x) = \min(\max(x, 0), 1)$ gives the uniform law on $[0, 1]$.

## Statements

- [Construction of measures on ℝ](stieltjes-measure-construction.md)
- [Construction of measures on ℝ, as unique existence](exists-unique-probability-measure-of-sti.md): unique-existence form
