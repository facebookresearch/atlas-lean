# Skorokhod representation theorem

Let $X$ be a Polish space with its Borel $\sigma$-algebra, and let $\mu_n$ ($n \in \mathbb{N}$) and $\mu$ be probability measures on $X$ such that $\mu_n$ converges weakly to $\mu$. Write $\lambda$ for Lebesgue measure restricted to $[0, 1]$, a probability measure on $\mathbb{R}$. Then there are measurable maps $Y_n : \mathbb{R} \to X$ and $Y : \mathbb{R} \to X$ such that, under $\lambda$, each $Y_n$ has law $\mu_n$, $Y$ has law $\mu$, and $Y_n(t) \to Y(t)$ for $\lambda$-almost every $t$.

## Idea

Weak convergence is a statement about laws only; the theorem realises it as almost sure convergence of random variables with those laws on one probability space, the unit interval. On $X = \mathbb{R}$ the construction is explicit: take for $Y_n$ and $Y$ the quantile functions of $\mu_n$ and $\mu$, so that a uniform point $t$ is sent to a sample of each law. Weak convergence makes the quantile functions converge at every continuity point of the limit's quantile function, and a monotone function has only countably many discontinuities, a $\lambda$-null set. The theorem simplifies many proofs: the continuous mapping theorem follows at once, and Fatou's lemma gives $\int f \, d\mu \le \liminf \int f \, d\mu_n$ for nonnegative continuous $f$.

## Statements

- [Skorokhod representation theorem](skorokhod-representation.md)

## Background

- [Skorokhod representation on the real line](../skorokhod-representation-on-the-real-line/README.md): the real-line form, built from quantile functions

## Sources

- A. V. Skorokhod, *Limit theorems for stochastic processes*, Theory of Probability and Its Applications (1956).
