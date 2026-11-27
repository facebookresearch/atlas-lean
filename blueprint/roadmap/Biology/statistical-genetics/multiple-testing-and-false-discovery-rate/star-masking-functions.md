# Accumulation and masking functions for STAR

An **accumulation function** is a non-decreasing bounded $h:[0,1]\to[0,\infty)$ with $\int_0^1 h(p)\,dp = 1$. A **masking function** for $h$ is a measurable $g:[0,1]\to[0,1]$ such that, for $u \sim \mathrm{Unif}[0,1]$,

$$\mathbb{E}[h(u) \mid g(u)] = \mathbb{E}[h(u)] = 1 \quad \text{almost surely}. \tag{2}$$

**Proposition (conservative nulls).** If $(h,g)$ satisfy (2) and a null $p$-value $p$ has a non-decreasing density on $[0,1]$, then $\mathbb{E}[h(p) \mid g(p)] \ge 1$ almost surely.

**Theorem (construction of $g$).** Let $h$ be a non-negative non-decreasing function with $\int_0^1 h = 1$, and set $H(p) = \int_0^p \{h(x)-1\}\,dx$. Then

1. there is a continuous, strictly decreasing function $s:[0,1]\to[0,1]$, differentiable outside a Lebesgue-null set, with $H(s(p)) = H(p)$, $s(0) = 1$, $s(1) = 0$;
2. $g(p) = \min\{p, s(p)\}$ satisfies (2).

Example: $h(p) = 2\,\mathbf 1\{p \ge 1/2\}$ gives $s(p) = 1-p$ and $g(p) = \min\{p, 1-p\}$; a masked value $g(p) = q < 1/2$ leaves exactly the two candidates $p \in \{q, 1-q\}$.

## Expansion

$H$ is convex (its derivative $h-1$ is non-decreasing) with $H(0) = H(1) = 0$, so it decreases then increases and each level set in its range has one point on each side of the minimizer; $s$ maps one to the other. Conditional on $g(u) = q$, $u$ sits at $q$ or $s(q)$ with probabilities proportional to $1$ and $|s'(q)|$, and $H(s(q)) = H(q)$ differentiated gives $(h(s(q))-1)s'(q) = h(q)-1$, which is exactly the statement that the conditional mean of $h$ is $1$. A non-decreasing null density tilts mass toward the larger point $s(q)$, where $h$ is larger, giving the proposition.

## Sources

- Lihua Lei, Aaditya Ramdas and William Fithian, "A general interactive framework for false discovery rate control under structural constraints", Biometrika (2020), <https://doi.org/10.1093/biomet/asaa064>. Section 2.1, Eq. (2) and Proposition 1; Section 2.3, Theorem 2.
