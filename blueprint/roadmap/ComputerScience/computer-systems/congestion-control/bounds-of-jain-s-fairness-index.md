# Bounds of Jain's fairness index

For $n \ge 1$ and an allocation $x \in [0, \infty)^n \setminus \{0\}$, [Jain's fairness index](jain-s-fairness-index.md) satisfies:

1. $1/n \le F(x) \le 1$, with $F(x) = 1$ exactly when all $x_i$ are equal and $F(x) = 1/n$ exactly when a single user has a positive share;
2. $F(cx) = F(x)$ for every $c > 0$ (independence of scale);
3. $F$ is continuous on $[0, \infty)^n \setminus \{0\}$;
4. if $k$ of the $n$ users share the resource equally and the remaining $n - k$ receive nothing, $F(x) = k/n$.

The upper bound is the Cauchy–Schwarz inequality $(\sum_i x_i)^2 \le n \sum_i x_i^2$; the lower bound follows from $\sum_i x_i^2 \le (\sum_i x_i)^2$ for nonnegative $x_i$.

## Depends on

- [Jain's fairness index](jain-s-fairness-index.md)

## Sources

- D.-M. Chiu and R. Jain, "Analysis of the increase and decrease algorithms for congestion avoidance in computer networks", *Computer Networks and ISDN Systems* 17(1):1–14, 1989, Section 1.4, properties (a)–(d) of the fairness index.
