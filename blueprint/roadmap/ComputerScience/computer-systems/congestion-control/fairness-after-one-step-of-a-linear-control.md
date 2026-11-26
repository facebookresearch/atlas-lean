# Fairness after one step of a linear control

Let $x \in [0, \infty)^n$ with $x \ne 0$, and let $a \ge 0$ and $b > 0$, so that one step of a [linear control](linear-increase-decrease-controls.md) maps $x_i$ to $a + bx_i$ for every user. With $c = a/b$,

$$
F(a + bx) = F(c + x) = F(x) + \bigl(1 - F(x)\bigr)\left( 1 - \frac{\sum_i x_i^2}{\sum_i (c + x_i)^2} \right),
$$

where $F$ is [Jain's fairness index](jain-s-fairness-index.md). Hence $F(a + bx) \ge F(x)$, with equality exactly when $a = 0$ or $F(x) = 1$: a step with a positive additive component strictly increases the fairness of an unfair allocation, while a purely multiplicative step leaves it unchanged.

The identity follows by writing $S_1 = \sum_i x_i$, $S_2 = \sum_i x_i^2$ and $Q = \sum_i (c + x_i)^2 = nc^2 + 2cS_1 + S_2$; then $1 - (1 - F(x))S_2/Q = (nc + S_1)^2/(nQ) = F(c + x)$, and $F(a + bx) = F(c + x)$ by independence of scale.

## Depends on

- [Jain's fairness index](jain-s-fairness-index.md)
- [Linear increase/decrease controls](linear-increase-decrease-controls.md)

## Proof depends on

- [Bounds of Jain's fairness index](bounds-of-jain-s-fairness-index.md): independence of scale, and $F(x) \le 1$.

## Sources

- D.-M. Chiu and R. Jain, "Analysis of the increase and decrease algorithms for congestion avoidance in computer networks", *Computer Networks and ISDN Systems* 17(1):1–14, 1989, Section 2.3, equations (4)–(7) and the discussion following them.
