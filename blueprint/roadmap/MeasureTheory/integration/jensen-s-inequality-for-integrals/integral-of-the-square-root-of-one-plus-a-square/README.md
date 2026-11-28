# Two-sided bound for the integral of the square root of one plus a square

Let $\mu$ be a probability measure and $h \ge 0$ a measurable function with
$A = \int h \, d\mu < \infty$. Then

$$\sqrt{1 + A^2} \le \int \sqrt{1 + h^2}\, d\mu \le 1 + A.$$

## Idea

The function $t \mapsto \sqrt{1 + t^2}$ is convex, so Jensen's inequality for the probability
measure $\mu$ gives the lower bound, and the pointwise inequality $\sqrt{1 + t^2} \le 1 + t$ for
$t \ge 0$ gives the upper one. For Lebesgue measure on $[0, 1]$ and $h = |F'|$, with $F$ absolutely
continuous, the middle term is the length of the graph of $F$, and the lower bound says that the
graph is at least as long as the segment joining its endpoints.

## Statements

- [Two-sided bound for the integral of the square root of one plus a square](sqrt-one-add-sq-integral-le-and-le-one-a.md)

## Background

- [Jensen's inequality](../jensen-s-inequality/README.md): gives the lower bound
