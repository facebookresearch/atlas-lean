# Hölder's inequality

Let $\mu$ be a measure on a set $X$ with a σ-algebra, and let $p, q > 1$ be real numbers with $1/p + 1/q = 1$. For
almost everywhere measurable functions $f, g \colon X \to [0, \infty]$,

$$\int_X f g \, d\mu \le \Big( \int_X f^p \, d\mu \Big)^{1/p} \Big( \int_X g^q \, d\mu \Big)^{1/q},$$

with integrals and products taken in $[0, \infty]$ and $0 \cdot \infty = 0$. This is the general form of Hölder's
inequality for measurable functions $F, G \colon X \to \mathbb{C}$: taking $f = |F|$ and $g = |G|$ gives
$\int_X |FG| \, d\mu \le \|F\|_p \, \|G\|_q$, where $\|H\|_r = \big(\int_X |H|^r \, d\mu\big)^{1/r}$.

## Idea

Young's inequality $ab \le a^p/p + b^q/q$ for $a, b \ge 0$, a consequence of the concavity of the logarithm, gives the
case $\|f\|_p = \|g\|_q = 1$ after integration; the general case follows by scaling, once the cases where a norm is $0$
or $\infty$ are set aside. For $p = q = 2$ it is the Cauchy–Schwarz inequality for integrals. Hölder's inequality is
what makes each $g \in L^q$ act on $L^p$ by $f \mapsto \int f g \, d\mu$, with norm at most $\|g\|_q$, and it is the
main step in the proof of Minkowski's inequality. The card's second statement is the case of an essentially bounded
second factor, for every $p$; for $p = 1$ and measurable complex $f$ and $g$ it gives
$\int |fg| \, d\mu \le \|f\|_1 \|g\|_\infty$.

## Statements

- [Hölder's inequality for functions with values in $[0, \infty]$](lintegral-mul-le-lp-mul-lq.md)
- [Hölder's inequality with an essentially bounded factor](e-lp-norm-le-e-lp-norm-mul-e-lp-norm-top.md): an essentially bounded second factor, for every $p$; for $p = 1$ and the product of complex numbers it gives $\int |fg| \, d\mu \le \|f\|_1 \|g\|_\infty$.

## Background

- [L^p spaces](../../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): the $L^p$ norms

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 7.9 (version read: the open-access PDF dated 12 June 2026).
