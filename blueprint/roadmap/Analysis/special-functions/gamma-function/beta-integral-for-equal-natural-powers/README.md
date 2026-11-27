# Beta integral for equal natural powers

For every natural number $r$, including $r = 0$,

$$\int_0^1 x^r (1 - x)^r \, dx = \frac{1}{(2r + 1) \binom{2r}{r}}.$$

## Idea

The integral is the [beta integral](../gamma-beta-relation.md) $B(r + 1, r + 1) = \frac{(r!)^2}{(2r + 1)!}$, and $\frac{(r!)^2}{(2r+1)!} = \frac{1}{(2r + 1) \binom{2r}{r}}$. It can be proved by integrating by parts $r$ times, each time moving a power from $(1 - x)$ to $x$. For $r = 1$ it gives $\int_0^1 x(1 - x)\,dx = \frac{1}{6}$. For positive $r$ it is Lemma 3 of Ding, Zhu and Wang's study of sums of integer powers, whose Theorem 1 is a trace formula for powers of $2 \times 2$ matrices; for $r = 0$ the integrand is constant and both sides are $1$.

## Statements

- [Integral of $x^r (1 - x)^r$ over $(0, 1)$](integral-pow-one-sub-pow.md)
