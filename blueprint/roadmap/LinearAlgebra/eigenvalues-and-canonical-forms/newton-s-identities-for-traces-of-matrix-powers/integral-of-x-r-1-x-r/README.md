# An integral of $x^r (1 - x)^r$

For every natural number $r$, including $r = 0$,

$$\int_0^1 x^r (1 - x)^r \, dx = \frac{1}{(2r + 1) \binom{2r}{r}}.$$

## Idea

The integral is the beta integral $B(r + 1, r + 1) = \frac{(r!)^2}{(2r + 1)!}$, and $\frac{(r!)^2}{(2r+1)!} = \frac{1}{(2r + 1) \binom{2r}{r}}$. It can be proved by integrating by parts $r$ times, each time moving a power from $(1 - x)$ to $x$. For $r = 1$ it gives $\int_0^1 x(1 - x)\,dx = \frac{1}{6}$. It comes from the same study of sums of integer powers as the trace formula for $2 \times 2$ matrices, which is why it sits in this topic.

## Statements

- [Integral of $x^r (1 - x)^r$ over $(0, 1)$](integral-pow-one-sub-pow.md)
