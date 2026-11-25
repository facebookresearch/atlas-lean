# A nonnegative derivative makes a function nondecreasing on a half-line

Let $a$ be real and let $f, f' : \mathbb{R} \to \mathbb{R}$ be such that $f$ has the two-sided
derivative $f'(t)$ at every $t \ge a$, and $f'(t) \ge 0$ for every $t > a$. Then $f$ is
nondecreasing on $[a, \infty)$: $f(s) \le f(t)$ whenever $a \le s \le t$.

The sign of $f'(a)$ is not used; the derivative at $a$ is only needed for continuity of $f$ at $a$.
Applied to $-S$ and to $R$ it gives that [susceptibles decrease](antitone-on-susceptible.md) and
[removed individuals accumulate](monotone-on-removed.md) along an SIR solution.
