# A bounded integrable function is square integrable

Let $f : \mathbb{R}^d \to \mathbb{R}$ satisfy $|f| \le M$ everywhere. If $f \in L^1(\mathbb{R}^d)$,
then $f \in L^2(\mathbb{R}^d)$ and $\|f\|_2 \le M^{1/2} \|f\|_1^{1/2}$, for Lebesgue measure.

## Idea

For $d \ge 1$ the exponents on $\mathbb{R}^d$ control two different things: large values on small
sets, and small values on large sets. The function $|x|^{-a}$ near $0$ lies in $L^1$ but not $L^2$
for $d/2 \le a < d$, and $(1 + |x|)^{-a}$ lies in $L^2$ but not $L^1$ for $d/2 < a \le d$, so
neither space contains the other; for $d = 0$ the space is a single point of mass $1$ and
$L^1 = L^2$. A bound removes the first obstruction in every dimension: $|f|^2 \le M |f|$ gives the
inequality.

## Statements

- [A bounded integrable function is square integrable](mem-lp-two-and-e-lp-norm-two-le-of-bound.md)
- [$L^1(\mathbb{R}^d)$ and $L^2(\mathbb{R}^d)$ are incomparable](not-mem-lp-two-subset-one-and-not-mem-lp.md): for $d \ge 1$, an example showing that the bound is needed: a function in $L^1(\mathbb{R}^d)$ but not in $L^2(\mathbb{R}^d)$ (the page also gives one in $L^2$ but not in $L^1$).
