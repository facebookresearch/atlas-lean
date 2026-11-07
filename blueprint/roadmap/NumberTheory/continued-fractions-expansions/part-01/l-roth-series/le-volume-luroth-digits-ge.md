# Lower bound for the measure of large Lüroth digit values

Let $m$ be a natural number,
let $D = [2, \infty)^m$, let $F : \mathbb{R}^m \to \mathbb{R}$ satisfy $F(x) > 0$ for every
$x \in D$, and let $M$ be a real number with
$F(x) \le M\,F(\lfloor x_1 \rfloor, \ldots, \lfloor x_m \rfloor)$ for every $x \in D$ (the
paper's condition (6)). Put
$G(y) = \int_{\{x \in D \,:\, F(x) \ge y\}} \prod_{i=1}^m x_i^{-2}\,dx$ for real $y$, let
$\lambda$ be Lebesgue measure on $\mathbb{R}$ and let $d_1(x), d_2(x), \ldots$ be the Lüroth
digits of $x$. Then for every real $y$,

$$G(My) \le \lambda\{x \in (0, 1] : F(d_1(x), \ldots, d_m(x)) \ge y\}.$$

The paper states it only at the values of the sequence in its Theorem 4, under that theorem's
hypotheses, which also require $F$ to be measurable and non-decreasing; only positivity and
condition (6) are assumed here.

## Sources

- Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 7.
