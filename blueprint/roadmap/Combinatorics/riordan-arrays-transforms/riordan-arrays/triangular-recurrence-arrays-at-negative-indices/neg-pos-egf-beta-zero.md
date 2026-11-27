# Generating function of the negative-positive numbers for $\beta = \beta' = 0$

Let
$\alpha, \gamma, \alpha', \gamma'$ be integers and let $a^{NP}$ be the negative-positive numbers
for the parameters $(\alpha, 0, \gamma; \alpha', 0, \gamma')$. For every $n \ge 0$, in the ring
$\mathbb{Q}[[u]]$ of formal power series,

$$
\sum_{k \ge 0} a^{NP}_{-n,k} u^k =
\Bigl(\prod_{j=0}^{n-1} \bigl((\gamma - j\alpha) + (\gamma' - j\alpha') u\bigr)\Bigr)^{-1},
$$

where the inverse of a power series with constant term $0$ is taken to be $0$.

Coefficientwise in $x^n/n!$ this is Theorem 1, which says that the exponential generating
function $\bar F(u, x) = \sum_{n,k \ge 0} a^{NP}_{-n,k} u^k x^n/n!$ equals the hypergeometric
series ${}_0F_1(-; b; -x/(\alpha + \alpha' u))$
with $b = -(\gamma + \gamma' u)/(\alpha + \alpha' u)$, and $e^{x/(\gamma + \gamma' u)}$ when
$\alpha = \alpha' = 0$: the rising factorial $b^{\overline{n}} = b(b+1)\cdots(b+n-1)$ satisfies
$b^{\overline{n}} (-(\alpha + \alpha' u))^n =
\prod_{j\lt n} (\gamma + \gamma' u - j(\alpha + \alpha' u))$. The paper's existence hypothesis
($\gamma - j\alpha \ne 0$ for all $j$) is not needed: a zero divisor makes both sides $0$ from
that row on.

## Sources

- Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Theorem 1.
