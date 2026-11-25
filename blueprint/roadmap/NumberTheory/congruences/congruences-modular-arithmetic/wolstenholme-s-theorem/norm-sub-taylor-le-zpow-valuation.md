# Congruence form of the higher $p$-adic mean value theorem

Let $p$ be a prime, let
$|\cdot|$ be the $p$-adic absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space
over $\mathbb{Q}_p$ whose norm is ultrametric. Let $N$ and $m$ be natural numbers with
$1 \le m \le p$, let $f(t) = \sum_{j\lt N} a_j t^j$ with $a_j \in B$, let $t, h \in \mathbb{Q}_p$
with $|t| \le 1$, and let $w$ be a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le p^{-w}$ for every $j < N$. Write

$$R = \Big\| f(t+h) - \sum_{q\lt m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\|$$

and let $v_p(h)$ be the $p$-adic valuation of $h$, taken to be $0$ when $h = 0$. Then
$R \le p^{-(m v_p(h) + w)}$ if $m < p$ and $v_p(h) \ge 1/(p-m)$;
$R \le p^{-(p v_p(h) + w - 1)}$ if $m = p$ and $v_p(h) \ge 1/p$; and $R = 0$ if $h = 0$.

Reading a congruence modulo $p^v$ in $B$ as norm at most $p^{-v}$, the first two bounds say
$f(t+h) \equiv \sum_{q\lt m} f^{(q)}(t) h^q / q!$ modulo $p^{m v_p(h) + w}$ and
$p^{p v_p(h) + w - 1}$ respectively.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2.
