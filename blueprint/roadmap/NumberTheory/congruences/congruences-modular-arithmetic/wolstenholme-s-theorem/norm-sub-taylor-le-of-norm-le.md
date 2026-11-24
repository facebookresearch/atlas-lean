# Higher $p$-adic mean value theorem

Let $p$ be a prime, let $|\cdot|$ be the $p$-adic
absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space over $\mathbb{Q}_p$ whose
norm is ultrametric. Let $N$ and $m$ be natural numbers with $1 \le m \le p$, let
$f(t) = \sum_{j\lt N} a_j t^j$ be a polynomial with coefficients $a_j \in B$, and let
$t, h \in \mathbb{Q}_p$ with $|t| \le 1$. Suppose that $|h| \le p^{-1/(p-m)}$ if $m < p$, that
$|h| \le p^{-1/p}$ if $m = p$, and that $C \ge 0$ is a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le C$ for every $j < N$. Then

$$\Big\| f(t+h) - \sum_{q\lt m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\| \le
\Big| \frac{h^m}{m} \Big| \, C.$$

The inner sum $\sum_{q \le j < N} \binom{j}{q} t^{j-q} a_j$ is $f^{(q)}(t)/q!$, and the least
admissible $C$ is the sup of the norms of the coefficients of $f^{(m)}$.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 1.
