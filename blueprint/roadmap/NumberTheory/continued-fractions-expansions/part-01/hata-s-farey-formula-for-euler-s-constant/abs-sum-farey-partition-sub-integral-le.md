# Riemann-sum bound for Farey partitions

Let $a, b, c, d, m$ be natural numbers with
$a > 0$, $bc = ad + 1$, $c \le d$ and $m \ge 2$. Let $A, B : \mathbb{N} \to \mathbb{N}$ satisfy
$A(1) = a$, $B(1) = b$, $A(m) = c$, $B(m) = d$ and $B(k) A(k+1) = A(k) B(k+1) + 1$ for
$1 \le k \le m - 1$, and let $\delta$ be a real number with $1/(B(k) B(k+1)) \le \delta$ for
$1 \le k \le m - 1$. Then

$$
\left| \sum_{k=1}^{m-1} \frac{A(k) B(k+1) + B(k) A(k+1)}{A(k) B(k) A(k+1) B(k+1)} -
\int_{a/b}^{c/d} \frac{2}{t} \, dt \right| \le
\left( \frac{c}{d} - \frac{a}{b} \right) \frac{b^2}{a^2} \, \delta.
$$

In words: the fractions $A(k)/B(k)$ cut the Farey interval $[a/b, c/d]$ into consecutive Farey
intervals, the $k$-th summand is $f([A(k)/B(k), A(k+1)/B(k+1)])$ with
$f([x/y, z/w]) = (xw + yz)/(xyzw)$, and $\delta$ stands for any upper bound of
$\max_k 1/(B(k) B(k+1))$.

## Sources

- Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 2, inequality (2).
