# The binomial family is TP2

Let $n, a, a'$ be natural numbers with $a \le a'$ and $p, p'$ real with $0 \le p \le p' \le 1$. Then

$$B(a \mid n, p')\, B(a' \mid n, p) \le B(a' \mid n, p')\, B(a \mid n, p),$$

where $B(i \mid n, p) = \binom{n}{i} p^i (1 - p)^{n - i}$ (with $\binom{n}{i} = 0$ for $i > n$ and truncated subtraction $n - i$).
