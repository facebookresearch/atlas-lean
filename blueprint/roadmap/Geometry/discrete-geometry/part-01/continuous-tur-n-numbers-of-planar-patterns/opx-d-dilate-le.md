# Dilation bound for the d-dimensional continuous Turán number

Let $d$ be a natural
number, let $P \subseteq \mathbb{R}^d$ be finite and let $c_1, c_2, q, n$ be real numbers with
$c_1 > 0$, $q > 1$ and $n > 0$. Suppose that for every coordinate $i$ and all $p, p' \in P$ with
$p_i < p'_i$ such that no $r \in P$ has $p_i < r_i < p'_i$, we have
$c_1 \le p'_i - p_i \le c_2$. Let $qP = \{q p : p \in P\}$ and
$m = \lceil q c_2 / c_1 \rceil + 1$. Then the $d$-dimensional continuous Turán number
$\mathrm{opx}$ satisfies

$$
\mathrm{opx}(n, qP, d) \le
m^d \, \mathrm{opx}(\lceil \lceil n / c_1 \rceil / m \rceil \, c_1, P, d).
$$

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Lemma 5.10.
