# Formula and recurrence for Schreier-type multisets

Let $s, p \ge 1$, and for $n \ge 1$
let $|A^{(s)}_{p,n}|$ be the number of distinct sub-multisets $F$ of
$\{1^s, \dots, (n - 1)^s, n\}$ with $n \in F$ and $\min F \ge p|F|$, where $|F|$ counts
multiplicity. For $1 \le n \le sp + 1$,

$$|A^{(s)}_{p,n}| = \sum_{k=1}^{\lfloor (sn+1)/(sp+1) \rfloor} \binom{n - pk + k - 2}{k - 1},$$

and for $n \ge sp + 2$,

$$|A^{(s)}_{p,n}| = \sum_{i=0}^{s} |A^{(s)}_{p,n-1-ip}|.$$

In the first sum $pk \le n$, so the top $n - pk + k - 2$ is negative only for $k = 1$ and $n = p$,
where the coefficient is $\binom{-1}{0} = 1$; the natural-number subtraction gives
$\binom{0}{0} = 1$ there as well.

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Theorem 1 (`integers-2026-A53-thm-1`).
