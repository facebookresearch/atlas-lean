# Closed form and recurrence for colored Schreier multiset counts

Let $s \ge 1$ and
$p \ge 1$, and write $|B^{(s)}_{p,n}|$ for the number of colored Schreier-type multisets. For
$1 \le n \le sp + 1$,

$$|B^{(s)}_{p,n}| = \sum_{k=1}^{\lfloor (ns+1)/(ps+1) \rfloor} \binom{(n - kp)s}{k - 1},$$

and for $n \ge sp + 2$,

$$|B^{(s)}_{p,n}| = \sum_{i=0}^{s} \binom{s}{i} \, |B^{(s)}_{p,n-1-ip}|.$$

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Theorem 2.
