# Fibonacci values and a recurrence for Schreier sets avoiding multiples

Let $u \ge 2$,
write $|D_{u,n}|$ for the number of Schreier-type sets avoiding multiples of $u$, and write $F_n$
for the Fibonacci numbers, with $F_0 = 0$ and $F_1 = 1$. For $1 \le n \le 2u - 1$,
$|D_{u,n}| = F_n$, and for $n \ge 2u$, as an identity of integers,

$$|D_{u,n}| = \sum_{i=1}^{u} (-1)^{i-1} \binom{u}{i} |D_{u,n-i}| + |D_{u,n-2u+1}|.$$

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Theorem 3.
