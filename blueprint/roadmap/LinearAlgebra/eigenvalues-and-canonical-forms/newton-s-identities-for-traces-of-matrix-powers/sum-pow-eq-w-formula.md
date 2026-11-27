# A formula for sums of powers through the sums W(n, r)

Let $n$ be a natural number and $k \ge 1$ an integer. With $W(n, r) = \sum_{i=1}^{n} \left(\frac{i}{n+1}\right)^r \left(1 - \frac{i}{n+1}\right)^r$,

$$1^k + 2^k + \cdots + n^k = \frac{k (n+1)^k}{2} \sum_{r=0}^{\lfloor k/2 \rfloor} \frac{(-1)^r}{k - r} \binom{k - r}{r} W(n, r).$$

The identity holds for every $n \ge 0$; at $n = 0$ both sides are $0$.

## Sources

Peiran Ding, Yanjun Zhu and Lei Wang, "A New Formula for the Sum of Integer Powers Based on Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Theorem 2.
