# Iterated partial sums

Let $M$ be an additive commutative monoid and let
$a = (a_n)_{n \ge 0}$ be a sequence in $M$. For $k, m \ge 0$, the $k$-fold iterated partial sum
$P^{(k)}(a)(m)$ is the seeded partial sum $t^s_{k,m}$ of $a$ for the zero seed sequence $s = 0$.
Thus $P^{(0)}(a)(m) = a_m$ and $P^{(k+1)}(a)(m) = \sum_{i\lt m} P^{(k)}(a)(i)$.

## Sources

- Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (definition of `P^{(k)}`).
