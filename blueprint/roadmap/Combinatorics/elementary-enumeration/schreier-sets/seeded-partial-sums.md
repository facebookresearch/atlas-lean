# Seeded partial sums

Let $M$ be an additive commutative monoid, and let
$s = (s_n)_{n \ge 0}$ (the seed sequence) and $a = (a_n)_{n \ge 0}$ be sequences in $M$. The
seeded partial sums $t^s_{k,n}$, for $k, n \ge 0$, are defined by recursion on $k$:
$t^s_{0,n} = a_n$ and $t^s_{k+1,n} = s_k + \sum_{i\lt n} t^s_{k,i}$.

## Sources

- Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Section 3 (partial sum operator `P_b` and the sequences `t^s_{k,n}`).
