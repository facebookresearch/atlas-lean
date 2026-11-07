# Effect of the seed on seeded partial sums

Let $R$ be a commutative ring, let
$a = (a_n)_{n \ge 0}$ and $b = (b_n)_{n \ge 0}$ be sequences in $R$, and write $t^b_{k,n}$ for
the seeded partial sums of $a$ with seed sequence $b$ and $t^0_{k,n}$ for those with the zero
seed sequence. Then for all $k, n \ge 0$,
$t^b_{k,n} - t^0_{k,n} = \sum_{i\lt k} \binom{n}{i} b_{k-1-i}$, where the binomial coefficients
are read as elements of $R$.

## Sources

- Hùng Việt Chu and Zachary Louis Vasseur, *Weighted Schreier-type Sets and the Fibonacci Sequence*, The Fibonacci Quarterly 62 (2024), no. 4, Lemma 3.2 (`fq-2024-chu08302024rev-lem-3.2`).
