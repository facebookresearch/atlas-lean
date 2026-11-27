# Thirty-two-approximately stable committees always exist

For every instance of committee selection with monotone preferences over committees, arbitrary positive candidate weights and every weight limit $K > 0$, a $32$-approximately stable committee of weight at most $K$ exists. Conversely, for every $c$ with $1 \le c < 2$ there is an instance, depending on $c$, that admits no $c$-approximately stable committee of weight at most $K$; the instances have unit candidate weights, an integral weight limit $K \ge 1$ and ranking preferences, in which each voter compares committees by her favorite member. Efficient computation is known only in special settings; for approval preferences and participatory budgeting it is open.

## Proof sketch

First show that a $2$-approximately stable lottery exists: a distribution over committees of weight at most $K$ such that for every nonempty committee $W'$ the expected number of voters preferring $W'$ is less than $2 \cdot \frac{s(W')}{K} \cdot n$; this follows from a minimax (LP duality) argument. Then round the lottery to a single committee by an iterative dependent rounding that is robust to every possible nonempty deviating committee simultaneously; the analysis groups candidates by weight scale and uses a concentration bound, and the losses combine to the constant $32$.

## Depends on

- [Approximately stable committee](approximately-stable-committee.md)

## Sources

- Z. Jiang, K. Munagala, K. Wang, "Approximately Stable Committee Selection", STOC 2020, arXiv:1910.14008.
