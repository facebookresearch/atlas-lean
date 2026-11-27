# Thirty-two-approximately stable committees always exist

For every instance of committee selection with monotone preferences over committees, arbitrary positive candidate weights and every weight limit $K$, a $32$-approximately stable committee of weight at most $K$ exists. Some monotone preferences admit no $c$-approximately stable committee for any $c < 2$. Efficient computation is known only in special settings; for approval preferences and participatory budgeting it is open.

## Proof sketch

First show that a $2$-approximately stable lottery exists: a distribution over committees of weight at most $K$ such that for every committee $W'$ the expected number of voters preferring $W'$ is less than $2 \cdot \frac{s(W')}{K} \cdot n$; this follows from a minimax (LP duality) argument. Then round the lottery to a single committee by an iterative dependent rounding that is robust to every possible deviating committee simultaneously; the analysis groups candidates by weight scale and uses a concentration bound, and the losses combine to the constant $32$.

## Depends on

- [Approximately stable committee](approximately-stable-committee.md)

## Sources

- Z. Jiang, K. Munagala, K. Wang, "Approximately Stable Committee Selection", STOC 2020, arXiv:1910.14008.
