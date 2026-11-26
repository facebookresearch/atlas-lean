# Failure probability of the LSH index

For the LSH index with $L$ independent tables whose hash collides on near pairs with probability at least $P_1$ and on far pairs with probability at most $P_2$, every answer returned is within distance $cr$ of the query, and for every query $q$ with a point of $P$ within distance $r$,

$$
\Pr[\text{failure}] \le (1 - P_1)^L + \frac{L\, |P|\, P_2}{T}.
$$

With AND-composition of $k$ functions this is $(1 - p_1^k)^L + L |P| p_2^k / T$, and with the standard parameters it is at most $e^{-1} + 1/3$. The bound holds for seeds drawn from arbitrary probability measures provided collision events are measurable.

## Proof sketch

A failure means either the near point collides with $q$ in no table, which has probability at most $(1 - P_1)^L$, or the first $T$ candidates are all far. The expected number of far candidates over $L$ tables is at most $L |P| P_2$, so by Markov's inequality there are at least $T$ of them with probability at most $L|P|P_2 / T$. With $k = \lceil \log_{1/p_2} |P| \rceil$ we have $|P| p_2^k \le 1$ and $p_1^k \ge p_1 |P|^{-\rho}$, so $L p_1^k \ge 1$ and $(1 - p_1^k)^L \le e^{-1}$.

## Depends on

- [Locality-sensitive hashing index with L tables and a stopping rule](lsh-index.md)

## Proof depends on

- [Amplification of locality-sensitive families by banding](../locality-sensitive-hashing/amplification-of-locality-sensitive-families-by.md)

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
