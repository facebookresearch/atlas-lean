# Sum-of-parts recurrence for the partition function

For every natural number $E$, the number $p(E)$ of integer partitions of $E$ satisfies

$$E \, p(E) = \sum_{v=1}^{E} \sum_{k=1}^{\lfloor E/v \rfloor} v \, p(E - kv).$$

Both sides count the sum of all parts of all partitions of $E$: the left side by partition, the
right side by part value $v$ and multiplicity threshold $k$.

## Sources

- P. Erdős, *On an elementary proof of some asymptotic formulas in the theory of partitions*, Ann. of Math. (2) 43 (1942), no. 3, 437–450, identity (2).
