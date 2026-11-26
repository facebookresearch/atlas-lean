# Funnelsort

*Funnelsort* sorts an array of $N$ elements by splitting it into $N^{1/3}$ contiguous segments of size $N^{2/3}$, sorting each segment recursively, and merging the $N^{1/3}$ sorted segments with an $N^{1/3}$-merger, which produces all $N$ outputs in one invocation. It uses no knowledge of $Z$ or $L$.

## Depends on

- [The k-merger (funnel)](k-merger.md)

## Sources

- Matteo Frigo, Charles E. Leiserson, Harald Prokop, Sridhar Ramachandran, "Cache-Oblivious Algorithms", FOCS (1999); ACM Transactions on Algorithms 8(1) (2012).
