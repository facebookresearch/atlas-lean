# Comparison lower bounds for minimum, maximum and second largest

In the comparison model, for $n \ge 2$ distinct keys: every algorithm that finds the minimum makes at least $n - 1$ comparisons in the worst case; every algorithm that finds both the minimum and the maximum makes at least $\lceil 3n/2 \rceil - 2$ comparisons; and every algorithm that finds the second largest key makes at least $n + \lceil \log_2 n \rceil - 2$ comparisons. All three bounds are attained, by a linear scan, by pairing the keys and comparing winners and losers separately, and by a knockout tournament followed by a tournament among the keys beaten by the winner.

## Depends on

- [Comparison trees](../algorithm-analysis-models/comparison-trees.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- J. Erickson, *Algorithms*, 1st ed., 2019, <https://jeffe.cs.illinois.edu/teaching/algorithms/>
- D. E. Knuth, *The Art of Computer Programming*, vol. 3: Sorting and Searching, 2nd ed., Addison-Wesley, 1998
