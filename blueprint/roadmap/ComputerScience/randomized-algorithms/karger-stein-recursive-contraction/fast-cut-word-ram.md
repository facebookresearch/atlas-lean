# Karger-Stein FastCut on the randomized word RAM

There is a randomized word-RAM program that, given an $n$-vertex weighted multigraph ($n \ge 2$) by its symmetric weight matrix, runs one FastCut recursion tree with an explicit stack and on every run halts within $2500\, n^2 (\lfloor \log_2 n \rfloor + 2)$ instructions using at most $6n^2$ random draws, always outputs the weight of a genuine nontrivial cut (hence at least the minimum cut), and outputs the minimum cut weight with probability at least $1/(\lfloor \log_2 n \rfloor + 15)$. Repeating $O(\log^2 n)$ times gives a minimum cut with high probability in $O(n^2 \log^3 n)$ time.

## Depends on

- [The Karger-Stein FastCut recursion](fast-cut-recursion.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)

## Proof depends on

- [Success probability of FastCut](fast-cut-success-probability.md)

## Sources

- D. R. Karger and C. Stein, "A New Approach to the Minimum Cut Problem", Journal of the ACM 43(4), 1996.
