# Karger-Stein FastCut on the randomized word RAM

There is a randomized word-RAM program that, given an $n$-vertex weighted multigraph ($n \ge 2$) by its symmetric weight matrix, runs one FastCut recursion tree in $O(n^2 \log n)$ instructions, always outputs the weight of a nontrivial cut (hence at least the minimum cut weight), and outputs the minimum cut weight with probability $\Omega(1/\log n)$. Repeating it $O(\log^2 n)$ times finds a minimum cut, indeed all minimum cuts, with high probability in $O(n^2 \log^3 n)$ instructions.

## Proof sketch

Karger and Stein: one level of the recursion on $n$ super-vertices makes two contractions to $\lceil n/\sqrt 2 + 1 \rceil$ super-vertices, each in $O(n^2)$ time with the weight-matrix implementation of Section 3, so the running time satisfies $T(n) = 2T(\lceil n/\sqrt 2 + 1 \rceil) + O(n^2) = O(n^2 \log n)$ (Lemma 4.1); on the randomized word RAM each weighted choice is one $\mathrm{rand}$ draw and a binary search, so this bound holds for every run, and an explicit stack replaces the recursion. Every leaf returns the weight of a nontrivial cut and the program returns the smallest. A fixed minimum cut survives each contraction with probability at least $1/2$ (Corollary 2.3), and the success probability $p_k$ at recursion level $k$ satisfies $p_0 \ge 1/15$ and $p_{k+1} \ge p_k - p_k^2/4$; with $z_k = 4/p_k - 1$ this gives $k < z_k < 59 + 2k$, and the depth is $2\log_2 n + O(1)$, so the success probability is $\Omega(1/\log n)$ (Lemma 4.3). Repetition gives the high-probability bound (Theorem 4.4).

## Depends on

- [The Karger-Stein FastCut recursion](fast-cut-recursion.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)

## Proof depends on

- [Success probability of FastCut](fast-cut-success-probability.md)

## Sources

- D. R. Karger and C. Stein, "A New Approach to the Minimum Cut Problem", Journal of the ACM 43(4), 1996, Corollary 2.3, Section 3, Lemmas 4.1 and 4.3 and Theorem 4.4.
