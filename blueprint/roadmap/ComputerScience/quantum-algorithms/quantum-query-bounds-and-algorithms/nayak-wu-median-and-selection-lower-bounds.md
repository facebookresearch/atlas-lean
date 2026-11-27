# Nayak–Wu: quantum lower bounds for approximate median and k-th smallest

Let the input be a list $X = (x_1, \dots, x_N)$ of numbers in $[0, 1]$, given by a value oracle, and let $\Delta \in [1/2, N)$ and $\varepsilon \in [1/(2N), 1)$. A **$\Delta$-approximate $k$-th smallest element** ($1 \le k \le N$) is an entry $x_i$ that is a $j$-th smallest element of $X$ for some $j$ with $k - \Delta < j < k + \Delta$; an **$\varepsilon$-approximate median** is an entry $x_i$ with $|\{j : x_j < x_i\}| < (1 + \varepsilon)N/2$ and $|\{j : x_j > x_i\}| < (1 + \varepsilon)N/2$. Every bounded-error quantum query algorithm for the first problem makes

$$\Omega\Big(\sqrt{\frac{N}{\Delta}} + \frac{\sqrt{k(N-k)}}{\Delta}\Big)$$

queries, and every bounded-error quantum query algorithm for the second makes $\Omega(1/\varepsilon)$ queries. Both bounds also hold for the relaxed problems in which the output need not be an entry of $X$, and in the comparison-tree model.

## Proof sketch

Reduce from distinguishing two weight layers of a Boolean string: for a $0/1$ list, the value of an approximate $k$-th smallest element reveals whether the number of zeros is below or above a window of width about $2\Delta$ around $k$, and the weight-layer lower bound applies to the two layers bounding that window. The median bound is the case $k = \lceil N/2 \rceil$, $\Delta = \varepsilon N/2$.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Adversary lower bounds for parity, threshold functions and majority](adversary-bounds-for-symmetric-functions.md)
- [Nayak–Wu: quantum lower bound for approximate counting](nayak-wu-approximate-counting-lower-bound.md)

## Sources

- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", STOC 1999, Section 1.2 (problem definitions), Theorem 1.5 and Corollaries 1.6 and 1.9.
