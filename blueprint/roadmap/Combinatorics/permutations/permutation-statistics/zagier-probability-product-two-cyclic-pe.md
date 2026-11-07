# Zagier's formula for products of two cyclic permutations

Let $n$ and $k$ be integers
with $n \ge 1$ and $1 \le k \le n$. Call a permutation of an $n$-element set cyclic when it has
exactly one cycle, fixed points counted as cycles. Write $c(n+1, k)$ for the unsigned Stirling
number of the first kind, the number of permutations of $n + 1$ elements with exactly $k$
cycles. If $\sigma$ and $\tau$ are chosen independently and uniformly among the cyclic
permutations of an $n$-element set, then the probability that $\sigma\tau$ has exactly $k$
cycles, fixed points included, is

$$\frac{1 + (-1)^{n-k}}{(n+1)!} \, c(n+1, k).$$

Proof: We formalize the plane-permutation transposition and reflection bijections of
Chen and Reidys, arXiv:1502.07674, lines 786-1074, and their specialization to Zagier's
recurrence, lines 1167-1370. A generating-polynomial coefficient identity supplies the
matching Stirling recurrence; descending induction on the cycle count finishes.

## Sources

- R. Cori and G. Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer Sequences 28 (2025), Article 25.3.3, Theorem [Zagier], lines 351-359, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Hetyei/hetyei2.tex>, quoting D. Zagier.
