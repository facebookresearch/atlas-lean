# Zagier's formula for products of two cyclic permutations

Let $n$ and $k$ be integers
with $n \ge 1$ and $1 \le k \le n$. Call a permutation of an $n$-element set cyclic when it has
exactly one cycle, fixed points counted as cycles. Write $c(n+1, k)$ for the unsigned Stirling
number of the first kind, the number of permutations of $n + 1$ elements with exactly $k$
cycles. If $\sigma$ and $\tau$ are chosen independently and uniformly among the cyclic
permutations of an $n$-element set, then the probability that $\sigma\tau$ has exactly $k$
cycles, fixed points included, is

$$\frac{1 + (-1)^{n-k}}{(n+1)!} \, c(n+1, k).$$

Proof: the transposition and reflection bijections on plane permutations of R. X. F. Chen and
C. M. Reidys, "Plane permutations and applications to a result of Zagier–Stanley and distances
of permutations" (arXiv:1502.07674), specialized as in their proof of Zagier's result, give a
recurrence for these counts. A coefficient identity for generating polynomials supplies the
matching recurrence for the Stirling numbers, and descending induction on the number of cycles
finishes the proof.

## Sources

- Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer Sequences 28 (2025), Article 25.3.3, Theorem 4 (quoting D. Zagier), <https://cs.uwaterloo.ca/journals/JIS/VOL28/Hetyei/hetyei2.pdf>.
