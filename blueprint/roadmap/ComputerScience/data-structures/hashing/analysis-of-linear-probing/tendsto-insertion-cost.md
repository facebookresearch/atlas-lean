# Expected cost of an unsuccessful linear-probing search at a fixed load factor

Let $0 \le \alpha < 1$, and let a cyclic table of $N$ cells hold $n_N$ items, where $n_N < N$ for
all large $N$ and $n_N / N \to \alpha$. Then the [expected number of probes](insertion-cost.md) to
insert one more item, which is also the expected cost of an unsuccessful search, satisfies

$$M(N, n_N + 1) \longrightarrow \frac{1}{2}\left(1 + \frac{1}{(1 - \alpha)^2}\right)
\qquad (N \to \infty).$$

Section 8 of Knuth's 1963 note gives $\frac12\bigl(1 + (1-\alpha)^{-2}\bigr)$ with
$\alpha = (k - 1)/N$ as an approximation and an upper bound for $M(N, k)$, and says that it becomes
exact as $N \to \infty$ for fixed $\alpha$. The limit statement here is that claim; it follows
from [Theorem 2](insertion-cost-eq.md) and the [convergence of $E_1$](tendsto-knuth-e.md) to
$(1-\alpha)^{-2}$. The hypotheses hold for instance with $\alpha = 0$ and $n_N = 0$, where the
cost is $1$ for every positive $N$.

The restriction $\alpha < 1$ matters: entering the last item into a table with one empty
cell costs $M(N, N) = (N + 1)/2$ probes on average (Section 8 of the note), which is unbounded.

## Informally uses

- [Knuth's exact mean insertion cost for linear probing](insertion-cost-eq.md): the exact formula
  whose limit is taken.
- [Limit of Knuth's sums at a fixed load factor](tendsto-knuth-e.md): the limit of $E_1$.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 8: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
