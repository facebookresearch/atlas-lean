# Expected cost of a successful linear-probing search at a fixed load factor

Let $0 \le \alpha < 1$, and let a cyclic table of $N$ cells hold $n_N$ items, where
$1 \le n_N \le N$ for all large $N$ and $n_N / N \to \alpha$. Then the
[average cost of a successful search](successful-search-cost.md) satisfies

$$T(N, n_N) \longrightarrow \frac{1}{2}\left(1 + \frac{1}{1 - \alpha}\right)
\qquad (N \to \infty).$$

Section 8 of Knuth's 1963 note gives $\frac12\bigl(1 + (1-\alpha)^{-1}\bigr)$ as an approximation
and upper bound for $T(N, k)$, exact as $N \to \infty$ for fixed $\alpha$. It notes that Schay and
Spruth (1962) obtained the same expression with $\alpha = k/N$ by a Poisson approximation. In the
full case the note conjectures $T(N, N) = \sqrt{\pi N / 8} + O(1)$ from its table (a
handwritten annotation on the typeset note records a proof dated 1965); that case is not covered
here.

## Informally uses

- [Knuth's exact mean successful-search cost for linear probing](successful-search-cost-eq.md):
  the exact formula whose limit is taken.
- [Limit of Knuth's sums at a fixed load factor](tendsto-knuth-e.md): the limit of $E_0$, applied
  with $n_N - 1$ items.

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Sections 8 and 9: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
