# Limit of Knuth's sums at a fixed load factor

Let $r$ be a natural number and $0 \le \alpha < 1$. If $n_N / N \to \alpha$ as $N \to \infty$,
then [Knuth's sums](knuth-e.md) satisfy

$$E_r(N, n_N + 1) \longrightarrow \frac{1}{(1 - \alpha)^{r+1}} = \sum_{j \ge 0} \binom{r + j}{r}\alpha^j .$$

This is the claim of Section 8 of Knuth's 1963 note that the approximation
$E_r(N, k) \approx (1-\alpha)^{-(r+1)}$, with $\alpha = (k-1)/N$, becomes exact as $N \to \infty$
for fixed $\alpha$. The proof is dominated convergence for series (Tannery's theorem): the $j$-th
term $\binom{r+j}{r}\prod_{i<j}(n_N - i)/N$ tends to $\binom{r+j}{r}\alpha^j$ and is eventually
bounded by $\binom{r+j}{r}\beta^j$ for a fixed $\beta$ with $\alpha < \beta < 1$. For a
half-full table, $n_N = \lfloor N/2 \rfloor$ and $\alpha = 1/2$, it gives $E_1 \to 4$.

With $r = 1$ and $r = 0$, this turns Knuth's exact formulas
[for insertions](insertion-cost-eq.md) and [for successful searches](successful-search-cost-eq.md)
into the limits $\frac12\bigl(1 + (1-\alpha)^{-2}\bigr)$ and $\frac12\bigl(1 + (1-\alpha)^{-1}\bigr)$
stated in [the unsuccessful-search limit](tendsto-insertion-cost.md) and
[the successful-search limit](tendsto-successful-search-cost.md).

## Sources

- D. E. Knuth, "Notes on 'open' addressing", 22 July 1963, typeset by H. Prodinger in 1997,
  Section 8: https://jeffe.cs.illinois.edu/teaching/datastructures/2011/notes/knuth-OALP.pdf
