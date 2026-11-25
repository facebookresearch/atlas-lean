# Sign of the Robertson–Spärck Jones idf

For a collection of $N \ge 1$ documents and a term with document frequency $0 \le \mathrm{df} \le N$, the Robertson–Spärck Jones weight
$\mathrm{idf}_{\mathrm{RSJ}} = \log \frac{N - \mathrm{df} + 1/2}{\mathrm{df} + 1/2}$ is negative if and only if $\mathrm{df} > N/2$, zero if and only if $\mathrm{df} = N/2$, and
equals $-\log(2N + 1) < 0$ when the term occurs in every document; the classical weight $\log(N/\mathrm{df})$ is $0$ at $\mathrm{df} = N$ and positive for
$1 \le \mathrm{df} < N$.

## Proof

The ratio $\frac{N - \mathrm{df} + 1/2}{\mathrm{df} + 1/2}$ is below $1$ exactly when $N - \mathrm{df} < \mathrm{df}$; at $\mathrm{df} = N$ it is $\frac{1/2}{N + 1/2} = \frac{1}{2N+1}$.

## Depends on

- [Binary independence model and BM25 term weighting](binary-independence-model-and-bm25-term-weighting.md)

## Sources

- S. Robertson and H. Zaragoza, *The probabilistic relevance framework: BM25 and beyond*, Foundations and Trends in Information Retrieval 3(4) (2009), Section 3.1, Equation (3.3), p. 349 (the Robertson/Spärck Jones weight without relevance information).
