# Static query count of the exponentiation recursion

For every number of steps $m$, every $n$ and all indices $\mathit{acc}, \mathit{base} < n$, the [static query count](num-queries.md) of the [exponentiation recursion](pow-prog-aux.md) with $m$ steps from accumulator index $\mathit{acc}$ and base index $\mathit{base}$ is exactly $m$.

This is a property of the syntax: no oracle or environment is involved. The length of the transcript of an actual run is the separate statement [the exponentiation recursion issues exactly $m$ queries](length-queries-of-pow-prog-aux.md).
