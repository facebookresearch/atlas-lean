# Leftmost carrying

Let $w = w_0 w_1 \cdots w_{\ell-1}$ be a word of natural-number digits,
written most significant digit first with positions numbered from $0$, and let $k$ be the least
index with $k + 3 < \ell$ and $w_{k+1}, w_{k+2}, w_{k+3} > 0$. Leftmost carrying replaces the
block $w_k w_{k+1} w_{k+2} w_{k+3}$ by $(w_k + 1)(w_{k+1} - 1)(w_{k+2} - 1)(w_{k+3} - 1)$ and
leaves the other digits unchanged; it is undefined when there is no such $k$.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Section 6.1.
