# Letter counts of the Hofstadter word as cardinalities

Let $x_k$ be the fixed point,
starting with $k$, of the substitution sending the letter $k$ to $k\,1$ and every other letter
$i$ to $i + 1$, and write $x_k[j]$ for its letter at index $j$. For every predicate $P$ on letters
and every $n$, the number $C_k^{(P)}(n)$ of letters satisfying $P$ in the prefix
$x_k[0] \cdots x_k[n-1]$ equals the number of indices $j < n$ with $P(x_k[j])$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Section 4.
