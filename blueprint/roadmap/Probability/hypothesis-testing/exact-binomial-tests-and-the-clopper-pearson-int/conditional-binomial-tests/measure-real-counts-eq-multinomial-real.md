# Cell counts of independent draws are multinomial

Let $\iota$ be a finite set of cells, $X_0, X_1, \dots$ mutually independent measurable random elements of $\iota$ on a probability space with $P(X_k = i) = p_i$ for every $k$ and $i$, and $C_i = \#\{k < n : X_k = i\}$ the cell counts of the first $n$ draws. Write $M_n(p; x) = \frac{n!}{\prod_i x_i!}\prod_i p_i^{x_i}$ if $\sum_i x_i = n$ and $M_n(p; x) = 0$ otherwise. Then $P(C = x) = M_n(p; x)$ for every $x \in \mathbb{N}^\iota$.

## Sources

- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley (1968), §VI.9.
