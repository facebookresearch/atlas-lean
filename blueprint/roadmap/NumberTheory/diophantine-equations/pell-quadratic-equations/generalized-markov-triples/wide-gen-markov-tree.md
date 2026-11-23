# The wide generalized Markov tree

Fix a natural number $k$. The wide $k$-generalized
Markov tree $\mathrm{WMT}(k)$ is the binary tree of triples of natural numbers with root
$(1, 1, 1)$ in which a vertex $(a, b, c)$ has left child
$(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$ and right child
$(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$, the left and right Vieta jumpings. For a path $w$,
a finite sequence of left and right steps, the vertex of $\mathrm{WMT}(k)$ at $w$ is the triple
reached from the root by taking the steps of $w$ in order; the empty path gives the root.

The quotients are divisions of natural numbers, rounded down, with division by $0$ giving $0$.

## Sources

- Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2.
