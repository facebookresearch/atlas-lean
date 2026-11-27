# Syndrome decoding

Let $H$ be a $\rho \times \iota$ parity-check matrix over a field $F$, with $\iota$ finite, and let $T$ be a
table assigning an error pattern $T(s) \in F^\iota$ to every syndrome $s \in F^\rho$. Syndrome decoding with $T$
sends a received word $y \in F^\iota$ to $y - T(Hy)$: it subtracts the error pattern that the table assigns to
the syndrome of $y$.
