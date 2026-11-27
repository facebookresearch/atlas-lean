# Syndrome table by exhaustive search

Let $F$ be a field, $\iota$ and $\rho$ finite sets,
$H$ a $\rho \times \iota$ parity-check matrix over $F$, and $t \in \mathbb{N}$, where the words
$F^\iota$ come with a fixed enumeration. The search table sends a syndrome $s \in F^\rho$ to the
first word $e \in F^\iota$ in the enumeration with Hamming weight at most $t$ and syndrome
$He = s$, and to $0$ if there is no such word.
