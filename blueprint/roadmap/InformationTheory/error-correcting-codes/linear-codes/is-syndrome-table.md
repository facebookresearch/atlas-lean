# Syndrome table correct up to a radius

Let $H$ be a $\rho \times \iota$ matrix over a field
$F$, with $\iota$ finite, and let $t$ be a natural number. A syndrome table for $H$, that is, a map
$T$ from syndromes $s \in F^\rho$ to error patterns $T(s) \in F^\iota$, is correct up to radius
$t$ when, for every word $e \in F^\iota$ of Hamming weight at most $t$, the word $T(He)$ has the
same syndrome as $e$, that is $H \, T(He) = He$, and has Hamming weight at most $t$.

This is weaker than asking for minimum-weight coset leaders, and equivalent to it inside the
radius when $2t < d$, where $d$ is the minimum distance of the code with parity-check matrix $H$
(each coset then holds at most one word of weight at most $t$). Outside the radius the table is
unconstrained, so for heavier errors the decoder's output need not even be a codeword.
