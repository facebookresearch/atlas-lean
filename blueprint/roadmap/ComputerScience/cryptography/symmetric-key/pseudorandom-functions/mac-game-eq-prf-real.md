# The MAC reduction in the real PRF world

Let $K$ and $R$ be finite nonempty types, let
$F \colon K \to M \to T$ be a keyed function, and let $A$ be a forger: for coins $r \in R$,
$A(r)$ is an adaptive oracle algorithm with queries in $M$, answers in $T$ and output in
$M \times T$. Then the output distribution of the existential-forgery experiment for $F$ and $A$
equals the output distribution of the real world of the PRF experiment for $F$ with the
distinguisher that, on coins $r$, runs the MAC reduction on $A(r)$ starting from the empty query
log.
