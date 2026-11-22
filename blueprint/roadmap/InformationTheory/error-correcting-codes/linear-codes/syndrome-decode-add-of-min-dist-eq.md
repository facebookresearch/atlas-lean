# Syndrome decoding up to half the minimum distance

Let $H$ be a parity-check matrix over
a field $F$ such that the code $C$ with parity-check matrix $H$ has finite minimum distance $d$,
and let $t = \lfloor (d - 1)/2 \rfloor$. If a syndrome table is correct up to radius $t$ for
$H$, then for every codeword $c \in C$ and every word $e$ of Hamming weight at most $t$,
syndrome decoding with this table sends the received word $c + e$ to $c$.
