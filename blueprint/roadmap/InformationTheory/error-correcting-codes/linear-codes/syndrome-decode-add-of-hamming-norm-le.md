# Syndrome decoding corrects every error of weight at most $t$

Let $H$ be a parity-check
matrix over a field $F$, let $C$ be the code with parity-check matrix $H$, let
$d \in \mathbb{N} \cup \{\infty\}$ be its minimum distance, and let $t \in \mathbb{N}$ with
$2t < d$. If a syndrome table is correct up to radius $t$ for $H$, then for every codeword
$c \in C$ and every word $e$ of Hamming weight at most $t$, syndrome decoding with this table
sends the received word $c + e$ to $c$.

The error pattern the table returns differs from the true error by a codeword of weight at most
$2t$, which must be zero.
