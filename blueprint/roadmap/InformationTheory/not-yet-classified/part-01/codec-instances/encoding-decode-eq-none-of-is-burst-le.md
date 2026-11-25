# CRC detects short burst errors

Let $F$ be a field and $g \in F[X]$ a nonzero generator polynomial not divisible by $X$. Call $e$ a burst of length at most $L$ if $e = X^i b$ with $b(0) \ne 0$ and $\deg b < L$. For every message $m$ and every burst $e$ of length at most $\deg g$, decoding the CRC codeword of $m$ corrupted by $e$ reports an error (returns no message).
