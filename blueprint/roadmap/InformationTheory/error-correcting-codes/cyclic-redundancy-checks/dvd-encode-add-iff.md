# CRC detection criterion

Let $F$ be a field, let $g$, $m$ and $e$ be polynomials over
$F$, and let $c$ be the CRC encoding of $m$ with generator $g$. Then $g$ divides $c + e$ if and
only if $g$ divides $e$: a codeword plus an error pattern passes the check exactly when $g$
divides the error. For a nonzero $g$, the [CRC codec](../hamming-7-4-code/hamming-crc-and-reed-solomon-codec-instances/encoding-2.md) therefore rejects the coefficient list of $c + e$ exactly when $g$ does not divide $e$.
