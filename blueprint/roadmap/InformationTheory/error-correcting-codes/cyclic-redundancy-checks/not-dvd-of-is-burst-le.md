# Short bursts are detected

Let $F$ be a field, let $g$ be a polynomial over $F$ that is
not divisible by $X$, and let $L$ be a natural number with $L \le \deg g$. If a polynomial $e$
over $F$ is a burst of length at most $L$, then $g$ does not divide $e$. Taking $L = \deg g$ for a nonzero $g$, the [CRC codec](../hamming-crc-and-reed-solomon-codec-instances/encoding-2.md) rejects every codeword corrupted by a burst of length at most $\deg g$.

Write $e = X^i b$ with $b(0) \ne 0$ and $\deg b < L$. Since $X \nmid g$, $g$ is coprime to
$X^i$, so $g \mid X^i b$ would force $g \mid b$, impossible for a nonzero $b$ of smaller degree.
