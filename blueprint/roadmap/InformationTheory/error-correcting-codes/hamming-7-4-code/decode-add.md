# The decoder corrects every error of weight at most 1

For every codeword $c$ of the
Hamming code and every word $e \in \mathbb{F}_2^7$ of Hamming weight at most $1$, decoding
$c + e$ returns $c$. Taking the data bits, the [Hamming(7,4) codec](../hamming-crc-and-reed-solomon-codec-instances/encoding.md) decodes the codeword of a message $m$ plus such an $e$ to $m$.
